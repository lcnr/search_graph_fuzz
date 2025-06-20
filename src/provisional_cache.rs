use rand::rngs::SmallRng;
use rand::{Rng, SeedableRng};
use rustc_type_ir::search_graph::*;
use rustc_type_ir::solve::GoalSource;
use std::cell::{Cell, RefCell};
use std::fmt::Debug;
use std::iter;
use std::marker::PhantomData;
use std::mem;
use tracing::{debug, debug_span};

use crate::{random_path_kind, Index};

#[derive(Clone, Copy)]
struct Ctxt<'a> {
    cost: &'a Cell<usize>,
    graph: &'a Graph,
    cache: &'a RefCell<GlobalCache<Ctxt<'a>>>,
}

#[derive(Debug, Copy, Clone, Hash, PartialEq, Eq, PartialOrd, Ord)]
enum Res {
    Error,
    Ambig,
    Yes,
}
impl<'a> Cx for Ctxt<'a> {
    type Input = Index;
    type Result = Res;
    type DepNodeIndex = ();
    type Tracked<T: Debug + Clone> = T;
    fn mk_tracked<T: Debug + Clone>(self, value: T, _: ()) -> T {
        value
    }
    fn get_tracked<T: Debug + Clone>(self, value: &T) -> T {
        value.clone()
    }
    fn with_cached_task<T>(self, task: impl FnOnce() -> T) -> (T, Self::DepNodeIndex) {
        (task(), ())
    }
    fn with_global_cache<R>(self, f: impl FnOnce(&mut GlobalCache<Self>) -> R) -> R {
        f(&mut *self.cache.borrow_mut())
    }
    fn evaluation_is_concurrent(&self) -> bool {
        false
    }
}

struct CtxtDelegate<'a, const WITH_CACHE: bool>(PhantomData<&'a ()>);
impl<'a, const WITH_CACHE: bool> Delegate for CtxtDelegate<'a, WITH_CACHE> {
    type Cx = Ctxt<'a>;
    const FIXPOINT_STEP_LIMIT: usize = 2;

    const ENABLE_PROVISIONAL_CACHE: bool = WITH_CACHE;
    type ValidationScope = !;
    fn enter_validation_scope(_: Self::Cx, _: <Self::Cx as Cx>::Input) -> Option<!> {
        None
    }

    type ProofTreeBuilder = ();
    fn inspect_is_noop(_: &mut Self::ProofTreeBuilder) -> bool {
        true
    }

    const DIVIDE_AVAILABLE_DEPTH_ON_OVERFLOW: usize = 2;

    fn initial_provisional_result(_cx: Ctxt<'a>, kind: PathKind, _input: Index) -> Res {
        match kind {
            PathKind::Coinductive => Res::Yes,
            PathKind::Unknown => Res::Ambig,
            PathKind::Inductive => Res::Error,
        }
    }

    fn is_initial_provisional_result(
        cx: Self::Cx,
        kind: PathKind,
        input: <Self::Cx as Cx>::Input,
        result: <Self::Cx as Cx>::Result,
    ) -> bool {
        Self::initial_provisional_result(cx, kind, input) == result
    }

    fn on_stack_overflow(_cx: Ctxt<'a>, _inspect: &mut (), _input: Index) -> Res {
        Res::Ambig
    }

    fn on_fixpoint_overflow(_cx: Ctxt<'a>, _input: Index) -> Res {
        Res::Ambig
    }

    fn is_ambiguous_result(_: <Self::Cx as Cx>::Result) -> bool {
        false // This fast path is annoying
    }

    fn propagate_ambiguity(
        _: Self::Cx,
        _: <Self::Cx as Cx>::Input,
        from_result: <Self::Cx as Cx>::Result,
    ) -> <Self::Cx as Cx>::Result {
        from_result
    }
}

#[derive(Debug, Default)]
struct Candidate {
    flipped: bool,
    children: Vec<(Index, PathKind)>,
}

#[derive(Debug, Default)]
struct Node {
    candidates: Vec<Candidate>,
}

#[derive(Debug, Default)]
struct Graph {
    nodes: Vec<Node>,
}

impl Graph {
    fn generate(
        num_nodes: usize,
        max_children: usize,
        roots: &[Index],
        rng: &mut impl Rng,
    ) -> Graph {
        'outer: loop {
            let mut nodes = Vec::new();
            for _ in 0..num_nodes {
                let num_choices = rng.gen_range(0..=max_children);
                nodes.push(Node {
                    candidates: iter::repeat_with(|| {
                        let num_children = rng.gen_range(0..=max_children);
                        Candidate {
                            flipped: rng.gen(),
                            children: iter::repeat_with(|| {
                                (Index(rng.gen_range(0..num_nodes)), random_path_kind(rng))
                            })
                            .take(num_children)
                            .collect(),
                        }
                    })
                    .take(num_choices)
                    .collect(),
                })
            }

            let graph = Graph { nodes };
            let mut reached = vec![false; num_nodes];
            for r in roots {
                reached[r.0] = true;
            }
            loop {
                let mut has_changed = false;
                for i in 0..num_nodes {
                    if reached[i] {
                        for (nested, _source) in graph.nodes[i]
                            .candidates
                            .iter()
                            .flat_map(|c| c.children.iter())
                        {
                            if !reached[nested.0] {
                                has_changed = true;
                            }
                            reached[nested.0] = true;
                        }
                    }
                }

                if !has_changed {
                    if reached.iter().all(|e| *e) {
                        return graph.normalize(roots);
                    } else {
                        continue 'outer;
                    }
                }
            }
        }
    }

    fn normalize(mut self, roots: &[Index]) -> Graph {
        let mut by_occurance = vec![];
        let mut queue = roots.to_vec();
        while let Some(value) = queue.pop() {
            if by_occurance.contains(&value) {
                continue;
            }
            by_occurance.push(value);
            for &(nested, _) in self.nodes[value.0]
                .candidates
                .iter()
                .flat_map(|c| c.children.iter())
                .rev()
            {
                queue.push(nested);
            }
        }

        let mut nodes = vec![];
        for &i in &by_occurance {
            let Node { mut candidates } = mem::take(&mut self.nodes[i.0]);
            for (index, _source) in candidates.iter_mut().flat_map(|c| c.children.iter_mut()) {
                *index = Index(by_occurance.iter().position(|&i| i == *index).unwrap());
            }
            nodes.push(Node { candidates });
        }

        Graph { nodes }
    }
}

#[tracing::instrument(level = "debug", skip(cx, search_graph), ret)]
fn evaluate_canonical_goal<'a, const WITH_CACHE: bool>(
    cx: Ctxt<'a>,
    search_graph: &mut SearchGraph<CtxtDelegate<'a, WITH_CACHE>>,
    node: Index,
    step_kind_from_parent: PathKind,
) -> Res {
    cx.cost.set(cx.cost.get() + 1);
    search_graph
        .with_new_goal(
            cx,
            node,
            step_kind_from_parent,
            &mut (),
            |search_graph, cx, node, _| {
                cx.cost
                    .set(cx.cost.get() + 5 + search_graph.debug_current_depth());
                let mut success = Res::Error;
                let print_candidate = cx.graph.nodes[node.0].candidates.len() > 1;
                if print_candidate {
                    cx.cost.set(cx.cost.get() + 5);
                }
                for (i, Candidate { flipped, children }) in
                    cx.graph.nodes[node.0].candidates.iter().enumerate()
                {
                    let span;
                    let _span;
                    if print_candidate {
                        span = debug_span!("candidate", ?i);
                        _span = span.enter();
                    }
                    let result =
                        children
                            .iter()
                            .fold(Res::Yes, |curr, &(index, step_kind_from_parent)| {
                                curr.min(evaluate_canonical_goal(
                                    cx,
                                    search_graph,
                                    index,
                                    step_kind_from_parent,
                                ))
                            });
                    let result = if *flipped {
                        debug!("flip result");
                        cx.cost.set(cx.cost.get() + 1);
                        match result {
                            Res::Yes => Res::Error,
                            Res::Ambig => Res::Ambig,
                            Res::Error => Res::Yes,
                        }
                    } else {
                        result
                    };
                    debug!(?result);
                    success = success.max(result);
                }
                success
            },
        )
        .1
}

#[allow(unused)]
pub(super) fn test_from_seed(
    cost: &Cell<usize>,
    num_nodes: usize,
    max_children: usize,
    recursion_limit: usize,
    seed: u64,
) {
    let mut rng = SmallRng::seed_from_u64(seed);
    let num_root_goals = rng.gen_range(0..num_nodes);
    cost.set(cost.get() + num_root_goals * 10);
    let roots = iter::once(Index(0))
        .chain(iter::repeat_with(|| Index(rng.gen_range(0..num_nodes))).take(num_root_goals))
        .collect::<Vec<_>>();

    let graph = &Graph::generate(num_nodes, max_children, &roots, &mut rng);
    debug!(?graph);
    let cx = Ctxt {
        cost,
        graph,
        cache: &Default::default(),
    };
    let mut search_graph = SearchGraph::new(recursion_limit);
    for root in roots {
        let res = evaluate_canonical_goal::<true>(cx, &mut search_graph, root, PathKind::Inductive);
        match (res, expected(num_nodes, graph, root)) {
            (Res::Yes, Res::Yes) | (Res::Ambig, _) | (Res::Error, Res::Error) => {}
            (res, exp) => panic!("res: {res:?}, expected: {exp:?}"),
        }
        assert!(search_graph.is_empty());
    }
}

fn expected(recursion_limit: usize, graph: &Graph, node: Index) -> Res {
    debug!(?node, "validate result");
    let cx = Ctxt {
        cost: &Cell::new(0),
        graph,
        cache: &Default::default(),
    };
    let mut search_graph = SearchGraph::new(recursion_limit);
    evaluate_canonical_goal::<false>(cx, &mut search_graph, node, PathKind::Inductive)
}
