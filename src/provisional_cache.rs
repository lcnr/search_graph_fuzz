use rand::prelude::SliceRandom;
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
pub enum Res {
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
            PathKind::Unknown | PathKind::ForcedAmbiguity => Res::Ambig,
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

    fn on_stack_overflow(_cx: Ctxt<'a>, _input: Index, _inspect: &mut ()) -> Res {
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

    fn compute_goal(
        search_graph: &mut SearchGraph<Self>,
        cx: Self::Cx,
        input: <Self::Cx as Cx>::Input,
        inspect: &mut Self::ProofTreeBuilder,
    ) -> <Self::Cx as Cx>::Result {
        cx.cost
            .set(cx.cost.get() + 5 + search_graph.debug_current_depth());
        let mut success = Res::Error;
        let print_candidate = cx.graph.nodes[input.0].candidates.len() > 1;
        if print_candidate {
            cx.cost.set(cx.cost.get() + 5);
        }
        for (
            i,
            &Candidate {
                initial_result,
                ref children,
            },
        ) in cx.graph.nodes[input.0].candidates.iter().enumerate()
        {
            let span;
            let _span;
            if print_candidate {
                span = debug_span!("candidate", ?i);
                _span = span.enter();
            }

            let result = children.iter().fold(
                initial_result,
                |curr, &(index, flipped, step_kind_from_parent)| {
                    cx.cost.set(cx.cost.get() + 1);
                    if curr != Res::Error {
                        let mut result =
                            search_graph.evaluate_goal(cx, index, step_kind_from_parent, &mut ());
                        if flipped {
                            cx.cost.set(cx.cost.get() + 2);
                            result = match result {
                                Res::Yes => Res::Error,
                                Res::Ambig => Res::Ambig,
                                Res::Error => Res::Yes,
                            };
                            debug!(?result, "flip child result");
                        }
                        curr.min(result)
                    } else {
                        Res::Error
                    }
                },
            );
            debug!(?initial_result, ?result);
            success = success.max(result);
        }
        success
    }
}

#[derive(Debug)]
pub struct Candidate {
    pub initial_result: Res,
    pub children: Vec<(Index, bool, PathKind)>,
}

#[derive(Debug, Default)]
pub struct Node {
    pub candidates: Vec<Candidate>,
}

#[derive(Debug, Default)]
pub struct Graph {
    pub nodes: Vec<Node>,
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
                            initial_result: [Res::Yes, Res::Yes, Res::Ambig]
                                .choose(rng)
                                .copied()
                                .unwrap(),
                            children: iter::repeat_with(|| {
                                let flipped = rng.gen();
                                let path_kind = if flipped {
                                    PathKind::ForcedAmbiguity
                                } else {
                                    random_path_kind(rng)
                                };
                                (Index(rng.gen_range(0..num_nodes)), flipped, path_kind)
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
                        for (nested, _flipped, _source) in graph.nodes[i]
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
            for &(nested, _, _) in self.nodes[value.0]
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
            for (index, _flipped, _source) in
                candidates.iter_mut().flat_map(|c| c.children.iter_mut())
            {
                *index = Index(by_occurance.iter().position(|&i| i == *index).unwrap());
            }
            nodes.push(Node { candidates });
        }

        Graph { nodes }
    }
}

pub(super) fn test_graph(
    cost: &Cell<usize>,
    graph: Graph,
    roots: &[Index],
    recursion_limit: usize,
) {
    let graph = &graph.normalize(roots);
    let cx = Ctxt {
        cost,
        graph: &graph,
        cache: &Default::default(),
    };
    let mut search_graph: SearchGraph<CtxtDelegate<true>> = SearchGraph::new(recursion_limit);
    for &root in roots {
        let res = search_graph.evaluate_goal(cx, root, PathKind::Inductive, &mut ());
        match res {
            Res::Ambig => {}
            Res::Yes | Res::Error => {
                let exp = expected(graph.nodes.len(), graph, root);
                if exp != res {
                    panic!("res: {res:?}, expected: {exp:?}")
                }
            }
        }
        assert!(search_graph.is_empty());
    }
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
    let mut search_graph: SearchGraph<CtxtDelegate<true>> = SearchGraph::new(recursion_limit);
    for root in roots {
        let res = search_graph.evaluate_goal(cx, root, PathKind::Inductive, &mut ());
        match res {
            Res::Ambig | Res::Yes | Res::Error => {
                let exp = expected(num_nodes, graph, root);
                if exp != res {
                    panic!("res: {res:?}, expected: {exp:?}")
                }
            }
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
    let mut search_graph: SearchGraph<CtxtDelegate<false>> = SearchGraph::new(recursion_limit);
    search_graph.evaluate_goal(cx, node, PathKind::Inductive, &mut ())
}
