use rand::rngs::SmallRng;
use rand::{Rng, SeedableRng};
use rustc_type_ir::search_graph::*;
use rustc_type_ir::solve::SolverMode;
use std::borrow::Borrow;
use std::cell::{Cell, RefCell};
use std::fmt::Debug;
use std::iter;
use std::marker::PhantomData;
use std::mem;
use tracing::{debug, debug_span};

use crate::Index;

#[derive(Clone, Copy)]
struct Ctxt<'a> {
    cost: &'a Cell<usize>,
    recursion_limit: usize,
    graph: &'a Graph,
    cache: &'a RefCell<GlobalCache<Ctxt<'a>>>,
}
impl<'a> Cx for Ctxt<'a> {
    type Input = Index;
    type Result = bool;
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
    fn with_global_cache<R>(self, _: SolverMode, f: impl FnOnce(&mut GlobalCache<Self>) -> R) -> R {
        f(&mut *self.cache.borrow_mut())
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

    fn recursion_limit(cx: Ctxt<'a>) -> usize {
        cx.recursion_limit
    }

    fn initial_provisional_result(_cx: Ctxt<'a>, kind: CycleKind, _input: Index) -> bool {
        match kind {
            CycleKind::Coinductive => true,
            CycleKind::Inductive => false,
        }
    }

    fn is_initial_provisional_result(
        cx: Self::Cx,
        kind: CycleKind,
        input: <Self::Cx as Cx>::Input,
        result: <Self::Cx as Cx>::Result,
    ) -> bool {
        Self::initial_provisional_result(cx, kind, input) == result
    }

    fn on_stack_overflow(_cx: Ctxt<'a>, _inspect: &mut (), _input: Index) -> bool {
        false
    }

    fn on_fixpoint_overflow(_cx: Ctxt<'a>, _input: Index) -> bool {
        false
    }

    fn is_ambiguous_result(result: <Self::Cx as Cx>::Result) -> bool {
        result == false
    }

    fn propagate_ambiguity(
        _: Self::Cx,
        _: <Self::Cx as Cx>::Input,
        from_result: <Self::Cx as Cx>::Result,
    ) -> <Self::Cx as Cx>::Result {
        from_result
    }

    fn step_is_coinductive(cx: Ctxt<'a>, input: Index) -> bool {
        cx.graph.borrow().nodes[input.0].is_coinductive
    }
}

#[derive(Debug, Default)]
struct Node {
    is_coinductive: bool,
    children: Vec<Vec<Index>>,
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
                    is_coinductive: rng.gen(),
                    children: iter::repeat_with(|| {
                        let num_children = rng.gen_range(0..=max_children);
                        iter::repeat_with(|| Index(rng.gen_range(0..num_nodes)))
                            .take(num_children)
                            .collect()
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
                        for nested in graph.nodes[i].children.iter().flat_map(|c| c.iter()) {
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
            for &nested in self.nodes[value.0]
                .children
                .iter()
                .flat_map(|c| c.iter())
                .rev()
            {
                queue.push(nested);
            }
        }

        let mut nodes = vec![];
        for &i in &by_occurance {
            let Node {
                is_coinductive,
                mut children,
            } = mem::take(&mut self.nodes[i.0]);
            for index in children.iter_mut().flat_map(|c| c.iter_mut()) {
                *index = Index(by_occurance.iter().position(|&i| i == *index).unwrap());
            }
            nodes.push(Node {
                is_coinductive,
                children,
            });
        }

        Graph { nodes }
    }
}

#[tracing::instrument(level = "debug", skip(cx, search_graph), fields(coinductive = ?cx.graph.nodes[node.0].is_coinductive), ret)]
fn evaluate_canonical_goal<'a, const WITH_CACHE: bool>(
    cx: Ctxt<'a>,
    search_graph: &mut SearchGraph<CtxtDelegate<'a, WITH_CACHE>>,
    node: Index,
) -> bool {
    cx.cost
        .set(cx.cost.get() + 1 + search_graph.debug_current_depth());
    search_graph.with_new_goal(cx, node, &mut (), |search_graph, _| {
        cx.cost.set(cx.cost.get() + 5);
        let mut success = false;
        for (i, c) in cx.graph.nodes[node.0].children.iter().enumerate() {
            let span = debug_span!("candidate", ?i);
            let _span = span.enter();
            let result = c
                .iter()
                .all(|&index| evaluate_canonical_goal(cx, search_graph, index));
            debug!(?result);
            success |= result;
        }
        success
    })
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
    let roots = iter::once(Index(0))
        .chain(iter::repeat_with(|| Index(rng.gen_range(0..num_nodes))).take(num_root_goals))
        .collect::<Vec<_>>();

    let graph = &Graph::generate(num_nodes, max_children, &roots, &mut rng);
    debug!(?graph);
    let cx = Ctxt {
        cost,
        recursion_limit,
        graph,
        cache: &Default::default(),
    };
    let mut search_graph = SearchGraph::new(SolverMode::Normal);
    for root in roots {
        let res = evaluate_canonical_goal::<true>(cx, &mut search_graph, root);
        assert_eq!(res, expected(recursion_limit, graph, root));
        assert!(search_graph.is_empty());
    }
}

fn expected(recursion_limit: usize, graph: &Graph, node: Index) -> bool {
    debug!(?node, "validate result");
    let cx = Ctxt {
        cost: &Cell::new(0),
        recursion_limit,
        graph,
        cache: &Default::default(),
    };
    let mut search_graph = SearchGraph::new(SolverMode::Normal);
    evaluate_canonical_goal::<false>(cx, &mut search_graph, node)
}
