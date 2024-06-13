use core::num;
use rand::rngs::SmallRng;
use rand::{thread_rng, Rng, SeedableRng};
use rustc_search_graph::*;
use std::borrow::Borrow;
use std::hash::Hasher;
use std::iter;
use std::{cell::RefCell, hash::DefaultHasher};

#[derive(Clone, Copy)]
struct Ctxt<'a> {
    graph: &'a Graph,
    cache: &'a RefCell<GlobalCache<Ctxt<'a>>>,
}
impl<'a> Cx for Ctxt<'a> {
    type ProofTree = ();
    type Input = usize;
    type Result = u8;
    type DepNode = ();
    type Tracked<T: Clone> = T;
    fn mk_tracked<T: Clone>(self, value: T, _: ()) -> T {
        value
    }
    fn get_tracked<T: Clone>(self, value: &T) -> T {
        value.clone()
    }
    fn with_anon_task<R>(self, f: impl FnOnce() -> R) -> (R, ()) {
        (f(), ())
    }
    fn with_global_cache<R>(self, _: SolverMode, f: impl FnOnce(&mut GlobalCache<Self>) -> R) -> R {
        f(&mut *self.cache.borrow_mut())
    }
}

impl<'a> ProofTreeBuilder<Ctxt<'a>> for () {
    fn try_apply_proof_tree(&mut self, _: ()) -> bool {
        true
    }

    fn on_provisional_cache_hit(&mut self) {}

    fn on_cycle_in_stack(&mut self) {}

    fn finalize_canonical_goal_evaluation(&mut self, _: Ctxt<'a>) {}
}

struct CtxtDelegate;
impl<'a> Delegate<CtxtDelegate> for Ctxt<'a> {
    const FIXPOINT_STEP_LIMIT: usize = 4;
    type ProofTreeBuilder = ();

    fn recursion_limit(self) -> usize {
        32
    }

    fn is_initial_provisional_result(self, usage_kind: UsageKind, result: Self::Result) -> bool {
        match usage_kind {
            UsageKind::Coinductive => result == 0,
            UsageKind::Inductive => result == 10,
            UsageKind::Both => false,
        }
    }

    fn opt_initial_provisional_result(
        self,
        usage_kind: UsageKind,
        input: Self::Input,
    ) -> Option<Self::Result> {
        match usage_kind {
            UsageKind::Coinductive => Some(0),
            UsageKind::Inductive => Some(10),
            UsageKind::Both => None,
        }
    }

    fn reached_fixpoint(
        self,
        usage_kind: UsageKind,
        provisional_result: Option<Self::Result>,
        result: Self::Result,
    ) -> bool {
        (5..15).contains(&result)
            || provisional_result.is_some_and(|r| r == result)
            || self.is_initial_provisional_result(usage_kind, result)
    }

    fn on_stack_overflow(
        self,
        inspect: &mut Self::ProofTreeBuilder,
        input: Self::Input,
    ) -> Self::Result {
        11
    }

    fn on_fixpoint_overflow(self, input: Self::Input) -> Self::Result {
        12
    }

    fn step_is_coinductive(self, input: Self::Input) -> bool {
        self.graph.borrow().nodes[input].is_coinductive
    }
}

#[derive(Debug, Copy, Clone)]
struct Child {
    index: usize,
    cutoff: i8,
}

#[derive(Debug)]
struct Node {
    is_coinductive: bool,
    initial: u64,
    children: Vec<Child>,
}

#[derive(Debug, Default)]
struct Graph {
    nodes: Vec<Node>,
}

impl Graph {
    fn from_seed(num_nodes: usize, seed: u64) -> Graph {
        let mut nodes = Vec::new();
        let mut rng = SmallRng::seed_from_u64(seed);
        for _ in 0..num_nodes {
            let num_children = rng.gen_range(0..num_nodes + 2);
            nodes.push(Node {
                is_coinductive: false,
                initial: rng.gen(),
                children: iter::repeat_with(|| Child {
                    index: rng.gen_range(0..num_nodes),
                    cutoff: rng.gen(),
                })
                .take(num_children)
                .collect(),
            })
        }
        Graph { nodes }
    }
}

fn evaluate_canonical_goal<'a>(
    cx: Ctxt<'a>,
    search_graph: &mut SearchGraph<Ctxt<'a>, CtxtDelegate>,
    node: usize,
) -> u8 {
    search_graph.with_new_goal(cx, node, &mut (), |search_graph, _| {
        let mut hasher = DefaultHasher::new();
        hasher.write_u64(cx.graph.nodes[node].initial);
        for &Child { index, cutoff } in cx.graph.nodes[node].children.iter() {
            let current = hasher.finish() as u8;
            let should_call = if cutoff.is_positive() {
                current >= cutoff as u8
            } else {
                current <= u8::MAX - cutoff.abs() as u8
            };

            if should_call {
                let result = evaluate_canonical_goal(cx, search_graph, index);
                hasher.write_u8(result);
            }
        }

        hasher.finish() as u8
    })
}

fn loopy_loop() {
    let mut rng = thread_rng();
    loop {
        let seed = rng.gen();
        let graph = &Graph::from_seed(4, seed);
        let cx = Ctxt {
            graph,
            cache: &Default::default(),
        };
        let mut search_graph = SearchGraph::new(SolverMode::Normal);

        println!("{seed}");
        evaluate_canonical_goal(cx, &mut search_graph, 0);
        assert!(search_graph.is_empty());
    }
}

fn main() {
    let mut rng = thread_rng();
    // 7150588276811202185
    let graph = &Graph::from_seed(4, 3483092833210014794);
    let cx = Ctxt {
        graph,
        cache: &Default::default(),
    };
    let mut search_graph = SearchGraph::new(SolverMode::Normal);

    println!("13806361276763622790 {graph:?}");
    let graph = cx.graph.borrow();
    evaluate_canonical_goal(cx, &mut search_graph, 0);
    assert!(search_graph.is_empty());
}
