use rand::rngs::SmallRng;
use rand::{thread_rng, Rng, SeedableRng};
use rustc_search_graph::*;
use std::borrow::Borrow;
use std::fmt::Write;
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
    type Input = Index;
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
        _: Self::Input,
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

    fn on_stack_overflow(self, _: &mut Self::ProofTreeBuilder, _: Self::Input) -> Self::Result {
        11
    }

    fn on_fixpoint_overflow(self, _: Self::Input) -> Self::Result {
        12
    }

    fn step_is_coinductive(self, input: Self::Input) -> bool {
        self.graph.borrow().nodes[input.0].is_coinductive
    }
}

#[derive(Clone, Copy, PartialEq, Eq, Hash)]
struct Index(usize);
impl std::fmt::Debug for Index {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if self.0 < 26 {
            f.write_char(('A' as u8 + self.0 as u8) as char)
        } else {
            write!(f, "{}", self.0)
        }
    }
}

#[derive(Debug, Copy, Clone)]
struct Child {
    index: Index,
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
            let num_children = rng.gen_range(0..num_nodes);
            nodes.push(Node {
                is_coinductive: false,
                initial: rng.gen(),
                children: iter::repeat_with(|| Child {
                    index: Index(rng.gen_range(0..num_nodes)),
                    cutoff: rng.gen(),
                })
                .take(num_children)
                .collect(),
            })
        }
        Graph { nodes }
    }
}

#[tracing::instrument(level = "debug", skip(cx, search_graph), ret)]
fn evaluate_canonical_goal<'a>(
    cx: Ctxt<'a>,
    search_graph: &mut SearchGraph<Ctxt<'a>, CtxtDelegate>,
    node: Index,
) -> u8 {
    search_graph.with_new_goal(cx, node, &mut (), |search_graph, _| {
        let mut hasher = DefaultHasher::new();
        hasher.write_u64(cx.graph.nodes[node.0].initial);
        for &Child { index, cutoff } in cx.graph.nodes[node.0].children.iter() {
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

/// Run an action with a tracing log subscriber. The logging level is loaded
/// from `RUST_LOG`. The `formality_macro::test` expansion uses this to enable logs.
pub fn with_tracing_logs<T>(action: impl FnOnce() -> T) -> T {
    use tracing_subscriber::{layer::SubscriberExt, EnvFilter, Registry};
    use tracing_tree::HierarchicalLayer;
    let filter = EnvFilter::from_env("RUST_LOG");
    let subscriber = Registry::default()
        .with(filter)
        .with(HierarchicalLayer::new(2).with_writer(std::io::stdout));
    tracing::subscriber::with_default(subscriber, action)
}

#[allow(unused)]
fn loopy_loop() {
    let mut rng = thread_rng();
    loop {
        let seed = rng.gen();
        // 5: 12257704393984654560
        let graph = &Graph::from_seed(4, seed);
        let cx = Ctxt {
            graph,
            cache: &Default::default(),
        };
        let mut search_graph = SearchGraph::new(SolverMode::Normal);

        println!("{seed}");
        evaluate_canonical_goal(cx, &mut search_graph, Index(0));
        assert!(search_graph.is_empty());
    }
}

fn main() {
    //loopy_loop();
    with_tracing_logs(|| {
        let graph = &Graph::from_seed(4, 11585899145385698581);
        let cx = Ctxt {
            graph,
            cache: &Default::default(),
        };
        let mut search_graph = SearchGraph::new(SolverMode::Normal);

        println!("{graph:?}");
        evaluate_canonical_goal(cx, &mut search_graph, Index(0));
        assert!(search_graph.is_empty());
    })
}
