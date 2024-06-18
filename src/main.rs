use rand::distributions::{Distribution, Standard};
use rand::rngs::SmallRng;
use rand::{thread_rng, Rng, SeedableRng};
use rustc_search_graph::*;
use std::borrow::Borrow;
use std::fmt::Debug;
use std::fmt::Write;
use std::hash::Hasher;
use std::iter::{self};
use std::mem;
use std::{cell::RefCell, hash::DefaultHasher};

#[derive(Clone, Copy)]
struct Ctxt<'a> {
    recursion_limit: usize,
    graph: &'a Graph,
    cache: &'a RefCell<GlobalCache<Ctxt<'a>>>,
}
impl<'a> Cx for Ctxt<'a> {
    const VERIFY_CACHE: bool = false;
    type Input = Index;
    type Result = Res;
    type DepNode = ();
    type Tracked<T: Debug + Clone> = T;
    fn mk_tracked<T: Debug + Clone>(self, value: T, _: ()) -> T {
        value
    }
    fn get_tracked<T: Debug + Clone>(self, value: &T) -> T {
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
    fn is_noop(&self) -> bool {
        true
    }

    fn on_cycle_in_stack(&mut self) {}

    fn finalize_canonical_goal_evaluation(&mut self, _: Ctxt<'a>) {}
}

struct CtxtDelegate;
impl<'a> Delegate<CtxtDelegate> for Ctxt<'a> {
    const FIXPOINT_STEP_LIMIT: usize = 4;
    type ProofTreeBuilder = ();

    fn recursion_limit(self) -> usize {
        self.recursion_limit
    }

    fn initial_provisional_result(self, cycle_kind: PathKind, _: Self::Input) -> Self::Result {
        match cycle_kind {
            PathKind::Coinductive => Res(0),
            PathKind::Inductive => Res(10),
        }
    }

    fn is_initial_provisional_result(self, _: Self::Input, result: Self::Result) -> Option<PathKind> {
        match result {
            Res(0) => Some(PathKind::Coinductive),
            Res(10) => Some(PathKind::Inductive),
            _ => None,
        }
    }

    fn reached_fixpoint(
        self,
        input: Self::Input,
        usage_kind: UsageKind,
        provisional_result: Option<Self::Result>,
        result: Self::Result,
    ) -> bool {
        (Res(10)..Res(13)).contains(&result)
            || provisional_result.is_some_and(|r| r == result)
            || match usage_kind {
                UsageKind::Single(PathKind::Coinductive) => result == Res(0),
                UsageKind::Single(PathKind::Inductive) => result == Res(10),
                UsageKind::Mixed => false,
            }
    }

    fn on_stack_overflow(self, _: &mut Self::ProofTreeBuilder, _: Self::Input) -> Self::Result {
        Res(11)
    }

    fn on_fixpoint_overflow(self, _: Self::Input) -> Self::Result {
        Res(12)
    }

    fn step_kind(self, input: Self::Input) -> PathKind {
        if self.graph.borrow().nodes[input.0].is_coinductive {
            PathKind::Coinductive
        } else {
            PathKind::Inductive
        }
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

#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
struct Res(u8);
impl std::fmt::Debug for Res {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.0)
    }
}

impl Res {
    fn from_u64(value: u64) -> Self {
        Res((value % 16) as u8)
    }
}
impl Distribution<Res> for Standard {
    fn sample<R: Rng + ?Sized>(&self, rng: &mut R) -> Res {
        Res(rng.gen::<u8>() % 16)
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
struct Cutoff {
    is_min: bool,
    value: Res,
}
impl Cutoff {
    fn applies(self, result: Res) -> bool {
        if self.is_min {
            result < self.value
        } else {
            result > self.value
        }
    }
}
impl Distribution<Cutoff> for Standard {
    fn sample<R: Rng + ?Sized>(&self, rng: &mut R) -> Cutoff {
        Cutoff {
            is_min: rng.gen(),
            value: rng.gen(),
        }
    }
}

#[derive(Debug, Copy, Clone)]
struct Child {
    index: Index,
    cutoff: Cutoff,
}

#[derive(Debug, Default)]
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
    fn from_seed(num_nodes: usize, max_children: usize, seed: u64) -> Graph {
        let mut rng = SmallRng::seed_from_u64(seed);
        'outer: loop {
            let mut nodes = Vec::new();
            for _ in 0..num_nodes {
                let num_children = rng.gen_range(0..=max_children);
                nodes.push(Node {
                    is_coinductive: rng.gen(),
                    initial: rng.gen(),
                    children: iter::repeat_with(|| Child {
                        index: Index(rng.gen_range(0..num_nodes)),
                        cutoff: rng.gen(),
                    })
                    .take(num_children)
                    .collect(),
                })
            }

            let mut graph = Graph { nodes };
            graph.prune_trivially_skipped_nodes();
            let mut reached = vec![false; num_nodes];
            reached[0] = true;
            loop {
                let mut has_changed = false;
                for i in 0..num_nodes {
                    if reached[i] {
                        for child in &graph.nodes[i].children {
                            if !reached[child.index.0] {
                                has_changed = true;
                            }
                            reached[child.index.0] = true;
                        }
                    }
                }

                if !has_changed {
                    if reached.iter().all(|e| *e) {
                        return graph.normalize();
                    } else {
                        continue 'outer;
                    }
                }
            }
        }
    }

    fn prune_trivially_skipped_nodes(&mut self) {
        for node in &mut self.nodes {
            let mut hasher = DefaultHasher::new();
            hasher.write_u64(node.initial);
            let current = Res::from_u64(hasher.finish());
            while let Some(&Child { index: _, cutoff }) = node.children.first() {
                if cutoff.applies(current) {
                    node.children.remove(0);
                } else {
                    break;
                }
            }
        }
    }

    fn normalize(mut self) -> Graph {
        let mut by_occurance = vec![];
        let mut queue = vec![0];
        while let Some(value) = queue.pop() {
            if by_occurance.contains(&value) {
                continue;
            }
            by_occurance.push(value);
            for &child in self.nodes[value].children.iter().rev() {
                queue.push(child.index.0);
            }
        }

        let mut nodes = vec![];
        for &i in &by_occurance {
            let Node {
                is_coinductive,
                initial,
                mut children,
            } = mem::take(&mut self.nodes[i]);
            for Child { index, cutoff: _ } in children.iter_mut() {
                *index = Index(by_occurance.iter().position(|&i| i == index.0).unwrap());
            }
            nodes.push(Node {
                initial,
                is_coinductive,
                children,
            });
        }

        Graph { nodes }
    }
}

#[tracing::instrument(level = "debug", skip(cx, search_graph), ret)]
fn evaluate_canonical_goal<'a>(
    cx: Ctxt<'a>,
    search_graph: &mut SearchGraph<Ctxt<'a>, CtxtDelegate>,
    node: Index,
) -> Res {
    search_graph.with_new_goal(cx, node, &mut (), |search_graph, _| {
        let mut hasher = DefaultHasher::new();
        hasher.write_u64(cx.graph.nodes[node.0].initial);
        let mut trivial_skip = true;
        for &Child { index, cutoff } in cx.graph.nodes[node.0].children.iter() {
            let current = Res::from_u64(hasher.finish());
            if cutoff.applies(current) {
                if !trivial_skip {
                    tracing::debug!(?index, "skip nested");
                } else {
                    unreachable!()
                }
            } else {
                trivial_skip = false;
                let result = evaluate_canonical_goal(cx, search_graph, index);
                hasher.write_u8(result.0);
            }
        }

        Res::from_u64(hasher.finish())
    })
}

/// Run an action with a tracing log subscriber. The logging level is loaded
/// from `RUST_LOG`. The `formality_macro::test` expansion uses this to enable logs.
pub fn with_tracing_logs<T>(action: impl FnOnce() -> T) -> T {
    use std::io::Write;
    use tracing_subscriber::{layer::SubscriberExt, Registry};
    use tracing_tree::HierarchicalLayer;
    struct Writer;
    impl Write for Writer {
        fn write(&mut self, buf: &[u8]) -> std::io::Result<usize> {
            write!(
                std::io::stdout(),
                "{}",
                std::str::from_utf8(buf)
                    .unwrap()
                    .replace("  0ms DEBUG ", "")
                    .replace("  1ms DEBUG ", "")
                    .replace("  2ms DEBUG ", "")
            )?;
            Ok(buf.len())
        }

        fn flush(&mut self) -> std::io::Result<()> {
            std::io::stdout().flush()
        }
    }

    let subscriber = Registry::default().with(
        HierarchicalLayer::new(2)
            .with_ansi(false)
            .with_timer(())
            .with_writer(|| Writer),
    );
    tracing::subscriber::with_default(subscriber, action)
}

fn do_stuff(num_nodes: usize, max_children: usize, recursion_limit: usize, seed: u64) {
    if seed == 0 {
        let mut rng = thread_rng();
        for i in 0.. {
            let seed = rng.gen();
            let cx = Ctxt {
                recursion_limit,
                graph: &Graph::from_seed(num_nodes, max_children, seed),
                cache: &Default::default(),
            };
            let mut search_graph = SearchGraph::new(SolverMode::Normal);
            print!("\r{i:15}: {seed:20} ");
            evaluate_canonical_goal(cx, &mut search_graph, Index(0));
            assert!(search_graph.is_empty());
        }
    } else {
        with_tracing_logs(|| {
            let cx = Ctxt {
                recursion_limit,
                graph: &Graph::from_seed(num_nodes, max_children, seed),
                cache: &Default::default(),
            };
            let mut search_graph = SearchGraph::new(SolverMode::Normal);
            tracing::debug!(?cx.graph);
            evaluate_canonical_goal(cx, &mut search_graph, Index(0));
            assert!(search_graph.is_empty());
        })
    }
}

fn main() {
    do_stuff(9, 6, 8, 0);
}
