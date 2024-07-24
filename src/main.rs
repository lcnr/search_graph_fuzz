use rand::distributions::{Distribution, Standard};
use rand::rngs::SmallRng;
use rand::{thread_rng, Rng, SeedableRng};
use rustc_type_ir::search_graph::*;
use rustc_type_ir::solve::SolverMode;
use std::borrow::Borrow;
use std::cell::{Cell, RefCell};
use std::fmt::Debug;
use std::fmt::Write;
use std::hash::DefaultHasher;
use std::hash::Hasher;
use std::iter::{self};
use std::marker::PhantomData;
use std::mem;
use std::panic::{catch_unwind, AssertUnwindSafe};

struct DisableCache {
    rng: SmallRng,
    stack: Vec<Index>,
}

#[derive(Clone, Copy)]
struct Ctxt<'a> {
    cost: &'a Cell<usize>,
    disable_cache: &'a RefCell<DisableCache>,
    recursion_limit: usize,
    graph: &'a Graph,
    cache: &'a RefCell<GlobalCache<Ctxt<'a>>>,
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
    fn with_global_cache<R>(self, _: SolverMode, f: impl FnOnce(&mut GlobalCache<Self>) -> R) -> R {
        f(&mut *self.cache.borrow_mut())
    }
}

struct ValidationScope<'a> {
    cx: Ctxt<'a>,
    input: Index,
}
impl<'a> Drop for ValidationScope<'a> {
    fn drop(&mut self) {
        let entry = self.cx.disable_cache.borrow_mut().stack.pop();
        assert_eq!(entry, Some(self.input));
    }
}

struct CtxtDelegate<'a>(PhantomData<&'a ()>);
impl<'a> Delegate for CtxtDelegate<'a> {
    type Cx = Ctxt<'a>;
    const FIXPOINT_STEP_LIMIT: usize = 2;

    type ValidationScope = ValidationScope<'a>;
    fn enter_validation_scope(
        cx: Self::Cx,
        input: <Self::Cx as Cx>::Input,
    ) -> Option<ValidationScope<'a>> {
        let mut disable_cache = cx.disable_cache.borrow_mut();
        if disable_cache.stack.contains(&input) || disable_cache.rng.gen() {
            disable_cache.stack.push(input);
            Some(ValidationScope { cx, input })
        } else {
            None
        }
    }

    type ProofTreeBuilder = ();
    fn inspect_is_noop(_: &mut Self::ProofTreeBuilder) -> bool {
        true
    }

    fn recursion_limit(cx: Ctxt<'a>) -> usize {
        cx.recursion_limit
    }

    fn initial_provisional_result(_cx: Ctxt<'a>, kind: CycleKind, _input: Index) -> Res {
        match kind {
            CycleKind::Coinductive => Res(0),
            CycleKind::Inductive => Res(10),
        }
    }

    fn reached_fixpoint(
        cx: Ctxt<'a>,
        kind: UsageKind,
        input: Index,
        provisional_result: Option<Res>,
        result: Res,
    ) -> bool {
        if let Some(r) = provisional_result {
            r == result
        } else {
            match kind {
                UsageKind::Single(kind) => {
                    Self::initial_provisional_result(cx, kind, input) == result
                }
                UsageKind::Mixed => false,
            }
        }
    }

    fn on_stack_overflow(_cx: Ctxt<'a>, _inspect: &mut (), _input: Index) -> Res {
        Res(11)
    }

    fn on_fixpoint_overflow(_cx: Ctxt<'a>, _input: Index) -> Res {
        Res(12)
    }

    fn step_is_coinductive(cx: Ctxt<'a>, input: Index) -> bool {
        cx.graph.borrow().nodes[input.0].is_coinductive
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
    search_graph: &mut SearchGraph<CtxtDelegate<'a>>,
    node: Index,
) -> Res {
    cx.cost.set(cx.cost.get() + 4);
    search_graph.with_new_goal(cx, node, &mut (), |search_graph, _| {
        let mut hasher = DefaultHasher::new();
        hasher.write_u64(cx.graph.nodes[node.0].initial);
        let mut trivial_skip = true;
        for &Child { index, cutoff } in cx.graph.nodes[node.0].children.iter() {
            let current = Res::from_u64(hasher.finish());
            if cutoff.applies(current) {
                if !trivial_skip {
                    cx.cost.set(cx.cost.get() + 1);
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

fn test_from_seed(
    cost: &Cell<usize>,
    num_nodes: usize,
    max_children: usize,
    recursion_limit: usize,
    seed: u64,
) {
    let disable_cache = DisableCache {
        rng: SmallRng::seed_from_u64(seed),
        stack: Vec::new(),
    };
    let cx = Ctxt {
        cost,
        disable_cache: &RefCell::new(disable_cache),
        recursion_limit,
        graph: &Graph::from_seed(num_nodes, max_children, seed),
        cache: &Default::default(),
    };
    let mut search_graph = SearchGraph::new(SolverMode::Normal);

    let mut rng = SmallRng::seed_from_u64(seed);

    let num_root_goals = rng.gen_range(1..num_nodes);
    for i in 0..num_root_goals {
        let index = if i == 0 {
            0
        } else {
            rng.gen_range(0..num_nodes)
        };
        evaluate_canonical_goal(cx, &mut search_graph, Index(index));
        assert!(search_graph.is_empty());
        assert!(cx.disable_cache.borrow().stack.is_empty());
    }
    assert!(search_graph.is_empty());
    assert!(cx.disable_cache.borrow().stack.is_empty());
}

fn do_stuff(num_nodes: usize, max_children: usize, recursion_limit: usize, seed: u64) {
    if seed == 0 {
        let mut rng = thread_rng();
        let mut min_cost = usize::MAX;

        std::panic::set_hook(Box::new(|_| ()));
        loop {
            let mut cost = Cell::new(0);

            for i in 0.. {
                let seed = rng.gen();
                let res = catch_unwind(AssertUnwindSafe(|| {
                    print!("\r{i:15}: {seed:20} ");
                    cost = Cell::new(0);
                    test_from_seed(&cost, num_nodes, max_children, recursion_limit, seed);
                    print!("cost: {:5}", cost.get());
                }));

                if res.is_err() && cost.get() < min_cost {
                    println!("\r{i:15}: {seed:20} cost: {:5} (new best)", cost.get());
                    min_cost = cost.get();
                    break;
                }
            }
        }
    } else {
        with_tracing_logs(|| {
            test_from_seed(
                &Cell::new(0),
                num_nodes,
                max_children,
                recursion_limit,
                seed,
            )
        })
    }
}

fn main() {
    // 3 1 7837967547938528536
    do_stuff(4, 2, 2, 5802416440568674494);
}
