use rand::distributions::{Distribution, Standard};
use rand::rngs::SmallRng;
use rand::{Rng, SeedableRng};
use rustc_type_ir::search_graph::*;
use rustc_type_ir::solve::GoalSource;
use std::cell::{Cell, RefCell};
use std::fmt::Debug;
use std::fmt::Write;
use std::hash::DefaultHasher;
use std::hash::Hasher;
use std::iter::{self};
use std::marker::PhantomData;
use std::mem;

struct DisableCache {
    rng: SmallRng,
    stack: Vec<Index>,
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

#[derive(Clone, Copy)]
struct Ctxt<'a> {
    cost: &'a Cell<usize>,
    disable_cache: &'a RefCell<DisableCache>,
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
    fn with_global_cache<R>(self, f: impl FnOnce(&mut GlobalCache<Self>) -> R) -> R {
        f(&mut *self.cache.borrow_mut())
    }
    fn evaluation_is_concurrent(&self) -> bool {
        false
    }
}

struct CtxtDelegate<'a>(PhantomData<&'a ()>);
impl<'a> Delegate for CtxtDelegate<'a> {
    type Cx = Ctxt<'a>;
    const FIXPOINT_STEP_LIMIT: usize = 2;
    const ENABLE_PROVISIONAL_CACHE: bool = true;
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

    const DIVIDE_AVAILABLE_DEPTH_ON_OVERFLOW: usize = 2;

    fn initial_provisional_result(_cx: Ctxt<'a>, kind: PathKind, _input: Index) -> Res {
        match kind {
            PathKind::Coinductive => Res(0),
            PathKind::Inductive => Res(10),
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
        Res(11)
    }

    fn on_fixpoint_overflow(_cx: Ctxt<'a>, _input: Index) -> Res {
        Res(12)
    }

    fn is_ambiguous_result(result: <Self::Cx as Cx>::Result) -> bool {
        result.0 >= 10 && result.0 <= 12
    }

    fn propagate_ambiguity(
        _: Self::Cx,
        _: <Self::Cx as Cx>::Input,
        from_result: <Self::Cx as Cx>::Result,
    ) -> <Self::Cx as Cx>::Result {
        from_result
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
    step_kind: PathKind,
}

#[derive(Debug, Default)]
struct Node {
    initial: u64,
    children: Vec<Child>,
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
                let num_children = rng.gen_range(0..=max_children);
                nodes.push(Node {
                    initial: rng.gen(),
                    children: iter::repeat_with(|| Child {
                        index: Index(rng.gen_range(0..num_nodes)),
                        cutoff: rng.gen(),
                        step_kind: if rng.gen() {
                            PathKind::Coinductive
                        } else {
                            PathKind::Inductive
                        },
                    })
                    .take(num_children)
                    .collect(),
                })
            }

            let mut graph = Graph { nodes };
            graph.prune_trivially_skipped_nodes();
            let mut reached = vec![false; num_nodes];
            for r in roots {
                reached[r.0] = true;
            }
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
                        return graph.normalize(roots);
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
            while let Some(&Child {
                index: _,
                cutoff,
                step_kind: _,
            }) = node.children.first()
            {
                if cutoff.applies(current) {
                    node.children.remove(0);
                } else {
                    break;
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
            for &child in self.nodes[value.0].children.iter().rev() {
                queue.push(child.index);
            }
        }

        let mut nodes = vec![];
        for &i in &by_occurance {
            let Node {
                initial,
                mut children,
            } = mem::take(&mut self.nodes[i.0]);
            for Child {
                index,
                cutoff: _,
                step_kind: _,
            } in children.iter_mut()
            {
                *index = Index(by_occurance.iter().position(|&i| i == *index).unwrap());
            }
            nodes.push(Node { initial, children });
        }

        Graph { nodes }
    }
}

#[tracing::instrument(level = "debug", skip(cx, search_graph), ret)]
fn evaluate_canonical_goal<'a>(
    cx: Ctxt<'a>,
    search_graph: &mut SearchGraph<CtxtDelegate<'a>>,
    node: Index,
    step_kind_from_parent: PathKind,
) -> Res {
    cx.cost
        .set(cx.cost.get() + 1 + search_graph.debug_current_depth());
    search_graph.with_new_goal(
        cx,
        node,
        step_kind_from_parent,
        &mut (),
        |search_graph, _| {
            cx.cost.set(cx.cost.get() + 5);
            let mut hasher = DefaultHasher::new();
            hasher.write_u64(cx.graph.nodes[node.0].initial);
            let mut trivial_skip = true;
            for &Child {
                index,
                cutoff,
                step_kind,
            } in cx.graph.nodes[node.0].children.iter()
            {
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
                    let result = evaluate_canonical_goal(cx, search_graph, index, step_kind);
                    hasher.write_u8(result.0);
                }
            }

            Res::from_u64(hasher.finish())
        },
    )
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

    let disable_cache = DisableCache {
        rng: SmallRng::seed_from_u64(seed),
        stack: Vec::new(),
    };

    let num_root_goals = rng.gen_range(0..num_nodes);
    let roots = iter::once(Index(0))
        .chain(iter::repeat_with(|| Index(rng.gen_range(0..num_nodes))).take(num_root_goals))
        .collect::<Vec<_>>();

    let cx = Ctxt {
        cost,
        disable_cache: &RefCell::new(disable_cache),
        graph: &Graph::generate(num_nodes, max_children, &roots, &mut rng),
        cache: &Default::default(),
    };
    let mut search_graph = SearchGraph::new(recursion_limit);

    for node in roots {
        evaluate_canonical_goal(cx, &mut search_graph, node, PathKind::Inductive);
        assert!(search_graph.is_empty());
        assert!(cx.disable_cache.borrow().stack.is_empty());
    }
}
