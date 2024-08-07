#![feature(never_type)]
use rand::{thread_rng, Rng};
use std::cell::Cell;
use std::fmt::Write;
use std::io::Write as _;
use std::panic::{catch_unwind, AssertUnwindSafe};
use std::sync::atomic::{self, AtomicUsize};

mod global_cache;
mod provisional_cache;

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
                    .replace("DEBUG ", "")
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
    use crate::provisional_cache::test_from_seed;
    if seed == 0 {
        std::panic::set_hook(Box::new(|_| ()));
        let min_cost = AtomicUsize::new(usize::MAX);
        let num_tries = AtomicUsize::new(0);
        std::thread::scope(|s| {
            for _ in 0..16 {
                s.spawn(|| {
                    let mut rng = thread_rng();
                    loop {
                        let cost = Cell::new(0);
                        let seed = rng.gen();
                        let res = catch_unwind(AssertUnwindSafe(|| {
                            test_from_seed(&cost, num_nodes, max_children, recursion_limit, seed);
                        }));

                        if res.is_err() {
                            let prev = min_cost.fetch_min(cost.get(), atomic::Ordering::Relaxed);
                            if prev > cost.get() {
                                let i = num_tries.swap(0, atomic::Ordering::Relaxed);
                                println!("\r{i:15}: {seed:20} cost: {:5} (new best)", cost.get());
                                continue;
                            }
                        }

                        let old = num_tries.fetch_add(1, atomic::Ordering::Relaxed);
                        if old % 500000 == 0 {
                            print!("\r{old:15}");
                            let _ = std::io::stdout().flush();
                        }
                    }
                });
            }
        });
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
    // 8 3 20 4621883001622421945
    // 8 3 20 15886988225882956210
    // 6 3 10 6474412646705121343
    do_stuff(4, 3, 11, 6338606554841105063);
}
