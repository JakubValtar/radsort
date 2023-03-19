use criterion::{criterion_group, criterion_main, BenchmarkId, Criterion, Throughput};

// Test for performance regressions in the *head* revision since the *latest* release.
//
// ```
// cargo update
// cargo bench -- --save-baseline main
// critcmp main -g '\w+/(.*)'
// ```

criterion_main!(benches);
criterion_group!(benches, regression);

fn regression(c: &mut Criterion) {
    bench_type(c, |_| fastrand::u8(..));
    bench_type(c, |_| fastrand::u16(..));
    bench_type(c, |_| fastrand::u32(..));
    bench_type(c, |_| fastrand::u64(..));
    bench_type(c, |_| fastrand::u128(..));

    bench_type(c, |_| fastrand::i8(..));
    bench_type(c, |_| fastrand::i16(..));
    bench_type(c, |_| fastrand::i32(..));
    bench_type(c, |_| fastrand::i64(..));
    bench_type(c, |_| fastrand::i128(..));

    bench_type(c, |_| fastrand::f32());
    bench_type(c, |_| fastrand::f64());

    bench_type(c, |_| fastrand::bool());
    bench_type(c, |_| fastrand::char('\u{0}'..'\u{10FFFF}'));
}

fn bench_type<T>(c: &mut Criterion, gen: fn(usize) -> T)
where
    T: Clone + radsort::Key + radsort_latest::Key,
{
    let gen = |size| {
        fastrand::seed(0);
        (0..size).map(gen).collect()
    };

    bench_function(c, gen, "latest", radsort_latest::sort);
    bench_function(c, gen, "head", radsort::sort);
}

fn bench_function<T: Clone>(
    c: &mut Criterion,
    gen: impl Fn(usize) -> Vec<T>,
    name: &'static str,
    sort: impl Fn(&mut [T]),
) {
    let mut group = c.benchmark_group(name);
    let t_name = std::any::type_name::<T>();
    for size in 1..=3 {
        let elems = 100_u64.pow(size);
        group.throughput(Throughput::Elements(elems));
        group.bench_with_input(BenchmarkId::new(t_name, elems), &elems, |b, &elems| {
            let input = gen(elems as usize);
            b.iter_batched_ref(
                || input.clone(),
                |data| {
                    sort(data);
                },
                criterion::BatchSize::SmallInput,
            );
        });
    }
    group.finish();
}
