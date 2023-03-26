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

    bench_f32(c, |_| fastrand::f32());
    bench_f64(c, |_| fastrand::f64());

    bench_type(c, |_| fastrand::bool());
    bench_type(c, |_| fastrand::char('\u{0}'..'\u{10FFFF}'));
}

fn bench_type<T>(c: &mut Criterion, gen: fn(usize) -> T)
where
    T: Clone + Ord + radsort::Key + radsort_latest::Key + radsort_main::Key,
{
    let gen = |size| {
        fastrand::seed(0);
        (0..size).map(gen).collect()
    };

    bench_function(c, gen, "head", radsort::sort);
    bench_function(c, gen, "main", radsort_main::sort);
    bench_function(c, gen, "latest", radsort_latest::sort);
    bench_function(c, gen, "std stable", std_stable);
    bench_function(c, gen, "std unstable", std_unstable);
}

fn bench_f32(c: &mut Criterion, gen: fn(usize) -> f32) {
    let gen = |size| {
        fastrand::seed(0);
        (0..size).map(gen).collect()
    };

    bench_function(c, gen, "head", radsort::sort);
    bench_function(c, gen, "main", radsort_main::sort);
    bench_function(c, gen, "latest", radsort_latest::sort);
    bench_function(c, gen, "std stable", std_stable_f32);
    bench_function(c, gen, "std unstable", std_unstable_f32);
}

fn bench_f64(c: &mut Criterion, gen: fn(usize) -> f64) {
    let gen = |size| {
        fastrand::seed(0);
        (0..size).map(gen).collect()
    };

    bench_function(c, gen, "head", radsort::sort);
    bench_function(c, gen, "main", radsort_main::sort);
    bench_function(c, gen, "latest", radsort_latest::sort);
    bench_function(c, gen, "std stable", std_stable_f64);
    bench_function(c, gen, "std unstable", std_unstable_f64);
}

fn std_stable<T: Ord>(slice: &mut [T]) {
    slice.sort();
}

fn std_stable_f32(slice: &mut [f32]) {
    slice.sort_by(|a, b| a.total_cmp(b));
}

fn std_stable_f64(slice: &mut [f64]) {
    slice.sort_by(|a, b| a.total_cmp(b));
}

fn std_unstable<T: Ord>(slice: &mut [T]) {
    slice.sort_unstable();
}

fn std_unstable_f32(slice: &mut [f32]) {
    slice.sort_unstable_by(|a, b| a.total_cmp(b));
}

fn std_unstable_f64(slice: &mut [f64]) {
    slice.sort_unstable_by(|a, b| a.total_cmp(b));
}

fn bench_function<T: Clone>(
    c: &mut Criterion,
    gen: impl Fn(usize) -> Vec<T>,
    name: &'static str,
    sort: impl Fn(&mut [T]),
) {
    let mut group = c.benchmark_group(name);
    let t_name = std::any::type_name::<T>();
    for size in 0..=4 {
        let elems = 25 * 10_u64.pow(size);
        group.throughput(Throughput::Elements(elems));
        group.bench_with_input(BenchmarkId::new(t_name, elems), &elems, |b, &elems| {
            let input = gen(elems as usize);
            b.iter_batched_ref(
                || input.clone(),
                |data| {
                    sort(data);
                },
                criterion::BatchSize::LargeInput,
            );
        });
    }
    group.finish();
}
