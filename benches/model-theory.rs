use demo_lib::poc::issuer::issue;
use demo_lib::poc::prover::prove;
use demo_lib::poc::verifier::verify;

use criterion::{criterion_group, criterion_main, Criterion};

fn cb_i(c: &mut Criterion) {
    c.bench_function("issue (mt)", |b| b.iter(|| issue()));
}

fn cb_p(c: &mut Criterion) {
    c.bench_function("prove (mt)", |b| b.iter(|| prove()));
}

fn cb_v(c: &mut Criterion) {
    c.bench_function("verify (mt)", |b| b.iter(|| verify()));
}

criterion_group!(benches, cb_i, cb_p, cb_v);
criterion_main!(benches);
