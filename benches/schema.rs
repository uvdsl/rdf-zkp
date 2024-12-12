use demo_lib::poc::issuer_schema::issue;
use demo_lib::poc::prover_schema::prove;
use demo_lib::poc::verifier_schema::verify;

use criterion::{criterion_group, criterion_main, Criterion};

fn cb_i(c: &mut Criterion) {
    c.bench_function("issue (schema)", |b| b.iter(|| issue()));
}

fn cb_p(c: &mut Criterion) {
    c.bench_function("prove (schema)", |b| b.iter(|| prove()));
}

fn cb_v(c: &mut Criterion) {
    c.bench_function("verify (schema)", |b| b.iter(|| verify()));
}

criterion_group!(benches, cb_i, cb_p, cb_v);
criterion_main!(benches);
