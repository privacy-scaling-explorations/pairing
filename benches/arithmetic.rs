use criterion::{criterion_group, criterion_main, Criterion};

use ff::Field;
use pairing_bn256::bn256::Fr;
use rand::{RngCore, SeedableRng};
use rand_xorshift::XorShiftRng;
use std::ops::{AddAssign, MulAssign, SubAssign};

fn add_benchmark(mut rng: impl RngCore) {
    for _ in 0..10000 {
        let mut a = Fr::random(&mut rng);
        let b = a;
        a.add_assign(&b);
    }
}

fn sub_benchmark(mut rng: impl RngCore) {
    for _ in 0..10000 {
        let mut a = Fr::random(&mut rng);
        let b = a;
        a.sub_assign(&b);
    }
}

fn double_benchmark(mut rng: impl RngCore) {
    for _ in 0..10000 {
        let a = Fr::random(&mut rng);
        a.double();
    }
}

fn mul_benchmark(mut rng: impl RngCore) {
    for _ in 0..10000 {
        let mut a = Fr::random(&mut rng);
        let b = a;
        a.mul_assign(&b);
    }
}

fn square_benchmark(mut rng: impl RngCore) {
    for _ in 0..10000 {
        let a = Fr::random(&mut rng);
        a.square();
    }
}

fn field_arithmetic_benchmark(c: &mut Criterion) {
    let description = "add arithmetic bench";
    c.bench_function(description, |b| {
        b.iter(|| {
            let rng = XorShiftRng::from_seed([
                0x59, 0x62, 0xbe, 0x5d, 0x76, 0x3d, 0x31, 0x8d, 0x17, 0xdb, 0x37, 0x32, 0x54, 0x06,
                0xbc, 0xe5,
            ]);
            add_benchmark(rng)
        })
    });

    let description = "sub arithmetic bench";
    c.bench_function(description, |b| {
        b.iter(|| {
            let rng = XorShiftRng::from_seed([
                0x59, 0x62, 0xbe, 0x5d, 0x76, 0x3d, 0x31, 0x8d, 0x17, 0xdb, 0x37, 0x32, 0x54, 0x06,
                0xbc, 0xe5,
            ]);
            sub_benchmark(rng)
        })
    });

    let description = "double arithmetic bench";
    c.bench_function(description, |b| {
        b.iter(|| {
            let rng = XorShiftRng::from_seed([
                0x59, 0x62, 0xbe, 0x5d, 0x76, 0x3d, 0x31, 0x8d, 0x17, 0xdb, 0x37, 0x32, 0x54, 0x06,
                0xbc, 0xe5,
            ]);
            double_benchmark(rng)
        })
    });

    let description = "mul arithmetic bench";
    c.bench_function(description, |b| {
        b.iter(|| {
            let rng = XorShiftRng::from_seed([
                0x59, 0x62, 0xbe, 0x5d, 0x76, 0x3d, 0x31, 0x8d, 0x17, 0xdb, 0x37, 0x32, 0x54, 0x06,
                0xbc, 0xe5,
            ]);
            mul_benchmark(rng)
        })
    });

    let description = "square arithmetic bench";
    c.bench_function(description, |b| {
        b.iter(|| {
            let rng = XorShiftRng::from_seed([
                0x59, 0x62, 0xbe, 0x5d, 0x76, 0x3d, 0x31, 0x8d, 0x17, 0xdb, 0x37, 0x32, 0x54, 0x06,
                0xbc, 0xe5,
            ]);
            square_benchmark(rng)
        })
    });
}

criterion_group! {
    name = arithmetic;
    config = Criterion::default().sample_size(100);
    targets = field_arithmetic_benchmark
}

criterion_main!(arithmetic);
