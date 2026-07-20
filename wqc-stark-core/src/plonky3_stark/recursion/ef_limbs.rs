//! Shared EF\<M31, 3\> limb arithmetic for recursion AIRs (binomial \(X^3 - 5\)).

use p3_air::AirBuilder;
use p3_field::{Field, PrimeCharacteristicRing};

/// Extension mul of two EF elements.
pub fn ef_mul_limbs<AB: AirBuilder>(a: &[AB::Expr; 3], b: &[AB::Expr; 3]) -> [AB::Expr; 3]
where
    AB::F: PrimeCharacteristicRing,
{
    let w: AB::Expr = AB::F::from_u32(5).into();
    let a0_b0 = a[0].clone() * b[0].clone();
    let a1_b1 = a[1].clone() * b[1].clone();
    let a2_b2 = a[2].clone() * b[2].clone();
    let c0 = a0_b0.clone()
        + ((a[1].clone() + a[2].clone()) * (b[1].clone() + b[2].clone())
            - a1_b1.clone()
            - a2_b2.clone())
            * w.clone();
    let c1 = (a[0].clone() + a[1].clone()) * (b[0].clone() + b[1].clone())
        - a0_b0.clone()
        - a1_b1.clone()
        + a2_b2.clone() * w;
    let c2 = (a[0].clone() + a[2].clone()) * (b[0].clone() + b[2].clone()) - a0_b0 - a2_b2 + a1_b1;
    [c0, c1, c2]
}

pub fn ef_add_limbs<AB: AirBuilder>(a: &[AB::Expr; 3], b: &[AB::Expr; 3]) -> [AB::Expr; 3] {
    [
        a[0].clone() + b[0].clone(),
        a[1].clone() + b[1].clone(),
        a[2].clone() + b[2].clone(),
    ]
}

pub fn ef_sub_limbs<AB: AirBuilder>(a: &[AB::Expr; 3], b: &[AB::Expr; 3]) -> [AB::Expr; 3] {
    [
        a[0].clone() - b[0].clone(),
        a[1].clone() - b[1].clone(),
        a[2].clone() - b[2].clone(),
    ]
}

pub fn ef_halve_limbs<AB: AirBuilder>(a: &[AB::Expr; 3]) -> [AB::Expr; 3]
where
    AB::F: Field + PrimeCharacteristicRing,
{
    // 2^{-1} = 2^{30} over Mersenne31.
    let inv2: AB::Expr = AB::F::from_u32(1u32 << 30).into();
    [
        a[0].clone() * inv2.clone(),
        a[1].clone() * inv2.clone(),
        a[2].clone() * inv2,
    ]
}

pub fn ef_scale_by_base<AB: AirBuilder>(a: &[AB::Expr; 3], s: AB::Expr) -> [AB::Expr; 3] {
    [
        a[0].clone() * s.clone(),
        a[1].clone() * s.clone(),
        a[2].clone() * s,
    ]
}

pub fn ef_square_limbs<AB: AirBuilder>(a: &[AB::Expr; 3]) -> [AB::Expr; 3]
where
    AB::F: PrimeCharacteristicRing,
{
    ef_mul_limbs::<AB>(a, a)
}

/// Assert `a == b` limbwise.
pub fn ef_assert_eq<AB: AirBuilder>(builder: &mut AB, a: &[AB::Expr; 3], b: &[AB::Expr; 3]) {
    for i in 0..3 {
        builder.assert_zero(a[i].clone() - b[i].clone());
    }
}
