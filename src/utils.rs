use revm::primitives::U256;

pub fn u256_to_u64(value: &U256) -> Option<u64> {
    let limbs = value.as_limbs();

    if limbs[1] > 0 || limbs[2] > 0 || limbs[3] > 0 {
        None
    } else {
        Some(limbs[0])
    }
}
