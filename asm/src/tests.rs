#[cfg(test)]
mod test {
    #[cfg(all(target_arch = "x86_64", target_feature = "adx"))]
    use crate::arithmetic::asm_add_mod;

    #[test]
    fn add_mod_test() {
        use super::asm_add_mod;
        let limbs = [
            0xFFFFFFFFFFFFFF85,
            0xFFFFFFFFFFFFFFFF,
            0xFFFFFFFFFFFFFFFF,
            0xFFFFFFFFFFFFFFFF,
        ];
        let added = asm_add_mod(&limbs, &limbs);
        let sum = [
            0xAC96341C4FFFFF80,
            0x36FC76959F60CD29,
            0x666EA36F7879462E,
            0xE0A77C19A07DF2F,
        ];
        assert_eq!(added, sum);
    }

    #[test]
    fn sample_test() {
        assert_eq!(true, true)
    }
}
