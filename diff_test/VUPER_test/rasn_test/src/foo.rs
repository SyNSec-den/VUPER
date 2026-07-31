#[allow(
    non_camel_case_types,
    non_snake_case,
    non_upper_case_globals,
    unused,
    clippy::too_many_arguments
)]
pub mod foo {
    extern crate alloc;
    use core::borrow::Borrow;
    use lazy_static::lazy_static;
    use rasn::prelude::*;
    #[derive(AsnType, Debug, Clone, Decode, Encode, PartialEq, Eq, Hash)]
    #[rasn(automatic_tags)]
    #[non_exhaustive]
    pub struct S1 {
        pub b1: bool,
        #[rasn(extension_addition)]
        pub b2: Option<bool>,
    }
    impl S1 {
        pub fn new(b1: bool, b2: Option<bool>) -> Self {
            Self { b1, b2 }
        }
    }
}
