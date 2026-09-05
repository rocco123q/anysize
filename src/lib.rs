use std::ops::{Add, AddAssign, Sub, SubAssign};

/// For generating conversion functions between data types
macro_rules! generate_type_conversion_fn {
    {
        $vis:vis $a_base_ident:ident => $b_base_ident:ident as $ident:ident {
            $(#[feature($feature:literal)] $ty:ident as $name:ident),+$(,)?
        }
    } => {
        $(
            #[cfg(feature = $feature)]
            #[cfg_attr(not(feature = $feature), allow(rust_analyzer::inactive_code))]
            const _: () = {
                concat_idents::concat_idents!(a = $a_base_ident, $name {
                    type $a_base_ident = a;
                });
                concat_idents::concat_idents!(b = $b_base_ident, $name {
                    type $b_base_ident = b;
                });
                concat_idents::concat_idents!(into_b = as_, $ident {
                    impl $a_base_ident {
                        #[must_use]
                        $vis const fn into_b(self) -> $b_base_ident {
                            if $a_base_ident::BITS.gt($b_base_ident::BITS) {
                                $b_base_ident::new(self.get().div_ceil($a_base_ident::BITS.get() / $b_base_ident::BITS.get()))
                            } else {
                                $b_base_ident::new(self.get().div_ceil($b_base_ident::BITS.get() / $a_base_ident::BITS.get()))
                            }
                        }
                    }
                    impl Into<$b_base_ident> for $a_base_ident {
                        #[inline(always)]
                        fn into(self) -> $b_base_ident {
                            self.into_b()
                        }
                    }
                });
            };
        )+
    };
}
/// For generating conversion functions between inner types
macro_rules! generate_size_conversion_fn {
    {
        $vis:vis $base_ident:ident as $ident:ident {
            $(#[features($feature_a:literal, $feature_b:literal)] $(#[pointer_size($ptr_size:literal)])? $a_ty:ident as $a_name:ident $cmp:tt $b_ty:ident as $b_name:ident),+$(,)?
        }
    } => {
        $(
            #[cfg(all(feature = $feature_a, feature = $feature_b$(, target_pointer_width = $ptr_size)?))]
            #[cfg_attr(not(all(feature = $feature_a, feature = $feature_b$(, target_pointer_width = $ptr_size)?)), allow(rust_analyzer::inactive_code))]
            const _: () = {
            concat_idents::concat_idents!(a = $base_ident, $a_name {
                type $a_name = a;
            });
            concat_idents::concat_idents!(b = $base_ident, $b_name {
                type $b_name = b;
            });
            concat_idents::concat_idents!(into_b = as_, $b_ty {
                impl $a_name {
                    #[must_use]
                    #[inline(always)]
                    $vis const fn into_b(self) -> $b_name {
                        if 1 $cmp 0 {
                            assert!(self.get() <= $b_ty::MAX as $a_ty);
                        }
                        $b_name::new(self.get() as $b_ty)
                    }
                }
                impl Into<$b_name> for $a_name {
                    #[inline(always)]
                    fn into(self) -> $b_name {
                        self.into_b()
                    }
                }
            });
            concat_idents::concat_idents!(into_a = as_, $a_ty {
                impl $b_name {
                    #[must_use]
                    #[inline(always)]
                    $vis const fn into_a(self) -> $a_name {
                        if 0 $cmp 1 {
                            assert!(self.get() <= $a_ty::MAX as $b_ty);
                        }
                        $a_name::new(self.get() as $a_ty)
                    }
                }
                impl Into<$a_name> for $b_name {
                    #[inline(always)]
                    fn into(self) -> $a_name {
                        self.into_a()
                    }
                }
            });
        };)+
    };
}
/// Generating the type itself + some basic functionality with itself
macro_rules! generate_base {
    {
        $words:ident = $bit_size:literal;
        $vis:vis struct $base_ident:ident: $(#[feature($feature:literal)] $var_ty:ident $(as $var_ident:ident)?),+;
    } => {
        $(
            #[cfg(feature = $feature)]
            #[cfg_attr(not(feature = $feature), allow(rust_analyzer::inactive_code))]
            concat_idents::concat_idents!(struct_ident = $base_ident $(, $var_ident)? {
                //#[derive(Debug, Default, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
                $vis struct struct_ident {
                   pub(self) inner: $var_ty
                }

                impl Clone for struct_ident {
                    fn clone(&self) -> Self {
                        Self::new(self.inner)
                    }
                }
                impl Copy for struct_ident {}

                impl struct_ident {
                    concat_idents::concat_idents!(bits_ident = Bits $(, $var_ident)? {
                        $vis const BITS: bits_ident = bits_ident::new($bit_size);
                    });

                    $vis const ZERO: Self = Self::new(0);
                    $vis const ONE: Self = Self::new(1);
                    $vis const MAX: Self = Self::new($var_ty::MAX);

                    #[must_use]
                    #[inline(always)]
                    $vis const fn new($words: $var_ty) -> Self {
                        Self { inner: $words }
                    }
                    #[must_use]
                    #[inline(always)]
                    $vis const fn get(self) -> $var_ty {
                        self.inner
                    }
                    #[must_use]
                    $vis const fn of<T>() -> Self {
                        let size = if $bit_size < 8 {
                            size_of::<T>() * $bit_size
                        } else if $bit_size == 8 {
                            size_of::<T>()
                        } else {
                            size_of::<T>().div_ceil($bit_size / 8)
                        };
                        assert!(size <= $var_ty::MAX as usize);
                        Self::new(size as $var_ty)
                    }
                    #[must_use]
                    #[inline(always)]
                    $vis const fn next_power_of_two(self) -> Self {
                        Self::new(self.get().next_power_of_two())
                    }
                    #[must_use]
                    #[inline(always)]
                    $vis const fn is_power_of_two(self) -> bool {
                        self.get().is_power_of_two()
                    }

                    #[must_use]
                    #[inline(always)]
                    $vis const fn add(self, other: Self) -> Self {
                        Self::new(self.inner + other.inner)
                    }
                    #[must_use]
                    #[inline(always)]
                    $vis const fn sub(self, other: Self) -> Self {
                        Self::new(self.inner - other.inner)
                    }
                    #[must_use]
                    #[inline(always)]
                    $vis const fn mul(self, other: $var_ty) -> Self {
                        Self::new(self.inner * other)
                    }
                    #[must_use]
                    #[inline(always)]
                    $vis const fn div(self, other: $var_ty) -> Self {
                        Self::new(self.inner / other)
                    }
                    #[must_use]
                    #[inline(always)]
                    $vis const fn div_ceil(self, other: $var_ty) -> Self {
                        Self::new(self.inner.div_ceil(other))
                    }

                    #[must_use]
                    #[inline(always)]
                    $vis const fn eq(self, other: Self) -> bool {
                        self.inner == other.inner
                    }
                    #[must_use]
                    #[inline(always)]
                    $vis const fn ne(self, other: Self) -> bool {
                        self.inner != other.inner
                    }
                    #[must_use]
                    #[inline(always)]
                    $vis const fn gt(self, other: Self) -> bool {
                        self.inner > other.inner
                    }
                    #[must_use]
                    #[inline(always)]
                    $vis const fn ge(self, other: Self) -> bool {
                        self.inner >= other.inner
                    }
                    #[must_use]
                    #[inline(always)]
                    $vis const fn lt(self, other: Self) -> bool {
                        self.inner < other.inner
                    }
                    #[must_use]
                    #[inline(always)]
                    $vis const fn le(self, other: Self) -> bool {
                        self.inner <= other.inner
                    }

                    #[must_use]
                    #[inline(always)]
                    $vis const fn min(self, other: Self) -> Self {
                        if self.lt(other) {
                            self
                        } else {
                            other
                        }
                    }
                    #[must_use]
                    #[inline(always)]
                    $vis const fn max(self, other: Self) -> Self {
                        if self.gt(other) {
                            self
                        } else {
                            other
                        }
                    }
                    #[must_use]
                    #[inline(always)]
                    $vis const fn clamp(self, min: Self, max: Self) -> Self {
                        assert!(min.le(max));
                        if self.le(min) {
                            min
                        } else if self.ge(max) {
                            max
                        } else {
                            self
                        }
                    }
                }

                impl Add for struct_ident {
                    type Output = Self;

                    #[inline(always)]
                    fn add(self, rhs: Self) -> Self::Output {
                        self.add(rhs)
                    }
                }
                impl AddAssign for struct_ident {
                    #[inline(always)]
                    fn add_assign(&mut self, rhs: Self) {
                        *self = self.add(rhs);
                    }
                }
                impl Sub for struct_ident {
                    type Output = Self;

                    #[inline(always)]
                    fn sub(self, rhs: Self) -> Self::Output {
                        self.sub(rhs)
                    }
                }
                impl SubAssign for struct_ident {
                    #[inline(always)]
                    fn sub_assign(&mut self, rhs: Self) {
                        *self = self.sub(rhs);
                    }
                }
            });
        )+
    };
}
macro_rules! generate {
    ($vis:vis $words:ident = $bit_size:literal as $name:ident $(, impl Into<$(#[feature($feature:literal)] $impl_ty:ident as $impl_words:ident),+$(,)?>)*) => {
        generate_base! {
            $words = $bit_size;
            $vis struct $name:
                #[feature("u8")] u8 as U8,
                #[feature("u16")] u16 as U16,
                #[feature("u32")] u32 as U32,
                #[feature("u64")] u64 as U64,
                #[feature("u128")] u128 as U128,
                #[feature("usize")] usize as USize;
        }
        generate_size_conversion_fn! {
            $vis $name as $words {
                #[features("u8", "usize")] u8 as U8 < usize as USize,
                #[features("u8", "u16")] u8 as U8 < u16 as U16,
                #[features("u8", "u32")] u8 as U8 < u32 as U32,
                #[features("u8", "u64")] u8 as U8 < u64 as U64,
                #[features("u8", "u128")] u8 as U8 < u128 as U128,
                #[features("u16", "u32")] u16 as U16 < u32 as U32,
                #[features("u16", "u64")] u16 as U16 < u64 as U64,
                #[features("u16", "u128")] u16 as U16 < u128 as U128,
                #[features("u32", "u64")] u32 as U32 < u64 as U64,
                #[features("u32", "u128")] u32 as U32 < u128 as U128,
                #[features("u64", "u128")] u64 as U64 < u128 as U128,

                #[features("usize", "u16")] #[pointer_size("16")] usize as USize == u16 as U16,
                #[features("usize", "u32")] #[pointer_size("16")] usize as USize < u32 as U32,
                #[features("usize", "u64")] #[pointer_size("16")] usize as USize < u64 as U64,

                #[features("usize", "u16")] #[pointer_size("32")] usize as USize > u16 as U16,
                #[features("usize", "u32")] #[pointer_size("32")] usize as USize == u32 as U32,
                #[features("usize", "u64")] #[pointer_size("32")] usize as USize < u64 as U64,

                #[features("usize", "u16")] #[pointer_size("64")] usize as USize > u16 as U16,
                #[features("usize", "u32")] #[pointer_size("64")] usize as USize > u32 as U32,
                #[features("usize", "u64")] #[pointer_size("64")] usize as USize == u64 as U64,

                #[features("usize", "u128")] usize as USize < u128 as U128,
            }
        }
        $(
            $(
                #[cfg(feature = $feature)]
                #[cfg_attr(not(feature = $feature), allow(rust_analyzer::inactive_code))]
                generate_type_conversion_fn! {
                    $vis $name => $impl_ty as $impl_words {
                        #[feature("u8")] u8 as U8,
                        #[feature("u16")] u16 as U16,
                        #[feature("u32")] u32 as U32,
                        #[feature("u64")] u64 as U64,
                        #[feature("u128")] u128 as U128,
                        #[feature("usize")] usize as USize,
                    }
                }
            )+
        )?
    };
}

#[cfg(feature = "bits")]
generate!(pub bits = 1 as Bits, impl Into<
    #[feature("bytes")] Bytes as bytes,
    #[feature("hwords")] HWords as hwords,
    #[feature("words")] Words as words,
    #[feature("dwords")] DWords as dwords,
    #[feature("qwords")] QWords as qwords,
>);

#[cfg(feature = "bytes")]
generate!(pub bytes = 8 as Bytes, impl Into<
    #[feature("bits")] Bits as bits,
    #[feature("hwords")] HWords as hwords,
    #[feature("words")] Words as words,
    #[feature("dwords")] DWords as dwords,
    #[feature("qwords")] QWords as qwords,
>);

#[cfg(feature = "hwords")]
generate!(pub hwords = 16 as HWords, impl Into<
    #[feature("bits")] Bits as bits,
    #[feature("bytes")] Bytes as bytes,
    #[feature("words")] Words as words,
    #[feature("dwords")] DWords as dwords,
    #[feature("qwords")] QWords as qwords,
>);

#[cfg(feature = "words")]
generate!(pub words = 32 as Words, impl Into<
    #[feature("bits")] Bits as bits,
    #[feature("bytes")] Bytes as bytes,
    #[feature("hwords")] HWords as hwords,
    #[feature("dwords")] DWords as dwords,
    #[feature("qwords")] QWords as qwords,
>);

#[cfg(feature = "dwords")]
generate!(pub dwords = 64 as DWords, impl Into<
    #[feature("bits")] Bits as bits,
    #[feature("bytes")] Bytes as bytes,
    #[feature("hwords")] HWords as hwords,
    #[feature("words")] Words as words,
    #[feature("qwords")] QWords as qwords,
>);

#[cfg(feature = "qwords")]
generate!(pub qwords = 128 as QWords, impl Into<
    #[feature("bits")] Bits as bits,
    #[feature("bytes")] Bytes as bytes,
    #[feature("hwords")] HWords as hwords,
    #[feature("words")] Words as words,
    #[feature("dwords")] DWords as dwords,
>);
