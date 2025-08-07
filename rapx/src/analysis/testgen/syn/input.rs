use rand::{rngs::ThreadRng, Rng};
use rustc_abi::FIRST_VARIANT;
use rustc_middle::ty::{Ty, TyCtxt, TyKind};
use rustc_type_ir::{IntTy, UintTy};
use std::ops::{Range, RangeInclusive};

pub trait InputGen {
    fn gen_bool(&mut self) -> bool;
    fn gen_int(&mut self, int_ty: IntTy) -> i64;
    fn gen_uint(&mut self, uint_ty: UintTy) -> u64;
    fn gen_float(&mut self) -> f32;
    fn gen_char(&mut self) -> char;
    fn gen_str(&mut self) -> String;

    fn gen<'tcx>(&mut self, ty: Ty<'tcx>, tcx: TyCtxt<'tcx>) -> String {
        match ty.kind() {
            TyKind::Ref(_, inner_ty, mutability) => {
                if inner_ty.is_str() && mutability.is_not() {
                    return format!("\"{}\"", self.gen_str());
                }
                format!(
                    "{}{}",
                    mutability.ref_prefix_str(),
                    self.gen(*inner_ty, tcx)
                )
            }
            TyKind::Bool => self.gen_bool().to_string(),
            TyKind::Int(int_ty) => self.gen_int(*int_ty).to_string(),
            TyKind::Uint(uint_ty) => self.gen_uint(*uint_ty).to_string(),
            TyKind::Float(_) => self.gen_float().to_string(),
            TyKind::Char => format!("'{}'", self.gen_char()),
            TyKind::Str => {
                unreachable!("str should be referenced as &str");
            }
            TyKind::Array(inner_ty, const_) => {
                let len = const_
                    .to_value()
                    .try_to_target_usize(tcx)
                    .expect("Failed to get array length");
                let mut arr: Vec<String> = Vec::new();
                for _ in 0..len {
                    arr.push(self.gen(*inner_ty, tcx).to_string());
                }
                format!("[{}]", arr.join(", "))
            }
            TyKind::Tuple(tys) => {
                let mut fields = Vec::new();
                for ty in tys.iter() {
                    fields.push(self.gen(ty, tcx).to_string());
                }
                format!("({})", fields.join(", "))
            }
            TyKind::Adt(adt_def, generic_arg) => {
                let name = tcx.def_path_str_with_args(adt_def.did(), &[]);
                if adt_def.is_struct() {
                    // generate input for each field
                    let mut fields = Vec::new();
                    for field in adt_def.all_fields() {
                        let field_name = field.name.to_string();
                        let field_type = field.ty(tcx, generic_arg);
                        let field_input = self.gen(field_type, tcx).to_string();
                        fields.push(format!("{field_name}: {field_input}"));
                    }
                    return format!("{name} {{ {} }}", fields.join(", "));
                }
                if adt_def.is_enum() {
                    let mut fields = Vec::new();
                    // Always generate the first variant

                    let variant_def = adt_def.variant(FIRST_VARIANT);
                    let variant_name = variant_def.name.to_string();
                    for field in variant_def.fields.iter() {
                        let field_name = field.name.to_string();
                        let field_type = field.ty(tcx, generic_arg);
                        let field_input = self.gen(field_type, tcx).to_string();
                        fields.push(format!("{field_name}: {field_input}"));
                    }
                    if fields.is_empty() {
                        return format!("{name}::{variant_name}");
                    }
                    return format!("{name}::{variant_name} {{ {} }}", fields.join(", "));
                }
                panic!("Unsupported ADT: {:?}", ty)
            }
            TyKind::Slice(inner_ty) => {
                let len = 3; // Fixed length for simplicity
                let element = self.gen(*inner_ty, tcx).to_string();
                format!("[{}; {}]", element, len)
            }
            _ => panic!("Unsupported type: {:?}", ty),
        }
    }
}

pub struct SillyInputGen;

impl InputGen for SillyInputGen {
    fn gen_bool(&mut self) -> bool {
        false
    }

    fn gen_int(&mut self, int_ty: IntTy) -> i64 {
        42
    }

    fn gen_uint(&mut self, uint_ty: UintTy) -> u64 {
        42
    }

    fn gen_float(&mut self) -> f32 {
        42.0
    }

    fn gen_char(&mut self) -> char {
        'a'
    }

    fn gen_str(&mut self) -> String {
        "don't panic".to_owned()
    }
}

pub struct RandomGen<R: Rng> {
    rng: R,
}

impl RandomGen<ThreadRng> {
    pub fn new() -> RandomGen<ThreadRng> {
        RandomGen { rng: rand::rng() }
    }
}

fn range_for_int_ty(int_ty: IntTy) -> Range<i64> {
    let bit_width = int_ty.bit_width().unwrap_or(32) as u32;
    -(2i64.pow(bit_width - 1))..2i64.pow(bit_width - 1) - 1
}

fn range_for_uint_ty(uint_ty: UintTy) -> Range<u64> {
    let bit_width = uint_ty.bit_width().unwrap_or(32) as u32;
    0..2u64.pow(bit_width) - 1
}

fn gen_random_utf8_seq<R: Rng>(rng: &mut R, min_len: usize, max_len: usize) -> String {
    let len = rng.random_range(min_len..=max_len);
    rng.random_iter::<char>().take(len).collect()
}

impl<R: Rng> InputGen for RandomGen<R> {
    fn gen_bool(&mut self) -> bool {
        self.rng.random()
    }

    fn gen_int(&mut self, int_ty: IntTy) -> i64 {
        self.rng.random_range(range_for_int_ty(int_ty))
    }

    fn gen_uint(&mut self, uint_ty: UintTy) -> u64 {
        self.rng.random_range(range_for_uint_ty(uint_ty))
    }

    fn gen_float(&mut self) -> f32 {
        self.rng.random()
    }

    fn gen_char(&mut self) -> char {
        gen_random_utf8_seq(&mut self.rng, 1, 1)
            .chars()
            .nth(0)
            .unwrap()
    }

    fn gen_str(&mut self) -> String {
        gen_random_utf8_seq(&mut self.rng, 0, 16)
    }
}
