use rand::{rng, Rng};
use rustc_middle::ty::cast::IntTy;
use rustc_middle::ty::{self, Ty, TyCtxt, TyKind};
use rustc_target::abi::{VariantIdx, FIRST_VARIANT};

pub trait InputGen {
    fn gen<'tcx>(&mut self, ty: Ty<'tcx>, tcx: TyCtxt<'tcx>) -> String;
}

pub struct SillyInputGen;

impl InputGen for SillyInputGen {
    fn gen<'tcx>(&mut self, ty: Ty<'tcx>, tcx: TyCtxt<'tcx>) -> String {
        let ty = ty.peel_refs();
        match ty.kind() {
            TyKind::Bool => "false".to_owned(),
            TyKind::Int(_) => "42".to_owned(),
            TyKind::Uint(_) => "42".to_owned(),
            TyKind::Float(_) => "42.0".to_owned(),
            TyKind::Str => "\"don't panic\"".to_owned(),
            TyKind::Char => "'a'".to_owned(),
            TyKind::Array(..) => "[42]".to_owned(),
            TyKind::Tuple(..) => "()".to_owned(),
            TyKind::Adt(adt_def, generic_arg) => {
                let name = tcx.def_path_str(adt_def.did());
                if adt_def.is_struct() {
                    // generate input for each field
                    let mut fields = Vec::new();
                    for field in adt_def.all_fields() {
                        let field_name = field.name.to_string();
                        let field_type = field.ty(tcx, generic_arg);
                        let field_input = self.gen(field_type, tcx);
                        fields.push(format!("{field_name}: {field_input}"));
                    }
                    return format!("{name} {{ {} }}", fields.join(", "));
                }
                if adt_def.is_enum() {
                    let mut fields = Vec::new();
                    let variant_def = adt_def.variant(FIRST_VARIANT);
                    for field in variant_def.fields.iter() {
                        let field_name = field.name.to_string();
                        let field_type = field.ty(tcx, generic_arg);
                        let field_input = self.gen(field_type, tcx);
                        fields.push(format!("{field_input}"));
                    }
                    return format!("{name} {{ {} }}", fields.join(", "));
                }
                panic!("Unsupported ADT: {:?}", ty)
            }

            _ => panic!("Unsupported type: {:?}", ty),
        }
    }
}

// struct InputGen {
//     rng: rand::rngs::ThreadRng,
// }

// impl InputGen {
//     fn new() -> Self {
//         Self { rng: rng() }
//     }
//     fn gen_bool(&mut self) -> bool {
//         self.rng.random_bool(0.5)
//     }
//     fn gen_int(&mut self) -> i32 {
//         self.rng.random()
//     }
// }
