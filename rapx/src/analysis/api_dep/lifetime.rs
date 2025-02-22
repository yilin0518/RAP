// use rustc_hir::def_id::DefId;
// use rustc_middle::ty::{self, Ty, TyCtxt};
// use std::collections::HashMap;
// #[derive(Hash, Eq, PartialEq, Debug)]
// pub enum LifetimeKind {
//     Static,
//     Bound(usize),
//     An(usize),
// }

// #[derive(Hash, Eq, PartialEq, Debug)]
// pub struct Lifetime {
//     pub kind: LifetimeKind,
//     pub id: usize,
// }

// pub struct Map {
//     pub map: HashMap<(DefId, usize), Lifetime>, // (fn_def_id, param_no) -> Lifetime
//     pub count: usize,
// }

// impl Map {
//     pub fn new() -> Map {
//         Map {
//             map: HashMap::new(),
//             count: 0,
//         }
//     }

//     pub fn insert(&mut self, def_id: DefId, no: usize, lifetime: Lifetime) {
//         self.map.insert((def_id, no), lifetime);
//     }
//     pub fn get(&self, def_id: DefId, no: usize) -> Option<&Lifetime> {
//         self.map.get(&(def_id, no))
//     }
//     pub fn get_mut(&mut self, def_id: DefId, no: usize) -> Option<&mut Lifetime> {
//         self.map.get_mut(&(def_id, no))
//     }
//     pub fn count(&self) -> usize {
//         self.count
//     }
//     fn new_count(&mut self) -> usize {
//         self.count += 1;
//         self.count
//     }

//     fn get_region_index<'tcx>(tcx: TyCtxt<'tcx>,region: ty::Region<'tcx>){
//         match region.kind() {
//             ty::RegionKind::ReEarlyParam(early_param) => {
//                 early_param.index
//             }
//             ty::RegionKind::ReLateParam(_, _) => todo!(),
//             _ => unreachable!("unexpected region: {:?}", region),
//         };
//     }

//     pub fn get_or_create_lifetime_from_region<'tcx>(
//         &mut self,
//         tcx: TyCtxt<'tcx>,
//         fn_def_id: DefId,
//         generics: ty::Generics,
//         region: ty::Region<'tcx>,
//     ) -> Lifetime {
//         let index_no = 

//         match region.kind() {
//             ty::RegionKind::ReEarlyParam(early_param) => Lifetime { kind: LifetimeKind::Bound, name: (), id: () }
//             ty::RegionKind::ReLateParam(_) => todo!(),
//             ty::RegionKind::ReStatic => todo!(),
//             _ => unreachable!("unexpected region: {:?}", region),
//         }
//     }
// }
