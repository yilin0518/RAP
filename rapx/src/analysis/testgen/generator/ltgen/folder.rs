use rustc_infer::infer::{self, InferCtxt, TyCtxtInferExt};
use rustc_middle::ty::{self, Ty, TyCtxt};
use rustc_span::DUMMY_SP;

pub struct RegionExtractFolder<'tcx> {
    tcx: TyCtxt<'tcx>,
    regions: Vec<ty::Region<'tcx>>,
}

impl<'tcx> RegionExtractFolder<'tcx> {
    pub fn new(tcx: TyCtxt<'tcx>) -> RegionExtractFolder<'tcx> {
        RegionExtractFolder {
            tcx,
            regions: Vec::new(),
        }
    }
    pub fn regions(&self) -> &[ty::Region<'tcx>] {
        &self.regions
    }
}

impl<'tcx> ty::TypeFolder<TyCtxt<'tcx>> for RegionExtractFolder<'tcx> {
    fn cx(&self) -> TyCtxt<'tcx> {
        self.tcx
    }
    fn fold_region(&mut self, region: ty::Region<'tcx>) -> ty::Region<'tcx> {
        match region.kind() {
            ty::RegionKind::ReVar(_) | ty::RegionKind::ReStatic => {
                self.regions.push(region);
            }
            _ => {
                panic!("unexpected region kind: {:?}", region);
            }
        }
        region
    }
}

pub struct FreeVarFolder<'tcx> {
    tcx: TyCtxt<'tcx>,
    offset: usize,
}

impl<'tcx> FreeVarFolder<'tcx> {
    pub fn new(tcx: TyCtxt<'tcx>, offset: usize) -> FreeVarFolder<'tcx> {
        FreeVarFolder { tcx, offset }
    }
    pub fn current_offset(&self) -> usize {
        self.offset
    }
}

impl<'tcx> ty::TypeFolder<TyCtxt<'tcx>> for FreeVarFolder<'tcx> {
    fn cx(&self) -> TyCtxt<'tcx> {
        self.tcx
    }
    fn fold_region(&mut self, region: ty::Region<'tcx>) -> ty::Region<'tcx> {
        match region.kind() {
            ty::ReVar(_) | ty::ReStatic => region,
            _ => {
                let region =
                    ty::Region::new_var(self.cx(), ty::RegionVid::from_u32(self.offset as u32));
                self.offset += 1;
                region
            }
        }
    }
}

pub struct InfcxVarFolder<'tcx, 'a> {
    infcx: &'a InferCtxt<'tcx>,
    tcx: TyCtxt<'tcx>,
    cnt: usize,
}

impl<'tcx, 'a> InfcxVarFolder<'tcx, 'a> {
    pub fn new(infcx: &'a InferCtxt<'tcx>, tcx: TyCtxt<'tcx>) -> InfcxVarFolder<'tcx, 'a> {
        InfcxVarFolder { infcx, tcx, cnt: 0 }
    }

    pub fn cnt(&self) -> usize {
        self.cnt
    }
}

impl<'tcx, 'a> ty::TypeFolder<TyCtxt<'tcx>> for InfcxVarFolder<'tcx, 'a> {
    fn cx(&self) -> TyCtxt<'tcx> {
        self.tcx
    }
    fn fold_region(&mut self, region: ty::Region<'tcx>) -> ty::Region<'tcx> {
        match region.kind() {
            ty::ReVar(_) => {
                panic!("unexpected region kind: {:?}", region);
            }
            _ => {
                self.cnt += 1;
                self.infcx.next_region_var(infer::MiscVariable(DUMMY_SP))
            }
        }
    }
}
