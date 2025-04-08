pub mod context;
pub mod ltgen;
pub mod stmt;
pub mod syn;
pub mod utils;
pub mod input;
pub mod rulf;
use context::ContextBase;

pub trait Generator {
    fn gen<'tcx>(&mut self, cx: ContextBase<'tcx>) -> ContextBase<'tcx> {
        let mut new_cx = cx.clone();
        self.gen_in_place(&mut new_cx);
        new_cx
    }
    fn gen_in_place<'tcx>(&mut self, cx: &mut ContextBase<'tcx>);
}