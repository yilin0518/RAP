pub mod context;
pub mod ltgen;
pub mod syn;
pub mod utils;
use context::Context;

pub trait Generator {
    fn gen<'tcx>(&mut self, cx: Context<'tcx>) -> Context<'tcx> {
        let mut new_cx = cx.clone();
        self.gen_in_place(&mut new_cx);
        new_cx
    }
    fn gen_in_place<'tcx>(&mut self, cx: &mut Context<'tcx>);
}
