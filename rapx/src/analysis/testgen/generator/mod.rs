pub mod ltgen;
pub mod rulf;

use super::context::Context;

pub trait Generator {
    fn gen<'tcx, C: Context<'tcx> + Clone>(&mut self, cx: C) -> C {
        let mut new_cx = cx.clone();
        self.gen_in_place(&mut new_cx);
        new_cx
    }
    fn gen_in_place<'tcx, C: Context<'tcx>>(&mut self, cx: &mut C);
}
