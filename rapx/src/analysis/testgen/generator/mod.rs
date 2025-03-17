pub mod context;
pub mod ltgen;
pub mod utils;
use context::Context;

pub trait Generator {
    fn gen<'cx>(&mut self, cx: Context<'cx>) -> Context<'cx> {
        let mut new_cx = cx.clone();
        self.gen_in_place(&mut new_cx);
        new_cx
    }
    fn gen_in_place<'cx>(&mut self, cx: &mut Context<'cx>);
}
