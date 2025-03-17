use super::utils;
use crate::rap_debug;
use rustc_hir::def_id::DefId;
use rustc_middle::ty::{self, Ty, TyCtxt, TyKind};

#[derive(Debug, Copy, Clone)]
pub enum ArgSrc<'cx> {
    Input,
    Call(&'cx ApiCall<'cx>),
}

impl<'cx> ArgSrc<'cx> {
    pub fn input() -> ArgSrc<'cx> {
        ArgSrc::Input
    }
}

#[derive(Debug, Clone)]
pub struct ApiCall<'cx> {
    pub fn_did: DefId,
    pub args: Vec<ArgSrc<'cx>>, // restore where arg instance from
}

#[derive(Debug, Clone)]

pub struct Context<'cx> {
    api_seq: Vec<ApiCall<'cx>>,
}

impl<'cx> Context<'cx> {
    pub fn new() -> Context<'cx> {
        Context {
            api_seq: Vec::new(),
        }
    }
}
