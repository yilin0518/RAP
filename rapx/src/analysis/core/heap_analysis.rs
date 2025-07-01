pub mod default;

use rustc_abi::VariantIdx;
use rustc_middle::ty::{Ty, TyCtxt, TyKind};
use rustc_span::def_id::DefId;

use std::{
    collections::{HashMap, HashSet},
    env, fmt,
};

use crate::{rap_info, Analysis};

#[repr(u8)]
#[derive(Copy, Clone, Debug, Eq, PartialEq, Hash)]
pub enum RawTypeOwner {
    Unowned = 0,
    Owned = 1,
    Unknown = 2,
}

impl Default for RawTypeOwner {
    fn default() -> Self {
        Self::Unknown
    }
}

impl RawTypeOwner {
    pub fn is_owned(&self) -> bool {
        match self {
            RawTypeOwner::Owned => true,
            _ => false,
        }
    }
}

impl fmt::Display for RawTypeOwner {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let name = match self {
            RawTypeOwner::Unowned => "0",
            RawTypeOwner::Owned => "1",
            RawTypeOwner::Unknown => "2",
        };
        write!(f, "{}", name)
    }
}

pub type HAResult = HashMap<DefId, Vec<(RawTypeOwner, Vec<bool>)>>;

pub trait HeapAnalysis: Analysis {
    fn get_all_items(&mut self) -> HAResult;
}

#[derive(Copy, Clone, Debug)]
pub struct HeapItem;

impl HeapItem {
    /// This method is used to check if one adt-def is already a heap item.
    /// It is a summary of one type which demonstrate that we will consider all the fields/variants,
    /// although the analyzer will not traverse them (thus overhead is cheap).
    ///
    /// # Safety
    /// If `ty` is not an adt, the result is `Err`.
    ///
    /// # Case `ty::Ty`
    /// Given the adt `MyVec<T, A>` the result is `Ok(true)`.
    /// ```rust
    /// pub struct MyVec<T, A: Allocator = Global> {
    ///    buf: RawVec<T, A>, // this field is a heap item
    ///    len: usize,
    /// }
    /// ```
    ///
    /// # Example:
    /// ```rust
    ///  use rap::analysis::core::heap_item::HeapItem;
    ///  let ans = HeapItem::is_adt(rcanary.rcx, vec.ty);
    /// ```
    pub fn is_adt<'tcx>(adt_owner: HAResult, ty: Ty<'tcx>) -> Result<bool, &'static str> {
        match ty.kind() {
            TyKind::Adt(adtdef, ..) => {
                let ans = adt_owner.get(&adtdef.0 .0.did).unwrap();
                for i in ans.iter() {
                    if i.0 == RawTypeOwner::Owned {
                        return Ok(true);
                    }
                }
                Ok(false)
            }
            _ => Err("The input is not an ADT"),
        }
    }

    /// This method is used to check if one adt-def of the struct is already a heap item.
    /// It is a summary of one type which demonstrate that we will consider all the fields,
    /// although the analyzer will not traverse them (thus overhead is cheap).
    ///
    /// # Safety
    /// If `ty` is not an adt, the result is `Err`.
    /// If the input is the def of an enum type, the result is `Err`.
    ///
    /// # Case `ty::Ty`
    /// Given the adt `MyVec<T, A>` the result is `Ok(true)`.
    /// ```rust
    /// pub struct MyVec<T, A: Allocator = Global> {
    ///    buf: RawVec<T, A>, // this field is a heap item
    ///    len: usize,
    /// }
    /// ```
    ///
    /// # Example:
    /// ```rust
    /// use rap::analysis::core::heap_item::HeapItem;
    /// let ans = HeapItem::is_struct(rcanary.rcx, vec.ty);
    /// ```
    pub fn is_struct<'tcx>(adt_owner: HAResult, ty: Ty<'tcx>) -> Result<bool, &'static str> {
        match ty.kind() {
            TyKind::Adt(adtdef, ..) => {
                if !adtdef.is_struct() && !adtdef.is_union() {
                    return Err("The input is not a struct");
                }
                let ans = adt_owner.get(&adtdef.0 .0.did).unwrap();
                if ans[0].0 == RawTypeOwner::Owned {
                    return Ok(true);
                }
                Ok(false)
            }
            _ => Err("The input is not an ADT"),
        }
    }

    /// This method is used to check if one adt-def of the enum is already a heap item.
    /// It is a summary of one type which demonstrate that we will consider all the variants,
    /// although the analyzer will not traverse them (thus overhead is cheap).
    /// Note that, even for each variance, the result also analyze all its fields.
    /// It can be referred to the enum with enum-type variance.
    ///
    /// # Safety
    /// If `ty` is not an adt, the result is `Err`.
    /// If the input is the def of a struct type, the result is `Err`.
    ///
    /// # Case `ty::Ty`
    /// Given the adt `MyBuf<T>` the result is `Ok(true)`.
    /// ```rust
    /// pub enum MyBuf<T> {
    ///    Buf1(Vec<T>), // this variance is a heap item
    ///    Buf2(Vec<T>), // this variance is a heap item
    /// }
    /// ```
    ///
    /// # Example:
    /// ```rust
    /// use rap::analysis::core::heap_item::HeapItem;
    /// let ans = HeapItem::is_enum(rcanary.rcx, vec.ty);
    /// ```
    pub fn is_enum<'tcx>(adt_owner: HAResult, ty: Ty<'tcx>) -> Result<bool, &'static str> {
        match ty.kind() {
            TyKind::Adt(adtdef, ..) => {
                if !adtdef.is_enum() {
                    return Err("The input is not an enum");
                }
                let ans = adt_owner.get(&adtdef.0 .0.did).unwrap();
                for i in ans.iter() {
                    if i.0 == RawTypeOwner::Owned {
                        return Ok(true);
                    }
                }
                Ok(false)
            }
            _ => Err("The input is not an ADT"),
        }
    }

    /// This method is used to check if one variance of the enum is already a heap item.
    /// It is a summary of one variance which demonstrate that we will consider all the fields of it,
    /// although the analyzer will not traverse them (thus overhead is cheap).
    /// It can be referred to the enum with enum-type variance.
    ///
    /// # Safety
    /// If `ty` is not an adt, the result is `Err`.
    /// If the input is the def of a struct type, the result is `Err`.
    /// If the index `idx` is not valid (out of bound), the result is `Err`.
    ///
    /// # Case `ty::Ty`
    /// Given the adt `MyBuf<T>` the result for idx: 0, 1 is `Ok(true)`; the result for idx: 3 is `Err`.
    /// ```rust
    /// pub enum MyBuf<T> {
    ///    Buf1(Vec<T>), // this variance is a heap item
    ///    Buf2(Vec<T>), // this variance is a heap item
    /// }
    /// ```
    ///
    /// # Example:
    /// ```rust
    /// use rap::analysis::core::heap_item::HeapItem;
    /// let ans = HeapItem::is_enum_vidx(rcanary.rcx, vec.ty, 1);
    /// ```
    pub fn is_enum_vidx<'tcx>(
        adt_owner: HAResult,
        ty: Ty<'tcx>,
        idx: usize,
    ) -> Result<bool, &'static str> {
        match ty.kind() {
            TyKind::Adt(adtdef, ..) => {
                if !adtdef.is_enum() {
                    return Err("The input is not an enum");
                }
                let ans = adt_owner.get(&adtdef.0 .0.did).unwrap();
                if idx > ans.len() {
                    return Err("The index is not a valid variance");
                }
                if ans[idx].0 == RawTypeOwner::Owned {
                    return Ok(true);
                }
                Ok(false)
            }
            _ => Err("The input is not an ADT"),
        }
    }

    /// This method is used to give the result of all the variances of the enum.
    /// For each variance, it is a summary that we will consider all the fields of it,
    /// although the analyzer will not traverse them (thus overhead is cheap).
    /// It can be referred to the enum with enum-type variance.
    ///
    /// # Safety
    /// If `ty` is not an adt, the result is `Err`.
    /// If the input is the def of a struct type, the result is `Err`.
    ///
    /// # Case `ty::Ty`
    /// Given the adt `MyBuf<T>` the result is `[true, false]`.
    /// ```rust
    /// pub enum MyBuf<T> {
    ///    Buf1(Vec<T>), // this variance is a heap item
    ///    Buf2(()), // this variance is a heap item
    /// }
    /// ```
    ///
    /// # Example:
    /// ```rust
    /// use rap::analysis::core::heap_item::HeapItem;
    /// let ans = HeapItem::is_enum_flattened(rcanary.rcx, vec.ty);
    /// ```
    pub fn is_enum_flattened<'tcx>(
        adt_owner: HAResult,
        ty: Ty<'tcx>,
    ) -> Result<Vec<bool>, &'static str> {
        match ty.kind() {
            TyKind::Adt(adtdef, ..) => {
                if !adtdef.is_enum() {
                    return Err("The input is not an enum");
                }
                let ans = adt_owner.get(&adtdef.0 .0.did).unwrap();
                let mut v = Vec::with_capacity(ans.len());
                for i in ans.iter() {
                    if i.0 == RawTypeOwner::Owned {
                        v.push(true);
                    } else {
                        v.push(false);
                    }
                }
                Ok(v)
            }
            _ => Err("The input is not an ADT"),
        }
    }
}

pub struct IsolatedParameter;

impl IsolatedParameter {
    /// This method is used to check if one adt-def has at least one isolated parameter.
    /// It is a summary of one type which demonstrate that we will consider all the generics.
    /// Those generic parameters can be located in different fields/variants, and some of them can be
    /// found in multiple fields/variants.
    /// The analyzer will not traverse them to generate the result (thus overhead is cheap).
    ///
    /// # Safety
    /// If `ty` is not an adt, the result is `Err`.
    ///
    /// # Case `ty::Ty`
    /// Given the adt `MyVec<T, A>` the result is `Ok(true)`.
    /// ```rust
    /// pub struct MyVec<T, A: Allocator = Global> { // parameter A is an isolated parameter
    ///    buf: RawVec<T, A>,  // parameter A inside in RawVec
    ///    len: usize,
    /// }
    /// ```
    ///
    /// # Example:
    /// ```rust
    ///  use rap::analysis::core::heap_item::IsolatedParameter;
    ///  let ans = IsolatedParameter::is_adt(rcanary.rcx, vec.ty);
    /// ```
    pub fn is_adt<'tcx>(adt_owner: HAResult, ty: Ty<'tcx>) -> Result<bool, &'static str> {
        match ty.kind() {
            TyKind::Adt(adtdef, ..) => {
                let ans = adt_owner.get(&adtdef.0 .0.did).unwrap();
                for i in ans.iter() {
                    if i.1.iter().any(|&x| x == true) {
                        return Ok(true);
                    }
                }
                Ok(false)
            }
            _ => Err("The input is not an ADT"),
        }
    }

    /// This method is used to check if one adt-def of the struct has at least one isolated parameter.
    /// It is a summary of one type which demonstrate that we will consider all the generics.
    /// Those generic parameters can be located in different fields, and some of them can be
    /// found in multiple fields.
    /// The analyzer will not traverse them to generate the result (thus overhead is cheap).
    ///
    /// # Safety
    /// If `ty` is not an adt, the result is `Err`.
    ///
    /// # Case `ty::Ty`
    /// Given the adt `MyVec<T, A>` the result is `Ok(true)`.
    /// ```rust
    /// pub struct MyVec<T, A: Allocator = Global> { // parameter A is an isolated parameter
    ///    buf: RawVec<T, A>, // parameter A inside in RawVec
    ///    len: usize,
    /// }
    /// ```
    ///
    /// # Example:
    /// ```rust
    ///  use rap::analysis::core::heap_item::IsolatedParameter;
    ///  let ans = IsolatedParameter::is_adt(rcanary.rcx, vec.ty);
    /// ```
    pub fn is_struct<'tcx>(adt_owner: HAResult, ty: Ty<'tcx>) -> Result<bool, &'static str> {
        match ty.kind() {
            TyKind::Adt(adtdef, ..) => {
                if !adtdef.is_struct() && !adtdef.is_union() {
                    return Err("The input is not a struct");
                }
                let ans = adt_owner.get(&adtdef.0 .0.did).unwrap();
                if ans[0].1.iter().any(|&x| x == true) {
                    return Ok(true);
                }
                Ok(false)
            }
            _ => Err("The input is not an ADT"),
        }
    }

    /// This method is used to check if one adt-def of the enum has at least one isolated parameter.
    /// It is a summary of one type which demonstrate that we will consider all the generics in all the variants.
    /// Those generic parameters can be located in different fields, and some of them can be
    /// found in multiple fields.
    /// Note that, even for each variance, the result also analyze all its fields.
    /// It can be referred to the enum with enum-type variance.
    ///
    /// # Safety
    /// If `ty` is not an adt, the result is `Err`.
    /// If the input is the def of a struct type, the result is `Err`.
    ///
    /// # Case `ty::Ty`
    /// Given the adt `MyBuf<T, S, F>` the result is `Ok(true)`.
    /// ```rust
    /// pub enum MyBuf<T, S, F> { // parameter S F are an isolated parameters
    ///    Buf1(Vec<T>),
    ///    Buf2(S), // this variance is an isolated parameter
    ///    Buf3((F,S)), // this variance has 2 isolated parameters
    /// }
    /// ```
    ///
    /// # Example:
    /// ```rust
    ///  use rap::analysis::core::heap_item::IsolatedParameter;
    ///  let ans = IsolatedParameter::is_adt(rcanary.rcx, vec.ty);
    /// ```
    pub fn is_enum<'tcx>(adt_owner: HAResult, ty: Ty<'tcx>) -> Result<bool, &'static str> {
        match ty.kind() {
            TyKind::Adt(adtdef, ..) => {
                if !adtdef.is_enum() {
                    return Err("The input is not an enum");
                }
                let ans = adt_owner.get(&adtdef.0 .0.did).unwrap();
                for i in ans.iter() {
                    if i.1.iter().any(|&x| x == true) {
                        return Ok(true);
                    }
                }
                Ok(false)
            }
            _ => Err("The input is not an ADT"),
        }
    }

    /// This method is used to check if one variance of the enum has at least one isolated parameter.
    /// It is a summary of one type which demonstrate that we will consider all the generics in the given variance.
    /// Note that, even for this variance, the result also analyze all its fields.
    /// It can be referred to the enum with enum-type variance.
    ///
    /// # Safety
    /// If `ty` is not an adt, the result is `Err`.
    /// If the input is the def of a struct type, the result is `Err`.
    /// If the index `idx` is not valid (out of bound), the result is `Err`.
    ///
    /// # Case `ty::Ty`
    /// Given the adt `MyBuf<T, S, F>` the result for idx: 0 is `Ok(false)`; the result for idx: 1, 2 is `Ok(true)`; the result for idx: 3 is `Err`.
    /// ```rust
    /// pub enum MyBuf<T, S, F> { // parameter S F are an isolated parameters
    ///    Buf1(Vec<T>),
    ///    Buf2(S), // this variance is an isolated parameter
    ///    Buf3((F,S)), // this variance has 2 isolated parameters
    /// }
    /// ```
    ///
    /// # Example:
    /// ```rust
    ///  use rap::analysis::core::heap_item::IsolatedParameter;
    ///  let ans = IsolatedParameter::is_enum_vidx(rcanary.rcx, vec.ty, 1);
    /// ```
    pub fn is_enum_vidx<'tcx>(
        adt_owner: HAResult,
        ty: Ty<'tcx>,
        idx: usize,
    ) -> Result<bool, &'static str> {
        match ty.kind() {
            TyKind::Adt(adtdef, ..) => {
                if !adtdef.is_enum() {
                    return Err("The input is not an enum");
                }
                let ans = adt_owner.get(&adtdef.0 .0.did).unwrap();
                if idx > ans.len() {
                    return Err("The index is not a valid variance");
                }
                if ans[idx].1.iter().any(|&x| x == true) {
                    return Ok(true);
                }
                Ok(false)
            }
            _ => Err("The input is not an ADT"),
        }
    }

    /// This method is used to check if one adt-def of the enum has at least one isolated parameter.
    /// It is a summary of one type which demonstrate that we will consider all the generics in all the variants.
    /// Those generic parameters can be located in different fields, and some of them can be
    /// found in multiple fields.
    /// Note that, even for each variance, the result also analyze all its fields.
    /// It can be referred to the enum with enum-type variance.
    ///
    /// # Safety
    /// If `ty` is not an adt, the result is `Err`.
    /// If the input is the def of a struct type, the result is `Err`.
    ///
    /// # Case `ty::Ty`
    /// Given the adt `Vec<T, A>` the result is `Ok(true)`.
    /// ```rust
    /// pub enum MyBuf<T, S, F> { // parameter S F are an isolated parameters
    ///    Buf1(Vec<T>),
    ///    Buf2(S), // this variance is an isolated parameter
    ///    Buf3((F,S)), // this variance has 2 isolated parameters
    /// }
    /// ```
    ///
    /// # Example:
    /// ```rust
    ///  use rap::analysis::core::heap_item::IsolatedParameter;
    ///  let ans = IsolatedParameter::is_enum_flattened(rcanary.rcx, vec.ty);
    /// ```
    pub fn is_enum_flattened<'tcx>(
        adt_owner: HAResult,
        ty: Ty<'tcx>,
    ) -> Result<Vec<Vec<bool>>, &'static str> {
        match ty.kind() {
            TyKind::Adt(adtdef, ..) => {
                if !adtdef.is_enum() {
                    return Err("The input is not an enum");
                }
                let ans = adt_owner.get(&adtdef.0 .0.did).unwrap();
                let mut v: Vec<Vec<bool>> = Vec::default();
                for i in ans.iter() {
                    v.push(i.1.clone());
                }
                Ok(v)
            }
            _ => Err("The input is not an ADT"),
        }
    }
}

#[derive(Clone)]
struct IsolatedParam {
    record: Vec<bool>,
}

impl IsolatedParam {
    pub fn new(len: usize) -> Self {
        Self {
            record: vec![false; len],
        }
    }

    pub fn record_mut(&mut self) -> &mut Vec<bool> {
        &mut self.record
    }
}

#[derive(Clone)]
struct IsolatedParamFieldSubst {
    parameters: HashSet<usize>,
}

impl<'tcx> IsolatedParamFieldSubst {
    pub fn new() -> Self {
        Self {
            parameters: HashSet::new(),
        }
    }

    pub fn parameters(&self) -> &HashSet<usize> {
        &self.parameters
    }

    pub fn parameters_mut(&mut self) -> &mut HashSet<usize> {
        &mut self.parameters
    }

    pub fn contains_param(&self) -> bool {
        !self.parameters.is_empty()
    }
}

#[derive(Clone)]
struct IsolatedParamPropagation<'tcx, 'a> {
    tcx: TyCtxt<'tcx>,
    record: Vec<bool>,
    unique: HashSet<DefId>,
    source_enum: bool,
    ref_adt_owner: &'a HAResult,
}

impl<'tcx, 'a> IsolatedParamPropagation<'tcx, 'a> {
    pub fn new(
        tcx: TyCtxt<'tcx>,
        record: Vec<bool>,
        source_enum: bool,
        ref_adt_owner: &'a HAResult,
    ) -> Self {
        Self {
            tcx,
            record,
            unique: HashSet::new(),
            source_enum,
            ref_adt_owner,
        }
    }

    pub fn record_mut(&mut self) -> &mut Vec<bool> {
        &mut self.record
    }

    pub fn unique_mut(&mut self) -> &mut HashSet<DefId> {
        &mut self.unique
    }

    pub fn source_enum(&mut self) -> bool {
        self.source_enum
    }

    pub fn owner(&self) -> &'a HAResult {
        self.ref_adt_owner
    }
}

#[derive(Clone)]
struct OwnerPropagation<'tcx, 'a> {
    tcx: TyCtxt<'tcx>,
    ownership: RawTypeOwner,
    unique: HashSet<DefId>,
    ref_adt_owner: &'a HAResult,
}

impl<'tcx, 'a> OwnerPropagation<'tcx, 'a> {
    pub fn new(tcx: TyCtxt<'tcx>, ownership: RawTypeOwner, ref_adt_owner: &'a HAResult) -> Self {
        Self {
            tcx,
            ownership,
            unique: HashSet::new(),
            ref_adt_owner,
        }
    }

    pub fn ownership(&self) -> RawTypeOwner {
        self.ownership
    }

    pub fn unique_mut(&mut self) -> &mut HashSet<DefId> {
        &mut self.unique
    }

    pub fn owner(&self) -> &'a HAResult {
        self.ref_adt_owner
    }
}

#[derive(Clone)]
pub struct DefaultOwnership<'tcx, 'a> {
    tcx: TyCtxt<'tcx>,
    unique: HashSet<DefId>,
    ref_adt_owner: &'a HAResult,
    res: RawTypeOwner,
    param: bool,
    ptr: bool,
}

impl<'tcx, 'a> DefaultOwnership<'tcx, 'a> {
    pub fn new(tcx: TyCtxt<'tcx>, ref_adt_owner: &'a HAResult) -> Self {
        Self {
            tcx,
            unique: HashSet::new(),
            ref_adt_owner,
            res: RawTypeOwner::Unowned,
            param: false,
            ptr: false,
        }
    }

    pub fn tcx(&self) -> TyCtxt<'tcx> {
        self.tcx
    }

    pub fn unique(&self) -> &HashSet<DefId> {
        &self.unique
    }

    pub fn unique_mut(&mut self) -> &mut HashSet<DefId> {
        &mut self.unique
    }

    pub fn get_res(&self) -> RawTypeOwner {
        self.res
    }

    pub fn set_res(&mut self, res: RawTypeOwner) {
        self.res = res;
    }

    pub fn is_owning_true(&self) -> bool {
        self.res == RawTypeOwner::Owned
    }

    pub fn get_param(&self) -> bool {
        self.param
    }

    pub fn set_param(&mut self, p: bool) {
        self.param = p;
    }

    pub fn is_param_true(&self) -> bool {
        self.param == true
    }

    pub fn get_ptr(&self) -> bool {
        self.ptr
    }

    pub fn set_ptr(&mut self, p: bool) {
        self.ptr = p;
    }

    pub fn is_ptr_true(&self) -> bool {
        self.ptr == true
    }

    pub fn owner(&self) -> &'a HAResult {
        self.ref_adt_owner
    }
}

#[derive(Clone)]
pub struct FindPtr<'tcx> {
    tcx: TyCtxt<'tcx>,
    unique: HashSet<DefId>,
    ptr: bool,
}

impl<'tcx> FindPtr<'tcx> {
    pub fn new(tcx: TyCtxt<'tcx>) -> Self {
        Self {
            tcx,
            unique: HashSet::<DefId>::default(),
            ptr: false,
        }
    }

    pub fn tcx(&self) -> TyCtxt<'tcx> {
        self.tcx
    }

    pub fn unique(&self) -> &HashSet<DefId> {
        &self.unique
    }

    pub fn unique_mut(&mut self) -> &mut HashSet<DefId> {
        &mut self.unique
    }

    pub fn has_ptr(&self) -> bool {
        self.ptr
    }

    pub fn set_ptr(&mut self, ptr: bool) {
        self.ptr = ptr;
    }
}

pub fn is_display_verbose() -> bool {
    match env::var_os("ADT_DISPLAY") {
        Some(_) => true,
        _ => false,
    }
}

#[derive(Debug, Clone, Hash, Eq, PartialEq, Default)]
pub struct IndexedTy<'tcx>(pub Option<(usize, &'tcx TyKind<'tcx>, Option<usize>, bool)>);

impl<'tcx> IndexedTy<'tcx> {
    pub fn new(ty: Ty<'tcx>, vidx: Option<VariantIdx>) -> Self {
        match &ty.kind() {
            TyKind::Tuple(list) => IndexedTy(Some((list.len(), &ty.kind(), None, true))),
            TyKind::Adt(adtdef, ..) => {
                if adtdef.is_enum() {
                    if vidx.is_none() {
                        return IndexedTy(None);
                    }
                    let idx = vidx.unwrap();
                    let len = adtdef.variants()[idx].fields.len();
                    IndexedTy(Some((len, &ty.kind(), Some(idx.index()), true)))
                } else {
                    let len = adtdef.variants()[VariantIdx::from_usize(0)].fields.len();
                    IndexedTy(Some((len, &ty.kind(), None, true)))
                }
            }
            TyKind::Array(..) | TyKind::Param(..) | TyKind::RawPtr(..) | TyKind::Ref(..) => {
                IndexedTy(Some((1, &ty.kind(), None, true)))
            }
            TyKind::Bool
            | TyKind::Char
            | TyKind::Int(..)
            | TyKind::Uint(..)
            | TyKind::Float(..)
            | TyKind::Str
            | TyKind::Slice(..) => IndexedTy(Some((1, &ty.kind(), None, false))),
            _ => IndexedTy(None),
        }
    }

    // 0->unsupported, 1->trivial, 2-> needed
    pub fn get_priority(&self) -> usize {
        if self.0.is_none() {
            return 0;
        }
        match self.0.unwrap().0 {
            0 => 1,
            _ => match self.0.unwrap().3 {
                true => 2,
                false => 1,
            },
        }
    }
}



#[derive(Clone, Debug)]
pub struct OwnershipLayoutResult {
    layout: Vec<RawTypeOwner>,
    param: bool,
    requirement: bool,
    owned: bool,
}

impl OwnershipLayoutResult {
    pub fn new() -> Self {
        Self {
            layout: Vec::new(),
            param: false,
            requirement: false,
            owned: false,
        }
    }

    pub fn layout(&self) -> &Vec<RawTypeOwner> {
        &self.layout
    }

    pub fn layout_mut(&mut self) -> &mut Vec<RawTypeOwner> {
        &mut self.layout
    }

    pub fn get_param(&self) -> bool {
        self.param
    }

    pub fn set_param(&mut self, p: bool) {
        self.param = p;
    }

    pub fn is_param_true(&self) -> bool {
        self.param == true
    }

    pub fn get_requirement(&self) -> bool {
        self.requirement
    }

    pub fn set_requirement(&mut self, r: bool) {
        self.requirement = r;
    }

    pub fn is_requirement_true(&self) -> bool {
        self.requirement == true
    }

    pub fn is_empty(&self) -> bool {
        self.layout.is_empty()
    }

    pub fn is_owned(&self) -> bool {
        self.owned == true
    }

    pub fn set_owned(&mut self, o: bool) {
        self.owned = o;
    }

    pub fn update_from_default_ownership_visitor<'tcx, 'a>(
        &mut self,
        default_ownership: &mut DefaultOwnership<'tcx, 'a>,
    ) {
        if default_ownership.is_owning_true() || default_ownership.is_ptr_true() {
            self.set_requirement(true);
        }

        if default_ownership.is_owning_true() {
            self.set_owned(true);
        }

        self.layout_mut().push(default_ownership.get_res());

        self.set_param(default_ownership.get_param());
    }
}
