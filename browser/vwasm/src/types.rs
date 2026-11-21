//! Core WebAssembly 1.0 types, opcodes, module representation, traps, and outcomes (`vwasm`).

use vstd::prelude::*;

verus! {

pub const WASM_MAGIC: [u8; 4] = [0x00, 0x61, 0x73, 0x6d];
pub const WASM_VERSION_1: [u8; 4] = [0x01, 0x00, 0x00, 0x00];

pub const WASM_PAGE_SIZE: usize = 65_536;
pub const MAX_SPEC_PAGES: u32 = 65_536;
/// Maximum allocatable pages in a `usize`-indexed sandbox (2 GiB = 32,768 * 65,536 bytes,
/// guaranteed `<= u32::MAX <= usize::MAX` on both 32-bit and 64-bit targets).
pub const MAX_SANDBOX_PAGES: u32 = 32_768;
pub const MAX_LOCALS_PER_FUNC: usize = 4_096;
pub const MAX_WASM_CALL_DEPTH: usize = 1_024;
pub const MAX_TABLE_ENTRIES: u32 = 65_536;

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum ValType {
    I32,
    I64,
    F32,
    F64,
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum WasmVal {
    I32(i32),
    I64(i64),
    F32Bits(u32),
    F64Bits(u64),
}

pub open spec fn spec_default_val(vt: ValType) -> WasmVal {
    match vt {
        ValType::I32 => WasmVal::I32(0),
        ValType::I64 => WasmVal::I64(0),
        ValType::F32 => WasmVal::F32Bits(0),
        ValType::F64 => WasmVal::F64Bits(0),
    }
}

pub fn default_val(vt: ValType) -> (v: WasmVal)
    ensures
        v == spec_default_val(vt),
{
    match vt {
        ValType::I32 => WasmVal::I32(0),
        ValType::I64 => WasmVal::I64(0),
        ValType::F32 => WasmVal::F32Bits(0),
        ValType::F64 => WasmVal::F64Bits(0),
    }
}

pub open spec fn spec_val_has_type(v: WasmVal, vt: ValType) -> bool {
    match (v, vt) {
        (WasmVal::I32(_), ValType::I32) => true,
        (WasmVal::I64(_), ValType::I64) => true,
        (WasmVal::F32Bits(_), ValType::F32) => true,
        (WasmVal::F64Bits(_), ValType::F64) => true,
        _ => false,
    }
}

pub fn val_has_type(v: WasmVal, vt: ValType) -> (b: bool)
    ensures
        b == spec_val_has_type(v, vt),
{
    match (v, vt) {
        (WasmVal::I32(_), ValType::I32) => true,
        (WasmVal::I64(_), ValType::I64) => true,
        (WasmVal::F32Bits(_), ValType::F32) => true,
        (WasmVal::F64Bits(_), ValType::F64) => true,
        _ => false,
    }
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum I32UnOp {
    Clz,
    Ctz,
    Popcnt,
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum I32BinOp {
    Add,
    Sub,
    Mul,
    DivS,
    DivU,
    RemS,
    RemU,
    And,
    Or,
    Xor,
    Shl,
    ShrS,
    ShrU,
    Rotl,
    Rotr,
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum I64UnOp {
    Clz,
    Ctz,
    Popcnt,
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum I64BinOp {
    Add,
    Sub,
    Mul,
    DivS,
    DivU,
    RemS,
    RemU,
    And,
    Or,
    Xor,
    Shl,
    ShrS,
    ShrU,
    Rotl,
    Rotr,
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum IntRelOp {
    Eq,
    Ne,
    LtS,
    LtU,
    GtS,
    GtU,
    LeS,
    LeU,
    GeS,
    GeU,
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum LoadKind {
    I32Load,
    I64Load,
    F32Load,
    F64Load,
    I32Load8S,
    I32Load8U,
    I32Load16S,
    I32Load16U,
    I64Load8S,
    I64Load8U,
    I64Load16S,
    I64Load16U,
    I64Load32S,
    I64Load32U,
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum StoreKind {
    I32Store,
    I64Store,
    F32Store,
    F64Store,
    I32Store8,
    I32Store16,
    I64Store8,
    I64Store16,
    I64Store32,
}

pub open spec fn spec_load_width(kind: LoadKind) -> nat {
    match kind {
        LoadKind::I32Load8S | LoadKind::I32Load8U | LoadKind::I64Load8S | LoadKind::I64Load8U => 1,
        LoadKind::I32Load16S | LoadKind::I32Load16U | LoadKind::I64Load16S | LoadKind::I64Load16U => 2,
        LoadKind::I32Load | LoadKind::F32Load | LoadKind::I64Load32S | LoadKind::I64Load32U => 4,
        LoadKind::I64Load | LoadKind::F64Load => 8,
    }
}

pub fn load_width(kind: LoadKind) -> (w: usize)
    ensures
        w as nat == spec_load_width(kind),
        1 <= w <= 8,
{
    match kind {
        LoadKind::I32Load8S | LoadKind::I32Load8U | LoadKind::I64Load8S | LoadKind::I64Load8U => 1,
        LoadKind::I32Load16S | LoadKind::I32Load16U | LoadKind::I64Load16S | LoadKind::I64Load16U => 2,
        LoadKind::I32Load | LoadKind::F32Load | LoadKind::I64Load32S | LoadKind::I64Load32U => 4,
        LoadKind::I64Load | LoadKind::F64Load => 8,
    }
}

pub open spec fn spec_store_width(kind: StoreKind) -> nat {
    match kind {
        StoreKind::I32Store8 | StoreKind::I64Store8 => 1,
        StoreKind::I32Store16 | StoreKind::I64Store16 => 2,
        StoreKind::I32Store | StoreKind::F32Store | StoreKind::I64Store32 => 4,
        StoreKind::I64Store | StoreKind::F64Store => 8,
    }
}

pub fn store_width(kind: StoreKind) -> (w: usize)
    ensures
        w as nat == spec_store_width(kind),
        1 <= w <= 8,
{
    match kind {
        StoreKind::I32Store8 | StoreKind::I64Store8 => 1,
        StoreKind::I32Store16 | StoreKind::I64Store16 => 2,
        StoreKind::I32Store | StoreKind::F32Store | StoreKind::I64Store32 => 4,
        StoreKind::I64Store | StoreKind::F64Store => 8,
    }
}

/// Decoded Wasm 1.0 instruction stream prior to structured-block target resolution.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum RawInstr {
    Unreachable,
    Nop,
    Block(Option<ValType>),
    Loop(Option<ValType>),
    If(Option<ValType>),
    Else,
    End,
    Br(u32),
    BrIf(u32),
    BrTable { table_idx: usize, default_label: u32 },
    Return,
    Call(u32),
    CallIndirect(u32),
    Drop,
    Select,
    LocalGet(u32),
    LocalSet(u32),
    LocalTee(u32),
    GlobalGet(u32),
    GlobalSet(u32),
    MemLoad { load_kind: LoadKind, align: u32, offset: u32 },
    MemStore { store_kind: StoreKind, align: u32, offset: u32 },
    MemorySize,
    MemoryGrow,
    I32Const(i32),
    I64Const(i64),
    F32Const(u32),
    F64Const(u64),
    I32Eqz,
    I64Eqz,
    I32Rel(IntRelOp),
    I64Rel(IntRelOp),
    I32Unary(I32UnOp),
    I32Binary(I32BinOp),
    I64Unary(I64UnOp),
    I64Binary(I64BinOp),
    I32WrapI64,
    I64ExtendI32S,
    I64ExtendI32U,
    Unsupported(u8),
}

/// Jump-resolved Wasm 1.0 instruction executed in O(1) by the verified sandboxed interpreter.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum WasmOp {
    Unreachable,
    Nop,
    Block { end_pc: usize, arity: usize },
    Loop { loop_pc: usize },
    If { else_pc: usize, end_pc: usize, arity: usize },
    ElseJump { end_pc: usize },
    End,
    FuncEnd,
    Br(u32),
    BrIf(u32),
    BrTable { table_idx: usize, default_label: u32 },
    Return,
    Call(u32),
    CallIndirect(u32),
    Drop,
    Select,
    LocalGet(u32),
    LocalSet(u32),
    LocalTee(u32),
    GlobalGet(u32),
    GlobalSet(u32),
    MemLoad { load_kind: LoadKind, offset: u32 },
    MemStore { store_kind: StoreKind, offset: u32 },
    MemorySize,
    MemoryGrow,
    I32Const(i32),
    I64Const(i64),
    F32Const(u32),
    F64Const(u64),
    I32Eqz,
    I64Eqz,
    I32Rel(IntRelOp),
    I64Rel(IntRelOp),
    I32Unary(I32UnOp),
    I32Binary(I32BinOp),
    I64Unary(I64UnOp),
    I64Binary(I64BinOp),
    I32WrapI64,
    I64ExtendI32S,
    I64ExtendI32U,
    Unsupported(u8),
}

#[derive(Clone, PartialEq, Eq, Debug)]
pub struct FuncType {
    pub params: Vec<ValType>,
    pub results: Vec<ValType>,
}

pub struct SpecFuncType {
    pub params: Seq<ValType>,
    pub results: Seq<ValType>,
}

impl View for FuncType {
    type V = SpecFuncType;

    open spec fn view(&self) -> SpecFuncType {
        SpecFuncType { params: self.params@, results: self.results@ }
    }
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct MemoryLimits {
    pub min_pages: u32,
    pub max_pages: Option<u32>,
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct TableLimits {
    pub min_entries: u32,
    pub max_entries: Option<u32>,
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct GlobalDecl {
    pub val_type: ValType,
    pub mutable: bool,
    pub init: WasmVal,
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum ExportKind {
    Func,
    Table,
    Memory,
    Global,
}

#[derive(Clone, PartialEq, Eq, Debug)]
pub struct ExportDesc {
    pub name: Vec<u8>,
    pub kind: ExportKind,
    pub index: u32,
}

pub struct SpecExportDesc {
    pub name: Seq<u8>,
    pub kind: ExportKind,
    pub index: u32,
}

impl View for ExportDesc {
    type V = SpecExportDesc;

    open spec fn view(&self) -> SpecExportDesc {
        SpecExportDesc { name: self.name@, kind: self.kind, index: self.index }
    }
}

#[derive(Clone, PartialEq, Eq, Debug)]
pub struct FuncBody {
    pub type_idx: u32,
    pub locals: Vec<ValType>,
    pub ops: Vec<WasmOp>,
    pub br_tables: Vec<Vec<u32>>,
}

pub struct SpecFuncBody {
    pub type_idx: u32,
    pub locals: Seq<ValType>,
    pub ops: Seq<WasmOp>,
    pub br_tables: Seq<Seq<u32>>,
}

impl View for FuncBody {
    type V = SpecFuncBody;

    open spec fn view(&self) -> SpecFuncBody {
        SpecFuncBody {
            type_idx: self.type_idx,
            locals: self.locals@,
            ops: self.ops@,
            br_tables: Seq::new(self.br_tables@.len(), |i: int| self.br_tables@[i]@),
        }
    }
}

#[derive(Clone, PartialEq, Eq, Debug)]
pub struct ElemSegment {
    pub offset: u32,
    pub func_indices: Vec<u32>,
}

pub struct SpecElemSegment {
    pub offset: u32,
    pub func_indices: Seq<u32>,
}

impl View for ElemSegment {
    type V = SpecElemSegment;

    open spec fn view(&self) -> SpecElemSegment {
        SpecElemSegment { offset: self.offset, func_indices: self.func_indices@ }
    }
}

#[derive(Clone, PartialEq, Eq, Debug)]
pub struct DataSegment {
    pub mem_idx: u32,
    pub offset: u32,
    pub init: Vec<u8>,
}

pub struct SpecDataSegment {
    pub mem_idx: u32,
    pub offset: u32,
    pub init: Seq<u8>,
}

impl View for DataSegment {
    type V = SpecDataSegment;

    open spec fn view(&self) -> SpecDataSegment {
        SpecDataSegment { mem_idx: self.mem_idx, offset: self.offset, init: self.init@ }
    }
}

#[derive(Clone, PartialEq, Eq, Debug)]
pub struct WasmModule {
    pub types: Vec<FuncType>,
    pub func_type_indices: Vec<u32>,
    pub table: Option<TableLimits>,
    pub memory: Option<MemoryLimits>,
    pub globals: Vec<GlobalDecl>,
    pub exports: Vec<ExportDesc>,
    pub elem_segments: Vec<ElemSegment>,
    pub funcs: Vec<FuncBody>,
    pub data_segments: Vec<DataSegment>,
}

pub struct SpecWasmModule {
    pub types: Seq<SpecFuncType>,
    pub func_type_indices: Seq<u32>,
    pub table: Option<TableLimits>,
    pub memory: Option<MemoryLimits>,
    pub globals: Seq<GlobalDecl>,
    pub exports: Seq<SpecExportDesc>,
    pub elem_segments: Seq<SpecElemSegment>,
    pub funcs: Seq<SpecFuncBody>,
    pub data_segments: Seq<SpecDataSegment>,
}

impl View for WasmModule {
    type V = SpecWasmModule;

    open spec fn view(&self) -> SpecWasmModule {
        SpecWasmModule {
            types: Seq::new(self.types@.len(), |i: int| self.types@[i]@),
            func_type_indices: self.func_type_indices@,
            table: self.table,
            memory: self.memory,
            globals: self.globals@,
            exports: Seq::new(self.exports@.len(), |i: int| self.exports@[i]@),
            elem_segments: Seq::new(self.elem_segments@.len(), |i: int| self.elem_segments@[i]@),
            funcs: Seq::new(self.funcs@.len(), |i: int| self.funcs@[i]@),
            data_segments: Seq::new(self.data_segments@.len(), |i: int| self.data_segments@[i]@),
        }
    }
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum DecodeError {
    UnexpectedEof,
    InvalidMagic,
    UnsupportedVersion,
    InvalidLeb128,
    MalformedSection,
    UnsupportedType,
    UnsupportedSection(u8),
    UnsupportedOpcode(u8),
    InvalidLimits,
    InvalidMutability,
    InvalidInitExpr,
    InvalidExportKind,
    UnbalancedControlFlow,
    FunctionCountMismatch,
    TooManyLocals,
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum WasmTrap {
    Unreachable,
    IntegerDivideByZero,
    IntegerOverflow,
    OutOfBoundsMemoryAccess,
    CallStackExhausted,
    TypeMismatch,
    UndefinedElement,
    IndirectCallTypeMismatch,
    InvalidFunctionIndex,
    InvalidLocalIndex,
    InvalidGlobalIndex,
    ImmutableGlobalWrite,
    StackUnderflow,
    InvalidLabel,
}

#[derive(Clone, PartialEq, Eq, Debug)]
pub enum WasmOutcome {
    Done(Vec<WasmVal>),
    Trap(WasmTrap),
    OutOfFuel,
    Unsupported(u8),
}

pub enum SpecWasmOutcome {
    Done(Seq<WasmVal>),
    Trap(WasmTrap),
    OutOfFuel,
    Unsupported(u8),
}

impl View for WasmOutcome {
    type V = SpecWasmOutcome;

    open spec fn view(&self) -> SpecWasmOutcome {
        match self {
            WasmOutcome::Done(vals) => SpecWasmOutcome::Done(vals@),
            WasmOutcome::Trap(t) => SpecWasmOutcome::Trap(*t),
            WasmOutcome::OutOfFuel => SpecWasmOutcome::OutOfFuel,
            WasmOutcome::Unsupported(op) => SpecWasmOutcome::Unsupported(*op),
        }
    }
}

} // verus!
