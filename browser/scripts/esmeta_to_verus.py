#!/usr/bin/env python3
"""esmeta_to_verus.py — ECMA-262 `<emu-alg>` to Verus Specification & Verified Exec Compiler (J0).

Compiles real upstream `tc39/ecma262` `spec.html` `<emu-clause>` / `<emu-alg>` structured
step trees into an explicit ESMeta/IRES-style intermediate representation (typed AST + basic-block
Control-Flow Graph with SSA phi-lifting and mutation analysis), and emits Warblre-style interleaved
Verus `pub open spec fn` + `pub fn` implementations proved `exec == spec` by Z3.

Zero trusted escape hatches (`assume`, `admit`, `external_body`, `external`, `assume_specification`,
`unsafe` are never emitted).

Usage:
    python3 browser/scripts/esmeta_to_verus.py                 # compile spec_inputs -> src/generated.rs
    python3 browser/scripts/esmeta_to_verus.py --check         # verify src/generated.rs is up-to-date
    python3 browser/scripts/esmeta_to_verus.py --self-test     # run compiler unit test suite
    python3 browser/scripts/esmeta_to_verus.py --dump-ir       # dump IRES AST + CFG summary as JSON
"""
from __future__ import annotations

import argparse
import dataclasses
from dataclasses import dataclass, field
from enum import Enum
import html
from html.parser import HTMLParser
import json
from pathlib import Path
import re
import sys
import unittest
from typing import Optional


SCRIPT_DIR = Path(__file__).resolve().parent
BROWSER_DIR = SCRIPT_DIR.parent
DEFAULT_INPUT = BROWSER_DIR / "vjs-spec" / "spec_inputs" / "ecma262_clauses.html"
DEFAULT_OUTPUT = BROWSER_DIR / "vjs-spec" / "src" / "generated.rs"


# ===============================================================================================
# 1. Explicit IRES-Style Intermediate Representation (Types, Expressions, Statements, CFG)
# ===============================================================================================

class IRBaseType(str, Enum):
    JS_VALUE = "JsValue"
    NUMBER = "Number"
    BOOL = "Boolean"
    MATH_INT = "MathInt"
    POS_INT = "PosInt"
    INT_OR_INF = "IntOrInf"
    SIGNEDNESS = "Signedness"
    BITWISE_OP = "BitwiseOp"
    BITS32 = "Bits32"
    UNUSED = "Unused"


@dataclass(frozen=True)
class IRType:
    base: IRBaseType
    fallible: bool = False  # True => AbruptOrNormal<base>
    not_number_constraint: bool = False


class CompletionMode(str, Enum):
    PURE = "pure"          # plain call Op(...)
    QUESTION = "question"  # ? Op(...) — ReturnIfAbrupt
    BANG = "bang"          # ! Op(...) — AssertNotAbrupt (proved Normal in Verus!)


@dataclass
class IRParam:
    name: str          # spec identifier without underscores, e.g. "x", "arg", "bitWidth"
    rust_name: str     # snake_case Rust identifier
    ty: IRType
    raw_spec_type: str


# --- IR Expressions ---

class IRExpr:
    pass


@dataclass
class VarExpr(IRExpr):
    name: str


@dataclass
class LitBool(IRExpr):
    value: bool


@dataclass
class LitSpecialVal(IRExpr):
    # "undefined" | "null" | "NaN" | "+0_F" | "-0_F" | "+inf_F" | "-inf_F" | "1_F" | "0_Z" | "empty_str"
    kind: str


@dataclass
class LitMath(IRExpr):
    # "0" | "32" | "16" | "+inf" | "-inf"
    kind: str
    int_val: Optional[int] = None


@dataclass
class LitEnumTag(IRExpr):
    # "signed" | "unsigned" | "number" | "unused"
    tag: str


@dataclass
class LitBitOpToken(IRExpr):
    # "&" | "^" | "|"
    op: str


@dataclass
class TypePredExpr(IRExpr):
    target: IRExpr
    # "Boolean" | "Number" | "BigInt" | "String" | "Symbol" | "Object" | "FiniteNumber"
    type_name: str
    negated: bool = False


@dataclass
class ValuePredExpr(IRExpr):
    target: IRExpr
    # "undefined" | "null" | "NaN" | "+0_F" | "-0_F" | "+inf_F" | "-inf_F" | "true" | "false" | "0_Z" | "empty_str"
    kind: str
    negated: bool = False


@dataclass
class OneOfPredExpr(IRExpr):
    target: IRExpr
    checks: list[IRExpr]


@dataclass
class IdentityEqExpr(IRExpr):
    lhs: IRExpr
    rhs: IRExpr
    domain: str  # "Number" | "JsValue" | "Signedness" | "BitwiseOp"


@dataclass
class HostSupportsHtmlDdaExpr(IRExpr):
    pass


@dataclass
class HasInternalSlotExpr(IRExpr):
    target: IRExpr
    slot: str


@dataclass
class SameStringCodeUnitsExpr(IRExpr):
    lhs: IRExpr
    rhs: IRExpr


@dataclass
class RealEqExpr(IRExpr):
    lhs: IRExpr
    rhs: IRExpr


@dataclass
class MathCmpExpr(IRExpr):
    op: str  # "==" | ">=" | "<"
    lhs: IRExpr
    rhs: IRExpr


@dataclass
class Pow2Expr(IRExpr):
    exponent: IRExpr


@dataclass
class MathSubExpr(IRExpr):
    lhs: IRExpr
    rhs: IRExpr


@dataclass
class ModuloExpr(IRExpr):
    lhs: IRExpr
    modulus: IRExpr


@dataclass
class RealOfNumberExpr(IRExpr):
    expr: IRExpr


@dataclass
class TruncateRealExpr(IRExpr):
    expr: IRExpr


@dataclass
class NumberFromMathExpr(IRExpr):
    expr: IRExpr


@dataclass
class ToTwosComp32Expr(IRExpr):
    expr: IRExpr


@dataclass
class FromTwosComp32ToNumberExpr(IRExpr):
    expr: IRExpr


@dataclass
class BitwiseNot32Expr(IRExpr):
    expr: IRExpr


@dataclass
class BitShift32Expr(IRExpr):
    kind: str  # "shl" | "ashr" | "lshr"
    lhs: IRExpr
    shift: IRExpr


@dataclass
class BitwiseBinary32Expr(IRExpr):
    op: str  # "AND" | "XOR" | "OR"
    lhs: IRExpr
    rhs: IRExpr


@dataclass
class LogicExpr(IRExpr):
    op: str  # "and" | "or"
    items: list[IRExpr]


@dataclass
class CallExpr(IRExpr):
    callee: str
    args: list[IRExpr]
    mode: CompletionMode


# --- IR Statements ---

class IRStmt:
    step_label: str
    comment: str


@dataclass
class IRNote(IRStmt):
    step_label: str
    comment: str


@dataclass
class IRAssert(IRStmt):
    step_label: str
    comment: str
    cond: IRExpr


@dataclass
class IRLet(IRStmt):
    step_label: str
    comment: str
    var: str
    rhs: IRExpr
    mutable: bool = False


@dataclass
class IRSet(IRStmt):
    step_label: str
    comment: str
    var: str
    rhs: IRExpr


@dataclass
class IRReturn(IRStmt):
    step_label: str
    comment: str
    value: IRExpr


@dataclass
class IRThrow(IRStmt):
    step_label: str
    comment: str
    exception: str  # "TypeError"


@dataclass
class IRElifBranch:
    step_label: str
    comment: str
    cond: IRExpr
    body: list[IRStmt]


@dataclass
class IRIf(IRStmt):
    step_label: str
    comment: str
    cond: IRExpr
    then_body: list[IRStmt]
    elif_branches: list[IRElifBranch] = field(default_factory=list)
    else_step_label: Optional[str] = None
    else_comment: Optional[str] = None
    else_body: list[IRStmt] = field(default_factory=list)
    # Populated by SSA phi-lifting when every branch defines the same `Let _v_` used later:
    phi_var: Optional[str] = None


# --- Explicit IRES Basic-Block Control-Flow Graph ---

@dataclass
class CFGBlock:
    id: int
    kind: str  # "entry" | "stmt" | "branch" | "return" | "throw" | "join"
    label: str
    succs: list[int] = field(default_factory=list)


@dataclass
class IRCFG:
    entry: int
    blocks: dict[int, CFGBlock]


@dataclass
class IROperation:
    clause_number: str
    clause_id: str
    spec_name: str      # e.g. "Number::equal", "ToInt32", "IsLooselyEqual"
    rust_fn_name: str   # e.g. "number_equal", "to_int32", "is_loosely_equal"
    spec_fn_name: str   # e.g. "spec_number_equal", "spec_to_int32"
    params: list[IRParam]
    ret_type: IRType
    raw_ret_type: str
    step_count: int
    body: list[IRStmt]
    cfg: IRCFG
    is_recursive: bool = False
    callees: list[str] = field(default_factory=list)


# ===============================================================================================
# 2. Pass 1: Ecmarkup `<emu-clause>` and `<emu-alg>` Step-Tree Parser
# ===============================================================================================

@dataclass
class RawClause:
    clause_number: str
    clause_id: str
    clause_type: str
    h1_raw: str
    alg_raw: str


class EcmarkupClauseParser(HTMLParser):
    """Extracts top-level `<emu-clause>` headers and their direct `<emu-alg>` blocks,
    ignoring nested sub-clauses (such as grammar SDO sub-clauses inside `sec-tonumber`)."""

    def __init__(self) -> None:
        super().__init__(convert_charrefs=False)
        self.pending_clause_num: Optional[str] = None
        self.clause_depth = 0
        self.counters = [0]
        self.current_id = ""
        self.current_type = ""
        self.current_num = ""
        self.in_top_h1 = False
        self.in_top_alg = False
        self.has_captured_top_alg = False
        self.h1_buf: list[str] = []
        self.alg_buf: list[str] = []
        self.clauses: list[RawClause] = []

    def handle_comment(self, data: str) -> None:
        m = re.search(r"@ecma262-excerpt\s+clause=([0-9.]+)\s+id=(\S+)", data)
        if m:
            self.pending_clause_num = m.group(1)

    def handle_starttag(self, tag: str, attrs: list[tuple[str, Optional[str]]]) -> None:
        d = dict(attrs)
        if tag == "emu-clause":
            self.clause_depth += 1
            if self.clause_depth == 1:
                self.counters[-1] += 1
                self.current_id = d.get("id") or ""
                self.current_type = d.get("type") or ""
                self.current_num = self.pending_clause_num or ".".join(str(x) for x in self.counters)
                self.pending_clause_num = None
                self.h1_buf = []
                self.alg_buf = []
                self.has_captured_top_alg = False
        elif self.clause_depth == 1:
            if tag == "h1":
                self.in_top_h1 = True
            elif tag == "emu-alg" and not self.has_captured_top_alg:
                self.in_top_alg = True
            elif self.in_top_h1:
                self.h1_buf.append(self.get_starttag_text() or "")
            elif self.in_top_alg:
                self.alg_buf.append(self.get_starttag_text() or "")

    def handle_endtag(self, tag: str) -> None:
        if tag == "emu-clause":
            if self.clause_depth == 1 and self.current_id and self.alg_buf:
                self.clauses.append(
                    RawClause(
                        clause_number=self.current_num,
                        clause_id=self.current_id,
                        clause_type=self.current_type,
                        h1_raw="".join(self.h1_buf),
                        alg_raw="".join(self.alg_buf),
                    )
                )
            self.clause_depth -= 1
        elif self.clause_depth == 1:
            if tag == "h1" and self.in_top_h1:
                self.in_top_h1 = False
            elif tag == "emu-alg" and self.in_top_alg:
                self.in_top_alg = False
                self.has_captured_top_alg = True
            elif self.in_top_h1:
                self.h1_buf.append(f"</{tag}>")
            elif self.in_top_alg:
                self.alg_buf.append(f"</{tag}>")

    def handle_data(self, data: str) -> None:
        if self.clause_depth == 1:
            if self.in_top_h1:
                self.h1_buf.append(data)
            elif self.in_top_alg:
                self.alg_buf.append(data)

    def handle_entityref(self, name: str) -> None:
        self.handle_data(f"&{name};")

    def handle_charref(self, name: str) -> None:
        self.handle_data(f"&#{name};")


@dataclass
class StepNode:
    step_label: str
    raw_markup: str
    clean_text: str
    comment_line: str
    attributes: str
    children: list["StepNode"] = field(default_factory=list)


def _int_to_roman(n: int) -> str:
    vals = [(10, "x"), (9, "ix"), (5, "v"), (4, "iv"), (1, "i")]
    out = []
    for v, sym in vals:
        while n >= v:
            out.append(sym)
            n -= v
    return "".join(out)


def _format_step_index(depth: int, idx_1based: int) -> str:
    mode = depth % 3
    if mode == 0:
        return str(idx_1based)
    if mode == 1:
        return chr(ord("a") + idx_1based - 1)
    return _int_to_roman(idx_1based)


def normalize_ecmarkup_inline(raw: str) -> tuple[str, str]:
    """Normalize ecmarkup inline tags/entities into clean canonical ECMA-262 prose,
    splitting any leading `[id="...", ...]` step attribute prefix."""
    s = raw.strip()
    attr = ""
    if s.startswith("["):
        end_br = s.find("]")
        if end_br != -1:
            attr = s[1:end_br].strip()
            s = s[end_br + 1 :].strip()

    # Replace <emu-xref href="#sec-foo" ...></emu-xref> with #sec-foo
    s = re.sub(
        r'<emu-xref[^>]*href="([^"]+)"[^>]*>\s*</emu-xref>',
        lambda m: m.group(1),
        s,
    )
    # Unwrap <emu-meta ...>...</emu-meta>
    s = re.sub(r"</?emu-meta[^>]*>", "", s)
    # Subscripts <sub>𝔽</sub> -> _𝔽, <sub>ℤ</sub> -> _ℤ
    s = re.sub(r"<sub>\s*([^<]+?)\s*</sub>", r"_\1", s)
    # Superscripts <sup>...</sup> -> ^(...) if compound else ^x
    def _sup_repl(m: re.Match[str]) -> str:
        inner = m.group(1).strip()
        if re.fullmatch(r"[A-Za-z0-9_]+", inner):
            return f"^{inner}"
        return f"^({inner})"

    s = re.sub(r"<sup>\s*([^<]+?)\s*</sup>", _sup_repl, s)
    # Inline <code>AND</code> -> AND
    s = re.sub(r"<code>\s*([^<]+?)\s*</code>", r"\1", s)
    s = html.unescape(s)
    s = re.sub(r"\s+", " ", s).strip()
    return attr, s


def parse_alg_steps(alg_raw: str) -> tuple[list[StepNode], int]:
    """Parse indentation-structured `<emu-alg>` `1.` items into a tree of `StepNode`s."""
    raw_lines: list[tuple[int, str]] = []
    for line in alg_raw.splitlines():
        if not line.strip():
            continue
        m = re.match(r"^(\s*)1\.\s+(.*)$", line)
        if not m:
            raise ValueError(f"Unrecognized <emu-alg> line: {line!r}")
        indent = len(m.group(1))
        raw_lines.append((indent, m.group(2)))

    if not raw_lines:
        return [], 0

    base_indent = min(ind for ind, _ in raw_lines)
    roots: list[StepNode] = []
    stack: list[tuple[int, list[StepNode], str]] = [(base_indent, roots, "")]

    for indent, body_raw in raw_lines:
        while len(stack) > 1 and indent < stack[-1][0]:
            stack.pop()
        if indent > stack[-1][0]:
            parent_list = stack[-1][1]
            if not parent_list:
                raise ValueError(f"Unexpected indentation jump at: {body_raw!r}")
            parent_node = parent_list[-1]
            stack.append((indent, parent_node.children, parent_node.step_label))

        depth = len(stack) - 1
        siblings = stack[-1][1]
        prefix = stack[-1][2]
        local_label = _format_step_index(depth, len(siblings) + 1)
        full_label = f"{prefix}.{local_label}" if prefix else local_label
        attr, clean = normalize_ecmarkup_inline(body_raw)
        comment_line = f"{full_label}. {clean}"
        siblings.append(
            StepNode(
                step_label=full_label,
                raw_markup=body_raw.strip(),
                clean_text=clean,
                comment_line=comment_line,
                attributes=attr,
            )
        )

    return roots, len(raw_lines)


# ===============================================================================================
# 3. Signature Parser & Type Inference
# ===============================================================================================

def camel_to_snake(name: str) -> str:
    s = name.replace("::", "_")
    s = re.sub(r"([a-z0-9])([A-Z])", r"\1_\2", s)
    s = re.sub(r"([A-Z]+)([A-Z][a-z])", r"\1_\2", s)
    return s.lower()


def parse_spec_type(raw_ty: str) -> IRType:
    t = html.unescape(re.sub(r"<[^>]+>", "", raw_ty)).strip()
    t = re.sub(r"\s+", " ", t)
    fallible = False
    m_comp = re.match(
        r"^either a normal completion containing (.+?) or a throw completion$",
        t,
    )
    if m_comp:
        fallible = True
        t = m_comp.group(1).strip()
        if t.startswith("either "):
            t = t[len("either ") :].strip()

    if t in ("a Number", "an integral Number", "a non-negative integral Number"):
        return IRType(IRBaseType.NUMBER, fallible=fallible)
    if t == "a Boolean":
        return IRType(IRBaseType.BOOL, fallible=fallible)
    if t == "~unused~":
        return IRType(IRBaseType.UNUSED, fallible=fallible)
    if t == "~unsigned~ or ~signed~":
        return IRType(IRBaseType.SIGNEDNESS, fallible=fallible)
    if "`&`" in t and "`^`" in t and "`|`" in t:
        return IRType(IRBaseType.BITWISE_OP, fallible=fallible)
    if t == "a positive integer":
        return IRType(IRBaseType.POS_INT, fallible=fallible)
    if t == "an integer":
        return IRType(IRBaseType.MATH_INT, fallible=fallible)
    if "integer" in t and "+∞" in t and "-∞" in t:
        return IRType(IRBaseType.INT_OR_INF, fallible=fallible)
    if t == "an ECMAScript language value, but not a Number":
        return IRType(IRBaseType.JS_VALUE, fallible=fallible, not_number_constraint=True)
    if t == "an ECMAScript language value":
        return IRType(IRBaseType.JS_VALUE, fallible=fallible)
    raise ValueError(f"Unsupported ECMA-262 signature type: {raw_ty!r} (normalized: {t!r})")


def parse_h1_signature(h1_raw: str) -> tuple[str, list[IRParam], IRType, str]:
    clean_h1 = html.unescape(re.sub(r"<[^>]+>", "", h1_raw))
    clean_h1 = re.sub(r"\s+", " ", clean_h1).strip()
    m = re.match(r"^([A-Za-z0-9_:]+)\s*\((.*?)\)\s*:\s*(.+)$", clean_h1)
    if not m:
        raise ValueError(f"Cannot parse <h1> signature: {clean_h1!r}")
    op_name = m.group(1).strip()
    params_blob = m.group(2).strip()
    ret_raw = m.group(3).strip()

    params: list[IRParam] = []
    # Match `_name_: <type description>` separated by `, _` or trailing `,`
    for pm in re.finditer(r"_([A-Za-z0-9_]+)_\s*:\s*(.+?)(?=,\s*_[A-Za-z0-9_]+_\s*:|,\s*$|$)", params_blob):
        pname = pm.group(1)
        pty_raw = pm.group(2).strip().rstrip(",")
        rname = camel_to_snake(pname)
        if rname in ("in", "type", "ref", "match", "fn", "let", "int"):
            rname = f"{rname}_val"
        params.append(IRParam(name=pname, rust_name=rname, ty=parse_spec_type(pty_raw), raw_spec_type=pty_raw))

    ret_ty = parse_spec_type(ret_raw)
    return op_name, params, ret_ty, ret_raw


# ===============================================================================================
# 4. Pass 2: Prose-to-IRES Lowering (Expressions, Statements, SSA Phi & Mutation Pass, CFG)
# ===============================================================================================

KNOWN_TYPE_WORDS = {
    "a Boolean": "Boolean",
    "a Number": "Number",
    "a BigInt": "BigInt",
    "a String": "String",
    "a Symbol": "Symbol",
    "an Object": "Object",
    "a finite Number": "FiniteNumber",
}

KNOWN_VALUE_ATOMS = {
    "*undefined*": "undefined",
    "*null*": "null",
    "*NaN*": "NaN",
    "*+0*_𝔽": "+0_F",
    "*-0*_𝔽": "-0_F",
    "*+∞*_𝔽": "+inf_F",
    "*-∞*_𝔽": "-inf_F",
    "*true*": "true",
    "*false*": "false",
    "*0*_ℤ": "0_Z",
    "the empty String": "empty_str",
}


class StepCompiler:
    def __init__(self, op_name: str, params: list[IRParam], ret_type: IRType) -> None:
        self.op_name = op_name
        self.params = params
        self.ret_type = ret_type
        self.var_types: dict[str, IRBaseType] = {p.name: p.ty.base for p in params}
        self.var_rust: dict[str, str] = {p.name: p.rust_name for p in params}
        self.callees: set[str] = set()

    def rust_ident(self, spec_var: str) -> str:
        if spec_var not in self.var_rust:
            r = camel_to_snake(spec_var)
            if r in ("in", "type", "ref", "match", "fn", "let", "int"):
                r = f"{r}_val"
            self.var_rust[spec_var] = r
        return self.var_rust[spec_var]

    def parse_atom_check(self, target: IRExpr, item_str: str, negated: bool = False) -> IRExpr:
        it = item_str.strip()
        if it in KNOWN_TYPE_WORDS:
            return TypePredExpr(target=target, type_name=KNOWN_TYPE_WORDS[it], negated=negated)
        if it in KNOWN_VALUE_ATOMS:
            return ValuePredExpr(target=target, kind=KNOWN_VALUE_ATOMS[it], negated=negated)
        if it in ("`&`", "`^`", "`|`"):
            return IdentityEqExpr(lhs=target, rhs=LitBitOpToken(it[1]), domain="BitwiseOp")
        if it in ("~signed~", "~unsigned~"):
            return IdentityEqExpr(lhs=target, rhs=LitEnumTag(it[1:-1]), domain="Signedness")
        m_var = re.fullmatch(r"_([A-Za-z0-9_]+)_", it)
        if m_var:
            vname = m_var.group(1)
            dom = "Number" if self._expr_base_type(target) == IRBaseType.NUMBER else "JsValue"
            return IdentityEqExpr(lhs=target, rhs=VarExpr(vname), domain=dom)
        raise ValueError(f"Unrecognized predicate atom {it!r} in {self.op_name}")

    def _expr_base_type(self, e: IRExpr) -> IRBaseType:
        if isinstance(e, VarExpr):
            return self.var_types.get(e.name, IRBaseType.JS_VALUE)
        if isinstance(e, (NumberFromMathExpr, FromTwosComp32ToNumberExpr, BitwiseNot32Expr, BitShift32Expr)):
            return IRBaseType.NUMBER
        if isinstance(e, (ToTwosComp32Expr, BitwiseBinary32Expr)):
            return IRBaseType.BITS32
        if isinstance(e, (ModuloExpr, MathSubExpr, Pow2Expr)):
            return IRBaseType.MATH_INT
        if isinstance(e, TruncateRealExpr):
            return IRBaseType.INT_OR_INF
        if isinstance(e, LitSpecialVal):
            if e.kind in ("NaN", "+0_F", "-0_F", "+inf_F", "-inf_F", "1_F"):
                return IRBaseType.NUMBER
            return IRBaseType.JS_VALUE
        if isinstance(e, LitBool):
            return IRBaseType.BOOL
        if isinstance(e, LitMath):
            if e.kind in ("+inf", "-inf"):
                return IRBaseType.INT_OR_INF
            return IRBaseType.MATH_INT
        if isinstance(e, LitEnumTag):
            if e.tag == "unused":
                return IRBaseType.UNUSED
            return IRBaseType.SIGNEDNESS
        if isinstance(e, CallExpr):
            if e.callee in ("SameType", "Number::equal", "Number::sameValue", "Number::sameValueZero",
                            "SameValue", "SameValueZero", "SameValueNonNumber", "IsStrictlyEqual",
                            "IsLooselyEqual", "BigInt::equal"):
                return IRBaseType.BOOL
            if e.callee in ("ToNumber", "StringToNumber", "ToInt32", "ToUint32", "ToUint16", "NumberBitwiseOp"):
                return IRBaseType.NUMBER
            if e.callee == "ToIntegerOrInfinity":
                return IRBaseType.INT_OR_INF
            if e.callee == "ToFixedSizeInteger":
                return IRBaseType.MATH_INT
            return IRBaseType.JS_VALUE
        return IRBaseType.JS_VALUE

    def parse_math_term(self, s: str) -> IRExpr:
        s = s.strip()
        if s == "+∞":
            return LitMath("+inf")
        if s == "-∞":
            return LitMath("-inf")
        if re.fullmatch(r"\d+", s):
            return LitMath(s, int(s))
        m_var = re.fullmatch(r"_([A-Za-z0-9_]+)_", s)
        if m_var:
            return VarExpr(m_var.group(1))
        m_real = re.fullmatch(r"ℝ\(_([A-Za-z0-9_]+)_\)", s)
        if m_real:
            return RealOfNumberExpr(VarExpr(m_real.group(1)))
        m_pow = re.fullmatch(r"2\^(?:\((.+)\)|([A-Za-z0-9_]+))", s)
        if m_pow:
            inner = (m_pow.group(1) or m_pow.group(2)).strip()
            return Pow2Expr(self.parse_math_term(inner))
        m_sub = re.fullmatch(r"(.+?)\s*-\s*(.+)", s)
        if m_sub:
            return MathSubExpr(self.parse_math_term(m_sub.group(1)), self.parse_math_term(m_sub.group(2)))
        raise ValueError(f"Cannot parse mathematical term: {s!r} in {self.op_name}")

    def parse_condition(self, cond_str: str) -> IRExpr:
        c = cond_str.strip()

        # Compound `, or if ` (used in IsLooselyEqual step 13)
        if ", or if " in c:
            parts = [p.strip() for p in c.split(", or if ")]
            return LogicExpr("or", [self.parse_condition(p) for p in parts])

        # Host web-compat check
        if c.startswith("the host is a web browser or otherwise supports #sec-IsHTMLDDA-internal-slot"):
            return HostSupportsHtmlDdaExpr()

        # Exact string length & code unit check (SameValueNonNumber step 4.a)
        m_str = re.fullmatch(
            r"_([A-Za-z0-9_]+)_ and _([A-Za-z0-9_]+)_ have the same length and the same code units in the same positions",
            c,
        )
        if m_str:
            return SameStringCodeUnitsExpr(VarExpr(m_str.group(1)), VarExpr(m_str.group(2)))

        # `_x_ and _y_ are finite Numbers`
        m_both_fin = re.fullmatch(r"_([A-Za-z0-9_]+)_ and _([A-Za-z0-9_]+)_ are finite Numbers", c)
        if m_both_fin:
            return LogicExpr(
                "and",
                [
                    TypePredExpr(VarExpr(m_both_fin.group(1)), "FiniteNumber"),
                    TypePredExpr(VarExpr(m_both_fin.group(2)), "FiniteNumber"),
                ],
            )

        # Conjunction with `, ` + `, and ` (e.g. `A, B, and C` in IsLooselyEqual step 4.a/4.b)
        # Be careful NOT to split `either X, Y, or Z` or `one of X, Y, or Z`!
        if " and " in c and "either " not in c.split(" and ")[0] and "one of " not in c:
            # Split top-level `A, B, and C` or `A and B`
            if ", and " in c:
                head, last = c.rsplit(", and ", 1)
                clauses = [p.strip() for p in head.split(", ")] + [last.strip()]
                return LogicExpr("and", [self.parse_condition(p) for p in clauses])
            parts = [p.strip() for p in c.split(" and ")]
            if all(self._looks_like_atomic_clause(p) for p in parts):
                return LogicExpr("and", [self.parse_condition(p) for p in parts])

        # Special case where first conjunct has `either ... or ...` followed by `, ... and ...`
        m_either_prefix = re.match(
            r"^(_[A-Za-z0-9_]+_ is either [^,]+? or [^,]+?),\s*(.+?),\s*and\s+(.+)$",
            c,
        )
        if m_either_prefix:
            return LogicExpr(
                "and",
                [
                    self.parse_condition(m_either_prefix.group(1)),
                    self.parse_condition(m_either_prefix.group(2)),
                    self.parse_condition(m_either_prefix.group(3)),
                ],
            )

        # `A and B` where B may contain `either ... or ...` (e.g. IsLooselyEqual steps 11, 12)
        m_and_2 = re.match(
            r"^(_[A-Za-z0-9_]+_ is (?:either .+?|a [A-Za-z]+|an Object))\s+and\s+(_[A-Za-z0-9_]+_ is .+)$",
            c,
        )
        if m_and_2:
            return LogicExpr(
                "and",
                [self.parse_condition(m_and_2.group(1)), self.parse_condition(m_and_2.group(2))],
            )

        # Disjunction `A or B` between full clauses (e.g. `_int_ = +∞ or _int_ = -∞` or `IsGeneric... or IsData...`)
        if " or " in c and not re.search(r"\b(?:either|one of)\b", c):
            parts = [p.strip() for p in c.split(" or ")]
            return LogicExpr("or", [self.parse_condition(p) for p in parts])

        # Function predicate comparison: `Op(args) is *true*` / `*false*`
        m_call_bool = re.fullmatch(r"([A-Za-z0-9_:]+)\(([^)]*)\)\s+is\s+\*(true|false)\*", c)
        if m_call_bool:
            call_e = self.parse_call_expr(f"{m_call_bool.group(1)}({m_call_bool.group(2)})")
            want = m_call_bool.group(3) == "true"
            if want:
                return call_e
            return IdentityEqExpr(call_e, LitBool(False), domain="Boolean")

        # Internal slot check: `_arg_ has an [[IsHTMLDDA]] internal slot`
        m_slot = re.fullmatch(r"_([A-Za-z0-9_]+)_ has an \[\[([A-Za-z0-9_]+)\]\] internal slot", c)
        if m_slot:
            return HasInternalSlotExpr(VarExpr(m_slot.group(1)), m_slot.group(2))

        # `_x_ is one of A, B, ..., or Z`
        m_oneof = re.fullmatch(r"_([A-Za-z0-9_]+)_ is one of (.+)", c)
        if m_oneof:
            target = VarExpr(m_oneof.group(1))
            raw_list = m_oneof.group(2).replace(", or ", ", ").replace(" or ", ", ")
            items = [it.strip() for it in raw_list.split(",") if it.strip()]
            return OneOfPredExpr(target, [self.parse_atom_check(target, it) for it in items])

        # `_x_ is either A, B, ..., or Z` or `_x_ is either A or B`
        m_either = re.fullmatch(r"_([A-Za-z0-9_]+)_ is either (.+)", c)
        if m_either:
            target = VarExpr(m_either.group(1))
            raw_list = m_either.group(2).replace(", or ", ", ").replace(" or ", ", ")
            items = [it.strip() for it in raw_list.split(",") if it.strip()]
            return OneOfPredExpr(target, [self.parse_atom_check(target, it) for it in items])

        # `_x_ is not <type/atom>`
        m_is_not = re.fullmatch(r"_([A-Za-z0-9_]+)_ is not (.+)", c)
        if m_is_not:
            return self.parse_atom_check(VarExpr(m_is_not.group(1)), m_is_not.group(2), negated=True)

        # `_x_ is <type/atom>`
        m_is = re.fullmatch(r"_([A-Za-z0-9_]+)_ is (.+)", c)
        if m_is:
            return self.parse_atom_check(VarExpr(m_is.group(1)), m_is.group(2), negated=False)

        # `ℝ(_x_) = ℝ(_y_)`
        m_real_eq = re.fullmatch(r"ℝ\(_([A-Za-z0-9_]+)_\)\s*=\s*ℝ\(_([A-Za-z0-9_]+)_\)", c)
        if m_real_eq:
            return RealEqExpr(VarExpr(m_real_eq.group(1)), VarExpr(m_real_eq.group(2)))

        # Mathematical comparisons: `lhs = rhs`, `lhs ≥ rhs`, `lhs < rhs`
        m_cmp = re.fullmatch(r"(.+?)\s*(=|≥|<)\s*(.+)", c)
        if m_cmp:
            op_map = {"=": "==", "≥": ">=", "<": "<"}
            return MathCmpExpr(
                op_map[m_cmp.group(2)],
                self.parse_math_term(m_cmp.group(1)),
                self.parse_math_term(m_cmp.group(3)),
            )

        raise ValueError(f"Cannot parse ECMA-262 condition: {c!r} in {self.op_name}")

    def _looks_like_atomic_clause(self, p: str) -> bool:
        return bool(
            re.match(r"^_[A-Za-z0-9_]+_ (?:is|has)\b", p)
            or re.match(r"^[A-Za-z0-9_:]+\(", p)
            or any(op in p for op in ("=", "≥", "<"))
        )

    def split_call_args(self, args_str: str) -> list[str]:
        out: list[str] = []
        depth = 0
        cur: list[str] = []
        for ch in args_str:
            if ch == "(":
                depth += 1
                cur.append(ch)
            elif ch == ")":
                depth -= 1
                cur.append(ch)
            elif ch == "," and depth == 0:
                if "".join(cur).strip():
                    out.append("".join(cur).strip())
                cur = []
            else:
                cur.append(ch)
        if "".join(cur).strip():
            out.append("".join(cur).strip())
        return out

    def parse_call_expr(self, s: str) -> CallExpr:
        s = s.strip()
        mode = CompletionMode.PURE
        if s.startswith("? "):
            mode = CompletionMode.QUESTION
            s = s[2:].strip()
        elif s.startswith("! "):
            mode = CompletionMode.BANG
            s = s[2:].strip()
        m = re.fullmatch(r"([A-Za-z0-9_:]+)\((.*)\)", s)
        if not m:
            raise ValueError(f"Invalid call expression: {s!r} in {self.op_name}")
        callee = m.group(1)
        raw_args = self.split_call_args(m.group(2))
        args = [self.parse_value_expr(a) for a in raw_args]
        self.callees.add(callee)
        return CallExpr(callee=callee, args=args, mode=mode)

    def parse_value_expr(self, expr_str: str) -> IRExpr:
        s = expr_str.strip().rstrip(".")

        # Strip explanatory second sentence on bitwise/shift returns ("The mathematical value of...")
        if ". " in s:
            s = s.split(". ", 1)[0].strip()

        if s == "*true*":
            return LitBool(True)
        if s == "*false*":
            return LitBool(False)
        if s == "*undefined*":
            return LitSpecialVal("undefined")
        if s == "*null*":
            return LitSpecialVal("null")
        if s == "*NaN*":
            return LitSpecialVal("NaN")
        if s == "*+0*_𝔽":
            return LitSpecialVal("+0_F")
        if s == "*-0*_𝔽":
            return LitSpecialVal("-0_F")
        if s == "*+∞*_𝔽":
            return LitSpecialVal("+inf_F")
        if s == "*-∞*_𝔽":
            return LitSpecialVal("-inf_F")
        if s == "*1*_𝔽":
            return LitSpecialVal("1_F")
        if s == "~unused~":
            return LitEnumTag("unused")
        if s == "~signed~":
            return LitEnumTag("signed")
        if s == "~unsigned~":
            return LitEnumTag("unsigned")
        if s == "~number~":
            return LitEnumTag("number")
        if s in ("`&`", "`^`", "`|`"):
            return LitBitOpToken(s[1])
        if s == "+∞":
            return LitMath("+inf")
        if s == "-∞":
            return LitMath("-inf")
        if re.fullmatch(r"\d+", s):
            return LitMath(s, int(s))

        m_var = re.fullmatch(r"_([A-Za-z0-9_]+)_", s)
        if m_var:
            return VarExpr(m_var.group(1))

        # `𝔽(<inner>)`
        if s.startswith("𝔽(") and s.endswith(")"):
            return NumberFromMathExpr(self.parse_value_expr(s[2:-1]))

        # `truncate(ℝ(_number_))`
        m_trunc = re.fullmatch(r"truncate\(ℝ\(_([A-Za-z0-9_]+)_\)\)", s)
        if m_trunc:
            return TruncateRealExpr(VarExpr(m_trunc.group(1)))

        # `<lhs> modulo <rhs>`
        m_mod = re.fullmatch(r"(.+?)\s+modulo\s+(.+)", s)
        if m_mod:
            return ModuloExpr(self.parse_math_term(m_mod.group(1)), self.parse_math_term(m_mod.group(2)))

        # Bitwise / two's complement prose forms in §6.1.6.1:
        m_bnot = re.fullmatch(r"the bitwise complement of _([A-Za-z0-9_]+)_", s)
        if m_bnot:
            return BitwiseNot32Expr(VarExpr(m_bnot.group(1)))

        m_shl = re.fullmatch(
            r"the result of left shifting _([A-Za-z0-9_]+)_ by _([A-Za-z0-9_]+)_ bits",
            s,
        )
        if m_shl:
            return BitShift32Expr("shl", VarExpr(m_shl.group(1)), VarExpr(m_shl.group(2)))

        m_ashr = re.fullmatch(
            r"the result of performing a sign-extending right shift of _([A-Za-z0-9_]+)_ by _([A-Za-z0-9_]+)_ bits",
            s,
        )
        if m_ashr:
            return BitShift32Expr("ashr", VarExpr(m_ashr.group(1)), VarExpr(m_ashr.group(2)))

        m_lshr = re.fullmatch(
            r"the result of performing a zero-filling right shift of _([A-Za-z0-9_]+)_ by _([A-Za-z0-9_]+)_ bits",
            s,
        )
        if m_lshr:
            return BitShift32Expr("lshr", VarExpr(m_lshr.group(1)), VarExpr(m_lshr.group(2)))

        m_to_bits = re.fullmatch(
            r"the 32-bit two's complement bit string representing ℝ\(_([A-Za-z0-9_]+)_\)",
            s,
        )
        if m_to_bits:
            return ToTwosComp32Expr(VarExpr(m_to_bits.group(1)))

        m_bit_bin = re.fullmatch(
            r"the result of applying the bitwise (AND|XOR|OR)(?: \([^)]+\))? operation to _([A-Za-z0-9_]+)_ and _([A-Za-z0-9_]+)_",
            s,
        )
        if m_bit_bin:
            return BitwiseBinary32Expr(
                m_bit_bin.group(1),
                VarExpr(m_bit_bin.group(2)),
                VarExpr(m_bit_bin.group(3)),
            )

        m_from_bits = re.fullmatch(
            r"the Number value for the integer represented by the 32-bit two's complement bit string _([A-Za-z0-9_]+)_",
            s,
        )
        if m_from_bits:
            return FromTwosComp32ToNumberExpr(VarExpr(m_from_bits.group(1)))

        # Call expression `[?|!] Name(...)`
        if re.match(r"^(?:[?!]\s+)?[A-Za-z0-9_:]+\(.*\)$", s):
            return self.parse_call_expr(s)

        # Fallback mathematical subtraction `_fixedInt_ - 2^_bitWidth_`
        if " - " in s:
            return self.parse_math_term(s)

        raise ValueError(f"Cannot parse ECMA-262 value expression: {expr_str!r} in {self.op_name}")

    def compile_inline_action(self, step: StepNode, action_text: str) -> IRStmt:
        a = action_text.strip().rstrip(".")
        if a.startswith("return ") or a.startswith("Return "):
            val_s = a.split(" ", 1)[1]
            return IRReturn(step.step_label, step.comment_line, self.parse_value_expr(val_s))
        if a == "throw a *TypeError* exception" or a == "Throw a *TypeError* exception":
            return IRThrow(step.step_label, step.comment_line, "TypeError")
        m_set = re.fullmatch(r"[Ss]et _([A-Za-z0-9_]+)_ to (.+)", a)
        if m_set:
            vname = m_set.group(1)
            return IRSet(step.step_label, step.comment_line, vname, self.parse_value_expr(m_set.group(2)))
        raise ValueError(f"Unsupported inline action: {action_text!r} in {self.op_name}")

    def compile_step_list(self, nodes: list[StepNode]) -> list[IRStmt]:
        stmts: list[IRStmt] = []
        i = 0
        while i < len(nodes):
            node = nodes[i]
            txt = node.clean_text

            if txt.startswith("NOTE:"):
                stmts.append(IRNote(node.step_label, node.comment_line))
                i += 1
                continue

            if txt.startswith("Assert:"):
                cond_s = txt[len("Assert:") :].strip().rstrip(".")
                stmts.append(IRAssert(node.step_label, node.comment_line, self.parse_condition(cond_s)))
                i += 1
                continue

            m_let = re.fullmatch(r"Let _([A-Za-z0-9_]+)_ be (.+)\.", txt)
            if m_let:
                vname = m_let.group(1)
                self.rust_ident(vname)
                rhs = self.parse_value_expr(m_let.group(2))
                self.var_types[vname] = self._expr_base_type(rhs)
                stmts.append(IRLet(node.step_label, node.comment_line, vname, rhs))
                i += 1
                continue

            if txt.startswith("If ") and txt.endswith(", then"):
                cond_s = txt[len("If ") : -len(", then")].strip()
                cond_ir = self.parse_condition(cond_s)
                then_body = self.compile_step_list(node.children)
                elif_branches: list[IRElifBranch] = []
                else_label: Optional[str] = None
                else_comment: Optional[str] = None
                else_body: list[IRStmt] = []
                i += 1
                while i < len(nodes) and nodes[i].clean_text.startswith("Else if ") and nodes[i].clean_text.endswith(", then"):
                    en = nodes[i]
                    econd_s = en.clean_text[len("Else if ") : -len(", then")].strip()
                    elif_branches.append(
                        IRElifBranch(
                            step_label=en.step_label,
                            comment=en.comment_line,
                            cond=self.parse_condition(econd_s),
                            body=self.compile_step_list(en.children),
                        )
                    )
                    i += 1
                if i < len(nodes) and nodes[i].clean_text in ("Else,", "Else"):
                    en = nodes[i]
                    else_label = en.step_label
                    else_comment = en.comment_line
                    else_body = self.compile_step_list(en.children)
                    i += 1
                stmts.append(
                    IRIf(
                        step_label=node.step_label,
                        comment=node.comment_line,
                        cond=cond_ir,
                        then_body=then_body,
                        elif_branches=elif_branches,
                        else_step_label=else_label,
                        else_comment=else_comment,
                        else_body=else_body,
                    )
                )
                continue

            # Single-line conditional: `If <cond>, <action>.`
            if txt.startswith("If "):
                # Find comma before `return `, `throw `, or `set _`
                m_inline = re.match(r"^If (.+?),\s*((?:return|throw|set)\s+.+)$", txt)
                if not m_inline:
                    raise ValueError(f"Cannot split inline If step: {txt!r} in {self.op_name}")
                cond_ir = self.parse_condition(m_inline.group(1))
                act_ir = self.compile_inline_action(node, m_inline.group(2))
                # Clear duplicate comment on inner inline action since outer IRIf carries the step comment
                act_ir.comment = ""
                stmts.append(IRIf(step_label=node.step_label, comment=node.comment_line, cond=cond_ir, then_body=[act_ir]))
                i += 1
                continue

            if txt.startswith("Return ") or txt.startswith("Throw "):
                stmts.append(self.compile_inline_action(node, txt))
                i += 1
                continue

            raise ValueError(f"Unsupported ECMA-262 step {node.step_label}: {txt!r} in {self.op_name}")

        self._analyze_mutations_and_ssa_phis(stmts)
        return stmts

    def _collect_set_vars(self, stmts: list[IRStmt]) -> set[str]:
        mutated: set[str] = set()
        for st in stmts:
            if isinstance(st, IRSet):
                mutated.add(st.var)
            elif isinstance(st, IRIf):
                mutated |= self._collect_set_vars(st.then_body)
                for eb in st.elif_branches:
                    mutated |= self._collect_set_vars(eb.body)
                mutated |= self._collect_set_vars(st.else_body)
        return mutated

    def _last_defined_let(self, body: list[IRStmt]) -> Optional[str]:
        if body and isinstance(body[-1], IRLet):
            return body[-1].var
        return None

    def _analyze_mutations_and_ssa_phis(self, stmts: list[IRStmt]) -> None:
        mutated = self._collect_set_vars(stmts)
        for st in stmts:
            if isinstance(st, IRLet) and st.var in mutated:
                st.mutable = True
            elif isinstance(st, IRIf) and st.else_body:
                v0 = self._last_defined_let(st.then_body)
                if v0 and all(self._last_defined_let(eb.body) == v0 for eb in st.elif_branches) and self._last_defined_let(st.else_body) == v0:
                    st.phi_var = v0


def build_ires_cfg(stmts: list[IRStmt]) -> IRCFG:
    """Construct an explicit basic-block Control-Flow Graph (IRES CFG) from lowered IR statements."""
    blocks: dict[int, CFGBlock] = {}
    next_id = 0

    def new_block(kind: str, label: str) -> int:
        nonlocal next_id
        bid = next_id
        next_id += 1
        blocks[bid] = CFGBlock(id=bid, kind=kind, label=label)
        return bid

    entry = new_block("entry", "ENTRY")

    def lower_seq(seq: list[IRStmt], cur_heads: list[int]) -> list[int]:
        heads = cur_heads
        for st in seq:
            if not heads:
                break
            if isinstance(st, IRNote):
                continue
            if isinstance(st, (IRLet, IRSet, IRAssert)):
                b = new_block("stmt", f"{st.step_label}:{type(st).__name__}")
                for h in heads:
                    blocks[h].succs.append(b)
                heads = [b]
            elif isinstance(st, IRReturn):
                b = new_block("return", f"{st.step_label}:Return")
                for h in heads:
                    blocks[h].succs.append(b)
                heads = []
            elif isinstance(st, IRThrow):
                b = new_block("throw", f"{st.step_label}:Throw({st.exception})")
                for h in heads:
                    blocks[h].succs.append(b)
                heads = []
            elif isinstance(st, IRIf):
                br = new_block("branch", f"{st.step_label}:Branch")
                for h in heads:
                    blocks[h].succs.append(br)
                exits: list[int] = []
                exits.extend(lower_seq(st.then_body, [br]))
                prev_cond = br
                for eb in st.elif_branches:
                    ebr = new_block("branch", f"{eb.step_label}:ElifBranch")
                    blocks[prev_cond].succs.append(ebr)
                    exits.extend(lower_seq(eb.body, [ebr]))
                    prev_cond = ebr
                if st.else_body:
                    exits.extend(lower_seq(st.else_body, [prev_cond]))
                else:
                    exits.append(prev_cond)
                if exits:
                    join = new_block("join", f"{st.step_label}:Phi({st.phi_var})" if st.phi_var else f"{st.step_label}:Join")
                    for ex in exits:
                        blocks[ex].succs.append(join)
                    heads = [join]
                else:
                    heads = []
        return heads

    lower_seq(stmts, [entry])
    return IRCFG(entry=entry, blocks=blocks)


def topological_sort_operations(ops: list[IROperation]) -> list[IROperation]:
    """Order operations so callees appear before callers (preserving spec order on ties)."""
    by_name = {op.spec_name: op for op in ops}
    visited: set[str] = set()
    ordered: list[IROperation] = []

    def dfs(op: IROperation) -> None:
        if op.spec_name in visited:
            return
        visited.add(op.spec_name)
        for c in op.callees:
            if c != op.spec_name and c in by_name:
                dfs(by_name[c])
        ordered.append(op)

    for op in ops:
        dfs(op)
    return ordered


# ===============================================================================================
# 5. Pass 3 & 4: Warblre-Style Verus `spec fn` + `exec fn` Emitter
# ===============================================================================================

class VerusCodeEmitter:
    def __init__(self, ops: list[IROperation]) -> None:
        self.ops = ops
        self.op_map: dict[str, IROperation] = {op.spec_name: op for op in ops}

    @staticmethod
    def _strip_outer_parens(s: str) -> str:
        s = s.strip()
        while s.startswith("(") and s.endswith(")"):
            depth = 0
            matched_end = False
            for idx, ch in enumerate(s):
                if ch == "(":
                    depth += 1
                elif ch == ")":
                    depth -= 1
                    if depth == 0:
                        matched_end = idx == len(s) - 1
                        break
            if matched_end:
                s = s[1:-1].strip()
            else:
                break
        return s

    def spec_type_str(self, ty: IRType) -> str:
        base_map = {
            IRBaseType.JS_VALUE: "SpecJsValue",
            IRBaseType.NUMBER: "JsNumber",
            IRBaseType.BOOL: "bool",
            IRBaseType.MATH_INT: "int",
            IRBaseType.POS_INT: "nat",
            IRBaseType.INT_OR_INF: "MathIntOrInf",
            IRBaseType.SIGNEDNESS: "Signedness",
            IRBaseType.BITWISE_OP: "BitwiseOp",
            IRBaseType.BITS32: "u32",
            IRBaseType.UNUSED: "Unused",
        }
        b = base_map[ty.base]
        return f"AbruptOrNormal<{b}>" if ty.fallible else b

    def exec_param_type_str(self, ty: IRType) -> str:
        base_map = {
            IRBaseType.JS_VALUE: "&JsValue",
            IRBaseType.NUMBER: "JsNumber",
            IRBaseType.BOOL: "bool",
            IRBaseType.MATH_INT: "i64",
            IRBaseType.POS_INT: "u32",
            IRBaseType.INT_OR_INF: "MathIntOrInf",
            IRBaseType.SIGNEDNESS: "Signedness",
            IRBaseType.BITWISE_OP: "BitwiseOp",
            IRBaseType.BITS32: "u32",
            IRBaseType.UNUSED: "Unused",
        }
        return base_map[ty.base]

    def exec_ret_type_str(self, ty: IRType) -> str:
        base_map = {
            IRBaseType.JS_VALUE: "JsValue",
            IRBaseType.NUMBER: "JsNumber",
            IRBaseType.BOOL: "bool",
            IRBaseType.MATH_INT: "i64",
            IRBaseType.POS_INT: "u32",
            IRBaseType.INT_OR_INF: "MathIntOrInf",
            IRBaseType.SIGNEDNESS: "Signedness",
            IRBaseType.BITWISE_OP: "BitwiseOp",
            IRBaseType.BITS32: "u32",
            IRBaseType.UNUSED: "Unused",
        }
        b = base_map[ty.base]
        return f"AbruptOrNormal<{b}>" if ty.fallible else b

    def emit_module(self, source_label: str) -> str:
        lines: list[str] = [
            "//! AUTO-GENERATED BY `browser/scripts/esmeta_to_verus.py` — DO NOT EDIT BY HAND.",
            f"//! Source: `{source_label}` (pinned `tc39/ecma262` `spec.html` `<emu-clause>` excerpts).",
            "//! Each ECMA-262 `<emu-alg>` step is interleaved verbatim right above its Verus",
            "//! specification and proved-equivalent executable translation (Warblre style).",
            "use vstd::prelude::*;",
            "use crate::runtime::*;",
            "",
            "verus! {",
            "",
        ]
        for op in self.ops:
            lines.extend(self.emit_operation(op))
            lines.append("")
        lines.append("} // verus!")
        lines.append("")
        return "\n".join(lines)

    def emit_operation(self, op: IROperation) -> list[str]:
        var_types: dict[str, IRBaseType] = {p.name: p.ty.base for p in op.params}
        var_rust: dict[str, str] = {p.name: p.rust_name for p in op.params}
        param_names: set[str] = {p.name for p in op.params}

        def populate_vars(stmts: list[IRStmt]) -> None:
            sc = StepCompiler(op.spec_name, op.params, op.ret_type)
            for st in stmts:
                if isinstance(st, IRLet):
                    var_rust[st.var] = sc.rust_ident(st.var)
                    var_types[st.var] = sc._expr_base_type(st.rhs)
                elif isinstance(st, IRIf):
                    populate_vars(st.then_body)
                    for eb in st.elif_branches:
                        populate_vars(eb.body)
                    populate_vars(st.else_body)

        populate_vars(op.body)

        out: list[str] = [
            "// -----------------------------------------------------------------------------------------------",
            f"// ECMA-262 §{op.clause_number} {op.spec_name} (#{op.clause_id})",
            "// -----------------------------------------------------------------------------------------------",
            "",
        ]
        out.extend(self.emit_spec_fn(op, var_types, var_rust))
        out.append("")
        out.extend(self.emit_exec_fn(op, var_types, var_rust, param_names))
        alg_lemmas = self.emit_algebraic_lemmas(op)
        if alg_lemmas:
            out.append("")
            out.extend(alg_lemmas)
        return out

    def emit_algebraic_lemmas(self, op: IROperation) -> list[str]:
        """Synthesize standard algebraic `proof fn` obligations (`standard::auto_std!`-style)
        for binary relations, boolean projections, and nullish guards in `generated.rs`."""
        sfn = op.spec_fn_name
        rfn = op.rust_fn_name
        if len(op.params) == 2 and op.ret_type == IRType(IRBaseType.BOOL, fallible=False):
            pty = op.params[0].ty
            p1ty = op.params[1].ty
            if pty == p1ty and not pty.not_number_constraint:
                t_str = self.spec_type_str(pty)
                if op.spec_name in ("SameType", "Number::sameValue", "Number::sameValueZero", "SameValue", "SameValueZero"):
                    return [
                        f"pub proof fn gen_lemma_{rfn}_equivalence(x: {t_str}, y: {t_str}, z: {t_str})",
                        "    ensures",
                        f"        {sfn}(x, x),",
                        f"        {sfn}(x, y) == {sfn}(y, x),",
                        f"        ({sfn}(x, y) && {sfn}(y, z)) ==> {sfn}(x, z),",
                        "{",
                        "}",
                    ]
                if op.spec_name == "Number::equal":
                    return [
                        f"pub proof fn gen_lemma_{rfn}_algebraic(x: JsNumber, y: JsNumber, z: JsNumber)",
                        "    ensures",
                        f"        {sfn}(x, x) <==> !spec_is_nan(x),",
                        f"        {sfn}(x, y) == {sfn}(y, x),",
                        f"        ({sfn}(x, y) && {sfn}(y, z)) ==> {sfn}(x, z),",
                        "{",
                        "}",
                    ]
                if op.spec_name == "IsStrictlyEqual":
                    return [
                        f"pub proof fn gen_lemma_{rfn}_algebraic(x: SpecJsValue, y: SpecJsValue, z: SpecJsValue)",
                        "    ensures",
                        f"        {sfn}(x, x) <==> !spec_val_is_nan(x),",
                        f"        {sfn}(x, y) == {sfn}(y, x),",
                        f"        ({sfn}(x, y) && {sfn}(y, z)) ==> {sfn}(x, z),",
                        "{",
                        "}",
                    ]
        if op.spec_name == "ToBoolean":
            return [
                f"pub proof fn gen_lemma_{rfn}_idempotent(arg: SpecJsValue)",
                f"    ensures {sfn}(SpecJsValue::Boolean({sfn}(arg))) == {sfn}(arg),",
                "{",
                "}",
            ]
        if op.spec_name == "RequireObjectCoercible":
            return [
                f"pub proof fn gen_lemma_{rfn}_nullish_iff_throw(arg: SpecJsValue)",
                f"    ensures ({sfn}(arg) is ThrowTypeError) <==> (spec_is_undefined(arg) || spec_is_null(arg)),",
                "{",
                "}",
            ]
        return []

    # --- Spec Function Emission (Pure Functional Expression Tree with Interleaved Comments) ---

    def emit_spec_fn(
        self,
        op: IROperation,
        var_types: dict[str, IRBaseType],
        var_rust: dict[str, str],
    ) -> list[str]:
        params_sig = ", ".join(f"{p.rust_name}: {self.spec_type_str(p.ty)}" for p in op.params)
        ret_sig = self.spec_type_str(op.ret_type)
        lines = [f"pub open spec fn {op.spec_fn_name}({params_sig}) -> {ret_sig}"]
        if op.is_recursive:
            lines.append(f"    decreases {self._recursion_rank_expr(op, spec_mode=True)},")
        lines.append("{")
        lines.extend(self._emit_spec_stmts(op, op.body, var_types, var_rust, indent=4))
        lines.append("}")
        return lines

    def _recursion_rank_expr(self, op: IROperation, spec_mode: bool) -> str:
        if op.spec_name == "ToNumber":
            p = op.params[0].rust_name
            return f"spec_tonumber_rank({p})" if spec_mode else f"spec_tonumber_rank({p}@)"
        if op.spec_name == "IsLooselyEqual":
            px, py = op.params[0].rust_name, op.params[1].rust_name
            return f"spec_loosely_equal_rank({px}, {py})" if spec_mode else f"spec_loosely_equal_rank({px}@, {py}@)"
        raise ValueError(f"Missing termination rank synthesis for recursive op {op.spec_name}")

    def _emit_spec_stmts(
        self,
        op: IROperation,
        stmts: list[IRStmt],
        var_types: dict[str, IRBaseType],
        var_rust: dict[str, str],
        indent: int,
    ) -> list[str]:
        pad = " " * indent
        if not stmts:
            return []
        st = stmts[0]
        rest = stmts[1:]
        lines: list[str] = []

        if st.comment:
            lines.append(f"{pad}// {st.comment}")

        if isinstance(st, (IRNote, IRAssert)):
            lines.extend(self._emit_spec_stmts(op, rest, var_types, var_rust, indent))
            return lines

        if isinstance(st, IRThrow):
            lines.append(f"{pad}AbruptOrNormal::ThrowTypeError")
            return lines

        if isinstance(st, IRReturn):
            lines.extend(self._emit_spec_return_expr(op, st.value, var_types, var_rust, indent))
            return lines

        if isinstance(st, IRLet):
            v = var_rust[st.var]
            # Check if RHS contains a `?` completion call
            q_call = self._extract_question_call(st.rhs)
            if q_call is not None:
                call_code = self._emit_spec_call(q_call, var_types, var_rust)
                lines.append(f"{pad}match {call_code} {{")
                lines.append(f"{pad}    AbruptOrNormal::ThrowTypeError => AbruptOrNormal::ThrowTypeError,")
                lines.append(f"{pad}    AbruptOrNormal::Normal({v}) => {{")
                lines.extend(self._emit_spec_stmts(op, rest, var_types, var_rust, indent + 8))
                lines.append(f"{pad}    }}")
                lines.append(f"{pad}}}")
                return lines
            rhs_code = self._emit_spec_expr(st.rhs, var_types[st.var], var_types, var_rust)
            lines.append(f"{pad}let {v} = {rhs_code};")
            lines.extend(self._emit_spec_stmts(op, rest, var_types, var_rust, indent))
            return lines

        if isinstance(st, IRIf):
            # Case A: Inline `If <cond>, set _v_ to <rhs>` -> functional SSA shadowing!
            if len(st.then_body) == 1 and isinstance(st.then_body[0], IRSet) and not st.elif_branches and not st.else_body:
                set_st = st.then_body[0]
                v = var_rust[set_st.var]
                cond_code = self._strip_outer_parens(self._emit_spec_cond(st.cond, var_types, var_rust))
                rhs_code = self._emit_spec_expr(set_st.rhs, var_types[set_st.var], var_types, var_rust)
                lines.append(f"{pad}let {v} = if {cond_code} {{ {rhs_code} }} else {{ {v} }};")
                lines.extend(self._emit_spec_stmts(op, rest, var_types, var_rust, indent))
                return lines

            # Case B: SSA phi-lifted `If / Else if / Else` defining `let phi_var = ...`
            if st.phi_var is not None:
                pv = var_rust[st.phi_var]
                pty = var_types[st.phi_var]
                cond_code = self._strip_outer_parens(self._emit_spec_cond(st.cond, var_types, var_rust))
                then_let = st.then_body[-1]
                assert isinstance(then_let, IRLet)
                lines.append(f"{pad}let {pv} = if {cond_code} {{")
                for sub in st.then_body[:-1]:
                    if sub.comment:
                        lines.append(f"{pad}    // {sub.comment}")
                if then_let.comment:
                    lines.append(f"{pad}    // {then_let.comment}")
                lines.append(f"{pad}    {self._emit_spec_expr(then_let.rhs, pty, var_types, var_rust)}")
                for eb in st.elif_branches:
                    econd = self._strip_outer_parens(self._emit_spec_cond(eb.cond, var_types, var_rust))
                    elet = eb.body[-1]
                    assert isinstance(elet, IRLet)
                    lines.append(f"{pad}}} else if {econd} {{")
                    if eb.comment:
                        lines.append(f"{pad}    // {eb.comment}")
                    for sub in eb.body[:-1]:
                        if sub.comment:
                            lines.append(f"{pad}    // {sub.comment}")
                    if elet.comment:
                        lines.append(f"{pad}    // {elet.comment}")
                    lines.append(f"{pad}    {self._emit_spec_expr(elet.rhs, pty, var_types, var_rust)}")
                lines.append(f"{pad}}} else {{")
                if st.else_comment:
                    lines.append(f"{pad}    // {st.else_comment}")
                else_let = st.else_body[-1]
                assert isinstance(else_let, IRLet)
                for sub in st.else_body[:-1]:
                    if sub.comment:
                        lines.append(f"{pad}    // {sub.comment}")
                if else_let.comment:
                    lines.append(f"{pad}    // {else_let.comment}")
                lines.append(f"{pad}    {self._emit_spec_expr(else_let.rhs, pty, var_types, var_rust)}")
                lines.append(f"{pad}}};")
                lines.extend(self._emit_spec_stmts(op, rest, var_types, var_rust, indent))
                return lines

            # Case C: Conditional whose `then_body` always returns/throws vs conditionally returns (e.g. nested Ifs!)
            cond_code = self._strip_outer_parens(self._emit_spec_cond(st.cond, var_types, var_rust))
            if self._always_terminates(st.then_body) and not st.elif_branches and not st.else_body:
                lines.append(f"{pad}if {cond_code} {{")
                lines.extend(self._emit_spec_stmts(op, st.then_body, var_types, var_rust, indent + 4))
                lines.append(f"{pad}}} else {{")
                lines.extend(self._emit_spec_stmts(op, rest, var_types, var_rust, indent + 4))
                lines.append(f"{pad}}}")
                return lines

            # Nested guard block (e.g. ToBoolean step 3 / IsLooselyEqual step 4): flatten guarded sub-ifs
            if not st.elif_branches and not st.else_body and all(isinstance(ch, IRIf) and self._always_terminates(ch.then_body) for ch in st.then_body):
                lines.append(f"{pad}if {cond_code} {{")
                lines.extend(self._emit_spec_stmts(op, st.then_body + rest, var_types, var_rust, indent + 4))
                lines.append(f"{pad}}} else {{")
                lines.extend(self._emit_spec_stmts(op, rest, var_types, var_rust, indent + 4))
                lines.append(f"{pad}}}")
                return lines

        raise ValueError(f"Cannot emit spec statement {st!r} in {op.spec_name}")

    def _always_terminates(self, stmts: list[IRStmt]) -> bool:
        for st in stmts:
            if isinstance(st, (IRReturn, IRThrow)):
                return True
            if isinstance(st, IRIf) and st.else_body:
                if self._always_terminates(st.then_body) and all(self._always_terminates(eb.body) for eb in st.elif_branches) and self._always_terminates(st.else_body):
                    return True
        return False

    def _extract_question_call(self, expr: IRExpr) -> Optional[CallExpr]:
        if isinstance(expr, CallExpr) and expr.mode == CompletionMode.QUESTION:
            return expr
        return None

    def _find_nested_question_arg(self, call: CallExpr) -> Optional[tuple[int, CallExpr]]:
        for idx, a in enumerate(call.args):
            if isinstance(a, CallExpr) and a.mode == CompletionMode.QUESTION:
                return idx, a
        return None

    def _emit_spec_return_expr(
        self,
        op: IROperation,
        val: IRExpr,
        var_types: dict[str, IRBaseType],
        var_rust: dict[str, str],
        indent: int,
    ) -> list[str]:
        pad = " " * indent
        # Direct `? Op(...)` return
        if isinstance(val, CallExpr) and val.mode == CompletionMode.QUESTION:
            return [f"{pad}{self._emit_spec_call(val, var_types, var_rust)}"]

        # `! Op(..., ? SubOp(...), ...)` (e.g. IsLooselyEqual steps 11, 12!)
        if isinstance(val, CallExpr) and val.mode == CompletionMode.BANG:
            nested_q = self._find_nested_question_arg(val)
            if nested_q is not None:
                arg_idx, sub_call = nested_q
                tmp = f"__coerced_{arg_idx}"
                new_args = list(val.args)
                new_args[arg_idx] = VarExpr(tmp)
                vt_copy = dict(var_types)
                vr_copy = dict(var_rust)
                vt_copy[tmp] = IRBaseType.JS_VALUE
                vr_copy[tmp] = tmp
                rewritten = CallExpr(val.callee, new_args, val.mode)
                inner_code = self._emit_spec_expr(rewritten, op.ret_type.base, vt_copy, vr_copy)
                wrapped = f"AbruptOrNormal::Normal({inner_code})" if op.ret_type.fallible else inner_code
                return [
                    f"{pad}match {self._emit_spec_call(sub_call, var_types, var_rust)} {{",
                    f"{pad}    AbruptOrNormal::ThrowTypeError => AbruptOrNormal::ThrowTypeError,",
                    f"{pad}    AbruptOrNormal::Normal({tmp}) => {wrapped},",
                    f"{pad}}}",
                ]

        code = self._emit_spec_expr(val, op.ret_type.base, var_types, var_rust)
        if op.ret_type.fallible:
            return [f"{pad}AbruptOrNormal::Normal({code})"]
        return [f"{pad}{code}"]

    def _emit_spec_cond(
        self,
        cond: IRExpr,
        var_types: dict[str, IRBaseType],
        var_rust: dict[str, str],
    ) -> str:
        if isinstance(cond, LogicExpr):
            sep = " && " if cond.op == "and" else " || "
            return "(" + sep.join(self._emit_spec_cond(it, var_types, var_rust) for it in cond.items) + ")"
        if isinstance(cond, OneOfPredExpr):
            return "(" + " || ".join(self._emit_spec_cond(ch, var_types, var_rust) for ch in cond.checks) + ")"
        if isinstance(cond, TypePredExpr):
            v = self._emit_spec_expr(cond.target, IRBaseType.JS_VALUE, var_types, var_rust)
            fn_map = {
                "Boolean": "spec_is_boolean",
                "Number": "spec_is_number",
                "BigInt": "spec_is_bigint",
                "String": "spec_is_string",
                "Symbol": "spec_is_symbol",
                "Object": "spec_is_object",
                "FiniteNumber": "spec_val_is_finite_number",
            }
            c = f"{fn_map[cond.type_name]}({v})"
            return f"!{c}" if cond.negated else c
        if isinstance(cond, ValuePredExpr):
            t_ty = var_types.get(cond.target.name, IRBaseType.JS_VALUE) if isinstance(cond.target, VarExpr) else IRBaseType.JS_VALUE
            if t_ty == IRBaseType.NUMBER:
                v = self._emit_spec_expr(cond.target, IRBaseType.NUMBER, var_types, var_rust)
                nmap = {
                    "NaN": f"spec_is_nan({v})",
                    "+0_F": f"spec_is_pos_zero({v})",
                    "-0_F": f"spec_is_neg_zero({v})",
                    "+inf_F": f"spec_is_pos_inf({v})",
                    "-inf_F": f"spec_is_neg_inf({v})",
                }
                c = nmap[cond.kind]
            else:
                v = self._emit_spec_expr(cond.target, IRBaseType.JS_VALUE, var_types, var_rust)
                vmap = {
                    "undefined": f"spec_is_undefined({v})",
                    "null": f"spec_is_null({v})",
                    "NaN": f"spec_val_is_nan({v})",
                    "+0_F": f"spec_val_is_pos_zero({v})",
                    "-0_F": f"spec_val_is_neg_zero({v})",
                    "+inf_F": f"spec_val_is_pos_inf({v})",
                    "-inf_F": f"spec_val_is_neg_inf({v})",
                    "true": f"spec_is_bool_true({v})",
                    "false": f"spec_is_bool_false({v})",
                    "0_Z": f"spec_val_is_bigint_zero({v})",
                    "empty_str": f"spec_val_is_empty_string({v})",
                }
                c = vmap[cond.kind]
            return f"!{c}" if cond.negated else c
        if isinstance(cond, IdentityEqExpr):
            if cond.domain == "Number":
                a = self._emit_spec_expr(cond.lhs, IRBaseType.NUMBER, var_types, var_rust)
                b = self._emit_spec_expr(cond.rhs, IRBaseType.NUMBER, var_types, var_rust)
                return f"spec_number_is({a}, {b})"
            if cond.domain == "BitwiseOp":
                a = self._emit_spec_expr(cond.lhs, IRBaseType.BITWISE_OP, var_types, var_rust)
                b = self._emit_spec_expr(cond.rhs, IRBaseType.BITWISE_OP, var_types, var_rust)
                return f"({a} == {b})"
            if cond.domain == "Signedness":
                a = self._emit_spec_expr(cond.lhs, IRBaseType.SIGNEDNESS, var_types, var_rust)
                b = self._emit_spec_expr(cond.rhs, IRBaseType.SIGNEDNESS, var_types, var_rust)
                return f"({a} == {b})"
            if cond.domain == "Boolean":
                a = self._emit_spec_expr(cond.lhs, IRBaseType.BOOL, var_types, var_rust)
                b = self._emit_spec_expr(cond.rhs, IRBaseType.BOOL, var_types, var_rust)
                return f"({a} == {b})"
            a = self._emit_spec_expr(cond.lhs, IRBaseType.JS_VALUE, var_types, var_rust)
            b = self._emit_spec_expr(cond.rhs, IRBaseType.JS_VALUE, var_types, var_rust)
            return f"spec_val_non_number_is({a}, {b})"
        if isinstance(cond, HostSupportsHtmlDdaExpr):
            return "spec_host_supports_htmldda()"
        if isinstance(cond, HasInternalSlotExpr):
            v = self._emit_spec_expr(cond.target, IRBaseType.JS_VALUE, var_types, var_rust)
            return f"spec_has_htmldda_slot({v})"
        if isinstance(cond, SameStringCodeUnitsExpr):
            a = self._emit_spec_expr(cond.lhs, IRBaseType.JS_VALUE, var_types, var_rust)
            b = self._emit_spec_expr(cond.rhs, IRBaseType.JS_VALUE, var_types, var_rust)
            return f"spec_same_string_code_units({a}, {b})"
        if isinstance(cond, RealEqExpr):
            a = self._emit_spec_expr(cond.lhs, IRBaseType.JS_VALUE, var_types, var_rust)
            b = self._emit_spec_expr(cond.rhs, IRBaseType.JS_VALUE, var_types, var_rust)
            return f"spec_val_real_equal({a}, {b})"
        if isinstance(cond, MathCmpExpr):
            if isinstance(cond.rhs, LitMath) and cond.rhs.kind in ("+inf", "-inf"):
                v = self._emit_spec_expr(cond.lhs, IRBaseType.INT_OR_INF, var_types, var_rust)
                variant = "PosInf" if cond.rhs.kind == "+inf" else "NegInf"
                return f"({v} == MathIntOrInf::{variant})"
            a = self._emit_spec_math_int(cond.lhs, var_types, var_rust)
            b = self._emit_spec_math_int(cond.rhs, var_types, var_rust)
            return f"({a} {cond.op} {b})"
        if isinstance(cond, CallExpr):
            return self._emit_spec_call(cond, var_types, var_rust)
        raise ValueError(f"Cannot emit spec condition: {cond!r}")

    def _emit_spec_math_int(
        self,
        e: IRExpr,
        var_types: dict[str, IRBaseType],
        var_rust: dict[str, str],
    ) -> str:
        if isinstance(e, LitMath) and e.int_val is not None:
            return f"{e.int_val}int"
        if isinstance(e, VarExpr):
            ty = var_types[e.name]
            v = var_rust[e.name]
            if ty == IRBaseType.POS_INT:
                return f"({v} as int)"
            if ty == IRBaseType.INT_OR_INF:
                return f"(match {v} {{ MathIntOrInf::Finite(ex) => spec_exact_int_val(ex), _ => 0int }})"
            return v
        if isinstance(e, RealOfNumberExpr):
            n = self._emit_spec_expr(e.expr, IRBaseType.NUMBER, var_types, var_rust)
            return f"spec_integral_number_to_i64({n})"
        if isinstance(e, Pow2Expr):
            if isinstance(e.exponent, VarExpr):
                v = var_rust[e.exponent.name]
                return f"(spec_pow2({v}) as int)"
            if isinstance(e.exponent, MathSubExpr) and isinstance(e.exponent.lhs, VarExpr) and isinstance(e.exponent.rhs, LitMath):
                v = var_rust[e.exponent.lhs.name]
                k = e.exponent.rhs.int_val
                return f"(spec_pow2(({v} - {k}) as nat) as int)"
            raise ValueError(f"Unsupported Pow2 exponent in spec: {e.exponent!r}")
        if isinstance(e, MathSubExpr):
            return f"({self._emit_spec_math_int(e.lhs, var_types, var_rust)} - {self._emit_spec_math_int(e.rhs, var_types, var_rust)})"
        if isinstance(e, ModuloExpr):
            if isinstance(e.lhs, VarExpr) and var_types.get(e.lhs.name) == IRBaseType.INT_OR_INF and isinstance(e.modulus, Pow2Expr) and isinstance(e.modulus.exponent, VarExpr):
                v = var_rust[e.lhs.name]
                bw = var_rust[e.modulus.exponent.name]
                return f"(match {v} {{ MathIntOrInf::Finite(ex) => spec_exact_int_modulo_pow2(ex, {bw}), _ => 0int }})"
            a = self._emit_spec_math_int(e.lhs, var_types, var_rust)
            m = self._emit_spec_math_int(e.modulus, var_types, var_rust)
            return f"({a} % {m})"
        raise ValueError(f"Unsupported spec math int expr: {e!r}")

    def _adapt_spec_arg(
        self,
        expr: IRExpr,
        expected: IRBaseType,
        var_types: dict[str, IRBaseType],
        var_rust: dict[str, str],
    ) -> str:
        if isinstance(expr, VarExpr):
            actual = var_types[expr.name]
            v = var_rust[expr.name]
            if actual == expected:
                return v
            if actual == IRBaseType.JS_VALUE and expected == IRBaseType.NUMBER:
                return f"spec_unwrap_number({v})"
            if actual == IRBaseType.JS_VALUE and expected == IRBaseType.BOOL:
                return f"spec_unwrap_bool({v})"
            if actual == IRBaseType.NUMBER and expected == IRBaseType.JS_VALUE:
                return f"SpecJsValue::Number({v})"
        return self._emit_spec_expr(expr, expected, var_types, var_rust)

    def _emit_spec_call(
        self,
        call: CallExpr,
        var_types: dict[str, IRBaseType],
        var_rust: dict[str, str],
    ) -> str:
        # Built-in leaf operations implemented in `runtime.rs`:
        if call.callee == "BigInt::equal":
            a = self._adapt_spec_arg(call.args[0], IRBaseType.JS_VALUE, var_types, var_rust)
            b = self._adapt_spec_arg(call.args[1], IRBaseType.JS_VALUE, var_types, var_rust)
            return f"spec_val_bigint_equal({a}, {b})"
        if call.callee == "StringToNumber":
            a = self._adapt_spec_arg(call.args[0], IRBaseType.JS_VALUE, var_types, var_rust)
            return f"spec_string_to_number_val({a})"
        if call.callee == "StringToBigInt":
            a = self._adapt_spec_arg(call.args[0], IRBaseType.JS_VALUE, var_types, var_rust)
            return f"spec_string_to_bigint_val({a})"
        if call.callee == "ToPrimitive":
            a = self._adapt_spec_arg(call.args[0], IRBaseType.JS_VALUE, var_types, var_rust)
            if len(call.args) == 2 and isinstance(call.args[1], LitEnumTag) and call.args[1].tag == "number":
                return f"spec_to_primitive_number({a})"
            return f"spec_to_primitive_default({a})"

        target_op = self.op_map[call.callee]
        arg_codes = [
            self._adapt_spec_arg(arg_e, p.ty.base, var_types, var_rust)
            for arg_e, p in zip(call.args, target_op.params)
        ]
        raw_call = f"{target_op.spec_fn_name}({', '.join(arg_codes)})"
        if call.mode == CompletionMode.BANG:
            default_v = self._spec_dummy_val(target_op.ret_type.base)
            return f"(match {raw_call} {{ AbruptOrNormal::Normal(__v) => __v, AbruptOrNormal::ThrowTypeError => {default_v} }})"
        return raw_call

    def _spec_dummy_val(self, ty: IRBaseType) -> str:
        return {
            IRBaseType.NUMBER: "spec_pos_zero()",
            IRBaseType.BOOL: "false",
            IRBaseType.JS_VALUE: "SpecJsValue::Undefined",
            IRBaseType.INT_OR_INF: "MathIntOrInf::Finite(spec_exact_int_zero())",
            IRBaseType.MATH_INT: "0int",
            IRBaseType.UNUSED: "Unused",
        }[ty]

    def _emit_spec_expr(
        self,
        expr: IRExpr,
        expected: IRBaseType,
        var_types: dict[str, IRBaseType],
        var_rust: dict[str, str],
    ) -> str:
        if isinstance(expr, VarExpr):
            actual = var_types[expr.name]
            v = var_rust[expr.name]
            if actual == expected:
                return v
            if actual == IRBaseType.JS_VALUE and expected == IRBaseType.BOOL:
                return f"spec_unwrap_bool({v})"
            if actual == IRBaseType.JS_VALUE and expected == IRBaseType.NUMBER:
                return f"spec_unwrap_number({v})"
            if actual == IRBaseType.NUMBER and expected == IRBaseType.JS_VALUE:
                return f"SpecJsValue::Number({v})"
            return v
        if isinstance(expr, LitBool):
            return "true" if expr.value else "false"
        if isinstance(expr, LitSpecialVal):
            num_code = {
                "NaN": "spec_canon_nan()",
                "+0_F": "spec_pos_zero()",
                "-0_F": "spec_neg_zero()",
                "+inf_F": "spec_pos_inf()",
                "-inf_F": "spec_neg_inf()",
                "1_F": "spec_one_num()",
            }
            if expr.kind in num_code:
                nc = num_code[expr.kind]
                return f"SpecJsValue::Number({nc})" if expected == IRBaseType.JS_VALUE else nc
            if expr.kind == "undefined":
                return "SpecJsValue::Undefined"
            if expr.kind == "null":
                return "SpecJsValue::Null"
        if isinstance(expr, LitEnumTag):
            if expr.tag == "unused":
                return "Unused"
            if expr.tag == "signed":
                return "Signedness::Signed"
            if expr.tag == "unsigned":
                return "Signedness::Unsigned"
        if isinstance(expr, LitBitOpToken):
            return {"&": "BitwiseOp::BitAnd", "^": "BitwiseOp::BitXor", "|": "BitwiseOp::BitOr"}[expr.op]
        if isinstance(expr, LitMath):
            if expected == IRBaseType.INT_OR_INF:
                if expr.kind == "+inf":
                    return "MathIntOrInf::PosInf"
                if expr.kind == "-inf":
                    return "MathIntOrInf::NegInf"
                if expr.int_val == 0:
                    return "MathIntOrInf::Finite(spec_exact_int_zero())"
            if expected == IRBaseType.POS_INT:
                return f"{expr.int_val}nat"
            return f"{expr.int_val}int"
        if isinstance(expr, TruncateRealExpr):
            n = self._adapt_spec_arg(expr.expr, IRBaseType.NUMBER, var_types, var_rust)
            return f"MathIntOrInf::Finite(spec_truncate_finite_number({n}))"
        if isinstance(expr, NumberFromMathExpr):
            inner = self._emit_spec_expr(expr.expr, IRBaseType.MATH_INT, var_types, var_rust)
            nc = f"spec_number_from_int({inner})"
            return f"SpecJsValue::Number({nc})" if expected == IRBaseType.JS_VALUE else nc
        if isinstance(expr, (ModuloExpr, MathSubExpr, Pow2Expr)):
            return self._emit_spec_math_int(expr, var_types, var_rust)
        if isinstance(expr, ToTwosComp32Expr):
            n = self._adapt_spec_arg(expr.expr, IRBaseType.NUMBER, var_types, var_rust)
            return f"spec_i32_to_u32_bits(spec_integral_number_to_i64({n}))"
        if isinstance(expr, FromTwosComp32ToNumberExpr):
            b = self._emit_spec_expr(expr.expr, IRBaseType.BITS32, var_types, var_rust)
            return f"spec_number_from_int(spec_u32_bits_to_i32_int({b}))"
        if isinstance(expr, BitwiseNot32Expr):
            n = self._adapt_spec_arg(expr.expr, IRBaseType.NUMBER, var_types, var_rust)
            return f"spec_number_from_int(spec_u32_bits_to_i32_int(spec_bitnot_u32(spec_i32_to_u32_bits(spec_integral_number_to_i64({n})))))"
        if isinstance(expr, BitShift32Expr):
            ln = self._adapt_spec_arg(expr.lhs, IRBaseType.NUMBER, var_types, var_rust)
            sc = self._emit_spec_math_int(expr.shift, var_types, var_rust)
            if expr.kind == "shl":
                return f"spec_number_from_int(spec_u32_bits_to_i32_int(spec_shl_u32(spec_i32_to_u32_bits(spec_integral_number_to_i64({ln})), {sc} as u32)))"
            if expr.kind == "ashr":
                return f"spec_number_from_int(spec_u32_bits_to_i32_int(spec_ashr_u32(spec_i32_to_u32_bits(spec_integral_number_to_i64({ln})), {sc} as u32)))"
            return f"spec_number_from_int(spec_shr_u32(spec_integral_number_to_i64({ln}) as u32, {sc} as u32) as int)"
        if isinstance(expr, BitwiseBinary32Expr):
            a = self._emit_spec_expr(expr.lhs, IRBaseType.BITS32, var_types, var_rust)
            b = self._emit_spec_expr(expr.rhs, IRBaseType.BITS32, var_types, var_rust)
            fn_m = {"AND": "spec_bitand_u32", "XOR": "spec_bitxor_u32", "OR": "spec_bitor_u32"}[expr.op]
            return f"{fn_m}({a}, {b})"
        if isinstance(expr, CallExpr):
            c = self._emit_spec_call(expr, var_types, var_rust)
            ret_b = self._call_base_type(expr)
            if ret_b == IRBaseType.NUMBER and expected == IRBaseType.JS_VALUE:
                return f"SpecJsValue::Number({c})"
            return c
        raise ValueError(f"Unsupported spec expr: {expr!r}")

    def _call_base_type(self, call: CallExpr) -> IRBaseType:
        if call.callee in self.op_map:
            return self.op_map[call.callee].ret_type.base
        if call.callee == "StringToNumber":
            return IRBaseType.NUMBER
        if call.callee == "BigInt::equal":
            return IRBaseType.BOOL
        return IRBaseType.JS_VALUE

    # --- Exec Function Emission (`pub fn` with Machine-Checked `ensures exec == spec`) ---

    def emit_exec_fn(
        self,
        op: IROperation,
        var_types: dict[str, IRBaseType],
        var_rust: dict[str, str],
        param_names: set[str],
    ) -> list[str]:
        params_sig = ", ".join(f"{p.rust_name}: {self.exec_param_type_str(p.ty)}" for p in op.params)
        ret_sig = self.exec_ret_type_str(op.ret_type)

        reqs: list[str] = []
        for p in op.params:
            if p.ty.base == IRBaseType.POS_INT:
                reqs.append(f"1 <= {p.rust_name} && {p.rust_name} <= 32")
            if p.ty.not_number_constraint:
                reqs.append(f"!spec_is_number({p.rust_name}@)")
        if op.spec_name == "SameValueNonNumber":
            reqs.append(f"spec_same_type({op.params[0].rust_name}@, {op.params[1].rust_name}@)")

        spec_args = []
        for p in op.params:
            if p.ty.base == IRBaseType.JS_VALUE:
                spec_args.append(f"{p.rust_name}@")
            elif p.ty.base == IRBaseType.POS_INT:
                spec_args.append(f"{p.rust_name} as nat")
            else:
                spec_args.append(p.rust_name)
        spec_call = f"{op.spec_fn_name}({', '.join(spec_args)})"

        ens: list[str] = []
        if op.ret_type.base == IRBaseType.MATH_INT and not op.ret_type.fallible:
            ens.append(f"res as int == {spec_call}")
        else:
            ens.append(f"res == {spec_call}")

        # Rich structural postconditions enabling downstream `! Op(...)` non-abruptness & range proofs:
        if op.spec_name == "ToNumber":
            a = op.params[0].rust_name
            ens.append(
                f"(spec_is_number({a}@) || spec_is_undefined({a}@) || spec_is_null({a}@) || spec_is_boolean({a}@) || spec_is_string({a}@)) ==> (res is Normal)"
            )
        elif op.spec_name == "ToIntegerOrInfinity":
            a = op.params[0].rust_name
            ens.append(
                f"(spec_is_number({a}@) || spec_is_undefined({a}@) || spec_is_null({a}@) || spec_is_boolean({a}@) || spec_is_string({a}@)) ==> (res is Normal)"
            )
        elif op.spec_name == "ToFixedSizeInteger":
            ens.append("signed == Signedness::Unsigned ==> (0 <= res && (res as int) < (spec_pow2(bit_width as nat) as int))")
            ens.append("signed == Signedness::Signed ==> (-(spec_pow2((bit_width - 1) as nat) as int) <= (res as int) && (res as int) < (spec_pow2((bit_width - 1) as nat) as int))")
        elif op.spec_name == "ToInt32":
            a = op.params[0].rust_name
            ens.append(f"spec_is_number({a}@) ==> (res is Normal)")
            ens.append("match res { AbruptOrNormal::Normal(n) => spec_is_finite_num(n) && -2147483648int <= spec_integral_number_to_i64(n) && spec_integral_number_to_i64(n) <= 2147483647int, AbruptOrNormal::ThrowTypeError => true }")
        elif op.spec_name == "ToUint32":
            a = op.params[0].rust_name
            ens.append(f"spec_is_number({a}@) ==> (res is Normal)")
            ens.append("match res { AbruptOrNormal::Normal(n) => spec_is_finite_num(n) && 0int <= spec_integral_number_to_i64(n) && spec_integral_number_to_i64(n) < 4294967296int, AbruptOrNormal::ThrowTypeError => true }")
        elif op.spec_name == "ToUint16":
            a = op.params[0].rust_name
            ens.append(f"spec_is_number({a}@) ==> (res is Normal)")
            ens.append("match res { AbruptOrNormal::Normal(n) => spec_is_finite_num(n) && 0int <= spec_integral_number_to_i64(n) && spec_integral_number_to_i64(n) < 65536int, AbruptOrNormal::ThrowTypeError => true }")
        elif op.spec_name == "IsLooselyEqual":
            px, py = op.params[0].rust_name, op.params[1].rust_name
            ens.append(f"(!spec_is_object({px}@) && !spec_is_object({py}@)) ==> (res is Normal)")

        lines: list[str] = []
        if op.spec_name in ("IsLooselyEqual", "ToFixedSizeInteger"):
            lines.append("#[verifier::spinoff_prover]")
        lines.append(f"pub fn {op.rust_fn_name}({params_sig}) -> (res: {ret_sig})")
        if reqs:
            lines.append("    requires")
            for r in reqs:
                lines.append(f"        {r},")
        lines.append("    ensures")
        for e in ens:
            lines.append(f"        {e},")
        if op.is_recursive:
            lines.append(f"    decreases {self._recursion_rank_expr(op, spec_mode=False)},")
        lines.append("{")
        if op.spec_name in ("ToInt32", "ToUint32", "ToUint16", "ToFixedSizeInteger", "NumberBitwiseOp",
                            "Number::bitwiseNOT", "Number::leftShift", "Number::signedRightShift",
                            "Number::unsignedRightShift"):
            lines.append("    proof { lemma_pow2_small_values(); }")
        for p in op.params:
            if p.ty.base == IRBaseType.POS_INT:
                lines.append(f"    proof {{ lemma_pow2_bitwidth_bounds({p.rust_name}); }}")
        lines.extend(self._emit_exec_stmts(op, op.body, var_types, var_rust, param_names, indent=4, is_tail=True))
        lines.append("}")
        return lines

    def _spec_view_of_exec_var(self, var: str, var_types: dict[str, IRBaseType], var_rust: dict[str, str]) -> str:
        v = var_rust[var]
        ty = var_types[var]
        if ty == IRBaseType.JS_VALUE:
            return f"{v}@"
        if ty == IRBaseType.POS_INT:
            return f"({v} as nat)"
        if ty == IRBaseType.MATH_INT:
            return f"({v} as int)"
        return v

    def _emit_exec_stmts(
        self,
        op: IROperation,
        stmts: list[IRStmt],
        var_types: dict[str, IRBaseType],
        var_rust: dict[str, str],
        ref_vars: set[str],  # JS_VALUE vars currently held as `&JsValue` (params) vs owned `JsValue` (locals)
        indent: int,
        is_tail: bool,
    ) -> list[str]:
        pad = " " * indent
        lines: list[str] = []
        for idx, st in enumerate(stmts):
            last_in_tail = is_tail and (idx == len(stmts) - 1)
            if st.comment:
                lines.append(f"{pad}// {st.comment}")

            if isinstance(st, IRNote):
                continue

            if isinstance(st, IRAssert):
                # Map exec variable views for spec assertion
                view_rust = {k: self._spec_view_of_exec_var(k, var_types, var_rust) for k in var_rust}
                cond_spec = self._emit_spec_cond(st.cond, var_types, view_rust)
                lines.append(f"{pad}proof {{ assert({cond_spec}); }}")
                continue

            if isinstance(st, IRThrow):
                if last_in_tail:
                    lines.append(f"{pad}AbruptOrNormal::ThrowTypeError")
                else:
                    lines.append(f"{pad}return AbruptOrNormal::ThrowTypeError;")
                continue

            if isinstance(st, IRReturn):
                lines.extend(self._emit_exec_return(op, st.value, var_types, var_rust, ref_vars, indent, use_return=not last_in_tail))
                continue

            if isinstance(st, IRLet):
                v = var_rust[st.var]
                mut_kw = "mut " if st.mutable else ""
                if isinstance(st.rhs, CallExpr) and st.rhs.mode == CompletionMode.QUESTION:
                    pre, call_c = self._emit_exec_call(st.rhs, var_types, var_rust, ref_vars, indent)
                    lines.extend(pre)
                    lines.append(f"{pad}let {mut_kw}{v} = match {call_c} {{")
                    lines.append(f"{pad}    AbruptOrNormal::ThrowTypeError => {{ return AbruptOrNormal::ThrowTypeError; }}")
                    lines.append(f"{pad}    AbruptOrNormal::Normal(__val) => __val,")
                    lines.append(f"{pad}}};")
                elif isinstance(st.rhs, CallExpr) and st.rhs.mode == CompletionMode.BANG:
                    pre, call_c = self._emit_exec_call(st.rhs, var_types, var_rust, ref_vars, indent)
                    lines.extend(pre)
                    dummy_exec = self._exec_dummy_val(var_types[st.var])
                    lines.append(f"{pad}let {mut_kw}{v} = match {call_c} {{")
                    lines.append(f"{pad}    AbruptOrNormal::Normal(__val) => __val,")
                    lines.append(f"{pad}    AbruptOrNormal::ThrowTypeError => {{ proof {{ assert(false); }} {dummy_exec} }}")
                    lines.append(f"{pad}}};")
                else:
                    pre, rhs_c = self._emit_exec_expr(st.rhs, var_types[st.var], var_types, var_rust, ref_vars, indent)
                    lines.extend(pre)
                    lines.append(f"{pad}let {mut_kw}{v} = {self._strip_outer_parens(rhs_c)};")
                continue

            if isinstance(st, IRSet):
                v = var_rust[st.var]
                pre, rhs_c = self._emit_exec_expr(st.rhs, var_types[st.var], var_types, var_rust, ref_vars, indent)
                lines.extend(pre)
                lines.append(f"{pad}{v} = {self._strip_outer_parens(rhs_c)};")
                continue

            if isinstance(st, IRIf):
                if st.phi_var is not None:
                    pv = var_rust[st.phi_var]
                    pty = var_types[st.phi_var]
                    cond_c = self._strip_outer_parens(self._emit_exec_cond(st.cond, var_types, var_rust, ref_vars))
                    then_let = st.then_body[-1]
                    assert isinstance(then_let, IRLet)
                    lines.append(f"{pad}let {pv} = if {cond_c} {{")
                    lines.extend(self._emit_exec_stmts(op, st.then_body[:-1], var_types, var_rust, ref_vars, indent + 4, False))
                    if then_let.comment:
                        lines.append(f"{pad}    // {then_let.comment}")
                    pre, rc = self._emit_exec_expr(then_let.rhs, pty, var_types, var_rust, ref_vars, indent + 4)
                    lines.extend(pre)
                    lines.append(f"{pad}    {rc}")
                    for eb in st.elif_branches:
                        ec = self._strip_outer_parens(self._emit_exec_cond(eb.cond, var_types, var_rust, ref_vars))
                        elet = eb.body[-1]
                        assert isinstance(elet, IRLet)
                        lines.append(f"{pad}}} else if {ec} {{")
                        if eb.comment:
                            lines.append(f"{pad}    // {eb.comment}")
                        lines.extend(self._emit_exec_stmts(op, eb.body[:-1], var_types, var_rust, ref_vars, indent + 4, False))
                        if elet.comment:
                            lines.append(f"{pad}    // {elet.comment}")
                        pre, rc = self._emit_exec_expr(elet.rhs, pty, var_types, var_rust, ref_vars, indent + 4)
                        lines.extend(pre)
                        lines.append(f"{pad}    {rc}")
                    lines.append(f"{pad}}} else {{")
                    if st.else_comment:
                        lines.append(f"{pad}    // {st.else_comment}")
                    lines.extend(self._emit_exec_stmts(op, st.else_body[:-1], var_types, var_rust, ref_vars, indent + 4, False))
                    else_let = st.else_body[-1]
                    assert isinstance(else_let, IRLet)
                    if else_let.comment:
                        lines.append(f"{pad}    // {else_let.comment}")
                    pre, rc = self._emit_exec_expr(else_let.rhs, pty, var_types, var_rust, ref_vars, indent + 4)
                    lines.extend(pre)
                    lines.append(f"{pad}    {rc}")
                    lines.append(f"{pad}}};")
                    continue

                cond_c = self._strip_outer_parens(self._emit_exec_cond(st.cond, var_types, var_rust, ref_vars))
                lines.append(f"{pad}if {cond_c} {{")
                lines.extend(self._emit_exec_stmts(op, st.then_body, var_types, var_rust, ref_vars, indent + 4, False))
                for eb in st.elif_branches:
                    ec = self._strip_outer_parens(self._emit_exec_cond(eb.cond, var_types, var_rust, ref_vars))
                    lines.append(f"{pad}}} else if {ec} {{")
                    if eb.comment:
                        lines.append(f"{pad}    // {eb.comment}")
                    lines.extend(self._emit_exec_stmts(op, eb.body, var_types, var_rust, ref_vars, indent + 4, False))
                if st.else_body:
                    lines.append(f"{pad}}} else {{")
                    if st.else_comment:
                        lines.append(f"{pad}    // {st.else_comment}")
                    lines.extend(self._emit_exec_stmts(op, st.else_body, var_types, var_rust, ref_vars, indent + 4, False))
                lines.append(f"{pad}}}")
                continue

        return lines

    def _emit_exec_return(
        self,
        op: IROperation,
        val: IRExpr,
        var_types: dict[str, IRBaseType],
        var_rust: dict[str, str],
        ref_vars: set[str],
        indent: int,
        use_return: bool,
    ) -> list[str]:
        pad = " " * indent
        ret_kw = "return " if use_return else ""
        ret_semi = ";" if use_return else ""

        if isinstance(val, CallExpr) and val.mode == CompletionMode.QUESTION:
            pre, cc = self._emit_exec_call(val, var_types, var_rust, ref_vars, indent)
            return pre + [f"{pad}{ret_kw}{cc}{ret_semi}"]

        if isinstance(val, CallExpr) and val.mode == CompletionMode.BANG:
            nested_q = self._find_nested_question_arg(val)
            if nested_q is not None:
                arg_idx, sub_call = nested_q
                pre_q, sub_cc = self._emit_exec_call(sub_call, var_types, var_rust, ref_vars, indent)
                tmp = f"__coerced_{arg_idx}"
                lines = list(pre_q)
                lines.append(f"{pad}let {tmp} = match {sub_cc} {{")
                lines.append(f"{pad}    AbruptOrNormal::ThrowTypeError => {{ return AbruptOrNormal::ThrowTypeError; }}")
                lines.append(f"{pad}    AbruptOrNormal::Normal(__p) => __p,")
                lines.append(f"{pad}}};")
                new_args = list(val.args)
                new_args[arg_idx] = VarExpr(tmp)
                vt_copy = dict(var_types)
                vr_copy = dict(var_rust)
                vt_copy[tmp] = IRBaseType.JS_VALUE
                vr_copy[tmp] = tmp
                rewritten = CallExpr(val.callee, new_args, val.mode)
                pre_b, bang_cc = self._emit_exec_call(rewritten, vt_copy, vr_copy, ref_vars, indent)
                lines.extend(pre_b)
                dummy = self._exec_dummy_val(op.ret_type.base)
                unwrapped = f"match {bang_cc} {{ AbruptOrNormal::Normal(__v) => __v, AbruptOrNormal::ThrowTypeError => {{ proof {{ assert(false); }} {dummy} }} }}"
                final_e = f"AbruptOrNormal::Normal({unwrapped})" if op.ret_type.fallible else unwrapped
                lines.append(f"{pad}{ret_kw}{final_e}{ret_semi}")
                return lines

            pre_b, bang_cc = self._emit_exec_call(val, var_types, var_rust, ref_vars, indent)
            dummy = self._exec_dummy_val(op.ret_type.base)
            unwrapped = f"match {bang_cc} {{ AbruptOrNormal::Normal(__v) => __v, AbruptOrNormal::ThrowTypeError => {{ proof {{ assert(false); }} {dummy} }} }}"
            final_e = f"AbruptOrNormal::Normal({unwrapped})" if op.ret_type.fallible else unwrapped
            return pre_b + [f"{pad}{ret_kw}{final_e}{ret_semi}"]

        pre, code = self._emit_exec_expr(val, op.ret_type.base, var_types, var_rust, ref_vars, indent)
        if op.ret_type.base == IRBaseType.NUMBER and not op.ret_type.fallible and op.spec_name in (
            "ToInt32", "ToUint32", "ToUint16",
        ):
            pass
        if op.spec_name in ("ToInt32", "ToUint32", "ToUint16") and isinstance(val, NumberFromMathExpr):
            # Emit `lemma_number_from_int_roundtrip` right before returning `𝔽(...)` so range postconditions prove cleanly!
            pre_m, m_code = self._emit_exec_expr(val.expr, IRBaseType.MATH_INT, var_types, var_rust, ref_vars, indent)
            lines = list(pre_m)
            lines.append(f"{pad}let __fixed_i64: i64 = {m_code};")
            lines.append(f"{pad}proof {{ lemma_number_from_int_roundtrip(__fixed_i64 as int); }}")
            lines.append(f"{pad}let __num_res = number_from_i64(__fixed_i64);")
            lines.append(f"{pad}{ret_kw}AbruptOrNormal::Normal(__num_res){ret_semi}")
            return lines

        final_e = f"AbruptOrNormal::Normal({code})" if op.ret_type.fallible else code
        return pre + [f"{pad}{ret_kw}{final_e}{ret_semi}"]

    def _exec_ref_arg(self, var_name: str, var_rust: dict[str, str], ref_vars: set[str]) -> str:
        v = var_rust[var_name]
        return v if var_name in ref_vars else f"&{v}"

    def _emit_exec_cond(
        self,
        cond: IRExpr,
        var_types: dict[str, IRBaseType],
        var_rust: dict[str, str],
        ref_vars: set[str],
    ) -> str:
        if isinstance(cond, LogicExpr):
            sep = " && " if cond.op == "and" else " || "
            return "(" + sep.join(self._emit_exec_cond(it, var_types, var_rust, ref_vars) for it in cond.items) + ")"
        if isinstance(cond, OneOfPredExpr):
            return "(" + " || ".join(self._emit_exec_cond(ch, var_types, var_rust, ref_vars) for ch in cond.checks) + ")"
        if isinstance(cond, TypePredExpr):
            assert isinstance(cond.target, VarExpr)
            rv = self._exec_ref_arg(cond.target.name, var_rust, ref_vars)
            fn_map = {
                "Boolean": "val_is_boolean",
                "Number": "val_is_number",
                "BigInt": "val_is_bigint",
                "String": "val_is_string",
                "Symbol": "val_is_symbol",
                "Object": "val_is_object",
                "FiniteNumber": "val_is_finite_number",
            }
            c = f"{fn_map[cond.type_name]}({rv})"
            return f"!{c}" if cond.negated else c
        if isinstance(cond, ValuePredExpr):
            assert isinstance(cond.target, VarExpr)
            t_ty = var_types[cond.target.name]
            if t_ty == IRBaseType.NUMBER:
                v = var_rust[cond.target.name]
                nmap = {
                    "NaN": f"num_is_nan({v})",
                    "+0_F": f"num_is_pos_zero({v})",
                    "-0_F": f"num_is_neg_zero({v})",
                    "+inf_F": f"num_is_pos_inf({v})",
                    "-inf_F": f"num_is_neg_inf({v})",
                }
                c = nmap[cond.kind]
            else:
                rv = self._exec_ref_arg(cond.target.name, var_rust, ref_vars)
                vmap = {
                    "undefined": f"val_is_undefined({rv})",
                    "null": f"val_is_null({rv})",
                    "NaN": f"val_is_nan({rv})",
                    "+0_F": f"val_is_pos_zero({rv})",
                    "-0_F": f"val_is_neg_zero({rv})",
                    "+inf_F": f"val_is_pos_inf({rv})",
                    "-inf_F": f"val_is_neg_inf({rv})",
                    "true": f"val_is_bool_true({rv})",
                    "false": f"val_is_bool_false({rv})",
                    "0_Z": f"val_is_bigint_zero({rv})",
                    "empty_str": f"val_is_empty_string({rv})",
                }
                c = vmap[cond.kind]
            return f"!{c}" if cond.negated else c
        if isinstance(cond, IdentityEqExpr):
            if cond.domain == "Number":
                assert isinstance(cond.lhs, VarExpr) and isinstance(cond.rhs, VarExpr)
                return f"num_is_same({var_rust[cond.lhs.name]}, {var_rust[cond.rhs.name]})"
            if cond.domain == "BitwiseOp":
                assert isinstance(cond.lhs, VarExpr) and isinstance(cond.rhs, LitBitOpToken)
                rhs_v = {"&": "BitwiseOp::BitAnd", "^": "BitwiseOp::BitXor", "|": "BitwiseOp::BitOr"}[cond.rhs.op]
                return f"matches!({var_rust[cond.lhs.name]}, {rhs_v})"
            if cond.domain == "Signedness":
                assert isinstance(cond.lhs, VarExpr) and isinstance(cond.rhs, LitEnumTag)
                rhs_v = "Signedness::Signed" if cond.rhs.tag == "signed" else "Signedness::Unsigned"
                return f"matches!({var_rust[cond.lhs.name]}, {rhs_v})"
            if cond.domain == "Boolean":
                assert isinstance(cond.lhs, CallExpr) and isinstance(cond.rhs, LitBool)
                _, cc = self._emit_exec_call(cond.lhs, var_types, var_rust, ref_vars, 4)
                return f"!{cc}" if not cond.rhs.value else cc
            assert isinstance(cond.lhs, VarExpr) and isinstance(cond.rhs, VarExpr)
            return f"val_non_number_is({self._exec_ref_arg(cond.lhs.name, var_rust, ref_vars)}, {self._exec_ref_arg(cond.rhs.name, var_rust, ref_vars)})"
        if isinstance(cond, HostSupportsHtmlDdaExpr):
            return "host_supports_htmldda()"
        if isinstance(cond, HasInternalSlotExpr):
            assert isinstance(cond.target, VarExpr)
            return f"val_has_htmldda_slot({self._exec_ref_arg(cond.target.name, var_rust, ref_vars)})"
        if isinstance(cond, SameStringCodeUnitsExpr):
            assert isinstance(cond.lhs, VarExpr) and isinstance(cond.rhs, VarExpr)
            return f"val_same_string_code_units({self._exec_ref_arg(cond.lhs.name, var_rust, ref_vars)}, {self._exec_ref_arg(cond.rhs.name, var_rust, ref_vars)})"
        if isinstance(cond, RealEqExpr):
            assert isinstance(cond.lhs, VarExpr) and isinstance(cond.rhs, VarExpr)
            return f"val_real_equal({self._exec_ref_arg(cond.lhs.name, var_rust, ref_vars)}, {self._exec_ref_arg(cond.rhs.name, var_rust, ref_vars)})"
        if isinstance(cond, MathCmpExpr):
            if isinstance(cond.rhs, LitMath) and cond.rhs.kind in ("+inf", "-inf"):
                assert isinstance(cond.lhs, VarExpr)
                variant = "PosInf" if cond.rhs.kind == "+inf" else "NegInf"
                return f"matches!({var_rust[cond.lhs.name]}, MathIntOrInf::{variant})"
            a = self._emit_exec_math_i64(cond.lhs, var_types, var_rust)
            b = self._emit_exec_math_i64(cond.rhs, var_types, var_rust)
            return f"({a} {cond.op} {b})"
        if isinstance(cond, CallExpr):
            _, cc = self._emit_exec_call(cond, var_types, var_rust, ref_vars, 4)
            return cc
        raise ValueError(f"Cannot emit exec condition: {cond!r}")

    def _emit_exec_math_i64(
        self,
        e: IRExpr,
        var_types: dict[str, IRBaseType],
        var_rust: dict[str, str],
    ) -> str:
        if isinstance(e, LitMath) and e.int_val is not None:
            return f"{e.int_val}i64"
        if isinstance(e, VarExpr):
            v = var_rust[e.name]
            if var_types[e.name] == IRBaseType.POS_INT:
                return f"({v} as i64)"
            return v
        if isinstance(e, RealOfNumberExpr):
            assert isinstance(e.expr, VarExpr)
            return f"integral_number_to_i64({var_rust[e.expr.name]})"
        if isinstance(e, Pow2Expr):
            if isinstance(e.exponent, VarExpr):
                return f"(pow2_u64({var_rust[e.exponent.name]}) as i64)"
            if isinstance(e.exponent, MathSubExpr) and isinstance(e.exponent.lhs, VarExpr) and isinstance(e.exponent.rhs, LitMath):
                return f"(pow2_u64({var_rust[e.exponent.lhs.name]} - {e.exponent.rhs.int_val}u32) as i64)"
        if isinstance(e, MathSubExpr):
            return f"({self._emit_exec_math_i64(e.lhs, var_types, var_rust)} - {self._emit_exec_math_i64(e.rhs, var_types, var_rust)})"
        if isinstance(e, ModuloExpr):
            if isinstance(e.lhs, VarExpr) and var_types.get(e.lhs.name) == IRBaseType.INT_OR_INF and isinstance(e.modulus, Pow2Expr) and isinstance(e.modulus.exponent, VarExpr):
                v = var_rust[e.lhs.name]
                bw = var_rust[e.modulus.exponent.name]
                return f"(match {v} {{ MathIntOrInf::Finite(ex) => exact_int_modulo_pow2(ex, {bw}), _ => 0i64 }})"
            a = self._emit_exec_math_i64(e.lhs, var_types, var_rust)
            m = self._emit_exec_math_i64(e.modulus, var_types, var_rust)
            return f"({a} % {m})"
        raise ValueError(f"Unsupported exec math expr: {e!r}")

    def _exec_dummy_val(self, ty: IRBaseType) -> str:
        return {
            IRBaseType.NUMBER: "js_pos_zero()",
            IRBaseType.BOOL: "false",
            IRBaseType.JS_VALUE: "JsValue::Undefined",
            IRBaseType.INT_OR_INF: "MathIntOrInf::Finite(exact_int_zero())",
            IRBaseType.MATH_INT: "0i64",
            IRBaseType.UNUSED: "Unused",
        }[ty]

    def _emit_exec_call(
        self,
        call: CallExpr,
        var_types: dict[str, IRBaseType],
        var_rust: dict[str, str],
        ref_vars: set[str],
        indent: int,
    ) -> tuple[list[str], str]:
        pad = " " * indent
        pre_lines: list[str] = []

        if call.callee == "BigInt::equal":
            assert isinstance(call.args[0], VarExpr) and isinstance(call.args[1], VarExpr)
            return [], f"val_bigint_equal({self._exec_ref_arg(call.args[0].name, var_rust, ref_vars)}, {self._exec_ref_arg(call.args[1].name, var_rust, ref_vars)})"
        if call.callee == "StringToNumber":
            assert isinstance(call.args[0], VarExpr)
            return [], f"val_string_to_number({self._exec_ref_arg(call.args[0].name, var_rust, ref_vars)})"
        if call.callee == "StringToBigInt":
            assert isinstance(call.args[0], VarExpr)
            return [], f"val_string_to_bigint({self._exec_ref_arg(call.args[0].name, var_rust, ref_vars)})"
        if call.callee == "ToPrimitive":
            assert isinstance(call.args[0], VarExpr)
            rv = self._exec_ref_arg(call.args[0].name, var_rust, ref_vars)
            if len(call.args) == 2 and isinstance(call.args[1], LitEnumTag) and call.args[1].tag == "number":
                return [], f"to_primitive_number({rv})"
            return [], f"to_primitive_default({rv})"

        target_op = self.op_map[call.callee]
        arg_strs: list[str] = []
        for idx, (arg_e, p) in enumerate(zip(call.args, target_op.params)):
            if p.ty.base == IRBaseType.JS_VALUE:
                if isinstance(arg_e, VarExpr):
                    actual = var_types[arg_e.name]
                    if actual == IRBaseType.JS_VALUE:
                        arg_strs.append(self._exec_ref_arg(arg_e.name, var_rust, ref_vars))
                    elif actual == IRBaseType.NUMBER:
                        tmp = f"__arg_val_{idx}"
                        pre_lines.append(f"{pad}let {tmp} = JsValue::Number({var_rust[arg_e.name]});")
                        arg_strs.append(f"&{tmp}")
                    else:
                        raise ValueError(f"Cannot adapt {actual} to &JsValue")
                elif isinstance(arg_e, CallExpr) and arg_e.mode == CompletionMode.BANG:
                    sub_pre, sub_cc = self._emit_exec_call(arg_e, var_types, var_rust, ref_vars, indent)
                    pre_lines.extend(sub_pre)
                    sub_ret = self._call_base_type(arg_e)
                    dummy = self._exec_dummy_val(sub_ret)
                    tmp_raw = f"__bang_arg_{idx}"
                    pre_lines.append(f"{pad}let {tmp_raw} = match {sub_cc} {{ AbruptOrNormal::Normal(__v) => __v, AbruptOrNormal::ThrowTypeError => {{ proof {{ assert(false); }} {dummy} }} }};")
                    if sub_ret == IRBaseType.NUMBER:
                        tmp_v = f"__bang_jsval_{idx}"
                        pre_lines.append(f"{pad}let {tmp_v} = JsValue::Number({tmp_raw});")
                        arg_strs.append(f"&{tmp_v}")
                    else:
                        arg_strs.append(f"&{tmp_raw}")
                else:
                    raise ValueError(f"Unsupported exec &JsValue call arg: {arg_e!r}")
            elif p.ty.base == IRBaseType.NUMBER:
                if isinstance(arg_e, VarExpr) and var_types[arg_e.name] == IRBaseType.JS_VALUE:
                    arg_strs.append(f"val_unwrap_number({self._exec_ref_arg(arg_e.name, var_rust, ref_vars)})")
                else:
                    sub_p, sc = self._emit_exec_expr(arg_e, IRBaseType.NUMBER, var_types, var_rust, ref_vars, indent)
                    pre_lines.extend(sub_p)
                    arg_strs.append(sc)
            elif p.ty.base == IRBaseType.POS_INT:
                if isinstance(arg_e, LitMath) and arg_e.int_val is not None:
                    arg_strs.append(f"{arg_e.int_val}u32")
                elif isinstance(arg_e, VarExpr):
                    arg_strs.append(var_rust[arg_e.name])
                else:
                    raise ValueError(f"Unsupported POS_INT arg {arg_e!r}")
            else:
                sub_p, sc = self._emit_exec_expr(arg_e, p.ty.base, var_types, var_rust, ref_vars, indent)
                pre_lines.extend(sub_p)
                arg_strs.append(sc)

        return pre_lines, f"{target_op.rust_fn_name}({', '.join(arg_strs)})"

    def _emit_exec_expr(
        self,
        expr: IRExpr,
        expected: IRBaseType,
        var_types: dict[str, IRBaseType],
        var_rust: dict[str, str],
        ref_vars: set[str],
        indent: int,
    ) -> tuple[list[str], str]:
        if isinstance(expr, VarExpr):
            actual = var_types[expr.name]
            v = var_rust[expr.name]
            if actual == expected:
                if actual == IRBaseType.JS_VALUE and expr.name in ref_vars:
                    return [], f"{v}.clone()"
                return [], v
            if actual == IRBaseType.JS_VALUE and expected == IRBaseType.BOOL:
                return [], f"val_unwrap_bool({self._exec_ref_arg(expr.name, var_rust, ref_vars)})"
            if actual == IRBaseType.JS_VALUE and expected == IRBaseType.NUMBER:
                return [], f"val_unwrap_number({self._exec_ref_arg(expr.name, var_rust, ref_vars)})"
            if actual == IRBaseType.NUMBER and expected == IRBaseType.JS_VALUE:
                return [], f"JsValue::Number({v})"
            return [], v
        if isinstance(expr, LitBool):
            return [], ("true" if expr.value else "false")
        if isinstance(expr, LitSpecialVal):
            num_code = {
                "NaN": "js_canon_nan()",
                "+0_F": "js_pos_zero()",
                "-0_F": "js_neg_zero()",
                "+inf_F": "js_pos_inf()",
                "-inf_F": "js_neg_inf()",
                "1_F": "js_one_num()",
            }
            if expr.kind in num_code:
                nc = num_code[expr.kind]
                return [], (f"JsValue::Number({nc})" if expected == IRBaseType.JS_VALUE else nc)
            if expr.kind == "undefined":
                return [], "JsValue::Undefined"
            if expr.kind == "null":
                return [], "JsValue::Null"
        if isinstance(expr, LitEnumTag):
            if expr.tag == "unused":
                return [], "Unused"
            if expr.tag == "signed":
                return [], "Signedness::Signed"
            if expr.tag == "unsigned":
                return [], "Signedness::Unsigned"
        if isinstance(expr, LitBitOpToken):
            return [], {"&": "BitwiseOp::BitAnd", "^": "BitwiseOp::BitXor", "|": "BitwiseOp::BitOr"}[expr.op]
        if isinstance(expr, LitMath):
            if expected == IRBaseType.INT_OR_INF:
                if expr.kind == "+inf":
                    return [], "MathIntOrInf::PosInf"
                if expr.kind == "-inf":
                    return [], "MathIntOrInf::NegInf"
                if expr.int_val == 0:
                    return [], "MathIntOrInf::Finite(exact_int_zero())"
            if expected == IRBaseType.POS_INT:
                return [], f"{expr.int_val}u32"
            return [], f"{expr.int_val}i64"
        if isinstance(expr, TruncateRealExpr):
            assert isinstance(expr.expr, VarExpr)
            v = var_rust[expr.expr.name]
            return [], f"MathIntOrInf::Finite(truncate_finite_number({v}))"
        if isinstance(expr, NumberFromMathExpr):
            pre, inner = self._emit_exec_expr(expr.expr, IRBaseType.MATH_INT, var_types, var_rust, ref_vars, indent)
            nc = f"number_from_i64({inner})"
            return pre, (f"JsValue::Number({nc})" if expected == IRBaseType.JS_VALUE else nc)
        if isinstance(expr, (ModuloExpr, MathSubExpr, Pow2Expr)):
            return [], self._emit_exec_math_i64(expr, var_types, var_rust)
        if isinstance(expr, ToTwosComp32Expr):
            assert isinstance(expr.expr, VarExpr)
            v = var_rust[expr.expr.name]
            return [], f"i64_to_u32_bits(integral_number_to_i64({v}))"
        if isinstance(expr, FromTwosComp32ToNumberExpr):
            assert isinstance(expr.expr, VarExpr)
            v = var_rust[expr.expr.name]
            return [], f"number_from_i64(u32_bits_to_i64({v}))"
        if isinstance(expr, BitwiseNot32Expr):
            assert isinstance(expr.expr, VarExpr)
            v = var_rust[expr.expr.name]
            return [], f"number_from_i64(bitnot_i32_val(integral_number_to_i64({v})))"
        if isinstance(expr, BitShift32Expr):
            assert isinstance(expr.lhs, VarExpr) and isinstance(expr.shift, VarExpr)
            lv = var_rust[expr.lhs.name]
            sv = var_rust[expr.shift.name]
            fn_m = {"shl": "shl_i32_val", "ashr": "ashr_i32_val", "lshr": "lshr_u32_val"}[expr.kind]
            return [], f"number_from_i64({fn_m}(integral_number_to_i64({lv}), {sv}))"
        if isinstance(expr, BitwiseBinary32Expr):
            assert isinstance(expr.lhs, VarExpr) and isinstance(expr.rhs, VarExpr)
            a = var_rust[expr.lhs.name]
            b = var_rust[expr.rhs.name]
            fn_m = {"AND": "bitand_u32_exec", "XOR": "bitxor_u32_exec", "OR": "bitor_u32_exec"}[expr.op]
            return [], f"{fn_m}({a}, {b})"
        if isinstance(expr, CallExpr):
            return self._emit_exec_call(expr, var_types, var_rust, ref_vars, indent)
        raise ValueError(f"Unsupported exec expr: {expr!r}")


# ===============================================================================================
# 6. End-to-End Compilation Driver
# ===============================================================================================

def compile_spec_html_to_ir(html_text: str) -> list[IROperation]:
    parser = EcmarkupClauseParser()
    parser.feed(html_text)

    ops: list[IROperation] = []
    for rc in parser.clauses:
        spec_name, params, ret_ty, raw_ret = parse_h1_signature(rc.h1_raw)
        steps, step_count = parse_alg_steps(rc.alg_raw)
        sc = StepCompiler(spec_name, params, ret_ty)
        body = sc.compile_step_list(steps)
        cfg = build_ires_cfg(body)
        rust_fn = camel_to_snake(spec_name)
        ops.append(
            IROperation(
                clause_number=rc.clause_number,
                clause_id=rc.clause_id,
                spec_name=spec_name,
                rust_fn_name=rust_fn,
                spec_fn_name=f"spec_{rust_fn}",
                params=params,
                ret_type=ret_ty,
                raw_ret_type=raw_ret,
                step_count=step_count,
                body=body,
                cfg=cfg,
                is_recursive=(spec_name in sc.callees),
                callees=sorted(sc.callees),
            )
        )
    return topological_sort_operations(ops)


def compile_spec_html_to_verus(html_text: str, source_label: str = "browser/vjs-spec/spec_inputs/ecma262_clauses.html") -> tuple[list[IROperation], str]:
    ops = compile_spec_html_to_ir(html_text)
    emitter = VerusCodeEmitter(ops)
    return ops, emitter.emit_module(source_label)


# ===============================================================================================
# 7. Compiler Unit Test Suite (`--self-test`)
# ===============================================================================================

class TestEsmetaToVerusCompiler(unittest.TestCase):
    def test_hierarchical_step_numbering_1_a_i(self) -> None:
        alg = """
            1. If _x_ is *true*, then
              1. If _y_ is *false*, then
                1. Return *false*.
              1. Return *true*.
            1. Return *false*.
        """
        roots, total = parse_alg_steps(alg)
        self.assertEqual(total, 5)
        self.assertEqual(roots[0].step_label, "1")
        self.assertEqual(roots[0].children[0].step_label, "1.a")
        self.assertEqual(roots[0].children[0].children[0].step_label, "1.a.i")
        self.assertEqual(roots[0].children[1].step_label, "1.b")
        self.assertEqual(roots[1].step_label, "2")

    def test_ecmarkup_inline_normalization_and_attributes(self) -> None:
        attr, clean = normalize_ecmarkup_inline(
            '[id="step-web-compat", normative-optional] If _x_ is *+0*<sub>𝔽</sub> and _n_ &ge; 2<sup>_bitWidth_ - 1</sup>, return *true*.'
        )
        self.assertEqual(attr, 'id="step-web-compat", normative-optional')
        self.assertEqual(clean, "If _x_ is *+0*_𝔽 and _n_ ≥ 2^(_bitWidth_ - 1), return *true*.")

    def test_if_elif_else_coalescing_and_ssa_phi_lifting(self) -> None:
        snippet = """
        <emu-clause id="sec-numberbitwiseop" type="abstract operation">
          <h1>NumberBitwiseOp ( _op_: `&amp;`, `^`, or `|`, _x_: a Number, _y_: a Number, ): an integral Number</h1>
          <emu-alg>
            1. Let _leftNumber_ be ! ToInt32(_x_).
            1. Let _rightNumber_ be ! ToInt32(_y_).
            1. Let _leftBits_ be the 32-bit two's complement bit string representing ℝ(_leftNumber_).
            1. Let _rightBits_ be the 32-bit two's complement bit string representing ℝ(_rightNumber_).
            1. If _op_ is `&amp;`, then
              1. Let _result_ be the result of applying the bitwise <code>AND</code> operation to _leftBits_ and _rightBits_.
            1. Else if _op_ is `^`, then
              1. Let _result_ be the result of applying the bitwise <code>XOR</code> (exclusive OR) operation to _leftBits_ and _rightBits_.
            1. Else,
              1. Assert: _op_ is `|`.
              1. Let _result_ be the result of applying the bitwise <code>OR</code> (inclusive OR) operation to _leftBits_ and _rightBits_.
            1. Return the Number value for the integer represented by the 32-bit two's complement bit string _result_.
          </emu-alg>
        </emu-clause>
        """
        ops = compile_spec_html_to_ir(snippet)
        self.assertEqual(len(ops), 1)
        op = ops[0]
        if_stmt = op.body[4]
        self.assertIsInstance(if_stmt, IRIf)
        assert isinstance(if_stmt, IRIf)
        self.assertEqual(len(if_stmt.elif_branches), 1)
        self.assertEqual(len(if_stmt.else_body), 2)
        self.assertIsInstance(if_stmt.else_body[0], IRAssert)
        self.assertEqual(if_stmt.phi_var, "result")
        # Verify CFG has join block with Phi(result)
        join_labels = [b.label for b in op.cfg.blocks.values() if b.kind == "join"]
        self.assertIn("5:Phi(result)", join_labels)

    def test_set_mutation_analysis_and_modulo_lowering(self) -> None:
        snippet = """
        <emu-clause id="sec-tofixedsizeinteger" type="abstract operation">
          <h1>ToFixedSizeInteger ( _int_: an integer, +∞, or -∞, _signed_: ~unsigned~ or ~signed~, _bitWidth_: a positive integer, ): an integer</h1>
          <emu-alg>
            1. If _int_ = +∞ or _int_ = -∞, return 0.
            1. Let _fixedInt_ be _int_ modulo 2<sup>_bitWidth_</sup>.
            1. NOTE: The following step does not change the two's complement representation of _fixedInt_.
            1. If _signed_ is ~signed~ and _fixedInt_ ≥ 2<sup>_bitWidth_ - 1</sup>, set _fixedInt_ to _fixedInt_ - 2<sup>_bitWidth_</sup>.
            1. Return _fixedInt_.
          </emu-alg>
        </emu-clause>
        """
        ops, rust_src = compile_spec_html_to_verus(snippet, "unit_test")
        op = ops[0]
        let_stmt = op.body[1]
        assert isinstance(let_stmt, IRLet)
        self.assertTrue(let_stmt.mutable)
        self.assertIsInstance(let_stmt.rhs, ModuloExpr)
        # Spec uses pure SSA shadowing while exec uses `let mut fixed_int`!
        self.assertIn("let fixed_int = if (signed == Signedness::Signed)", rust_src)
        self.assertIn("let mut fixed_int = ", rust_src)

    def test_topological_call_graph_ordering(self) -> None:
        full_text = DEFAULT_INPUT.read_text()
        ops = compile_spec_html_to_ir(full_text)
        idx = {o.spec_name: i for i, o in enumerate(ops)}
        # Callees appear strictly before non-mutual callers
        self.assertLess(idx["SameType"], idx["SameValue"])
        self.assertLess(idx["Number::sameValue"], idx["SameValue"])
        self.assertLess(idx["SameValueNonNumber"], idx["SameValue"])
        self.assertLess(idx["Number::equal"], idx["IsStrictlyEqual"])
        self.assertLess(idx["IsStrictlyEqual"], idx["IsLooselyEqual"])
        self.assertLess(idx["ToNumber"], idx["ToIntegerOrInfinity"])
        self.assertLess(idx["ToIntegerOrInfinity"], idx["ToInt32"])
        self.assertLess(idx["ToFixedSizeInteger"], idx["ToInt32"])
        self.assertLess(idx["ToInt32"], idx["NumberBitwiseOp"])
        self.assertLess(idx["NumberBitwiseOp"], idx["Number::bitwiseAND"])

    def test_completion_shorthands_question_and_bang(self) -> None:
        full_text = DEFAULT_INPUT.read_text()
        ops = compile_spec_html_to_ir(full_text)
        by_name = {o.spec_name: o for o in ops}
        # ToInt32 step 1 uses `? ToIntegerOrInfinity(_arg_)`
        s1 = by_name["ToInt32"].body[0]
        assert isinstance(s1, IRLet) and isinstance(s1.rhs, CallExpr)
        self.assertEqual(s1.rhs.mode, CompletionMode.QUESTION)
        # Number::leftShift step 1 uses `! ToInt32(_x_)`
        ls1 = by_name["Number::leftShift"].body[0]
        assert isinstance(ls1, IRLet) and isinstance(ls1.rhs, CallExpr)
        self.assertEqual(ls1.rhs.mode, CompletionMode.BANG)

    def test_cfg_every_operation_has_entry_and_exit_blocks(self) -> None:
        full_text = DEFAULT_INPUT.read_text()
        ops = compile_spec_html_to_ir(full_text)
        for op in ops:
            self.assertIn(op.cfg.entry, op.cfg.blocks)
            kinds = {b.kind for b in op.cfg.blocks.values()}
            self.assertIn("entry", kinds)
            self.assertTrue("return" in kinds or "throw" in kinds, f"{op.spec_name} missing exit block")

    def test_nested_subclauses_skipped_cleanly(self) -> None:
        full_text = DEFAULT_INPUT.read_text()
        ops = compile_spec_html_to_ir(full_text)
        names = [o.spec_name for o in ops]
        # All 10 required operations + 15 supporting clauses = 25 compiled operations
        for req in [
            "ToBoolean", "ToInt32", "ToUint32", "ToUint16",
            "RequireObjectCoercible", "SameValue", "SameValueZero",
            "SameValueNonNumber", "IsStrictlyEqual", "IsLooselyEqual",
            "Number::equal", "Number::sameValue", "Number::sameValueZero",
            "ToNumber", "ToIntegerOrInfinity", "ToFixedSizeInteger", "SameType",
        ]:
            self.assertIn(req, names)
        # Nested grammar subclause `StringNumericValue` inside `sec-tonumber` is NOT misparsed as top-level
        self.assertNotIn("StringNumericValue", names)
        self.assertEqual(len(ops), 25)

    def test_recursion_and_decreases_synthesis(self) -> None:
        full_text = DEFAULT_INPUT.read_text()
        ops, rust_src = compile_spec_html_to_verus(full_text)
        by_name = {o.spec_name: o for o in ops}
        self.assertTrue(by_name["ToNumber"].is_recursive)
        self.assertTrue(by_name["IsLooselyEqual"].is_recursive)
        self.assertFalse(by_name["SameValue"].is_recursive)
        self.assertIn("decreases spec_tonumber_rank(arg),", rust_src)
        self.assertIn("decreases spec_tonumber_rank(arg@),", rust_src)
        self.assertIn("decreases spec_loosely_equal_rank(x, y),", rust_src)
        self.assertIn("decreases spec_loosely_equal_rank(x@, y@),", rust_src)

    def test_warblre_interleaved_comments_and_zero_trusted_markers(self) -> None:
        full_text = DEFAULT_INPUT.read_text()
        _, rust_src = compile_spec_html_to_verus(full_text)
        self.assertIn("// 1. If _arg_ is either *undefined* or *null*, throw a *TypeError* exception.", rust_src)
        self.assertIn("// 1. Assert: SameType(_x_, _y_) is *true*.", rust_src)
        for forbidden in ["assume(", "admit(", "external_body", "verifier::external", "assume_specification", "unsafe"]:
            self.assertNotIn(forbidden, rust_src)


def main() -> int:
    ap = argparse.ArgumentParser(description="Compile ECMA-262 <emu-alg> clauses to verified Verus code.")
    ap.add_argument("--input", type=Path, default=DEFAULT_INPUT, help="Input <emu-clause> HTML file")
    ap.add_argument("--output", type=Path, default=DEFAULT_OUTPUT, help="Output Verus .rs file")
    ap.add_argument("--check", action="store_true", help="Verify output matches compiled input byte-for-byte")
    ap.add_argument("--self-test", action="store_true", help="Run compiler unit tests")
    ap.add_argument("--dump-ir", action="store_true", help="Print JSON summary of compiled IRES operations & CFGs")
    args = ap.parse_args()

    if args.self_test:
        suite = unittest.defaultTestLoader.loadTestsFromTestCase(TestEsmetaToVerusCompiler)
        res = unittest.TextTestRunner(verbosity=2).run(suite)
        return 0 if res.wasSuccessful() else 1

    html_text = args.input.read_text(encoding="utf-8")
    ops, verus_code = compile_spec_html_to_verus(html_text)

    if args.dump_ir:
        summary = [
            {
                "clause": op.clause_number,
                "id": op.clause_id,
                "name": op.spec_name,
                "spec_fn": op.spec_fn_name,
                "exec_fn": op.rust_fn_name,
                "spec_steps": op.step_count,
                "is_recursive": op.is_recursive,
                "callees": op.callees,
                "cfg_blocks": len(op.cfg.blocks),
            }
            for op in ops
        ]
        print(json.dumps(summary, indent=2))
        return 0

    if args.check:
        if not args.output.exists():
            print(f"ERROR: {args.output} does not exist", file=sys.stderr)
            return 1
        existing = args.output.read_text(encoding="utf-8")
        if existing != verus_code:
            print(f"ERROR: {args.output} is out of date with {args.input}", file=sys.stderr)
            return 1
        print(f"OK: {args.output} matches compiled {args.input} ({len(ops)} ECMA-262 operations)")
        return 0

    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(verus_code, encoding="utf-8")
    print(f"Compiled {len(ops)} ECMA-262 <emu-alg> clauses -> {args.output} ({len(verus_code.splitlines())} lines)")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
