//! ECMA-262 §12 Lexical Grammar token definitions, reserved words, strict-mode reserved words,
//! contextual keywords, punctuators, spans, and spec views.
use vstd::prelude::*;

verus! {

/// Byte-offset source span `[start, end)` within the input buffer.
#[derive(Structural, Clone, Copy, PartialEq, Eq, Debug)]
pub struct Span {
    pub start: usize,
    pub end: usize,
}

impl Span {
    pub open spec fn wf(&self, len: nat) -> bool {
        self.start <= self.end && self.end <= len
    }
}

/// Full ECMAScript keyword, future reserved word, strict-mode reserved word, and contextual keyword set (§12.7.2).
#[derive(Structural, Clone, Copy, PartialEq, Eq, Debug)]
pub enum Keyword {
    // Unconditionally reserved words in Script & Module
    Break,
    Case,
    Catch,
    Class,
    Const,
    Continue,
    Debugger,
    Default,
    Delete,
    Do,
    Else,
    Enum,
    Export,
    Extends,
    False,
    Finally,
    For,
    Function,
    If,
    Import,
    In,
    Instanceof,
    New,
    Null,
    Return,
    Super,
    Switch,
    This,
    Throw,
    True,
    Try,
    Typeof,
    Var,
    Void,
    While,
    With,
    // Contextually / strict-mode reserved words
    Let,
    Static,
    Yield,
    Await,
    Async,
    Of,
    // Strict-mode FutureReservedWord (§12.7.2)
    Implements,
    Interface,
    Package,
    Private,
    Protected,
    Public,
}

/// Canonical ASCII byte spelling of every `Keyword`.
pub open spec fn spec_keyword_bytes(kw: Keyword) -> Seq<u8> {
    match kw {
        Keyword::If => seq![0x69u8, 0x66],
        Keyword::In => seq![0x69u8, 0x6E],
        Keyword::Do => seq![0x64u8, 0x6F],
        Keyword::Of => seq![0x6Fu8, 0x66],
        Keyword::Var => seq![0x76u8, 0x61, 0x72],
        Keyword::Let => seq![0x6Cu8, 0x65, 0x74],
        Keyword::For => seq![0x66u8, 0x6F, 0x72],
        Keyword::New => seq![0x6Eu8, 0x65, 0x77],
        Keyword::Try => seq![0x74u8, 0x72, 0x79],
        Keyword::Case => seq![0x63u8, 0x61, 0x73, 0x65],
        Keyword::Else => seq![0x65u8, 0x6C, 0x73, 0x65],
        Keyword::Enum => seq![0x65u8, 0x6E, 0x75, 0x6D],
        Keyword::Null => seq![0x6Eu8, 0x75, 0x6C, 0x6C],
        Keyword::This => seq![0x74u8, 0x68, 0x69, 0x73],
        Keyword::True => seq![0x74u8, 0x72, 0x75, 0x65],
        Keyword::Void => seq![0x76u8, 0x6F, 0x69, 0x64],
        Keyword::With => seq![0x77u8, 0x69, 0x74, 0x68],
        Keyword::Async => seq![0x61u8, 0x73, 0x79, 0x6E, 0x63],
        Keyword::Await => seq![0x61u8, 0x77, 0x61, 0x69, 0x74],
        Keyword::Break => seq![0x62u8, 0x72, 0x65, 0x61, 0x6B],
        Keyword::Catch => seq![0x63u8, 0x61, 0x74, 0x63, 0x68],
        Keyword::Class => seq![0x63u8, 0x6C, 0x61, 0x73, 0x73],
        Keyword::Const => seq![0x63u8, 0x6F, 0x6E, 0x73, 0x74],
        Keyword::False => seq![0x66u8, 0x61, 0x6C, 0x73, 0x65],
        Keyword::Super => seq![0x73u8, 0x75, 0x70, 0x65, 0x72],
        Keyword::Throw => seq![0x74u8, 0x68, 0x72, 0x6F, 0x77],
        Keyword::While => seq![0x77u8, 0x68, 0x69, 0x6C, 0x65],
        Keyword::Yield => seq![0x79u8, 0x69, 0x65, 0x6C, 0x64],
        Keyword::Delete => seq![0x64u8, 0x65, 0x6C, 0x65, 0x74, 0x65],
        Keyword::Export => seq![0x65u8, 0x78, 0x70, 0x6F, 0x72, 0x74],
        Keyword::Import => seq![0x69u8, 0x6D, 0x70, 0x6F, 0x72, 0x74],
        Keyword::Public => seq![0x70u8, 0x75, 0x62, 0x6C, 0x69, 0x63],
        Keyword::Return => seq![0x72u8, 0x65, 0x74, 0x75, 0x72, 0x6E],
        Keyword::Static => seq![0x73u8, 0x74, 0x61, 0x74, 0x69, 0x63],
        Keyword::Switch => seq![0x73u8, 0x77, 0x69, 0x74, 0x63, 0x68],
        Keyword::Typeof => seq![0x74u8, 0x79, 0x70, 0x65, 0x6F, 0x66],
        Keyword::Default => seq![0x64u8, 0x65, 0x66, 0x61, 0x75, 0x6C, 0x74],
        Keyword::Extends => seq![0x65u8, 0x78, 0x74, 0x65, 0x6E, 0x64, 0x73],
        Keyword::Finally => seq![0x66u8, 0x69, 0x6E, 0x61, 0x6C, 0x6C, 0x79],
        Keyword::Package => seq![0x70u8, 0x61, 0x63, 0x6B, 0x61, 0x67, 0x65],
        Keyword::Private => seq![0x70u8, 0x72, 0x69, 0x76, 0x61, 0x74, 0x65],
        Keyword::Continue => seq![0x63u8, 0x6F, 0x6E, 0x74, 0x69, 0x6E, 0x75, 0x65],
        Keyword::Debugger => seq![0x64u8, 0x65, 0x62, 0x75, 0x67, 0x67, 0x65, 0x72],
        Keyword::Function => seq![0x66u8, 0x75, 0x6E, 0x63, 0x74, 0x69, 0x6F, 0x6E],
        Keyword::Interface => seq![0x69u8, 0x6E, 0x74, 0x65, 0x72, 0x66, 0x61, 0x63, 0x65],
        Keyword::Protected => seq![0x70u8, 0x72, 0x6F, 0x74, 0x65, 0x63, 0x74, 0x65, 0x64],
        Keyword::Implements => seq![0x69u8, 0x6D, 0x70, 0x6C, 0x65, 0x6D, 0x65, 0x6E, 0x74, 0x73],
        Keyword::Instanceof => seq![0x69u8, 0x6E, 0x73, 0x74, 0x61, 0x6E, 0x63, 0x65, 0x6F, 0x66],
    }
}

/// Spec classifier mapping an identifier byte sequence to a `Keyword` if it matches one.
pub open spec fn spec_classify_ident(s: Seq<u8>) -> Option<Keyword> {
    if s.len() == 2 {
        if s[0] == 0x69 && s[1] == 0x66 {
            Some(Keyword::If)
        } else if s[0] == 0x69 && s[1] == 0x6E {
            Some(Keyword::In)
        } else if s[0] == 0x64 && s[1] == 0x6F {
            Some(Keyword::Do)
        } else if s[0] == 0x6F && s[1] == 0x66 {
            Some(Keyword::Of)
        } else {
            None
        }
    } else if s.len() == 3 {
        if s[0] == 0x76 && s[1] == 0x61 && s[2] == 0x72 {
            Some(Keyword::Var)
        } else if s[0] == 0x6C && s[1] == 0x65 && s[2] == 0x74 {
            Some(Keyword::Let)
        } else if s[0] == 0x66 && s[1] == 0x6F && s[2] == 0x72 {
            Some(Keyword::For)
        } else if s[0] == 0x6E && s[1] == 0x65 && s[2] == 0x77 {
            Some(Keyword::New)
        } else if s[0] == 0x74 && s[1] == 0x72 && s[2] == 0x79 {
            Some(Keyword::Try)
        } else {
            None
        }
    } else if s.len() == 4 {
        if s[0] == 0x63 && s[1] == 0x61 && s[2] == 0x73 && s[3] == 0x65 {
            Some(Keyword::Case)
        } else if s[0] == 0x65 && s[1] == 0x6C && s[2] == 0x73 && s[3] == 0x65 {
            Some(Keyword::Else)
        } else if s[0] == 0x65 && s[1] == 0x6E && s[2] == 0x75 && s[3] == 0x6D {
            Some(Keyword::Enum)
        } else if s[0] == 0x6E && s[1] == 0x75 && s[2] == 0x6C && s[3] == 0x6C {
            Some(Keyword::Null)
        } else if s[0] == 0x74 && s[1] == 0x68 && s[2] == 0x69 && s[3] == 0x73 {
            Some(Keyword::This)
        } else if s[0] == 0x74 && s[1] == 0x72 && s[2] == 0x75 && s[3] == 0x65 {
            Some(Keyword::True)
        } else if s[0] == 0x76 && s[1] == 0x6F && s[2] == 0x69 && s[3] == 0x64 {
            Some(Keyword::Void)
        } else if s[0] == 0x77 && s[1] == 0x69 && s[2] == 0x74 && s[3] == 0x68 {
            Some(Keyword::With)
        } else {
            None
        }
    } else if s.len() == 5 {
        if s[0] == 0x61 && s[1] == 0x73 && s[2] == 0x79 && s[3] == 0x6E && s[4] == 0x63 {
            Some(Keyword::Async)
        } else if s[0] == 0x61 && s[1] == 0x77 && s[2] == 0x61 && s[3] == 0x69 && s[4] == 0x74 {
            Some(Keyword::Await)
        } else if s[0] == 0x62 && s[1] == 0x72 && s[2] == 0x65 && s[3] == 0x61 && s[4] == 0x6B {
            Some(Keyword::Break)
        } else if s[0] == 0x63 && s[1] == 0x61 && s[2] == 0x74 && s[3] == 0x63 && s[4] == 0x68 {
            Some(Keyword::Catch)
        } else if s[0] == 0x63 && s[1] == 0x6C && s[2] == 0x61 && s[3] == 0x73 && s[4] == 0x73 {
            Some(Keyword::Class)
        } else if s[0] == 0x63 && s[1] == 0x6F && s[2] == 0x6E && s[3] == 0x73 && s[4] == 0x74 {
            Some(Keyword::Const)
        } else if s[0] == 0x66 && s[1] == 0x61 && s[2] == 0x6C && s[3] == 0x73 && s[4] == 0x65 {
            Some(Keyword::False)
        } else if s[0] == 0x73 && s[1] == 0x75 && s[2] == 0x70 && s[3] == 0x65 && s[4] == 0x72 {
            Some(Keyword::Super)
        } else if s[0] == 0x74 && s[1] == 0x68 && s[2] == 0x72 && s[3] == 0x6F && s[4] == 0x77 {
            Some(Keyword::Throw)
        } else if s[0] == 0x77 && s[1] == 0x68 && s[2] == 0x69 && s[3] == 0x6C && s[4] == 0x65 {
            Some(Keyword::While)
        } else if s[0] == 0x79 && s[1] == 0x69 && s[2] == 0x65 && s[3] == 0x6C && s[4] == 0x64 {
            Some(Keyword::Yield)
        } else {
            None
        }
    } else if s.len() == 6 {
        if s[0] == 0x64 && s[1] == 0x65 && s[2] == 0x6C && s[3] == 0x65 && s[4] == 0x74 && s[5] == 0x65 {
            Some(Keyword::Delete)
        } else if s[0] == 0x65 && s[1] == 0x78 && s[2] == 0x70 && s[3] == 0x6F && s[4] == 0x72 && s[5] == 0x74 {
            Some(Keyword::Export)
        } else if s[0] == 0x69 && s[1] == 0x6D && s[2] == 0x70 && s[3] == 0x6F && s[4] == 0x72 && s[5] == 0x74 {
            Some(Keyword::Import)
        } else if s[0] == 0x70 && s[1] == 0x75 && s[2] == 0x62 && s[3] == 0x6C && s[4] == 0x69 && s[5] == 0x63 {
            Some(Keyword::Public)
        } else if s[0] == 0x72 && s[1] == 0x65 && s[2] == 0x74 && s[3] == 0x75 && s[4] == 0x72 && s[5] == 0x6E {
            Some(Keyword::Return)
        } else if s[0] == 0x73 && s[1] == 0x74 && s[2] == 0x61 && s[3] == 0x74 && s[4] == 0x69 && s[5] == 0x63 {
            Some(Keyword::Static)
        } else if s[0] == 0x73 && s[1] == 0x77 && s[2] == 0x69 && s[3] == 0x74 && s[4] == 0x63 && s[5] == 0x68 {
            Some(Keyword::Switch)
        } else if s[0] == 0x74 && s[1] == 0x79 && s[2] == 0x70 && s[3] == 0x65 && s[4] == 0x6F && s[5] == 0x66 {
            Some(Keyword::Typeof)
        } else {
            None
        }
    } else if s.len() == 7 {
        if s[0] == 0x64 && s[1] == 0x65 && s[2] == 0x66 && s[3] == 0x61 && s[4] == 0x75 && s[5] == 0x6C && s[6] == 0x74 {
            Some(Keyword::Default)
        } else if s[0] == 0x65 && s[1] == 0x78 && s[2] == 0x74 && s[3] == 0x65 && s[4] == 0x6E && s[5] == 0x64 && s[6] == 0x73 {
            Some(Keyword::Extends)
        } else if s[0] == 0x66 && s[1] == 0x69 && s[2] == 0x6E && s[3] == 0x61 && s[4] == 0x6C && s[5] == 0x6C && s[6] == 0x79 {
            Some(Keyword::Finally)
        } else if s[0] == 0x70 && s[1] == 0x61 && s[2] == 0x63 && s[3] == 0x6B && s[4] == 0x61 && s[5] == 0x67 && s[6] == 0x65 {
            Some(Keyword::Package)
        } else if s[0] == 0x70 && s[1] == 0x72 && s[2] == 0x69 && s[3] == 0x76 && s[4] == 0x61 && s[5] == 0x74 && s[6] == 0x65 {
            Some(Keyword::Private)
        } else {
            None
        }
    } else if s.len() == 8 {
        if s[0] == 0x63 && s[1] == 0x6F && s[2] == 0x6E && s[3] == 0x74 && s[4] == 0x69 && s[5] == 0x6E && s[6] == 0x75 && s[7] == 0x65 {
            Some(Keyword::Continue)
        } else if s[0] == 0x64 && s[1] == 0x65 && s[2] == 0x62 && s[3] == 0x75 && s[4] == 0x67 && s[5] == 0x67 && s[6] == 0x65 && s[7] == 0x72 {
            Some(Keyword::Debugger)
        } else if s[0] == 0x66 && s[1] == 0x75 && s[2] == 0x6E && s[3] == 0x63 && s[4] == 0x74 && s[5] == 0x69 && s[6] == 0x6F && s[7] == 0x6E {
            Some(Keyword::Function)
        } else {
            None
        }
    } else if s.len() == 9 {
        if s[0] == 0x69 && s[1] == 0x6E && s[2] == 0x74 && s[3] == 0x65 && s[4] == 0x72 && s[5] == 0x66 && s[6] == 0x61 && s[7] == 0x63 && s[8] == 0x65 {
            Some(Keyword::Interface)
        } else if s[0] == 0x70 && s[1] == 0x72 && s[2] == 0x6F && s[3] == 0x74 && s[4] == 0x65 && s[5] == 0x63 && s[6] == 0x74 && s[7] == 0x65 && s[8] == 0x64 {
            Some(Keyword::Protected)
        } else {
            None
        }
    } else if s.len() == 10 {
        if s[0] == 0x69 && s[1] == 0x6D && s[2] == 0x70 && s[3] == 0x6C && s[4] == 0x65 && s[5] == 0x6D && s[6] == 0x65 && s[7] == 0x6E && s[8] == 0x74 && s[9] == 0x73 {
            Some(Keyword::Implements)
        } else if s[0] == 0x69 && s[1] == 0x6E && s[2] == 0x73 && s[3] == 0x74 && s[4] == 0x61 && s[5] == 0x6E && s[6] == 0x63 && s[7] == 0x65 && s[8] == 0x6F && s[9] == 0x66 {
            Some(Keyword::Instanceof)
        } else {
            None
        }
    } else {
        None
    }
}

/// Roundtrip theorem: classifying the canonical spelling of every `Keyword` recovers `Some(kw)`.
#[verifier::rlimit(40)]
pub proof fn lemma_classify_keyword_roundtrip(kw: Keyword)
    ensures
        spec_classify_ident(spec_keyword_bytes(kw)) == Some(kw),
{
    let s = spec_keyword_bytes(kw);
    match kw {
        Keyword::If | Keyword::In | Keyword::Do | Keyword::Of => {
            assert(s.len() == 2);
        },
        Keyword::Var | Keyword::Let | Keyword::For | Keyword::New | Keyword::Try => {
            assert(s.len() == 3);
        },
        Keyword::Case
        | Keyword::Else
        | Keyword::Enum
        | Keyword::Null
        | Keyword::This
        | Keyword::True
        | Keyword::Void
        | Keyword::With => {
            assert(s.len() == 4);
        },
        Keyword::Async
        | Keyword::Await
        | Keyword::Break
        | Keyword::Catch
        | Keyword::Class
        | Keyword::Const
        | Keyword::False
        | Keyword::Super
        | Keyword::Throw
        | Keyword::While
        | Keyword::Yield => {
            assert(s.len() == 5);
        },
        Keyword::Delete
        | Keyword::Export
        | Keyword::Import
        | Keyword::Public
        | Keyword::Return
        | Keyword::Static
        | Keyword::Switch
        | Keyword::Typeof => {
            assert(s.len() == 6);
        },
        Keyword::Default
        | Keyword::Extends
        | Keyword::Finally
        | Keyword::Package
        | Keyword::Private => {
            assert(s.len() == 7);
        },
        Keyword::Continue | Keyword::Debugger | Keyword::Function => {
            assert(s.len() == 8);
        },
        Keyword::Interface | Keyword::Protected => {
            assert(s.len() == 9);
        },
        Keyword::Implements | Keyword::Instanceof => {
            assert(s.len() == 10);
        },
    }
}

/// ECMA-262 §12.7.2: Keywords that can NEVER be used as an IdentifierReference, BindingIdentifier,
/// or LabelIdentifier in any syntactic context.
pub open spec fn spec_is_unconditional_reserved(kw: Keyword) -> bool {
    match kw {
        Keyword::Let
        | Keyword::Static
        | Keyword::Yield
        | Keyword::Await
        | Keyword::Async
        | Keyword::Of
        | Keyword::Implements
        | Keyword::Interface
        | Keyword::Package
        | Keyword::Private
        | Keyword::Protected
        | Keyword::Public => false,
        _ => true,
    }
}

/// ECMA-262 §12.7.2 & §13.1.1: Strict-mode reserved words (`implements`, `interface`, `let`,
/// `package`, `private`, `protected`, `public`, `static`, `yield`).
pub open spec fn spec_is_strict_reserved_word(kw: Keyword) -> bool {
    match kw {
        Keyword::Implements
        | Keyword::Interface
        | Keyword::Let
        | Keyword::Package
        | Keyword::Private
        | Keyword::Protected
        | Keyword::Public
        | Keyword::Static
        | Keyword::Yield => true,
        _ => false,
    }
}

/// ECMA-262 §13.1.1: Whether `kw` is permitted as an `Identifier` under `(strict, in_async, in_generator)`.
pub open spec fn spec_keyword_allowed_as_ident(
    kw: Keyword,
    strict: bool,
    in_async: bool,
    in_generator: bool,
) -> bool {
    if spec_is_unconditional_reserved(kw) {
        false
    } else if strict && spec_is_strict_reserved_word(kw) {
        false
    } else if in_async && kw == Keyword::Await {
        false
    } else if in_generator && kw == Keyword::Yield {
        false
    } else {
        true
    }
}

/// Whether raw byte name `s` is `"eval"` or `"arguments"` (forbidden as binding/assignment target in strict mode).
pub open spec fn spec_is_eval_or_arguments(s: Seq<u8>) -> bool {
    (s.len() == 4 && s[0] == 0x65 && s[1] == 0x76 && s[2] == 0x61 && s[3] == 0x6C)
        || (s.len() == 9
            && s[0] == 0x61
            && s[1] == 0x72
            && s[2] == 0x67
            && s[3] == 0x75
            && s[4] == 0x6D
            && s[5] == 0x65
            && s[6] == 0x6E
            && s[7] == 0x74
            && s[8] == 0x73)
}

/// Whether raw byte name `s` is `"let"` (forbidden as a `BoundName` in `let`/`const` declarations per §14.3.1.1).
pub open spec fn spec_is_let_name(s: Seq<u8>) -> bool {
    s.len() == 3 && s[0] == 0x6C && s[1] == 0x65 && s[2] == 0x74
}

pub fn keyword_bytes(kw: Keyword) -> (v: Vec<u8>)
    ensures
        v@ == spec_keyword_bytes(kw),
{
    match kw {
        Keyword::If => vec![0x69, 0x66],
        Keyword::In => vec![0x69, 0x6E],
        Keyword::Do => vec![0x64, 0x6F],
        Keyword::Of => vec![0x6F, 0x66],
        Keyword::Var => vec![0x76, 0x61, 0x72],
        Keyword::Let => vec![0x6C, 0x65, 0x74],
        Keyword::For => vec![0x66, 0x6F, 0x72],
        Keyword::New => vec![0x6E, 0x65, 0x77],
        Keyword::Try => vec![0x74, 0x72, 0x79],
        Keyword::Case => vec![0x63, 0x61, 0x73, 0x65],
        Keyword::Else => vec![0x65, 0x6C, 0x73, 0x65],
        Keyword::Enum => vec![0x65, 0x6E, 0x75, 0x6D],
        Keyword::Null => vec![0x6E, 0x75, 0x6C, 0x6C],
        Keyword::This => vec![0x74, 0x68, 0x69, 0x73],
        Keyword::True => vec![0x74, 0x72, 0x75, 0x65],
        Keyword::Void => vec![0x76, 0x6F, 0x69, 0x64],
        Keyword::With => vec![0x77, 0x69, 0x74, 0x68],
        Keyword::Async => vec![0x61, 0x73, 0x79, 0x6E, 0x63],
        Keyword::Await => vec![0x61, 0x77, 0x61, 0x69, 0x74],
        Keyword::Break => vec![0x62, 0x72, 0x65, 0x61, 0x6B],
        Keyword::Catch => vec![0x63, 0x61, 0x74, 0x63, 0x68],
        Keyword::Class => vec![0x63, 0x6C, 0x61, 0x73, 0x73],
        Keyword::Const => vec![0x63, 0x6F, 0x6E, 0x73, 0x74],
        Keyword::False => vec![0x66, 0x61, 0x6C, 0x73, 0x65],
        Keyword::Super => vec![0x73, 0x75, 0x70, 0x65, 0x72],
        Keyword::Throw => vec![0x74, 0x68, 0x72, 0x6F, 0x77],
        Keyword::While => vec![0x77, 0x68, 0x69, 0x6C, 0x65],
        Keyword::Yield => vec![0x79, 0x69, 0x65, 0x6C, 0x64],
        Keyword::Delete => vec![0x64, 0x65, 0x6C, 0x65, 0x74, 0x65],
        Keyword::Export => vec![0x65, 0x78, 0x70, 0x6F, 0x72, 0x74],
        Keyword::Import => vec![0x69, 0x6D, 0x70, 0x6F, 0x72, 0x74],
        Keyword::Public => vec![0x70, 0x75, 0x62, 0x6C, 0x69, 0x63],
        Keyword::Return => vec![0x72, 0x65, 0x74, 0x75, 0x72, 0x6E],
        Keyword::Static => vec![0x73, 0x74, 0x61, 0x74, 0x69, 0x63],
        Keyword::Switch => vec![0x73, 0x77, 0x69, 0x74, 0x63, 0x68],
        Keyword::Typeof => vec![0x74, 0x79, 0x70, 0x65, 0x6F, 0x66],
        Keyword::Default => vec![0x64, 0x65, 0x66, 0x61, 0x75, 0x6C, 0x74],
        Keyword::Extends => vec![0x65, 0x78, 0x74, 0x65, 0x6E, 0x64, 0x73],
        Keyword::Finally => vec![0x66, 0x69, 0x6E, 0x61, 0x6C, 0x6C, 0x79],
        Keyword::Package => vec![0x70, 0x61, 0x63, 0x6B, 0x61, 0x67, 0x65],
        Keyword::Private => vec![0x70, 0x72, 0x69, 0x76, 0x61, 0x74, 0x65],
        Keyword::Continue => vec![0x63, 0x6F, 0x6E, 0x74, 0x69, 0x6E, 0x75, 0x65],
        Keyword::Debugger => vec![0x64, 0x65, 0x62, 0x75, 0x67, 0x67, 0x65, 0x72],
        Keyword::Function => vec![0x66, 0x75, 0x6E, 0x63, 0x74, 0x69, 0x6F, 0x6E],
        Keyword::Interface => vec![0x69, 0x6E, 0x74, 0x65, 0x72, 0x66, 0x61, 0x63, 0x65],
        Keyword::Protected => vec![0x70, 0x72, 0x6F, 0x74, 0x65, 0x63, 0x74, 0x65, 0x64],
        Keyword::Implements => vec![0x69, 0x6D, 0x70, 0x6C, 0x65, 0x6D, 0x65, 0x6E, 0x74, 0x73],
        Keyword::Instanceof => vec![0x69, 0x6E, 0x73, 0x74, 0x61, 0x6E, 0x63, 0x65, 0x6F, 0x66],
    }
}

pub fn classify_ident(s: &[u8]) -> (r: Option<Keyword>)
    ensures
        r == spec_classify_ident(s@),
{
    let n = s.len();
    if n == 2 {
        if s[0] == 0x69 && s[1] == 0x66 {
            Some(Keyword::If)
        } else if s[0] == 0x69 && s[1] == 0x6E {
            Some(Keyword::In)
        } else if s[0] == 0x64 && s[1] == 0x6F {
            Some(Keyword::Do)
        } else if s[0] == 0x6F && s[1] == 0x66 {
            Some(Keyword::Of)
        } else {
            None
        }
    } else if n == 3 {
        if s[0] == 0x76 && s[1] == 0x61 && s[2] == 0x72 {
            Some(Keyword::Var)
        } else if s[0] == 0x6C && s[1] == 0x65 && s[2] == 0x74 {
            Some(Keyword::Let)
        } else if s[0] == 0x66 && s[1] == 0x6F && s[2] == 0x72 {
            Some(Keyword::For)
        } else if s[0] == 0x6E && s[1] == 0x65 && s[2] == 0x77 {
            Some(Keyword::New)
        } else if s[0] == 0x74 && s[1] == 0x72 && s[2] == 0x79 {
            Some(Keyword::Try)
        } else {
            None
        }
    } else if n == 4 {
        if s[0] == 0x63 && s[1] == 0x61 && s[2] == 0x73 && s[3] == 0x65 {
            Some(Keyword::Case)
        } else if s[0] == 0x65 && s[1] == 0x6C && s[2] == 0x73 && s[3] == 0x65 {
            Some(Keyword::Else)
        } else if s[0] == 0x65 && s[1] == 0x6E && s[2] == 0x75 && s[3] == 0x6D {
            Some(Keyword::Enum)
        } else if s[0] == 0x6E && s[1] == 0x75 && s[2] == 0x6C && s[3] == 0x6C {
            Some(Keyword::Null)
        } else if s[0] == 0x74 && s[1] == 0x68 && s[2] == 0x69 && s[3] == 0x73 {
            Some(Keyword::This)
        } else if s[0] == 0x74 && s[1] == 0x72 && s[2] == 0x75 && s[3] == 0x65 {
            Some(Keyword::True)
        } else if s[0] == 0x76 && s[1] == 0x6F && s[2] == 0x69 && s[3] == 0x64 {
            Some(Keyword::Void)
        } else if s[0] == 0x77 && s[1] == 0x69 && s[2] == 0x74 && s[3] == 0x68 {
            Some(Keyword::With)
        } else {
            None
        }
    } else if n == 5 {
        if s[0] == 0x61 && s[1] == 0x73 && s[2] == 0x79 && s[3] == 0x6E && s[4] == 0x63 {
            Some(Keyword::Async)
        } else if s[0] == 0x61 && s[1] == 0x77 && s[2] == 0x61 && s[3] == 0x69 && s[4] == 0x74 {
            Some(Keyword::Await)
        } else if s[0] == 0x62 && s[1] == 0x72 && s[2] == 0x65 && s[3] == 0x61 && s[4] == 0x6B {
            Some(Keyword::Break)
        } else if s[0] == 0x63 && s[1] == 0x61 && s[2] == 0x74 && s[3] == 0x63 && s[4] == 0x68 {
            Some(Keyword::Catch)
        } else if s[0] == 0x63 && s[1] == 0x6C && s[2] == 0x61 && s[3] == 0x73 && s[4] == 0x73 {
            Some(Keyword::Class)
        } else if s[0] == 0x63 && s[1] == 0x6F && s[2] == 0x6E && s[3] == 0x73 && s[4] == 0x74 {
            Some(Keyword::Const)
        } else if s[0] == 0x66 && s[1] == 0x61 && s[2] == 0x6C && s[3] == 0x73 && s[4] == 0x65 {
            Some(Keyword::False)
        } else if s[0] == 0x73 && s[1] == 0x75 && s[2] == 0x70 && s[3] == 0x65 && s[4] == 0x72 {
            Some(Keyword::Super)
        } else if s[0] == 0x74 && s[1] == 0x68 && s[2] == 0x72 && s[3] == 0x6F && s[4] == 0x77 {
            Some(Keyword::Throw)
        } else if s[0] == 0x77 && s[1] == 0x68 && s[2] == 0x69 && s[3] == 0x6C && s[4] == 0x65 {
            Some(Keyword::While)
        } else if s[0] == 0x79 && s[1] == 0x69 && s[2] == 0x65 && s[3] == 0x6C && s[4] == 0x64 {
            Some(Keyword::Yield)
        } else {
            None
        }
    } else if n == 6 {
        if s[0] == 0x64 && s[1] == 0x65 && s[2] == 0x6C && s[3] == 0x65 && s[4] == 0x74 && s[5] == 0x65 {
            Some(Keyword::Delete)
        } else if s[0] == 0x65 && s[1] == 0x78 && s[2] == 0x70 && s[3] == 0x6F && s[4] == 0x72 && s[5] == 0x74 {
            Some(Keyword::Export)
        } else if s[0] == 0x69 && s[1] == 0x6D && s[2] == 0x70 && s[3] == 0x6F && s[4] == 0x72 && s[5] == 0x74 {
            Some(Keyword::Import)
        } else if s[0] == 0x70 && s[1] == 0x75 && s[2] == 0x62 && s[3] == 0x6C && s[4] == 0x69 && s[5] == 0x63 {
            Some(Keyword::Public)
        } else if s[0] == 0x72 && s[1] == 0x65 && s[2] == 0x74 && s[3] == 0x75 && s[4] == 0x72 && s[5] == 0x6E {
            Some(Keyword::Return)
        } else if s[0] == 0x73 && s[1] == 0x74 && s[2] == 0x61 && s[3] == 0x74 && s[4] == 0x69 && s[5] == 0x63 {
            Some(Keyword::Static)
        } else if s[0] == 0x73 && s[1] == 0x77 && s[2] == 0x69 && s[3] == 0x74 && s[4] == 0x63 && s[5] == 0x68 {
            Some(Keyword::Switch)
        } else if s[0] == 0x74 && s[1] == 0x79 && s[2] == 0x70 && s[3] == 0x65 && s[4] == 0x6F && s[5] == 0x66 {
            Some(Keyword::Typeof)
        } else {
            None
        }
    } else if n == 7 {
        if s[0] == 0x64 && s[1] == 0x65 && s[2] == 0x66 && s[3] == 0x61 && s[4] == 0x75 && s[5] == 0x6C && s[6] == 0x74 {
            Some(Keyword::Default)
        } else if s[0] == 0x65 && s[1] == 0x78 && s[2] == 0x74 && s[3] == 0x65 && s[4] == 0x6E && s[5] == 0x64 && s[6] == 0x73 {
            Some(Keyword::Extends)
        } else if s[0] == 0x66 && s[1] == 0x69 && s[2] == 0x6E && s[3] == 0x61 && s[4] == 0x6C && s[5] == 0x6C && s[6] == 0x79 {
            Some(Keyword::Finally)
        } else if s[0] == 0x70 && s[1] == 0x61 && s[2] == 0x63 && s[3] == 0x6B && s[4] == 0x61 && s[5] == 0x67 && s[6] == 0x65 {
            Some(Keyword::Package)
        } else if s[0] == 0x70 && s[1] == 0x72 && s[2] == 0x69 && s[3] == 0x76 && s[4] == 0x61 && s[5] == 0x74 && s[6] == 0x65 {
            Some(Keyword::Private)
        } else {
            None
        }
    } else if n == 8 {
        if s[0] == 0x63 && s[1] == 0x6F && s[2] == 0x6E && s[3] == 0x74 && s[4] == 0x69 && s[5] == 0x6E && s[6] == 0x75 && s[7] == 0x65 {
            Some(Keyword::Continue)
        } else if s[0] == 0x64 && s[1] == 0x65 && s[2] == 0x62 && s[3] == 0x75 && s[4] == 0x67 && s[5] == 0x67 && s[6] == 0x65 && s[7] == 0x72 {
            Some(Keyword::Debugger)
        } else if s[0] == 0x66 && s[1] == 0x75 && s[2] == 0x6E && s[3] == 0x63 && s[4] == 0x74 && s[5] == 0x69 && s[6] == 0x6F && s[7] == 0x6E {
            Some(Keyword::Function)
        } else {
            None
        }
    } else if n == 9 {
        if s[0] == 0x69 && s[1] == 0x6E && s[2] == 0x74 && s[3] == 0x65 && s[4] == 0x72 && s[5] == 0x66 && s[6] == 0x61 && s[7] == 0x63 && s[8] == 0x65 {
            Some(Keyword::Interface)
        } else if s[0] == 0x70 && s[1] == 0x72 && s[2] == 0x6F && s[3] == 0x74 && s[4] == 0x65 && s[5] == 0x63 && s[6] == 0x74 && s[7] == 0x65 && s[8] == 0x64 {
            Some(Keyword::Protected)
        } else {
            None
        }
    } else if n == 10 {
        if s[0] == 0x69 && s[1] == 0x6D && s[2] == 0x70 && s[3] == 0x6C && s[4] == 0x65 && s[5] == 0x6D && s[6] == 0x65 && s[7] == 0x6E && s[8] == 0x74 && s[9] == 0x73 {
            Some(Keyword::Implements)
        } else if s[0] == 0x69 && s[1] == 0x6E && s[2] == 0x73 && s[3] == 0x74 && s[4] == 0x61 && s[5] == 0x6E && s[6] == 0x63 && s[7] == 0x65 && s[8] == 0x6F && s[9] == 0x66 {
            Some(Keyword::Instanceof)
        } else {
            None
        }
    } else {
        None
    }
}

pub fn is_unconditional_reserved(kw: Keyword) -> (r: bool)
    ensures
        r == spec_is_unconditional_reserved(kw),
{
    match kw {
        Keyword::Let
        | Keyword::Static
        | Keyword::Yield
        | Keyword::Await
        | Keyword::Async
        | Keyword::Of
        | Keyword::Implements
        | Keyword::Interface
        | Keyword::Package
        | Keyword::Private
        | Keyword::Protected
        | Keyword::Public => false,
        _ => true,
    }
}

pub fn is_strict_reserved_word(kw: Keyword) -> (r: bool)
    ensures
        r == spec_is_strict_reserved_word(kw),
{
    match kw {
        Keyword::Implements
        | Keyword::Interface
        | Keyword::Let
        | Keyword::Package
        | Keyword::Private
        | Keyword::Protected
        | Keyword::Public
        | Keyword::Static
        | Keyword::Yield => true,
        _ => false,
    }
}

pub fn keyword_allowed_as_ident(
    kw: Keyword,
    strict: bool,
    in_async: bool,
    in_generator: bool,
) -> (r: bool)
    ensures
        r == spec_keyword_allowed_as_ident(kw, strict, in_async, in_generator),
{
    if is_unconditional_reserved(kw) {
        false
    } else if strict && is_strict_reserved_word(kw) {
        false
    } else if in_async && kw == Keyword::Await {
        false
    } else if in_generator && kw == Keyword::Yield {
        false
    } else {
        true
    }
}

pub fn is_eval_or_arguments(s: &[u8]) -> (r: bool)
    ensures
        r == spec_is_eval_or_arguments(s@),
{
    (s.len() == 4 && s[0] == 0x65 && s[1] == 0x76 && s[2] == 0x61 && s[3] == 0x6C)
        || (s.len() == 9
            && s[0] == 0x61
            && s[1] == 0x72
            && s[2] == 0x67
            && s[3] == 0x75
            && s[4] == 0x6D
            && s[5] == 0x65
            && s[6] == 0x6E
            && s[7] == 0x74
            && s[8] == 0x73)
}

pub fn is_let_name(s: &[u8]) -> (r: bool)
    ensures
        r == spec_is_let_name(s@),
{
    s.len() == 3 && s[0] == 0x6C && s[1] == 0x65 && s[2] == 0x74
}

/// All punctuators of ECMA-262 §12.8.1 (1- to 4-character tokens).
#[derive(Structural, Clone, Copy, PartialEq, Eq, Debug)]
pub enum Punctuator {
    LBrace,             // {
    RBrace,             // }
    LParen,             // (
    RParen,             // )
    LBracket,           // [
    RBracket,           // ]
    Dot,                // .
    Ellipsis,           // ...
    OptionalChain,      // ?.
    Semicolon,          // ;
    Comma,              // ,
    Lt,                 // <
    Gt,                 // >
    Le,                 // <=
    Ge,                 // >=
    EqEq,               // ==
    Ne,                 // !=
    EqEqEq,             // ===
    NeEq,               // !==
    Plus,               // +
    Minus,              // -
    Star,               // *
    Slash,              // /
    Percent,            // %
    StarStar,           // **
    PlusPlus,           // ++
    MinusMinus,         // --
    Shl,                // <<
    Shr,                // >>
    UShr,               // >>>
    Amp,                // &
    Pipe,               // |
    Caret,              // ^
    Bang,               // !
    Tilde,              // ~
    AmpAmp,             // &&
    PipePipe,           // ||
    QuestionQuestion,   // ??
    Question,           // ?
    Colon,              // :
    Eq,                 // =
    PlusEq,             // +=
    MinusEq,            // -=
    StarEq,             // *=
    SlashEq,            // /=
    PercentEq,          // %=
    StarStarEq,         // **=
    ShlEq,              // <<=
    ShrEq,              // >>=
    UShrEq,             // >>>=
    AmpEq,              // &=
    PipeEq,             // |=
    CaretEq,            // ^=
    AmpAmpEq,           // &&=
    PipePipeEq,         // ||=
    QuestionQuestionEq, // ??=
    Arrow,              // =>
}

/// Lexical & Syntactic diagnostic categories.
#[derive(Structural, Clone, Copy, PartialEq, Eq, Debug)]
pub enum DiagnosticKind {
    UnterminatedComment,
    UnterminatedStringLiteral,
    UnterminatedTemplateLiteral,
    InvalidHexEscape,
    InvalidUnicodeEscape,
    InvalidNumericLiteral,
    NumericFollowedByIdent,
    UnexpectedCharacter,
    InvalidUtf8Encoding,
    LoneSurrogateInSource,
    UnexpectedToken,
    UnexpectedEof,
    MissingSemicolon,
    LineTerminatorInThrow,
    LineTerminatorBeforeArrow,
    UnparenthesizedNullishAndLogicalMix,
    UnaryBeforeExponentiation,
    NewOnOptionalChain,
    ConstWithoutInitializer,
    MultipleDefaultInSwitch,
    TryWithoutCatchOrFinally,
    RestParamNotLast,
    RestParamWithDefault,
    CoverInitializedNameInObject,
    SingleStmtLexicalDecl,
    ModuleDeclarationInScript,
    EarlyDuplicateLexicalName,
    EarlyLexicalVarCollision,
    EarlyDuplicateParamName,
    EarlyDuplicateProtoProperty,
    EarlyStrictReservedWord,
    EarlyStrictEvalOrArgumentsBinding,
    EarlyStrictEvalOrArgumentsAssign,
    EarlyStrictWithStatement,
    EarlyStrictDeleteIdentifier,
    EarlyStrictLegacyOctal,
    EarlyUseStrictWithNonSimpleParams,
    EarlyInvalidAssignmentTarget,
    EarlyDuplicateLabel,
    EarlyUndefinedLabel,
    EarlyNonIterationContinueLabel,
    EarlyInvalidBreak,
    EarlyInvalidContinue,
    EarlyReturnOutsideFunction,
    EarlyNewTargetOutsideFunction,
    EarlyAwaitOutsideAsync,
    EarlyAwaitInFormalParams,
    EarlyYieldOutsideGenerator,
    EarlyYieldInFormalParams,
    EarlyLetBoundInLexicalDecl,
    AstArenaOverflow,
}

/// Diagnostic carrying exact reason and byte span.
#[derive(Structural, Clone, Copy, PartialEq, Eq, Debug)]
pub struct SyntaxDiagnostic {
    pub kind: DiagnosticKind,
    pub span: Span,
}

/// Explicit refusal reasons for ECMAScript constructs outside J3's subset (never silently dropped).
#[derive(Structural, Clone, Copy, PartialEq, Eq, Debug)]
pub enum UnsupportedSyntaxKind {
    ClassSyntax,
    SuperExpression,
    MetaPropertyImportMeta,
    DynamicImport,
    DestructuringPattern,
    TemplateSubstitution,
    TaggedTemplate,
    RegExpLiteral,
    PrivateIdentifier,
    ForAwaitOfOutsideSupported,
    MaxNestingDepthExceeded,
}

#[derive(Structural, Clone, Copy, PartialEq, Eq, Debug)]
pub struct UnsupportedSyntax {
    pub kind: UnsupportedSyntaxKind,
    pub span: Span,
}

/// Executable token payload.
#[derive(Clone, PartialEq, Eq, Debug)]
pub enum TokenKind {
    Ident {
        name: Vec<u8>,
        has_escape: bool,
    },
    Keyword(Keyword),
    Number {
        raw: Vec<u8>,
        is_bigint: bool,
        has_legacy_octal_or_leading_zero: bool,
    },
    StringLit {
        units: Vec<u16>,
        has_legacy_octal_escape: bool,
        is_exact_use_strict: bool,
    },
    NoSubTemplate {
        units: Vec<u16>,
        has_invalid_escape: bool,
    },
    Punct(Punctuator),
    Eof,
}

/// Spec-level view of `TokenKind`.
pub enum SpecTokenKind {
    Ident {
        name: Seq<u8>,
        has_escape: bool,
    },
    Keyword(Keyword),
    Number {
        raw: Seq<u8>,
        is_bigint: bool,
        has_legacy_octal_or_leading_zero: bool,
    },
    StringLit {
        units: Seq<u16>,
        has_legacy_octal_escape: bool,
        is_exact_use_strict: bool,
    },
    NoSubTemplate {
        units: Seq<u16>,
        has_invalid_escape: bool,
    },
    Punct(Punctuator),
    Eof,
}

impl View for TokenKind {
    type V = SpecTokenKind;

    open spec fn view(&self) -> SpecTokenKind {
        match self {
            TokenKind::Ident { name, has_escape } => SpecTokenKind::Ident {
                name: name@,
                has_escape: *has_escape,
            },
            TokenKind::Keyword(kw) => SpecTokenKind::Keyword(*kw),
            TokenKind::Number { raw, is_bigint, has_legacy_octal_or_leading_zero } => {
                SpecTokenKind::Number {
                    raw: raw@,
                    is_bigint: *is_bigint,
                    has_legacy_octal_or_leading_zero: *has_legacy_octal_or_leading_zero,
                }
            },
            TokenKind::StringLit { units, has_legacy_octal_escape, is_exact_use_strict } => {
                SpecTokenKind::StringLit {
                    units: units@,
                    has_legacy_octal_escape: *has_legacy_octal_escape,
                    is_exact_use_strict: *is_exact_use_strict,
                }
            },
            TokenKind::NoSubTemplate { units, has_invalid_escape } => {
                SpecTokenKind::NoSubTemplate {
                    units: units@,
                    has_invalid_escape: *has_invalid_escape,
                }
            },
            TokenKind::Punct(p) => SpecTokenKind::Punct(*p),
            TokenKind::Eof => SpecTokenKind::Eof,
        }
    }
}

/// Executable token with span and ASI line-terminator flag (§12.9).
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct Token {
    pub kind: TokenKind,
    pub span: Span,
    pub preceded_by_line_terminator: bool,
}

/// Spec-level token.
pub struct SpecToken {
    pub kind: SpecTokenKind,
    pub span: Span,
    pub preceded_by_line_terminator: bool,
}

impl View for Token {
    type V = SpecToken;

    open spec fn view(&self) -> SpecToken {
        SpecToken {
            kind: self.kind@,
            span: self.span,
            preceded_by_line_terminator: self.preceded_by_line_terminator,
        }
    }
}

pub open spec fn spec_tokens_view(tokens: Seq<Token>) -> Seq<SpecToken> {
    tokens.map_values(|t: Token| t@)
}

} // verus!
