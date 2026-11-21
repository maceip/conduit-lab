//! `vjs_vm`: Verified JS Bytecode Compiler and Stack VM (J7 of `vjs`, `docs/verified-browser-engine.md` §3.3).
//!
//! Proves:
//! 1. Executable AST evaluator refines `spec_eval_program`.
//! 2. Executable bytecode compiler refines `spec_compile_program`.
//! 3. Executable stack VM refines `spec_run_vm`.
//! 4. Machine-checked CompCert/CakeML-style compiler simulation theorem (`compiler_proof`):
//!    - Code-composition and arbitrary-bottom-stack / call-stack preservation for expressions
//!      and statements (`lemma_compile_expr_sim`, `lemma_compile_stmt_sim`).
//!    - Top-level semantic preservation: `spec_run_vm(spec_compile_program(p), ...) == spec_eval_program(p, ...)`.
//!    - End-to-end executable equivalence between AST evaluation and compiled bytecode execution.
#![forbid(unsafe_code)]

pub mod ast;
pub mod bytecode;
pub mod compiler;
pub mod compiler_proof;
