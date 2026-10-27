import Flapjack.CakeParser.Frontend
import Flapjack.Compiler.Backend.SourceToFlat.ToRiscV
import Flapjack.Compiler.Inference.Infer.Core

/-! Experimental composition of the source parser with the restricted backend.
This bypasses CakeML's type inference and initial basis, and the backend still
has unsupported cases. It is not the original `cake` compiler or a parity claim. -/
namespace Flapjack.Compiler.Backend.SourceToFlat
open Flapjack.Basis.Pure.MlString

inductive UntypedSourceResult where
  | parseExhausted
  | parseRejected
  | backendRejected
  | success : List (BitVec 8) → List (BitVec 64) → Backend.Config → UntypedSourceResult

/-- Connect byte-oriented parsing to the existing restricted RISC-V compiler.
Type checking, basis initialization, diagnostics, and whole-compiler parity
remain to be implemented before this can serve as the CakeML executable. -/
def compileUntypedSourceFuel (lexerFuel parserFuel backendFuel : Nat)
    (config : Backend.Config) (source : List HolChar) : UntypedSourceResult :=
  match CakeParser.Frontend.parseSourceFuel lexerFuel parserFuel source with
  | .exhausted => .parseExhausted
  | .rejected => .parseRejected
  | .success decls => match compileCakeToRiscVConfiguredFuel backendFuel config decls with
    | none => .backendRejected
    | some (bytes, bitmaps, config) => .success bytes bitmaps config


inductive PrimitiveCheckedSourceResult where
  | parseExhausted
  | parseRejected
  | inferenceError : Flapjack.Compiler.Inference.Infer.Core.Error → PrimitiveCheckedSourceResult
  | backendRejected
  | success : List (BitVec 8) → List (BitVec 64) → Backend.Config → PrimitiveCheckedSourceResult

/-- Parse and infer against CakeML's primitive type environment before using
the restricted backend. This does not load the CakeML standard basis, reproduce
original diagnostics, or establish whole-compiler output parity. -/
def compilePrimitiveCheckedSourceFuel (lexerFuel parserFuel inferFuel unifFuel backendFuel : Nat)
    (config : Backend.Config) (source : List HolChar) : PrimitiveCheckedSourceResult :=
  match CakeParser.Frontend.parseSourceFuel lexerFuel parserFuel source with
  | .exhausted => .parseExhausted
  | .rejected => .parseRejected
  | .success decls =>
    match Flapjack.Compiler.Inference.Infer.Core.inferProgramFuel inferFuel unifFuel decls with
    | .error e => .inferenceError e
    | .ok _ => match compileCakeToRiscVConfiguredFuel backendFuel config decls with
      | none => .backendRejected
      | some (bytes, bitmaps, config) => .success bytes bitmaps config

end Flapjack.Compiler.Backend.SourceToFlat
