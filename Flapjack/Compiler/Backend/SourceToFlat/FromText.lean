import Flapjack.CakeParser.Frontend
import Flapjack.Compiler.Backend.SourceToFlat.ToRiscV

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

end Flapjack.Compiler.Backend.SourceToFlat
