module

public import Flapjack.Compiler.Backend.LabLang
public import Flapjack.Compiler.Encoders.Asm
public import Flapjack.Basis.Pure.MlString

@[expose] public section

/-! Width-indexed exact carriers for the `labLang` datatypes, instantiating the
generic carriers at HOL's actual payload types. -/
namespace Flapjack.Compiler.Backend.LabLang
open Flapjack.Compiler.Encoders.Asm Flapjack.Basis.Pure.MlString

/-- Exact HOL `labLang$asm_with_lab` at a fixed word width. -/
@[hol "cakeml/compiler/backend/labLangScript.sml" "asm_with_lab"]
abbrev AsmWithLabHOL (width : Nat) [NeZero width] :=
  AsmWithLab HolCmp (HolRegImm width) MlString

/-- Exact HOL `labLang$asm_or_cbw` at a fixed word width. -/
@[hol "cakeml/compiler/backend/labLangScript.sml" "asm_or_cbw"]
abbrev AsmOrCbwHOL (width : Nat) [NeZero width] :=
  AsmOrCbw (HolAsm width) HolMemop (HolAddr width)

/-- Exact HOL `labLang$line` at a fixed word width. -/
@[hol "cakeml/compiler/backend/labLangScript.sml" "line"]
abbrev LineHOL (width : Nat) [NeZero width] :=
  Line (AsmOrCbwHOL width) (AsmWithLabHOL width) (BitVec width)

/-- Exact HOL `labLang$sec` at a fixed word width. -/
@[hol "cakeml/compiler/backend/labLangScript.sml" "sec"]
abbrev SecHOL (width : Nat) [NeZero width] :=
  Section (LineHOL width)

end Flapjack.Compiler.Backend.LabLang
