import Flapjack.Compiler.Backend.PresLang.Asm
import Flapjack.Compiler.Backend.PresLang.Clos
import Flapjack.Compiler.Backend.LabLang

/-! Labelled-assembly explorer display, following the `lab_*_to_display_def`
and `lab_to_strs_def` definitions in `presLangScript.sml`. The representation
uses the existing generic Lean assembly carriers and String-backed display
tree, so it is untagged pending representation review. The explorer driver
does not yet execute it. -/
namespace Flapjack.Compiler.Backend.PresLang.Lab
open Flapjack.Basis.Pure.MlString Flapjack.Compiler.Backend
open Flapjack.Compiler.Encoders.Asm

abbrev Operation (width : Nat) := LabLang.AsmWithLab Cmp (WordRegImm (BitVec width)) MlString
abbrev Instruction (width : Nat) := LabLang.AsmOrCbw (AsmData width) WordMemOp (WordLangAddr (BitVec width))
abbrev Line (width : Nat) := LabLang.Line (Instruction width) (Operation width) (BitVec width)
abbrev Section (width : Nat) := LabLang.Section (Line width)

private def item (name : String) (xs : List DisplayExpr) : DisplayExpr := .item none name xs
private def number (n : Nat) : DisplayExpr := .string (toString n)
private def label (names : Spt MlString) (sec : Nat) : DisplayExpr :=
  .string (Clos.attachName names (some sec))

/-- Render a labelled branch or FFI operation. -/
def operation (names : Spt MlString) : Operation width → DisplayExpr
  | .jump (.lab s n) => item "jump" [label names s, number n]
  | .jumpCmp cmp r imm (.lab s n) => item "jump_cmp"
      [.tuple [Asm.comparison cmp, number r, Asm.regImm imm], label names s, number n]
  | .call (.lab s n) => item "call" [label names s, number n]
  | .locValue r (.lab s n) => item "loc_value" [number r, label names s, number n]
  | .callFFI name => item "call_FFI" [.string (Source.byteString name)]
  | .install => .string "install"
  | .halt => .string "halt"

/-- Render a LabLang line; machine encoding and location metadata are
intentionally omitted, as in the original explorer. -/
def line (names : Spt MlString) : Line width → DisplayExpr
  | .label s n _ => item "label" [label names s, number n]
  | .asm (.asmi inst) _ _ => item "asm" [Asm.assembly inst]
  | .asm (.cbw a b) _ _ => item "cbw" [number a, number b]
  | .asm (.shareMem op r addr) _ _ => item "share_mem" [Asm.memoryOp op, number r, Asm.address addr]
  | .labAsm op _ _ _ => operation names op

/-- Render sections in order using the original two-newline separator. -/
def sections (names : Spt MlString) (ss : List (Section width)) : List String :=
  mapAppendDisplayStrings (fun sec =>
    displayStrTreeToStrings "\n\n" (displayToStrTree
      (.list (label names sec.sectionId :: sec.lines.map (line names))))) ss

/-- Encode byte-valued display characters as original CakeML bytes. -/
def sectionBytes (names : Spt MlString) (ss : List (Section width)) : List HolChar :=
  (sections names ss).flatMap fun fragment => fragment.toList.map (fun c => BitVec.ofNat 8 c.toNat)

end Flapjack.Compiler.Backend.PresLang.Lab
