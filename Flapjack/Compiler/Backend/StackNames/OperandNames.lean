import Flapjack.Compiler.Backend.StackNames

namespace Flapjack.Compiler.Backend.StackNames
open Flapjack.Compiler.Encoders.Asm

/-- Local projection of HOL tlookup: missing keys retain the original register.
This is infrastructure for the exact Spt-based naming definitions. -/
def findNameSpt (names : Flapjack.Spt Nat) (register : Nat) : Nat :=
  (Flapjack.sptLookup register names).getD register

@[hol "cakeml/compiler/backend/stack_namesScript.sml" "ri_find_name_def"
  (words_as_type_indexed_bitvec)]
def riFindNameHOL {width : Nat} [NeZero width] (names : Flapjack.Spt Nat) :
    HolRegImm width → HolRegImm width
  | .reg register => .reg (findNameSpt names register)
  | .imm value => .imm value

@[hol "cakeml/compiler/backend/stack_namesScript.sml" "dest_find_name_def"]
def destFindNameHOL (names : Flapjack.Spt Nat) : Sum Nat Nat → Sum Nat Nat
  | .inr register => .inr (findNameSpt names register)
  | other => other

/-- Flapjack helper correspondence, not a separate HOL declaration. -/
theorem findNameSpt_eq_lookupHelper (names : Flapjack.Spt Nat) (r : Nat) :
    findNameSpt names r = findName (fun key => Flapjack.sptLookup key names) r := by
  unfold findNameSpt findName Flapjack.FLOOKUP
  dsimp only
  cases Flapjack.sptLookup r names <;> rfl

/-- Unconditional operand codec correspondence; exact carrier migration of the
core naming compiler remains open under .15.7.7. -/
theorem riFindNameHOL_toWord {width : Nat} [NeZero width]
    (names : Flapjack.Spt Nat) (operand : HolRegImm width) :
    HolRegImm.toWordRegImm (riFindNameHOL names operand) =
      riFindName (fun key => Flapjack.sptLookup key names) (HolRegImm.toWordRegImm operand) := by
  cases operand <;> simp [riFindNameHOL, riFindName, HolRegImm.toWordRegImm, findNameSpt_eq_lookupHelper]

/-- Unconditional sum-operand correspondence, not an executed-route claim. -/
theorem destFindNameHOL_eq_lookupHelper (names : Flapjack.Spt Nat) (operand : Sum Nat Nat) :
    destFindNameHOL names operand = destFindName (fun key => Flapjack.sptLookup key names) operand := by
  cases operand <;> simp [destFindNameHOL, destFindName, findNameSpt_eq_lookupHelper]

end Flapjack.Compiler.Backend.StackNames
