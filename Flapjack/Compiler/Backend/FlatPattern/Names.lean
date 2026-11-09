import Flapjack.Compiler.Backend.FlatPattern.Config
import Flapjack.Compiler.Backend.FlatLang
import Flapjack.Basis.Pure.MlString

/-! Generated-name encoding used by CakeML's flat pattern compiler. -/

namespace Flapjack.Compiler.Backend.FlatPattern
open Flapjack.Basis.Pure.MlString

/-- Sum the character offsets from position `i` to the end of the HOL string.
The executable closed form is HOL's proved `sum_string_ords_eq`; the HOL
definition itself is recursive over string indices. -/
@[hol "cakeml/compiler/backend/flat_patternScript.sml" "sum_string_ords_def"]
def sumStringOrds (i : Nat) (str : MlString) : Nat :=
  ((str.explode.drop i).map (fun c => c.toNat - 35)).foldr (· + ·) 0

/-- Decode the reserved `..` name prefix; other names decode to zero. The HOL
index tests agree with this list match, as replayed in the HOL probe. -/
@[hol "cakeml/compiler/backend/flat_patternScript.sml" "dec_name_to_num_def"]
def decNameToNum (name : MlString) : Nat :=
  match name.explode with
  | a :: b :: _ => if a = 46 && b = 46 then sumStringOrds 2 name else 0
  | _ => 0

/-- The executable sum satisfies HOL's index-recursive equation. This is a
Flapjack correspondence witness for the tagged definition, not a separate
HOL theorem. -/
theorem sumStringOrds_indexEquation (i : Nat) (str : MlString) :
    sumStringOrds i str =
      if h : i < str.explode.length then
        (str.explode[i]'h).toNat - 35 + sumStringOrds (i + 1) str
      else 0 := by
  by_cases h : i < str.explode.length
  · simp only [dif_pos h, sumStringOrds]
    rw [List.drop_eq_getElem_cons h]
    rfl
  · simp [h, sumStringOrds, List.drop_eq_nil_of_le (Nat.le_of_not_gt h)]

/-- The executable decoder satisfies HOL's length and indexed-byte tests. This
is a Flapjack correspondence witness for the tagged definition, not a
separate HOL theorem. -/
theorem decNameToNum_indexEquation (name : MlString) :
    decNameToNum name =
      if h : name.explode.length < 2 then 0
      else if name.explode[0]'(by omega) = 46 ∧ name.explode[1]'(by omega) = 46 then
        sumStringOrds 2 name
      else 0 := by
  cases name with
  | implode chars =>
    cases chars with
    | nil => rfl
    | cons a rest =>
      cases rest with
      | nil => rfl
      | cons b tail =>
        by_cases ha : a = 46 <;> by_cases hb : b = 46 <;>
          simp [decNameToNum, MlString.explode, ha, hb,
            show ¬ tail.length + 1 + 1 < 2 by omega]
        all_goals split <;> simp_all

/-- Encode a number into the original byte-string name representation. In the
base case `i + 35 < 256`, so the byte construction agrees with HOL `CHR`. -/
@[hol "cakeml/compiler/backend/flat_patternScript.sml" "enc_num_to_name_aux_def"]
def encNumToNameAux (i : Nat) (xs : List HolChar) : List HolChar :=
  if i < 90 then 46 :: 46 :: BitVec.ofNat 8 (i + 35) :: xs
  else encNumToNameAux (i - 90) (125 :: xs)
termination_by i
decreasing_by omega

/-- Produce the `mlstring` used for a compiler-generated name. -/
@[hol "cakeml/compiler/backend/flat_patternScript.sml" "enc_num_to_name_def"]
def encNumToName (i : Nat) : MlString := .implode (encNumToNameAux i [])

/-- Largest generated-name index in a list of names. -/
@[hol "cakeml/compiler/backend/flat_patternScript.sml" "max_dec_name_def"]
def maxDecName : List MlString → Nat
  | [] => 0
  | name :: names => max (decNameToNum name) (maxDecName names)

/-- Only global initialization is classified as setting globals. -/
@[hol "cakeml/compiler/backend/flat_patternScript.sml" "op_sets_globals_def"]
def opSetsGlobals : FlatLang.Op → Bool
  | .globalVarInit _ => true
  | _ => false

end Flapjack.Compiler.Backend.FlatPattern
