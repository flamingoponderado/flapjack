module

public import Flapjack.Compiler.Backend.ClosCall.Compile
public import Flapjack.FiniteMap.UpdateListExact
public import Flapjack.Misc.ShiftSeq

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

/-! Code installed by successive direct-call compiler oracle entries. -/
namespace Flapjack.Compiler.Backend.ClosCall
open Flapjack

/-- The code map after compiling the first `k` oracle entries. -/
@[hol "cakeml/compiler/backend/proofs/clos_callProofScript.sml" "nth_code_def"
  (fmap_as_finite_support_result)]
noncomputable def nthCode {A B : Type}
    (code : HolFiniteMapExact Nat (Nat × ClosLang.Exp))
    (co : Nat → (NumSet × A) × List ClosLang.Exp × B) : Nat → HolFiniteMapExact Nat (Nat × ClosLang.Exp)
  | 0 => code
  | k + 1 =>
      let entry := co 0
      let compiled := compileInc entry.1.1 (entry.2.1, entry.2.2)
      nthCode (HolFiniteMapExact.holUpdateList code compiled.2.2) (holShiftSeq 1 co) k

/-- Independent raw lookup fold used to check the canonical map representation. -/
private noncomputable def nthCodeRaw {A B : Type}
    (code : Nat → Option (Nat × ClosLang.Exp))
    (co : Nat → (NumSet × A) × List ClosLang.Exp × B) : Nat → Nat → Option (Nat × ClosLang.Exp)
  | 0 => code
  | k + 1 =>
      let entry := co 0
      let compiled := compileInc entry.1.1 (entry.2.1, entry.2.2)
      nthCodeRaw (@FUPDATE_LIST_HOL Nat (Nat × ClosLang.Exp) (Classical.typeDecidableEq Nat) code compiled.2.2)
        (holShiftSeq 1 co) k

/-- Lookup of the canonical map agrees with the raw update fold. -/
theorem holFmapAsFiniteSupportResultWitness_nthCode {A B : Type}
    (code : HolFiniteMapExact Nat (Nat × ClosLang.Exp))
    (co : Nat → (NumSet × A) × List ClosLang.Exp × B) (k key : Nat) :
    (nthCode code co k).lookup key = nthCodeRaw code.lookup co k key := by
  induction k generalizing code co with
  | zero => rfl
  | succ k ih =>
    simp only [nthCode, nthCodeRaw]
    rw [ih]
    rfl

end Flapjack.Compiler.Backend.ClosCall
