import Flapjack.Compiler.Backend.Semantics.BvlSem.Build

/-! Reference-domain growth during BVL constant construction. -/
namespace Flapjack.Compiler.Backend.BvlProps
open Flapjack.Compiler.Backend.BvlSem (Value Ref doPart doBuild)

/-- Constructing one constant part does not deallocate references. This is
Flapjack infrastructure for the original constant-building domain lemma. -/
theorem doPart_refs_mono (m : Nat → Value) (part : ClosLang.ConstPart)
    (refs : HolFiniteMapExact Nat (Ref Value)) (key : Nat)
    (present : refs.lookup key ≠ none) : (doPart m part refs).2.lookup key ≠ none := by
  cases part with
  | str text =>
    simp only [doPart, HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL]
    split <;> simp_all
  | _ => simpa [doPart] using present

/-- The source-shaped constant builder preserves its input reference domain.
This remains untagged while the finite-map product result of `doBuild` has no
reviewed representation qualifier. -/
theorem doBuild_refs_mono (parts : List ClosLang.ConstPart) (m : Nat → Value) (index : Nat)
    (refs : HolFiniteMapExact Nat (Ref Value)) (key : Nat)
    (present : refs.lookup key ≠ none) : (doBuild m index parts refs).2.lookup key ≠ none := by
  induction parts generalizing m index refs with
  | nil => simpa [doBuild] using present
  | cons part parts ih =>
    rcases h : doPart m part refs with ⟨value, next⟩
    have preserved := doPart_refs_mono m part refs key present
    rw [h] at preserved
    have tail := ih (fun k => if k = index then value else m k) (index + 1) next preserved
    simpa [doBuild, h] using tail

/-- Building a constant from the zero-valued initial environment also
preserves its input reference domain. -/
theorem doBuildConst_refs_mono (parts : List ClosLang.ConstPart)
    (refs : HolFiniteMapExact Nat (Ref Value)) (key : Nat)
    (present : refs.lookup key ≠ none) :
    (BvlSem.doBuildConst parts refs).2.lookup key ≠ none :=
  doBuild_refs_mono parts (fun _ => .number 0) 0 refs key present

end Flapjack.Compiler.Backend.BvlProps
