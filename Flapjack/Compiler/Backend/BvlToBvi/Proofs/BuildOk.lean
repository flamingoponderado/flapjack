import Flapjack.Compiler.Backend.BvlToBvi.Proofs.StateOk
import Flapjack.Compiler.Backend.BvlToBvi.Proofs.ValueOk
import Flapjack.Compiler.Backend.Semantics.BvlProps.BuildRefs

/-! Well-formedness during source constant construction. -/
namespace Flapjack.Compiler.Backend.BvlToBvi.Proofs
open Flapjack.Compiler.Backend.BvlSem (Value Ref State doPart doBuild)

namespace BuildCarrier
/-- Canonical BVL reference-map state roundtrip. -/
theorem holFmapAsFiniteSupportRelationWitness_State {C F : Type} :
    (∀ s : BvlSem.StateBroad C F, (BvlSem.State.ofBroad s).toBroad = s) ∧
      (∀ s : State C F, BvlSem.State.ofBroad s.toBroad = s) :=
  BvlSem.holFmapAsFiniteSupportWitness
end BuildCarrier

/-- Replacing or allocating a byte array keeps existing well-formed source
values valid and introduces no new values requiring validation. -/
theorem stateOk_updateByteArray {C F : Type} (s : BvlSem.State C F)
    (key : Nat) (flag : Bool) (bytes : List (BitVec 8)) (ok : stateOk s) :
    stateOk { s with refs := s.refs.updateEq (key, .byteArray flag bytes) } := by
  let refs := s.refs.updateEq (key, .byteArray flag bytes)
  have subset : ∀ k, s.refs.lookup k ≠ none → refs.lookup k ≠ none := by
    intro k present
    exact BvlProps.refs_update_mono s.refs key k (.byteArray flag bytes) present
  constructor
  · intro item member
    have original := ok.1 item member
    cases item with
    | none => trivial
    | some value => exact bvOk_domain_mono s.refs value refs original subset
  · intro k
    by_cases eq : k = key
    · simp [HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL, eq]
    · have prior := ok.2 k
      have lookup : refs.lookup k = s.refs.lookup k := by
        simp [refs, HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL, eq]
      rw [lookup]
      cases h : s.refs.lookup k with
      | none => trivial
      | some ref =>
        cases ref with
        | valueArray values =>
          simp only [h] at prior
          exact bvOkList_domain_mono s.refs values refs prior subset
        | thunk code value =>
          simp only [h] at prior
          exact bvOk_domain_mono s.refs value refs prior subset
        | _ => trivial

/-- A constant part preserves state well-formedness and returns a value valid
in its resulting reference domain. -/
theorem doPart_ok {C F : Type} (m : Nat → Value) (part : ClosLang.ConstPart)
    (s : BvlSem.State C F) (ok : stateOk s)
    (valuesOk : ∀ k, bvOk s.refs (m k)) :
    stateOk { s with refs := (doPart m part s.refs).2 } ∧
      bvOk (doPart m part s.refs).2 (doPart m part s.refs).1 := by
  cases part with
  | int value => simpa [doPart, bvOk] using ok
  | w64 value => simpa [doPart, bvOk] using ok
  | con tag indices =>
    constructor
    · simpa [doPart] using ok
    · simp only [doPart, bvOk]
      apply (bvOkList_iff s.refs _).2
      intro value member
      obtain ⟨index, _, rfl⟩ := List.mem_map.mp member
      exact valuesOk index
  | str text =>
    constructor
    · simpa [doPart] using stateOk_updateByteArray s (BvlSem.leastUnusedRef s.refs) true text.explode ok
    · simp [doPart, bvOk, HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL]

/-- Sequential constant construction preserves source-state well-formedness
and returns a well-formed value. -/
@[hol "cakeml/compiler/backend/proofs/bvl_to_bviProofScript.sml" "do_build_ok"
  (fmap_as_finite_support_relation := [State.refs, refs])]
theorem doBuild_ok {C F : Type} (parts : List ClosLang.ConstPart) (m : Nat → Value)
    (index : Nat) (s : State C F) (value : Value)
    (refs : HolFiniteMapExact Nat (Ref Value))
    (run : doBuild m index parts s.refs = (value, refs))
    (ok : stateOk s) (valuesOk : ∀ k, bvOk s.refs (m k)) :
    stateOk { s with refs := refs } ∧ bvOk refs value := by
  induction parts generalizing m index s with
  | nil =>
    simp only [doBuild, Prod.mk.injEq] at run
    rcases run with ⟨rfl, rfl⟩
    exact ⟨ok, valuesOk _⟩
  | cons part parts ih =>
    rcases h : doPart m part s.refs with ⟨partValue, nextRefs⟩
    have partOk := doPart_ok m part s ok valuesOk
    rw [h] at partOk
    have subset : ∀ key, s.refs.lookup key ≠ none → nextRefs.lookup key ≠ none := by
      intro key present
      have growth := BvlProps.doPart_refs_mono m part s.refs key present
      simpa [h] using growth
    have newValuesOk : ∀ k, bvOk nextRefs (if k = index then partValue else m k) := by
      intro k
      split
      · exact partOk.2
      · exact bvOk_domain_mono s.refs (m k) nextRefs (valuesOk k) subset
    have tailRun : doBuild (fun k => if k = index then partValue else m k)
        (index + 1) parts nextRefs = (value, refs) := by
      simpa [doBuild, h] using run
    have tail := ih (fun k => if k = index then partValue else m k) (index + 1)
      { s with refs := nextRefs } tailRun partOk.1 newValuesOk
    simpa using tail

end Flapjack.Compiler.Backend.BvlToBvi.Proofs
