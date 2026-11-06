import Flapjack.Compiler.Backend.BvlToBvi.Proofs.ApplyOk

/-! Global-operation cases of BVL well-formedness preservation. -/
namespace Flapjack.Compiler.Backend.BvlToBvi.Proofs
open Flapjack.Compiler.Backend.BvlSem (Value State doApp)

namespace GlobalCarrier
/-- Canonical BVL reference-map state roundtrip. -/
theorem holFmapAsFiniteSupportWitness {C F : Type} :
    (∀ s : BvlSem.StateBroad C F, (BvlSem.State.ofBroad s).toBroad = s) ∧
      (∀ s : State C F, BvlSem.State.ofBroad s.toBroad = s) :=
  BvlSem.holFmapAsFiniteSupportWitness
end GlobalCarrier

/-- Reading an initialized global yields a well-formed value. -/
theorem stateOk_getGlobal {C F : Type} (s : State C F) (index : Nat) (value : Value)
    (ok : stateOk s) (read : (s.globals[index]?).join = some value) :
    bvOk s.refs value := by
  cases h : s.globals[index]? with
  | none => simp [h] at read
  | some item =>
    cases item with
    | none => simp [h] at read
    | some item =>
      simp [h] at read
      subst value
      exact ok.1 (some item) (List.mem_of_getElem? h)

/-- Writing a well-formed value keeps the global portion of a valid state valid. -/
theorem stateOk_setGlobal {C F : Type} (s : State C F) (index : Nat) (value : Value)
    (ok : stateOk s) (valueOk : bvOk s.refs value) :
    stateOk { s with globals := s.globals.set index (some value) } := by
  constructor
  · intro item member
    rcases List.mem_or_eq_of_mem_set member with old | fresh
    · exact ok.1 item old
    · subst item
      exact valueOk
  · exact ok.2

/-- Extending the global array with uninitialized entries preserves validity. -/
theorem stateOk_allocGlobal {C F : Type} (s : State C F) (count : Nat)
    (ok : stateOk s) :
    stateOk { s with globals := s.globals ++ List.replicate count none } := by
  constructor
  · intro item member
    rcases List.mem_append.mp member with old | fresh
    · exact ok.1 item old
    · have eq := List.eq_of_mem_replicate fresh
      subst item
      trivial
  · exact ok.2

/-- Global-operation case of primitive application. -/
@[hol "cakeml/compiler/backend/proofs/bvl_to_bviProofScript.sml" "do_app_ok"
  (fmap_as_finite_support := [refs])]
theorem doApp_ok_global {C F : Type} (op : ClosLang.GlobOp)
    (args env : List Value) (s t : Flapjack.Compiler.Backend.BvlSem.State C F) (value : Value)
    (ok : stateOk s) (argsOk : bvOkList s.refs args)
    (run : doApp (.globOp op) args s = .val (value, t)) :
    stateOk t ∧ bvOk t.refs value ∧ (bvOkList s.refs env → bvOkList t.refs env) := by
  simp only [doApp] at run
  cases h : BvlSem.applyGlobal op args s with
  | none => simp [h] at run
  | some pair =>
    cases pair with
    | mk result next =>
      simp only [h, Flapjack.SemanticPrimitivesHOL.Result.val.injEq, Prod.mk.injEq] at run
      rcases run with ⟨rfl, rfl⟩
      unfold BvlSem.applyGlobal at h
      repeat' first | split at h | contradiction
      all_goals simp_all [bvOk, bvOkList, BvlSem.unitValue]
      all_goals rcases h with ⟨hval, hstate⟩
      all_goals subst next
      all_goals try exact stateOk_getGlobal s _ result ok hval
      all_goals subst result
      all_goals first
        | exact ⟨stateOk_setGlobal s _ _ ok argsOk, by simp [bvOk, bvOkList], id⟩
        | exact ⟨stateOk_allocGlobal s _ ok, by simp [bvOk, bvOkList], id⟩

end Flapjack.Compiler.Backend.BvlToBvi.Proofs
