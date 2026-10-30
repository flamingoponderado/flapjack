import Flapjack.Compiler.Backend.BvlToBvi.Proofs.BuildOk

/-! Primitive-application cases of BVL well-formedness preservation. -/
namespace Flapjack.Compiler.Backend.BvlToBvi.Proofs
open Flapjack.Compiler.Backend.BvlSem (Value Ref State doApp)

namespace ApplyCarrier
/-- Canonical BVL reference-map state roundtrip. -/
theorem holFmapAsFiniteSupportWitness {C F : Type} :
    (∀ s : BvlSem.StateBroad C F, (BvlSem.State.ofBroad s).toBroad = s) ∧
      (∀ s : State C F, BvlSem.State.ofBroad s.toBroad = s) :=
  BvlSem.holFmapAsFiniteSupportWitness
end ApplyCarrier

/-- Constant-building case of primitive application. It preserves state and
result well-formedness, as well as any previously valid environment. -/
@[hol "cakeml/compiler/backend/proofs/bvl_to_bviProofScript.sml" "do_app_ok"
  (fmap_as_finite_support := [refs])]
theorem doApp_ok_build {C F : Type} (parts : List ClosLang.ConstPart)
    (args env : List Value) (s t : Flapjack.Compiler.Backend.BvlSem.State C F) (value : Value)
    (ok : stateOk s) (_argsOk : bvOkList s.refs args)
    (run : doApp (.blockOp (.build parts)) args s = .val (value, t)) :
    stateOk t ∧ bvOk t.refs value ∧ (bvOkList s.refs env → bvOkList t.refs env) := by
  have subset := BvlProps.doApp_refs_mono (.blockOp (.build parts)) args s t value run
  have preserve := fun envOk => bvOkList_domain_mono s.refs env t.refs envOk subset
  cases args with
  | nil =>
    rcases h : BvlSem.doBuildConst parts s.refs with ⟨built, refs⟩
    simp only [doApp, BvlSem.applyBlock, h,
      Flapjack.SemanticPrimitivesHOL.Result.val.injEq, Prod.mk.injEq] at run
    rcases run with ⟨rfl, rfl⟩
    have builtOk := doBuild_ok parts (fun _ => .number 0) 0 s built refs h ok (by
      intro k
      simp [bvOk])
    exact ⟨builtOk.1, builtOk.2, preserve⟩
  | cons head tail =>
    simp [doApp, BvlSem.applyBlock] at run

/-- Code-label case of primitive application. -/
@[hol "cakeml/compiler/backend/proofs/bvl_to_bviProofScript.sml" "do_app_ok"
  (fmap_as_finite_support := [refs])]
theorem doApp_ok_label {C F : Type} (index : Nat)
    (args env : List Value) (s t : Flapjack.Compiler.Backend.BvlSem.State C F) (value : Value)
    (ok : stateOk s) (_argsOk : bvOkList s.refs args)
    (run : doApp (.label index) args s = .val (value, t)) :
    stateOk t ∧ bvOk t.refs value ∧ (bvOkList s.refs env → bvOkList t.refs env) := by
  simp only [doApp] at run
  split at run
  · simp only [Flapjack.SemanticPrimitivesHOL.Result.val.injEq, Prod.mk.injEq] at run
    rcases run with ⟨rfl, rfl⟩
    exact ⟨ok, by simp [bvOk], id⟩
  · contradiction

/-- Code-installation case of primitive application. -/
@[hol "cakeml/compiler/backend/proofs/bvl_to_bviProofScript.sml" "do_app_ok"
  (fmap_as_finite_support := [refs])]
theorem doApp_ok_install {C F : Type}
    (args env : List Value) (s t : Flapjack.Compiler.Backend.BvlSem.State C F) (value : Value)
    (ok : stateOk s) (_argsOk : bvOkList s.refs args)
    (run : doApp .install args s = .val (value, t)) :
    stateOk t ∧ bvOk t.refs value ∧ (bvOkList s.refs env → bvOkList t.refs env) := by
  simp only [doApp, BvlSem.doInstall] at run
  repeat' first | split at run | contradiction
  all_goals simp only [Flapjack.SemanticPrimitivesHOL.Result.val.injEq, Prod.mk.injEq] at run
  all_goals rcases run with ⟨rfl, rfl⟩
  all_goals exact ⟨ok, by simp [bvOk], id⟩

/-- FFI case of primitive application. -/
@[hol "cakeml/compiler/backend/proofs/bvl_to_bviProofScript.sml" "do_app_ok"
  (fmap_as_finite_support := [refs])]
theorem doApp_ok_ffi {C F : Type} (name : Flapjack.Basis.Pure.MlString.MlString)
    (args env : List Value) (s t : Flapjack.Compiler.Backend.BvlSem.State C F) (value : Value)
    (ok : stateOk s) (_argsOk : bvOkList s.refs args)
    (run : doApp (.ffi name) args s = .val (value, t)) :
    stateOk t ∧ bvOk t.refs value ∧ (bvOkList s.refs env → bvOkList t.refs env) := by
  have subset := BvlProps.doApp_refs_mono (.ffi name) args s t value run
  have preserve := fun envOk => bvOkList_domain_mono s.refs env t.refs envOk subset
  simp only [doApp] at run
  repeat' first | split at run | contradiction
  all_goals simp only [Flapjack.SemanticPrimitivesHOL.Result.val.injEq, Prod.mk.injEq] at run
  all_goals rcases run with ⟨rfl, rfl⟩
  all_goals exact ⟨stateOk_updateByteArray _ _ _ _ ok, by simp [bvOk, bvOkList, BvlSem.unitValue], preserve⟩

/-- Integer-operation case of primitive application. -/
@[hol "cakeml/compiler/backend/proofs/bvl_to_bviProofScript.sml" "do_app_ok"
  (fmap_as_finite_support := [refs])]
theorem doApp_ok_int {C F : Type} (op : ClosLang.IntOp)
    (args env : List Value) (s t : Flapjack.Compiler.Backend.BvlSem.State C F) (value : Value)
    (ok : stateOk s) (_argsOk : bvOkList s.refs args)
    (run : doApp (.intOp op) args s = .val (value, t)) :
    stateOk t ∧ bvOk t.refs value ∧ (bvOkList s.refs env → bvOkList t.refs env) := by
  simp only [doApp, BvlSem.applyNumeric] at run
  cases h : BvlSem.doIntApp op args with
  | none => simp [h] at run
  | some result =>
    simp only [h, Option.map, Flapjack.SemanticPrimitivesHOL.Result.val.injEq, Prod.mk.injEq] at run
    rcases run with ⟨rfl, rfl⟩
    have resultOk : bvOk s.refs result := by
      unfold BvlSem.doIntApp at h
      repeat' first | split at h | contradiction
      all_goals try simp only [Option.some.injEq] at h
      all_goals subst result
      all_goals simp [bvOk, bvOkList, BvlSem.boolValue]
    exact ⟨ok, resultOk, id⟩

/-- Word-operation case of primitive application. -/
@[hol "cakeml/compiler/backend/proofs/bvl_to_bviProofScript.sml" "do_app_ok"
  (fmap_as_finite_support := [refs])]
theorem doApp_ok_word {C F : Type} (op : ClosLang.WordOp)
    (args env : List Value) (s t : Flapjack.Compiler.Backend.BvlSem.State C F) (value : Value)
    (ok : stateOk s) (_argsOk : bvOkList s.refs args)
    (run : doApp (.wordOp op) args s = .val (value, t)) :
    stateOk t ∧ bvOk t.refs value ∧ (bvOkList s.refs env → bvOkList t.refs env) := by
  simp only [doApp, BvlSem.applyNumeric] at run
  cases h : BvlSem.doWordApp op args with
  | none => simp [h] at run
  | some result =>
    simp only [h, Option.map, Flapjack.SemanticPrimitivesHOL.Result.val.injEq, Prod.mk.injEq] at run
    rcases run with ⟨rfl, rfl⟩
    have resultOk : bvOk s.refs result := by
      unfold BvlSem.doWordApp at h
      repeat' split at h
      all_goals try (simp only [Option.some.injEq] at h; subst result; simp [bvOk, bvOkList, BvlSem.boolValue])
      all_goals unfold BvlSem.doWordAppIntegral at h
      all_goals repeat' first | split at h | contradiction
      all_goals try dsimp only [bind, Option.bind, pure] at h
      all_goals try split at h
      all_goals try contradiction
      all_goals try dsimp only [bind, Option.bind, pure] at h
      all_goals try split at h
      all_goals try contradiction
      all_goals try dsimp only [pure] at h
      all_goals try simp only [Option.some.injEq] at h
      all_goals subst result
      all_goals simp [bvOk, bvOkList, BvlSem.boolValue]
    exact ⟨ok, resultOk, id⟩

end Flapjack.Compiler.Backend.BvlToBvi.Proofs
