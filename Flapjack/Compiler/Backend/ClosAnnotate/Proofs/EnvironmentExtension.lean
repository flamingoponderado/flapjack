module

public import Flapjack.Compiler.Backend.ClosAnnotate.Proofs.ValueRelation

@[expose] public section

/-! Extending related closure environments with newly bound values. -/
namespace Flapjack.Compiler.Backend.ClosAnnotate
open Flapjack.Compiler.Backend.ClosSem

private theorem holEl_append_left (front tail : List Value) (index : Nat) (bound : index < front.length) :
    @Flapjack.holEl Value ⟨unitValue⟩ index (front ++ tail) =
      @Flapjack.holEl Value ⟨unitValue⟩ index front := by
  let _ : Nonempty Value := ⟨unitValue⟩
  rw [Flapjack.holEl_eq_getElem _ _ (by simp; omega), Flapjack.holEl_eq_getElem _ _ bound]
  simp [List.getElem_append_left, bound]

private theorem holEl_append_right (front tail : List Value) (index : Nat) (bound : index < tail.length) :
    @Flapjack.holEl Value ⟨unitValue⟩ (front.length + index) (front ++ tail) =
      @Flapjack.holEl Value ⟨unitValue⟩ index tail := by
  let _ : Nonempty Value := ⟨unitValue⟩
  rw [Flapjack.holEl_eq_getElem _ _ (by simp; omega), Flapjack.holEl_eq_getElem _ _ bound]
  simp [List.getElem_append_right]

/-- Adding equal-length prefixes preserves an environment relation beyond
the prefixes, without requiring their elements to be related. -/
@[hol "cakeml/compiler/backend/proofs/clos_annotateProofScript.sml" "env_ok_EXTEND_IGNORE"
  (nested_list_rel_as_mutual := [FunctionsRel])]
theorem envOk_extend_ignore (nextFront front : List Value) (n prefixLength m l : Nat) (index : Spt Nat)
    (env nextEnv : List Value)
    (h : nextFront.length = front.length ∧ front.length ≤ n ∧ prefixLength = front.length ∧
      EnvOk m l index env nextEnv (n - prefixLength)) :
    EnvOk m (l + prefixLength) index (front ++ env) (nextFront ++ nextEnv) n := by
  obtain ⟨sameLength, beyond, rfl, related⟩ := h
  have decomposition : n = front.length + (n - front.length) := by omega
  rw [decomposition]
  cases related with
  | outside _ _ _ _ _ _ outside =>
    exact .outside _ _ _ _ _ _ (by omega)
  | «local» _ _ _ _ _ _ below valueRel sourceBound targetBound =>
    apply EnvOk.local m (l + front.length) index (front ++ env) (nextFront ++ nextEnv)
      (front.length + _) (by omega)
    · rw [holEl_append_right front env _ sourceBound]
      have : front.length + (n - front.length) = nextFront.length + (n - front.length) := by omega
      rw [this, holEl_append_right nextFront nextEnv _ targetBound]
      exact valueRel
    · simp only [List.length_append]; omega
    · simp only [List.length_append]; omega
  | captured _ _ _ _ _ _ compact above below _ lookup sourceBound targetBound valueRel =>
    apply EnvOk.captured m (l + front.length) index (front ++ env) (nextFront ++ nextEnv)
      (front.length + _) compact (by omega) (by omega) (by omega)
    · have sameIndex : front.length + (n - front.length) - (l + front.length) = n - front.length - l := by omega
      simpa [sameIndex] using lookup
    · simp only [List.length_append]; omega
    · simp only [List.length_append]; omega
    · rw [holEl_append_right front env _ sourceBound]
      have sameIndex : l + front.length + compact = nextFront.length + (l + compact) := by omega
      rw [sameIndex, holEl_append_right nextFront nextEnv _ targetBound]
      exact valueRel

/-- Prepending related bindings extends the local prefix while preserving
the compact mapping of all previously bound variables. -/
@[hol "cakeml/compiler/backend/proofs/clos_annotateProofScript.sml" "env_ok_EXTEND"
  (nested_list_rel_as_mutual := [FunctionsRel])]
theorem envOk_extend (front nextFront : List Value) (prefixLength n m l : Nat) (index : Spt Nat)
    (env nextEnv : List Value)
    (h : List.Forall₂ ValueRel front nextFront ∧ prefixLength = front.length ∧
      (prefixLength ≤ n → EnvOk m l index env nextEnv (n - prefixLength))) :
    EnvOk m (l + prefixLength) index (front ++ env) (nextFront ++ nextEnv) n := by
  obtain ⟨frontRel, rfl, tailRel⟩ := h
  have sameLength : nextFront.length = front.length := frontRel.length_eq.symm
  by_cases inFront : n < front.length
  · have targetBound : n < nextFront.length := by omega
    apply EnvOk.local m (l + front.length) index (front ++ env) (nextFront ++ nextEnv) n (by omega)
    · rw [holEl_append_left front env n inFront, holEl_append_left nextFront nextEnv n targetBound]
      rw [@Flapjack.holEl_eq_getElem Value ⟨unitValue⟩ n front inFront,
        @Flapjack.holEl_eq_getElem Value ⟨unitValue⟩ n nextFront targetBound]
      exact frontRel.get inFront targetBound
    · simp only [List.length_append]; omega
    · simp only [List.length_append]; omega
  · exact envOk_extend_ignore nextFront front n front.length m l index env nextEnv
      ⟨sameLength, by omega, rfl, tailRel (by omega)⟩

end Flapjack.Compiler.Backend.ClosAnnotate
