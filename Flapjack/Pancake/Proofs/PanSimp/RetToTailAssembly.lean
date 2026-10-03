import Flapjack.Pancake.Proofs.PanSimp.RetToTailCorrect
import Flapjack.Pancake.Proofs.PanSimp.SeqAssocAssembly
import Flapjack.Pancake.Semantics.PanSem.EvaluateInd

/-!
The recursive cases and the assembly of the original `ret_to_tail_correct`
(pan_simpProofScript.sml:182-341), with its helper lemmas
`evaluate_seq_call_ret_eq` (137), `evaluate_seq_no_error_fst` (153) and
`evaluate_while_no_error_imp` (103).
-/

namespace Flapjack.PanSimp.RetToTailCorrect

open Flapjack.Pancake.PanLang
open Flapjack.Basis.Pure.MlString
open PanSemStateFiniteExact

namespace RetToTailAssemblySupport
/-- Imported canonical-state roundtrip infrastructure; no separate HOL original. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} {σ : Type} [NeZero width] :
    (∀ (state : PanSemStateExact width σ) (h : state.FiniteSupport),
      (PanSemStateFiniteExact.ofExact state h).toExact = state) ∧
    (∀ state : PanSemStateFiniteExact width σ,
      PanSemStateFiniteExact.ofExact state.toExact state.toExact_finiteSupport = state) :=
  PanSemStateFiniteExact.holFmapAsFiniteSupportWitness
end RetToTailAssemblySupport

@[hol "cakeml/pancake/proofs/pan_simpProofScript.sml" "evaluate_seq_no_error_fst"
  (fmap_as_finite_support := [locals, globals, code, eshapes])
  (words_as_type_indexed_bitvec)]
theorem evaluateSeqNoErrorFstHOL {width : Nat} {σ : Type} [NeZero width]
    (p p' : ProgHOL width) (s : PanSemStateFiniteExact width σ) :
    (evaluateHOLFiniteState s (.seq p p')).1 ≠ some .error →
      (evaluateHOLFiniteState s p).1 ≠ some .error := by
  rw [evaluateHOLFiniteState_seq_line780]
  intro h he
  apply h
  simp only [he]

@[hol "cakeml/pancake/proofs/pan_simpProofScript.sml" "evaluate_seq_call_ret_eq"
  (fmap_as_finite_support := [locals, globals, code, eshapes])
  (words_as_type_indexed_bitvec)]
theorem evaluateSeqCallRetEqHOL {width : Nat} {σ : Type} [NeZero width] :
    ∀ (p : ProgHOL width) (s : PanSemStateFiniteExact width σ),
      (evaluateHOLFiniteState s p).1 ≠ some .error →
      evaluateHOLFiniteState s (seqCallRetHOL p) = evaluateHOLFiniteState s p := by
  intro p s h
  unfold seqCallRetHOL
  split
  · rename_i returnName function arguments returnedName
    split
    · rename_i heq
      subst heq
      revert h
      rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_call,
        evaluateHOLFiniteState_call]
      dsimp only
      cases hargs : evalListHOLFinite s
          (h := fun address => Classical.propDecidable (s.memaddrs address)) arguments with
      | none => intro _; rfl
      | some values =>
      dsimp only
      cases hl : lookupCodeHOLFinite s.code.lookup function values with
      | none => intro _; rfl
      | some entry =>
      obtain ⟨body, callee, returnShape⟩ := entry
      dsimp only
      by_cases hc : s.clock = 0
      · simp only [hc, ↓reduceIte]; intro _; trivial
      simp only [hc, ↓reduceIte]
      cases hb : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body with
      | mk res st =>
      rcases res with _ | r
      · intro _; rfl
      cases r with
      | returned v =>
        dsimp only
        by_cases hsh : shapeEqHOL (shapeOfHOLExact v) returnShape = true
        · by_cases hv : isValidValueHOLExact s.toExact .local returnName v = true
          · simp only [hsh, hv, ↓reduceIte, evaluateHOLFiniteState_return]
            simp only [setKvarHOLFinite, setVarHOLFinite]
            split
            · rename_i hnone
              change (s.locals.update (returnName, v)).lookup returnName = none at hnone
              simp [FUPDATE] at hnone
            · rename_i value hsome
              change (s.locals.update (returnName, v)).lookup returnName = some value at hsome
              have hvv : value = v := by simp [FUPDATE] at hsome; exact hsome.symm
              subst hvv
              by_cases hsz : sizeOfShapeWithContextHOL st.structs (shapeOfHOLExact value) ≤ 32
              · simp only [hsz, ↓reduceIte]; intro _; rfl
              · simp only [hsz, ↓reduceIte]; intro h; exact absurd rfl h
          · simp only [hsh, hv, ↓reduceIte]; intro h; exact absurd rfl h
        · simp only [hsh]; intro _; rfl
      | _ => intro _; rfl
    · rfl
  · rfl

end Flapjack.PanSimp.RetToTailCorrect
