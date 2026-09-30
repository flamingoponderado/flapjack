import Flapjack.Pancake.CrepInline.Pass
import Flapjack.Pancake.Semantics.CrepSem.EvaluateHOL

/-! Exact-evaluator no-return proof infrastructure for the crep_inline
counterpart. The core lemma exposes domain deciders only inside the proof;
the final source theorem will use the reviewed no-extra-argument evaluator. -/
namespace Flapjack.CrepInlineNoReturn

/-- Flapjack proof factoring: shared-memory operations produce ordinary
completion, Error or FinalFFI, never a Return payload. No HOL original is claimed. -/
private theorem shMemNoReturn {width : Nat} [NeZero width] {σ : Type}
    (operator : WordMemOp) (name : Nat) (address : BitVec width)
    (state : CrepSemHOLState width σ)
    (shDec : (a : BitVec width) → Decidable (state.shMemaddrs a))
    (value : List (HolWordLab width)) :
    (crepShMemLoadHOL operator name address state shDec).1 ≠ some (.return value) ∧
    (crepShMemStoreHOL operator name address state shDec).1 ≠ some (.return value) := by
  constructor <;> intro h
  all_goals simp only [crepShMemLoadHOL, crepShMemStoreHOL,
    crepShMemLoadExactHOL, crepShMemStoreExactHOL] at h
  all_goals repeat' (first | simp_all | split at h)

private theorem coreNoReturn {width : Nat} [NeZero width] {σ : Type}
    (state : CrepSemHOLState width σ)
    (memDec : (a : BitVec width) → Decidable (state.memaddrs a))
    (shMemDec : (a : BitVec width) → Decidable (state.shMemaddrs a))
    (program : CrepProgHOL width) :
    hasReturnHOLExact program = false → ∀ value,
      (evalCrepSemHOLProg state memDec shMemDec program).1 ≠ some (.return value) := by
  refine evalCrepSemHOLProg.inductHOL_general
    (motive := fun state memDec shMemDec program =>
      hasReturnHOLExact program = false → ∀ value,
        (evalCrepSemHOLProg state memDec shMemDec program).1 ≠ some (.return value))
    ?_ state memDec shMemDec program
  intro s md sd p ih hp value
  cases p <;> try simp only [hasReturnHOLExact, Bool.or_eq_false_iff] at hp
  all_goals try contradiction
  all_goals conv => lhs; arg 1; unfold evalCrepSemHOLProg
  case skip | «break» | «continue» | raise | tick | primitive | assign | store | store32 |
      storeByte | storeGlob | extCall =>
    intro h
    repeat' (first | simp_all | split at h)

  case dec name expression body =>
    intro h
    split at h
    · simp_all
    · rename_i bound he
      exact (ih (CrepSemHOLState.setVar name bound s) md sd body
        (Prod.Lex.right _ (by simp; omega)) hp value) h
  case ite condition first second =>
    have hfirst := ih s md sd first (Prod.Lex.right _ (by simp; omega)) hp.1 value
    have hsecond := ih s md sd second (Prod.Lex.right _ (by simp; omega)) hp.2 value
    intro h
    repeat' (first | simp_all | split at h)

  case seq first second =>
    have hfirst := ih s md sd first (Prod.Lex.right _ (by simp; omega)) hp.1 value
    intro h
    dsimp only at h
    split at h
    · rename_i next hstep
      have hclock := fixClockCrepSemHOL_IMP_LESS_EQ s
        (evalCrepSemHOLProg s md sd first) none next hstep
      exact (ih (crepStampExactDomains s next) md sd second (by
        have hsize : sizeOf second < sizeOf (.seq first second : CrepProgHOL width) := by
          simp; omega
        change Prod.Lex Nat.lt Nat.lt (next.clock, sizeOf second)
          (s.clock, sizeOf (.seq first second : CrepProgHOL width))
        rcases Nat.lt_or_eq_of_le hclock with hlt | heq
        · exact Prod.Lex.left _ _ hlt
        · rw [heq]
          exact Prod.Lex.right _ hsize) hp.2 value) h
    · rename_i result next hstep
      exact hfirst h

  case «while» condition body =>
    have hdec : s.clock ≠ 0 → (decClockCrepSemHOL s).clock < s.clock := by
      intro hc
      change s.clock - 1 < s.clock
      omega
    have hbody : s.clock ≠ 0 → ∀ ret,
        (evalCrepSemHOLProg (decClockCrepSemHOL s) md sd body).1 ≠ some (.return ret) := by
      intro hc ret
      exact ih (decClockCrepSemHOL s) md sd body (Prod.Lex.left _ _ (hdec hc)) hp ret
    have hloop : ∀ next : CrepSemHOLState width σ,
        next.clock ≤ (decClockCrepSemHOL s).clock → s.clock ≠ 0 →
        (evalCrepSemHOLProg (crepStampExactDomains s next) md sd
          (.while condition body)).1 ≠ some (.return value) := by
      intro next hbound hc
      exact ih (crepStampExactDomains s next) md sd (.while condition body)
        (Prod.Lex.left _ _ (Nat.lt_of_le_of_lt hbound (hdec hc))) hp value
    intro h
    repeat' (first | simp_all only [exitLoopCrepResult, Option.some.injEq] | split at h)
    all_goals try cases h
    case h_1 =>
      rename_i _ _ _ _ hc next heq
      exact (hloop next (fixClockCrepSemHOL_IMP_LESS_EQ _ _ none next heq) hc) h
    case h_2 =>
      rename_i _ _ _ _ hc next heq
      exact (hloop next (fixClockCrepSemHOL_IMP_LESS_EQ _ _ (some (CrepResultHOLExact.continue (width := width) 0)) next heq) hc) h
    case h_3.refl =>
      rename_i _ _ _ _ hc next _ _ _ _ heq _ _
      exact (hbody hc value) (congrArg Prod.fst heq)

  case shMem operator name expression =>
    intro h
    repeat' (first | simp_all [shMemNoReturn] | split at h)

  case call info function args =>
    dsimp only
    cases info with
    | none => cases hp
    | some info =>
      rcases info with ⟨resultVariable, handlerInfo⟩
      cases handlerInfo with
      | none =>
        intro h
        repeat' (first | simp_all | split at h)
      | some handlerInfo =>
        rcases handlerInfo with ⟨exception, handler⟩
        change hasReturnHOLExact handler = false at hp
        have hhandler : ∀ next : CrepSemHOLState width σ,
            next.clock < s.clock →
            (evalCrepSemHOLProg (crepStampExactDomains s { next with locals := s.locals })
              md sd handler).1 ≠ some (.return value) := by
          intro next hc
          exact ih (crepStampExactDomains s { next with locals := s.locals }) md sd handler
            (Prod.Lex.left _ _ hc) hp value
        intro h
        repeat' (first | simp_all | split at h)
        case h_5.isTrue =>
          rename_i _ values _ _ parameters calleeBody _ _ _ hc _ next heq _
          apply (hhandler next ?_) h
          have hbound := fixClockCrepSemHOL_IMP_LESS_EQ _ _
            (some (CrepResultHOLExact.exception (width := width) exception)) next heq
          change next.clock ≤ s.clock - 1 at hbound
          omega

/-- Canonical finite-support state roundtrip for the representation qualifier. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} [NeZero width] {σ : Type} :
    (∀ (state : CrepSemBroadState width σ) (h : state.FiniteSupport),
        (CrepSemBroadState.ofBroad state h).toBroad = state) ∧
    (∀ state : CrepSemHOLState width σ,
        CrepSemBroadState.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  CrepSemHOLState.holFmapAsFiniteSupportWitness

/-- The source no-return predicate alone excludes Return from the actual
clocked evaluator. Domain decision procedures remain internal; finite maps
use the canonical finite-support carrier and HOL words use positive BitVec widths. -/
@[hol "cakeml/pancake/proofs/crep_inlineProofScript.sml" "not_has_return_not_evaluate_return"
  (fmap_as_finite_support := [locals, globals, code]) (words_as_type_indexed_bitvec)]
theorem notHasReturnNotEvaluateReturn {width : Nat} [NeZero width] {σ : Type}
    (program : CrepProgHOL width) (state : CrepSemHOLState width σ)
    (h : hasReturnHOLExact program = false) :
    ∃ result next, evalCrepSemHOLProgExact state program = (result, next) ∧
      (match result with | some (.return _) => False | _ => True) := by
  classical
  have hn : ∀ value,
      (evalCrepSemHOLProgExact state program).1 ≠ some (.return value) := by
    rw [evalCrepSemHOLProgExact_eq_core state program
      (fun a => Classical.propDecidable (state.memaddrs a))
      (fun a => Classical.propDecidable (state.shMemaddrs a))]
    exact coreNoReturn state _ _ program h
  generalize heq : evalCrepSemHOLProgExact state program = output at *
  rcases output with ⟨result, next⟩
  refine ⟨result, next, rfl, ?_⟩
  cases result with
  | none => trivial
  | some result =>
    cases result <;> try trivial
    case «return» value => exact hn value rfl

/-- Same-result corollary with exactly the source conjunction of no-return
and evaluation equality; the target evaluation is a premise only here, as in HOL. -/
@[hol "cakeml/pancake/proofs/crep_inlineProofScript.sml" "not_has_return_not_evaluate_return'"
  (fmap_as_finite_support := [locals, globals, code]) (words_as_type_indexed_bitvec)]
theorem notHasReturnNotEvaluateReturnPrime {width : Nat} [NeZero width] {σ : Type}
    (program : CrepProgHOL width) (state : CrepSemHOLState width σ)
    (result : Option (CrepResultHOLExact width)) (next : CrepSemHOLState width σ)
    (value : List (HolWordLab width))
    (h : hasReturnHOLExact program = false ∧
      evalCrepSemHOLProgExact state program = (result, next)) :
    result ≠ some (.return value) := by
  obtain ⟨actual, finalState, heval, hn⟩ := notHasReturnNotEvaluateReturn program state h.1
  have heq := h.2.symm.trans heval
  have hr : result = actual := congrArg Prod.fst heq
  intro forbidden
  rw [← hr, forbidden] at hn
  exact hn

end Flapjack.CrepInlineNoReturn
