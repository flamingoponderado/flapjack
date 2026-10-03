import Flapjack.Pancake.Proofs.PanSimp.CompileCorrect
import Flapjack.Pancake.Semantics.PanSem.Semantics
import Flapjack.Pancake.Proofs.PanSimp

/-!
The original pan_simp `state_rel_imp_semantics`
(pan_simpProofScript.sml:1073-1301): `compile_correct` at every clock gives
the same result and FFI state for the entry call, so the whole observable
behaviour agrees.
-/

namespace Flapjack.PanSimp

open Flapjack.Pancake.PanLang
open Flapjack.Basis.Pure.MlString
open PanSemStateFiniteExact

namespace StateRelImpSemanticsSupport
/-- Imported canonical-state roundtrip infrastructure; no separate HOL original. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} {σ : Type} [NeZero width] :
    (∀ (state : PanSemStateExact width σ) (h : state.FiniteSupport),
      (PanSemStateFiniteExact.ofExact state h).toExact = state) ∧
    (∀ state : PanSemStateFiniteExact width σ,
      PanSemStateFiniteExact.ofExact state.toExact state.toExact_finiteSupport = state) :=
  PanSemStateFiniteExact.holFmapAsFiniteSupportWitness
end StateRelImpSemanticsSupport

/-- Flapjack statement infrastructure: eliminate the evaluator pair witnesses
inside the classical termination predicate. No independent HOL declaration. -/
private theorem terminationWitnessReduced {width : Nat} {σ : Type} [NeZero width]
    (run : Option (PanSemResultExact width) × PanSemStateFiniteExact width σ)
    (outcomeRelation : Option (PanSemResultExact width) → HolOutcome → Prop)
    (behaviour : HolBehaviour) :
    (∃ post result outcome, run = (result, post) ∧
      outcomeRelation result outcome ∧
      behaviour = HolBehaviour.terminate outcome post.ffi.ioEvents) ↔
    (∃ outcome, outcomeRelation run.1 outcome ∧
      behaviour = HolBehaviour.terminate outcome run.2.ffi.ioEvents) := by
  rcases run with ⟨result, post⟩
  constructor
  · rintro ⟨post', result', outcome, hpair, houtcome, hbehaviour⟩
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj hpair
    exact ⟨outcome, houtcome, hbehaviour⟩
  · rintro ⟨outcome, houtcome, hbehaviour⟩
    exact ⟨post, result, outcome, rfl, houtcome, hbehaviour⟩

/-- The semantic agreement from `state_rel` and source non-`Fail` alone; the
source proof of `state_rel_imp_semantics` uses no other hypothesis.
Flapjack infrastructure shared by the tagged theorems below. -/
theorem stateRelImpSemanticsCore {width : Nat} {σ : Type} [NeZero width]
    (s t : PanSemStateFiniteExact width σ) (start : MlS)
    (hrel : stateRel s t t.code) (hnonfail : semantics s start ≠ HolBehaviour.fail) :
    semantics t start = semantics s start := by
  classical
  have noError (clock : Nat) :
      (evaluateHOLFiniteState { s with clock := clock }
        (.call none start [])).1 ≠ some .error := by
    intro herror
    apply hnonfail
    unfold semantics
    dsimp only
    rw [if_pos]
    exact ⟨clock, by rw [herror]; trivial⟩
  have observations (clock : Nat) :
      (evaluateHOLFiniteState { t with clock := clock } (.call none start [])).1 =
        (evaluateHOLFiniteState { s with clock := clock } (.call none start [])).1 ∧
      (evaluateHOLFiniteState { t with clock := clock } (.call none start [])).2.ffi =
        (evaluateHOLFiniteState { s with clock := clock } (.call none start [])).2.ffi := by
    obtain ⟨ht, hnone, hsome⟩ := hrel
    have hclock : stateRel { s with clock := clock } { t with clock := clock }
        { t with clock := clock }.code := by
      refine ⟨?_, hnone, hsome⟩
      rw [ht]
    rcases hs : evaluateHOLFiniteState { s with clock := clock } (.call none start []) with
      ⟨result, sourcePost⟩
    have hne : result ≠ some .error := by simpa only [hs] using noError clock
    obtain ⟨targetPost, htarget, hpost⟩ := compileCorrectHOL (.call none start [])
      { s with clock := clock } result sourcePost { t with clock := clock } ⟨hs, hne, hclock⟩
    rw [evaluateSeqAssocHOL, evaluateSkipSeqHOL] at htarget
    rw [htarget, hpost.1]
    exact ⟨rfl, rfl⟩
  have results (clock : Nat) := (observations clock).1
  have events (clock : Nat) := congrArg (fun ffi : HolFfiState σ => ffi.ioEvents)
    (observations clock).2
  unfold semantics
  dsimp only
  simp only [terminationWitnessReduced, results, events]

/-- Original pan_simp `state_rel_imp_semantics`. `alist_to_fmap` is rendered
as the canonical update of the empty map with the reversed association list,
as in the accepted pan_to_crep `state_rel_imp_semantics`. The function-table
hypotheses are retained although, as in the source proof, only `state_rel`
and non-`Fail` are used. -/
@[hol "cakeml/pancake/proofs/pan_simpProofScript.sml" "state_rel_imp_semantics"
  (fmap_as_finite_support := [locals, globals, code, eshapes])
  (words_as_type_indexed_bitvec)]
theorem stateRelImpSemanticsHOL {width : Nat} {σ : Type} [NeZero width] :
    ∀ (s t : PanSemStateFiniteExact width σ) (pan_code : List (DeclHOL width)) (start : MlS),
      stateRel s t t.code ∧
        ((functionsHOL pan_code).map Prod.fst).Nodup ∧
        s.code = HolFiniteMapExact.empty.updateList (functionsHOL pan_code).reverse ∧
        t.code = HolFiniteMapExact.empty.updateList
          (functionsHOL (panSimpDeclsHOL pan_code)).reverse ∧
        semantics s start ≠ HolBehaviour.fail →
      semantics t start = semantics s start := by
  rintro s t pan_code start ⟨hrel, -, -, -, hnonfail⟩
  exact stateRelImpSemanticsCore s t start hrel hnonfail

/-- Declaration evaluation over a code-updated state: if the code maps are
related by `CodeRel`, the compiled declarations succeed whenever the source
ones do, and the final code maps are again related. Flapjack infrastructure
for `state_rel_imp_evaluate_decls`, generic in the memory-domain decider. -/
theorem evaluateDeclsCodeRel {width : Nat} {σ : Type} [NeZero width] :
    ∀ (decls : List (DeclHOL width)) (s : PanSemStateFiniteExact width σ)
      (h : DecidablePred s.memaddrs)
      (c : HolFiniteMapExact MlS (List (MlS × ShapeHOL) × ProgHOL width × ShapeHOL))
      (s' : PanSemStateFiniteExact width σ),
      CodeRel s.code c → @evaluateDeclsHOLFinite width σ _ s h decls = some s' →
      ∃ c', @evaluateDeclsHOLFinite width σ _ { s with code := c } h
          (panSimpDeclsHOL decls) = some { s' with code := c' } ∧ CodeRel s'.code c'
  | [], s, h, c, s', hc, hev => by
      simp only [evaluateDeclsHOLFinite, Option.some.injEq] at hev
      subst hev
      exact ⟨c, by simp [panSimpDeclsHOL, evaluateDeclsHOLFinite], hc⟩
  | .name n fields :: decls, s, h, c, s', hc, hev => by
      simp only [evaluateDeclsHOLFinite] at hev
      simp only [panSimpDeclsHOL, evaluateDeclsHOLFinite]
      exact evaluateDeclsCodeRel decls s h c s' hc hev
  | .decl shape name expression :: decls, s, h, c, s', hc, hev => by
      simp only [evaluateDeclsHOLFinite] at hev
      simp only [panSimpDeclsHOL, evaluateDeclsHOLFinite]
      have hcode := @evalHOLFinite_upd_code_eq width σ _ (emptyLocalsHOLFinite s) h c expression
      have hcode' : @evalHOLFinite width σ _ (emptyLocalsHOLFinite { s with code := c }) h
          expression = @evalHOLFinite width σ _ (emptyLocalsHOLFinite s) h expression := hcode
      rw [hcode']
      cases he : @evalHOLFinite width σ _ (emptyLocalsHOLFinite s) h expression with
      | none => simp only [he] at hev; exact absurd hev (by simp)
      | some value =>
          simp only [he] at hev ⊢
          by_cases hs : shapeEqHOL shape (shapeOfHOLExact value) = true
          · simp only [hs, if_true] at hev ⊢
            exact evaluateDeclsCodeRel decls (setGlobalHOLFinite name value s) h c s' hc hev
          · simp only [hs, Bool.false_eq_true, if_false] at hev
            exact absurd hev (by simp)
  | .function declaration :: decls, s, h, c, s', hc, hev => by
      simp only [evaluateDeclsHOLFinite] at hev
      simp only [panSimpDeclsHOL, evaluateDeclsHOLFinite]
      by_cases hwf : (declaration.params.all
            (fun parameter => isWfShapeExactHOL s.structs parameter.2) &&
          isWfShapeExactHOL s.structs declaration.returnShape) = true
      · rw [if_pos hwf] at hev
        rw [if_pos hwf]
        have hc' : CodeRel (s.code.update (declaration.name,
              (declaration.params, declaration.body, declaration.returnShape)))
            (c.update (declaration.name,
              (declaration.params, panSimpCompileHOL declaration.body,
                declaration.returnShape))) := by
          refine ⟨fun f hf => ?_, fun f vshs prog rshape hf => ?_⟩
          · simp only [HolFiniteMapExact.lookup_update, FUPDATE] at hf ⊢
            by_cases hn : declaration.name = f
            · simp [hn] at hf
            · simp only [beq_iff_eq, hn, if_false] at hf ⊢
              exact hc.1 f hf
          · simp only [HolFiniteMapExact.lookup_update, FUPDATE] at hf ⊢
            by_cases hn : declaration.name = f
            · simp only [hn, beq_self_eq_true, if_true, Option.some.injEq,
                Prod.mk.injEq] at hf ⊢
              obtain ⟨rfl, rfl, rfl⟩ := hf
              exact ⟨rfl, rfl, rfl⟩
            · simp only [beq_iff_eq, hn, if_false] at hf ⊢
              exact hc.2 f vshs prog rshape hf
        exact evaluateDeclsCodeRel decls
          { s with code := s.code.update (declaration.name,
            (declaration.params, declaration.body, declaration.returnShape)) } h _ s' hc' hev
      · rw [if_neg hwf] at hev
        exact absurd hev (by simp)
  | .exnDecl exceptionName shape :: decls, s, h, c, s', hc, hev => by
      simp only [evaluateDeclsHOLFinite] at hev
      simp only [panSimpDeclsHOL, evaluateDeclsHOLFinite]
      by_cases hok : ((s.eshapes.lookup exceptionName).isNone &&
          isWfShapeExactHOL s.structs shape) = true
      · rw [if_pos hok] at hev
        rw [if_pos hok]
        exact evaluateDeclsCodeRel decls
          { s with eshapes := s.eshapes.update (exceptionName, shape) } h c s' hc hev
      · rw [if_neg hok] at hev
        exact absurd hev (by simp)

/-- Original pan_simp `state_rel_imp_evaluate_decls`. The memory-domain
decider of `evaluate_decls` is chosen classically, as in the tagged
`semantics_decls`, which adds no premise. HOL's universally quantified `start`
occurs nowhere in the statement (a vacuous binder) and is omitted. The
`ALL_DISTINCT` hypothesis is retained although, as in the source proof, it is
not used. -/
@[hol "cakeml/pancake/proofs/pan_simpProofScript.sml" "state_rel_imp_evaluate_decls"
  (fmap_as_finite_support := [locals, globals, code, eshapes])
  (words_as_type_indexed_bitvec)]
theorem stateRelImpEvaluateDeclsHOL {width : Nat} {σ : Type} [NeZero width] :
    ∀ (s : PanSemStateFiniteExact width σ) (pan_code : List (DeclHOL width))
      (t s' : PanSemStateFiniteExact width σ),
      stateRel s t t.code ∧ ((functionsHOL pan_code).map Prod.fst).Nodup ∧
        (open Classical in evaluateDeclsHOLFinite s pan_code) = some s' →
      ∃ t', (open Classical in evaluateDeclsHOLFinite t (panSimpDeclsHOL pan_code)) = some t' ∧
        stateRel s' t' t'.code := by
  rintro s pan_code t s' ⟨⟨ht, hnone, hsome⟩, -, hev⟩
  obtain ⟨c', hev', hc'⟩ := evaluateDeclsCodeRel pan_code s _ t.code s' ⟨hnone, hsome⟩ hev
  refine ⟨{ s' with code := c' }, ?_, rfl, hc'.1, hc'.2⟩
  rw [ht]
  exact hev'

/-- Original pan_simp `state_rel_imp_semantics_decls`. The empty code maps
are `HolFiniteMapExact.empty` (HOL `FEMPTY`). The source proof concludes
through `state_rel_imp_semantics` after recovering its function-table
hypotheses from `evaluate_decls_functions`; only `state_rel` and non-`Fail`
are needed there, so this proof applies the shared core directly. The
`ALL_DISTINCT` and empty-code hypotheses are retained. -/
@[hol "cakeml/pancake/proofs/pan_simpProofScript.sml" "state_rel_imp_semantics_decls"
  (fmap_as_finite_support := [locals, globals, code, eshapes])
  (words_as_type_indexed_bitvec)]
theorem stateRelImpSemanticsDeclsHOL {width : Nat} {σ : Type} [NeZero width] :
    ∀ (s t : PanSemStateFiniteExact width σ) (pan_code : List (DeclHOL width)) (start : MlS),
      stateRel s t t.code ∧ ((functionsHOL pan_code).map Prod.fst).Nodup ∧
        s.code = HolFiniteMapExact.empty ∧ t.code = HolFiniteMapExact.empty ∧
        semanticsDecls s start pan_code ≠ HolBehaviour.fail →
      semanticsDecls s start pan_code = semanticsDecls t start (panSimpDeclsHOL pan_code) := by
  classical
  rintro s t pan_code start ⟨⟨ht, hnone, hsome⟩, hdist, -, -, hnonfail⟩
  unfold semanticsDecls at hnonfail ⊢
  rw [decsStcnamesHOLExact_panSimpDeclsHOL_eq]
  cases hst : decsStcnamesHOLExact [] pan_code with
  | none => rfl
  | some stCtxt =>
    simp only [hst] at hnonfail ⊢
    cases hev : evaluateDeclsHOLFinite { s with structs := stCtxt } pan_code with
    | none => simp only [hev] at hnonfail; exact absurd rfl hnonfail
    | some s' =>
      simp only [hev] at hnonfail
      have hrel : stateRel { s with structs := stCtxt } { t with structs := stCtxt }
          { t with structs := stCtxt }.code := by
        refine ⟨?_, hnone, hsome⟩
        rw [ht]
      obtain ⟨t', hev', hrel'⟩ := stateRelImpEvaluateDeclsHOL { s with structs := stCtxt }
        pan_code { t with structs := stCtxt } s' ⟨hrel, hdist, hev⟩
      have hev'' : evaluateDeclsHOLFinite { t with structs := stCtxt }
          (panSimpDeclsHOL pan_code) = some t' := hev'
      simp only [hev'']
      exact (stateRelImpSemanticsCore s' t' start hrel' hnonfail).symm

end Flapjack.PanSimp
