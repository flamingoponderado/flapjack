import Flapjack.Pancake.Proofs.PanGlobals
import Flapjack.Pancake.Proofs.PanGlobals.FreshLocalEval

namespace Flapjack.PanGlobalsFreshLocalIf
open Flapjack.Pancake.PanLang
open Flapjack.PanSemStateFiniteExact

/-- Canonical finite-state roundtrip; no standalone HOL declaration. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} {σ : Type} [NeZero width] :
    (∀ (state : PanSemStateExact width σ) (h : state.FiniteSupport),
        (ofExact state h).toExact = state) ∧
    (∀ state : PanSemStateFiniteExact width σ,
        ofExact state.toExact state.toExact_finiteSupport = state) :=
  PanSemStateFiniteExact.holFmapAsFiniteSupportWitness

/-- Local factoring of the original induction predicate; no separate HOL original. -/
def freshLocalGoal {width : Nat} {σ : Type} [NeZero width]
    (name : MlS) (value : ValueHOL width) (program : ProgHOL width)
    (state : PanSemStateFiniteExact width σ) : Prop :=
  ∀ (result : Option (PanSemResultExact width)) (post : PanSemStateFiniteExact width σ),
    name ∉ freeVarIdsHOL program ∧ evaluateHOLFiniteState state program = (result, post) →
    ∃ locals,
      evaluateHOLFiniteState {state with locals := state.locals.updateEq (name, value)} program =
        (result, {post with locals := locals}) ∧
      (goodResHOL result = true ∧ result ≠ some .error →
        locals = post.locals.updateEq (name, value))

/-- Genuine If case of evaluate_fresh_local1045-1091. The IH is precisely the
literal guard/value/payload/word evaluate_ind case, with the original predicate.
Failures preserve the updated state; successful guards use the selected branch
IH. No branch-evaluation or fresh-name assumption is added. -/
@[hol "cakeml/pancake/proofs/pan_globalsProofScript.sml" "evaluate_fresh_local"
  (fmap_as_finite_support := [locals, globals, code, eshapes])
  (words_as_type_indexed_bitvec)]
theorem evaluateFreshLocal_If {width : Nat} {σ : Type} [NeZero width]
    (name : MlS) (value : ValueHOL width) (condition : ExpHOL width)
    (thenBranch elseBranch : ProgHOL width) (state : PanSemStateFiniteExact width σ)
    (ih : ∀ (v1 : ValueHOL width) (v6 : HolWordLab width) (w : BitVec width),
      @evalHOLExact width σ _ state.toExact
        (fun a => Classical.propDecidable (state.memaddrs a)) condition = some v1 ∧
        v1 = .val v6 ∧ v6 = .word w →
      freshLocalGoal name value (if w ≠ 0 then thenBranch else elseBranch) state) :
    ∀ (result : Option (PanSemResultExact width)) (post : PanSemStateFiniteExact width σ),
      name ∉ freeVarIdsHOL (.ite condition thenBranch elseBranch) ∧
      evaluateHOLFiniteState state (.ite condition thenBranch elseBranch) = (result, post) →
      ∃ locals,
        evaluateHOLFiniteState {state with locals := state.locals.updateEq (name, value)}
          (.ite condition thenBranch elseBranch) = (result, {post with locals := locals}) ∧
        (goodResHOL result = true ∧ result ≠ some .error →
          locals = post.locals.updateEq (name, value)) := by
  classical
  intro result post ⟨hfresh, heval⟩
  have hf : name ∉ varExpHOL condition ∧ name ∉ freeVarIdsHOL thenBranch ∧
      name ∉ freeVarIdsHOL elseBranch := by
    constructor
    · intro hm; apply hfresh; simp [freeVarIdsHOL, hm]
    · constructor <;> intro hm <;> apply hfresh <;> simp [freeVarIdsHOL, hm]
  have hup : ({state with locals := state.locals.updateEq (name, value)} :
      PanSemStateFiniteExact width σ).toExact =
      {state.toExact with locals := FUPDATE_HOL state.toExact.locals (name, value)} := rfl
  have hguard := evalHOLExact_updLocals_not_mem state.toExact name value condition hf.1
  have hgEq : @evalHOLExact width σ _
      ({state with locals := state.locals.updateEq (name, value)} : PanSemStateFiniteExact width σ).toExact
      (fun a => Classical.propDecidable (state.memaddrs a)) condition =
      @evalHOLExact width σ _ state.toExact
      (fun a => Classical.propDecidable (state.memaddrs a)) condition := by
    simpa only [hup] using hguard
  rw [evaluateHOLFiniteState_ite] at heval
  cases hg : @evalHOLExact width σ _ state.toExact
      (fun a => Classical.propDecidable (state.memaddrs a)) condition with
  | none =>
      simp only [hg] at heval
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj heval
      refine ⟨state.locals.updateEq (name, value), ?_, fun _ => rfl⟩
      rw [evaluateHOLFiniteState_ite, hgEq, hg]
  | some v1 =>
      cases v1 with
      | rStruct fields =>
          simp only [hg] at heval
          obtain ⟨rfl, rfl⟩ := Prod.mk.inj heval
          refine ⟨state.locals.updateEq (name, value), ?_, fun _ => rfl⟩
          rw [evaluateHOLFiniteState_ite, hgEq, hg]
      | nStruct n fields =>
          simp only [hg] at heval
          obtain ⟨rfl, rfl⟩ := Prod.mk.inj heval
          refine ⟨state.locals.updateEq (name, value), ?_, fun _ => rfl⟩
          rw [evaluateHOLFiniteState_ite, hgEq, hg]
      | val payload =>
          cases payload with
          | word w =>
              have hchild := ih (.val (.word w)) (.word w) w ⟨hg, rfl, rfl⟩
              have hbranch : name ∉ freeVarIdsHOL (if w ≠ 0 then thenBranch else elseBranch) := by
                split <;> simp_all
              simp only [hg] at heval
              have hselected : evaluateHOLFiniteState state (if w ≠ 0 then thenBranch else elseBranch) = (result, post) := by
                by_cases hz : w = 0 <;> simpa only [hz, ne_eq, not_true_eq_false, not_false_eq_true, ↓reduceIte] using heval
              obtain ⟨locals, hev, hlocals⟩ := hchild result post ⟨hbranch, hselected⟩
              refine ⟨locals, ?_, hlocals⟩
              rw [evaluateHOLFiniteState_ite, hgEq, hg]
              by_cases hz : w = 0 <;> simpa only [hz, ne_eq, not_true_eq_false, not_false_eq_true, ↓reduceIte] using hev

end Flapjack.PanGlobalsFreshLocalIf
