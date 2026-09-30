import Flapjack.Pancake.Proofs.PanGlobals
import Flapjack.Pancake.Semantics.PanSem.StateExactFiniteMap

namespace Flapjack.PanGlobalsUnchangedLocalIf
open Flapjack.Pancake.PanLang
open Flapjack.PanSemStateFiniteExact

/-- Canonical finite-state roundtrip; no standalone HOL declaration. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} {σ : Type} [NeZero width] :
    (∀ (state : PanSemStateExact width σ) (h : state.FiniteSupport),
        (ofExact state h).toExact = state) ∧
    (∀ state : PanSemStateFiniteExact width σ,
        ofExact state.toExact state.toExact_finiteSupport = state) :=
  PanSemStateFiniteExact.holFmapAsFiniteSupportWitness

/-- The If evaluate_ind case of HOL1111-1137. The IH retains the literal
value/payload/word binders and guard conjunction from evaluate_ind. The source
value binder is unused, as in HOL. No new premise is added beyond that IH. -/
@[hol "cakeml/pancake/proofs/pan_globalsProofScript.sml" "evaluate_unchanged_local"
  (fmap_as_finite_support := [locals, globals, code, eshapes])
  (words_as_type_indexed_bitvec)]
theorem evaluateUnchangedLocal_If {width : Nat} {σ : Type} [NeZero width]
    (name : MlS) (_value : ValueHOL width) (condition : ExpHOL width)
    (thenBranch elseBranch : ProgHOL width) (state : PanSemStateFiniteExact width σ)
    (ih : ∀ (value : ValueHOL width) (payload : HolWordLab width) (word : BitVec width),
      @evalHOLExact width σ _ state.toExact
        (fun a => Classical.propDecidable (state.memaddrs a)) condition = some value ∧
        value = .val payload ∧ payload = .word word →
      ∀ (result : Option (PanSemResultExact width)) (post : PanSemStateFiniteExact width σ),
        name ∉ freeVarIdsHOL (if word ≠ 0 then thenBranch else elseBranch) ∧
        evaluateHOLFiniteState state (if word ≠ 0 then thenBranch else elseBranch) =
          (result, post) ∧ goodResHOL result = true ∧ result ≠ some .error →
        post.locals.lookup name = state.locals.lookup name) :
    ∀ (result : Option (PanSemResultExact width)) (post : PanSemStateFiniteExact width σ),
      name ∉ freeVarIdsHOL (.ite condition thenBranch elseBranch) ∧
      evaluateHOLFiniteState state (.ite condition thenBranch elseBranch) = (result, post) ∧
      goodResHOL result = true ∧ result ≠ some .error →
      post.locals.lookup name = state.locals.lookup name := by
  classical
  intro result post ⟨hfresh, heval, hgood, herror⟩
  have hf : name ∉ freeVarIdsHOL thenBranch ∧ name ∉ freeVarIdsHOL elseBranch := by
    constructor <;> intro hmem <;> apply hfresh <;> simp [freeVarIdsHOL, hmem]
  rw [evaluateHOLFiniteState_ite] at heval
  cases hg : @evalHOLExact width σ _ state.toExact
      (fun a => Classical.propDecidable (state.memaddrs a)) condition with
  | none =>
      simp only [hg] at heval
      exact False.elim (herror (Prod.mk.inj heval).1.symm)
  | some value =>
      cases value with
      | val payload =>
          cases payload with
          | word word =>
              have hchild := ih (.val (.word word)) (.word word) word ⟨hg, rfl, rfl⟩
              by_cases hz : word = 0
              · simp only [hg, hz, ↓reduceIte] at heval
                apply hchild result post
                simpa only [hz, ne_eq, not_true_eq_false, ↓reduceIte] using
                  And.intro hf.2 (And.intro heval (And.intro hgood herror))
              · simp only [hg, hz, ↓reduceIte] at heval
                apply hchild result post
                simpa only [hz, ne_eq, not_false_eq_true, ↓reduceIte] using
                  And.intro hf.1 (And.intro heval (And.intro hgood herror))
      | rStruct fields =>
          simp only [hg] at heval
          exact False.elim (herror (Prod.mk.inj heval).1.symm)
      | nStruct structName fields =>
          simp only [hg] at heval
          exact False.elim (herror (Prod.mk.inj heval).1.symm)

end Flapjack.PanGlobalsUnchangedLocalIf
