module

public import Flapjack.Compiler.Inference.TypeDCanon.Scheme

@[expose] public section

/-! Identifier bounds for source pattern and function bindings. -/
namespace Flapjack.Compiler.Inference.TypeDCanon
open Flapjack.Basis.Pure.MlString Flapjack.AstHOL Flapjack.TypeSystemHOL
  Flapjack.Compiler.Inference.InferProps Flapjack.Compiler.Inference.TypeDCanon

/-- Flapjack list-relation elimination for the source indexed binding argument. -/
private theorem every2MappedMember {α β γ : Type} (r : β → γ → Prop)
    (f : α → β) (g : α → γ) (xs : List α) :
    every2 r (xs.map f) (xs.map g) → ∀ x ∈ xs, r (f x) (g x) := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    intro rel y member
    cases rel with
    | cons head tail =>
      rcases List.mem_cons.mp member with rfl | member
      · exact head
      · exact ih tail y member

/-- Principal pattern-expression bindings contain only environment identifiers. -/
@[hol "cakeml/compiler/inference/proofs/type_dCanonScript.sml" "type_pe_bindings_tids"]
theorem typePeBindingsTids (tids : Nat → Prop) (env : TypeEnv) (tvs : Nat) (p : Pat)
    (e : Flapjack.AstHOL.Exp) (t : SemanticT) (bindings : List (MlString × SemanticT)) :
    primTids true tids ∧ setTidsTenv tids env ∧ TypeP tvs env p t bindings ∧
    TypeE env (bindTvar tvs .empty) e t ∧
    (∀ tvs' bindings' t', TypeP tvs' env p t' bindings' ∧
      TypeE env (bindTvar tvs' .empty) e t' →
      every2 tschemeInst ((tenvAddTvs tvs' bindings').map Prod.snd)
        ((tenvAddTvs tvs bindings).map Prod.snd)) →
    ∀ name ty, (name, ty) ∈ bindings → setTidsSubset tids ty := by
  rintro ⟨prim, bound, pat, exp, principal⟩ name ty member id occurs
  apply Classical.byContradiction
  intro absent
  let rename := singRenum id (id + 1)
  have typedP := typePTsTidRenameSingRenum id (id + 1) tids tvs env p t bindings
    ⟨absent, prim, pat, bound⟩
  have typedE := typeETsTidRenameSingRenum id (id + 1) tids env (bindTvar tvs .empty) e t
    ⟨absent, prim, exp, bound⟩
  have envEq : remapTenvE rename (bindTvar tvs .empty) = bindTvar tvs .empty := by
    simp [remapTenvEBindTvar, remapTenvE]
  rw [envEq] at typedE
  have all := principal tvs (bindings.map (fun entry => (entry.1, tsTidRename rename entry.2)))
    (tsTidRename rename t) ⟨typedP, typedE⟩
  have aligned : every2 tschemeInst
      (bindings.map (fun entry => (tvs, tsTidRename rename entry.2)))
      (bindings.map (fun entry => (tvs, entry.2))) := by
    simpa [tenvAddTvs, List.map_map, Function.comp_def] using all
  have related := every2MappedMember tschemeInst
    (fun entry : MlString × SemanticT => (tvs, tsTidRename rename entry.2))
    (fun entry : MlString × SemanticT => (tvs, entry.2)) bindings aligned (name, ty) member
  have unequal : id ≠ id + 1 := by omega
  exact ((singRenumNotTschemeInst id (id + 1) ty ⟨occurs, unequal⟩).2 tvs tvs).1 related

/-- Principal function bindings contain only environment identifiers. -/
@[hol "cakeml/compiler/inference/proofs/type_dCanonScript.sml" "type_funs_bindings_tids"]
theorem typeFunsBindingsTids (tids : Nat → Prop) (env : TypeEnv) (tvs : Nat)
    (funs : List (MlString × MlString × Flapjack.AstHOL.Exp)) (bindings : List (MlString × SemanticT)) :
    TypeFuns env (bindVarList 0 bindings (bindTvar tvs .empty)) funs bindings ∧
    setTidsTenv tids env ∧ primTids true tids ∧
    (∀ tvs' bindings', TypeFuns env (bindVarList 0 bindings' (bindTvar tvs' .empty)) funs bindings' →
      every2 tschemeInst (bindings'.map (fun entry => (tvs', entry.2)))
        (bindings.map (fun entry => (tvs, entry.2)))) →
    ∀ entry ∈ bindings, setTidsSubset tids entry.2 := by
  rintro ⟨typed, bound, prim, principal⟩ entry member id occurs
  apply Classical.byContradiction
  intro absent
  let rename := singRenum id (id + 1)
  have typedRenamed := typeFunsTsTidRenameSingRenum id (id + 1) tids env
    (bindVarList 0 bindings (bindTvar tvs .empty)) funs bindings ⟨absent, prim, typed, bound⟩
  simp only [remapTenvEBindVarList, remapTenvEBindTvar, remapTenvE] at typedRenamed
  have all := principal tvs (bindings.map (fun entry => (entry.1, tsTidRename rename entry.2))) typedRenamed
  have aligned : every2 tschemeInst
      (bindings.map (fun entry => (tvs, tsTidRename rename entry.2)))
      (bindings.map (fun entry => (tvs, entry.2))) := by
    simpa [List.map_map, Function.comp_def] using all
  have related := every2MappedMember tschemeInst
    (fun entry : MlString × SemanticT => (tvs, tsTidRename rename entry.2))
    (fun entry : MlString × SemanticT => (tvs, entry.2)) bindings aligned entry member
  have unequal : id ≠ id + 1 := by omega
  exact ((singRenumNotTschemeInst id (id + 1) entry.2 ⟨occurs, unequal⟩).2 tvs tvs).1 related

/-- Determinate monomorphic bindings contain only environment identifiers. -/
@[hol "cakeml/compiler/inference/proofs/type_dCanonScript.sml" "type_pe_bindings_tids_0"]
theorem typePeBindingsTidsZero (tids : Nat → Prop) (env : TypeEnv) (p : Pat) (e : Flapjack.AstHOL.Exp)
    (t : SemanticT) (bindings : List (MlString × SemanticT)) :
    primTids true tids ∧ setTidsTenv tids env ∧ TypeP 0 env p t bindings ∧
    TypeE env .empty e t ∧ typePeDeterm env .empty p e →
    ∀ name ty, (name, ty) ∈ bindings → setTidsSubset tids ty := by
  rintro ⟨prim, bound, pat, exp, determ⟩ name ty member id occurs
  apply Classical.byContradiction
  intro absent
  let rename := singRenum id (id + 1)
  have typedP := typePTsTidRenameSingRenum id (id + 1) tids 0 env p t bindings
    ⟨absent, prim, pat, bound⟩
  have typedE := typeETsTidRenameSingRenum id (id + 1) tids env .empty e t
    ⟨absent, prim, exp, bound⟩
  simp only [remapTenvE] at typedE
  have equality := determ t bindings (tsTidRename rename t)
    (bindings.map (fun entry => (entry.1, tsTidRename rename entry.2)))
      ⟨pat, exp, typedP, typedE⟩
  have fixed := mapFixedOnMembers (fun entry : MlString × SemanticT =>
    (entry.1, tsTidRename rename entry.2)) bindings equality.symm
  have eqType : tsTidRename rename ty = ty := congrArg Prod.snd (fixed (name, ty) member)
  exact singRenumInNotId ty id (id + 1) ⟨occurs, by omega⟩ eqType

end Flapjack.Compiler.Inference.TypeDCanon
