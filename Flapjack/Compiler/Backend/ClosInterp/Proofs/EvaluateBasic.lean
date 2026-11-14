module

public import Flapjack.Compiler.Backend.ClosInterp.Proofs.StateRelation
public import Flapjack.Compiler.Backend.Semantics.ClosSem.EvaluateExact

@[expose] public section

/-! Elementary closure evaluations used by the interpreter-insertion proof.
These are proof-side lemmas pending review of the evaluator carriers. -/
namespace Flapjack.Compiler.Backend.ClosInterp
open Flapjack.Compiler.Backend.BackendCommon

namespace BasicPort
/-- The closure state uses the canonical finite-support map representation. -/
theorem holFmapAsFiniteSupportWitness {C F : Type} :
    (∀ s : ClosSem.StateBroad C F, (ClosSem.State.ofBroad s).toBroad = s) ∧
      (∀ s : ClosSem.State C F, ClosSem.State.ofBroad s.toBroad = s) :=
  ClosSem.holFmapAsFiniteSupportWitness
end BasicPort

/-- A closed constant expression evaluates without changing state. -/
@[hol "cakeml/compiler/backend/proofs/clos_interpProofScript.sml" "evaluate_Constant"
  (fmap_as_finite_support := [refs, code])]
theorem evaluate_constant {C F : Type} (trace : Tra) (constant : ClosLang.Const)
    (env : List ClosSem.Value) (state : ClosSem.State C F) :
    ClosSem.evaluate [.op trace (.blockOp (.constant constant)) []] env state =
      (.val [ClosSem.makeConst constant], state) := by
  simp [ClosSem.evaluate, ClosSem.fixClock, ClosSem.doApp, ClosSem.applyBlock]

/-- A nullary constructor evaluates to its corresponding block. -/
@[hol "cakeml/compiler/backend/proofs/clos_interpProofScript.sml" "evaluate_Cons_nil"
  (fmap_as_finite_support := [refs, code])]
theorem evaluate_cons_nil {C F : Type} (trace : Tra) (tag : Nat)
    (env : List ClosSem.Value) (state : ClosSem.State C F) :
    ClosSem.evaluate [.op trace (.blockOp (.cons tag)) []] env state =
      (.val [.block tag []], state) := by
  simp [ClosSem.evaluate, ClosSem.fixClock, ClosSem.doApp, ClosSem.applyBlock]

/-- In related states, global zero supplies the installed interpreter. -/
@[hol "cakeml/compiler/backend/proofs/clos_interpProofScript.sml" "evaluate_Global_0"
  (fmap_as_finite_support := [refs, code])]
theorem evaluate_global_zero {C F : Type} (source target : ClosSem.State C F)
    (related : StateRel source target) (trace : Tra) (env : List ClosSem.Value) (clock : Nat) :
    ClosSem.evaluate [.op trace (.globOp (.global 0)) []] env { target with clock := clock } =
      (.val [.closure none [] [] 1 closInterpreter], { target with clock := clock }) := by
  have globals : target.globals.head? = some (some (.closure none [] [] 1 closInterpreter)) := by
    rw [← related.1.2.2.2.2.2.2.2.1]
    exact related.2
  cases h : target.globals with
  | nil => simp [h] at globals
  | cons first rest =>
    simp [h] at globals
    simp [ClosSem.evaluate, ClosSem.fixClock, ClosSem.doApp, ClosSem.applyGlobal,
      ClosSem.getGlobal, globals]

/-- Decoding an encoded closure-value list recovers the original list. -/
@[hol "cakeml/compiler/backend/proofs/clos_interpProofScript.sml" "v_to_list_list_to_v"]
theorem valueToList_listToValue (values : List ClosSem.Value) :
    ClosSem.valueToList (ClosSem.listToValue values) = some values :=
  ClosSem.valueToList_listToValue values

/-- Replace a singleton result list by an equal list. -/
@[hol "cakeml/compiler/backend/proofs/clos_interpProofScript.sml" "evaluate_SING_intro"]
theorem evaluate_singleton_intro {A B S : Type}
    (x : Flapjack.SemanticPrimitivesHOL.Result (List A) B × S) (v : A) (s : S) (vs : List A)
    (h : x = (.val [v], s) ∧ vs = [v]) : x = (.val vs, s) := by
  obtain ⟨rfl, rfl⟩ := h
  rfl

end Flapjack.Compiler.Backend.ClosInterp
