import Flapjack.Compiler.Backend.Parmove.Invariants.Preservation
namespace Flapjack.Test.ParmoveWfStepsParity
open Flapjack.Compiler.Backend.Parmove
-- pw_remove_pre=T
example : wf (γ := List (Move Nat)) ([(some (1:Nat),some 1)],[],[]) := by simp [wf, windmill, path]
-- pw_remove_post=T
example : wf (γ := List (Move Nat)) (([] : List (Move Nat)),[],[]) := by simp [wf, windmill, path]
-- pw_start_pre=T
example : wf (γ := List (Move Nat)) ([(some (1:Nat),some 2)],[],[]) := by simp [wf, windmill, path]
-- pw_start_post=T
example : wf (γ := List (Move Nat)) ([],[(some (1:Nat),some 2)],[]) := by simp [wf, windmill, path]
-- pw_extend_pre=T
example : wf (γ := List (Move Nat)) ([(some (3:Nat),some 1)],[(some 1,some 2)],[]) := by simp [wf, windmill, path]
-- pw_extend_post=T
example : wf (γ := List (Move Nat)) ([],[(some (3:Nat),some 1),(some 1,some 2)],[]) := by simp [wf, windmill, path]
-- pw_save_pre=T
example : wf (γ := List (Move Nat)) ([],[(some (1:Nat),some 2)],[]) := by simp [wf, windmill, path]
-- pw_save_post=T
example : wf (γ := List (Move Nat)) ([],[(some (1:Nat),none)],[(none,some 2)]) := by simp [wf, windmill, path]
-- pw_emit_head_pre=T
example : wf (γ := List (Move Nat)) ([],[(some (3:Nat),some 1),(some 1,some 2)],[]) := by simp [wf, windmill, path]
-- pw_emit_head_post=T
example : wf (γ := List (Move Nat)) ([],[(some (1:Nat),some 2)],[(some 3,some 1)]) := by simp [wf, windmill, path]
-- pw_emit_last_pre=T
example : wf (γ := List (Move Nat)) ([],[(some (1:Nat),some 2)],[]) := by simp [wf, windmill, path]
-- pw_emit_last_post=T
example : wf (γ := List (Move Nat)) (([] : List (Move Nat)),[],[(some 1,some 2)]) := by simp [wf, windmill, path]
-- pw_bad_source=F
example : ¬ wf (γ := List (Move Nat)) ([(some (1:Nat),none)],[],[]) := by simp [wf, windmill, path]
-- pw_bad_path=F
example : ¬ wf (γ := List (Move Nat)) ([],[(some (3:Nat),some 2),(some 1,some 2)],[]) := by simp [wf, windmill, path]
example {α : Type} (first second : State α) (step : Step first second)
    (valid : wf first) : wf second := wf_step first second step valid
example {α : Type} (first second : State α) (h : wf first ∧ Steps first second) :
    wf second := wf_steps first second h
example : wf (γ := List (Move Nat)) (([] : List (Move Nat)), [], [(some 1,some 2)]) := by
  apply wf_steps ([(some 1,some 2)],[],[])
  constructor
  · simp [wf, windmill, path]
  · exact (Relation.ReflTransGen.single (Step.start _ _ [] [] [])).trans
      (Relation.ReflTransGen.single (Step.emitLast _ _ [] [] (by simp)))
end Flapjack.Test.ParmoveWfStepsParity
