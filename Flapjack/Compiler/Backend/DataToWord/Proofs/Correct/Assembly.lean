module

public import Flapjack.Compiler.Backend.DataToWord.Proofs.Correct.Skip
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Correct.Tick
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Correct.Move
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Correct.Raise
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Correct.Return
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Correct.MakeSpace
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Correct.If
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Correct.Seq
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Correct.Call
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Correct.Force
public import Flapjack.Misc.ClockWeightInduction

@[expose] public section

/-! Assembly of the ported `data_compile_correct` cases along the evaluator
induction (`data_to_wordProofScript.sml` lines 293-1154). The `Assign` case
is supplied as a hypothesis until `data_to_word_assignProof`'s `assign_thm`
is ported; this is Flapjack proof infrastructure, not a HOL theorem. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs
open Flapjack Flapjack.SemanticPrimitivesHOL
open Flapjack.Compiler.Backend.BackendProps
open Flapjack.Compiler.Backend.DataToWord.Proofs.Gc

/-- Bridge a case theorem, stated with an explicit conclusion, to the
induction proposition `dataCompileCorrectInduction`. -/
syntax "dcc_bridge " term : tactic
macro_rules
  | `(tactic| dcc_bridge $h) => `(tactic| (
      intro conf n l l1 l2 res s1 t locs run nte rel depth
      obtain ⟨target1, res1, wordRun, stackBound, space, result⟩ :=
        $h conf n l l1 l2 res s1 t locs run nte rel depth
      refine ⟨target1, res1, wordRun, stackBound, space, fun hs => ?_⟩
      have hr := result hs
      rcases res with _ | (_ | (_ | (_ | _ | _))) <;> exact hr))

private theorem callClock {C F : Type} (args : List Flapjack.Compiler.Backend.DataSem.Value)
    (ss : Option Nat) (env : Spt Flapjack.Compiler.Backend.DataSem.Value) (b : Bool)
    (s : Flapjack.Compiler.Backend.DataSem.State C F) (h : s.clock ≠ 0) :
    (DataSem.callEnv args ss (DataSem.pushEnv env b (DataSem.decClock s))).clock < s.clock := by
  simp [DataSem.callEnv, DataSem.pushEnv, DataSem.decClock]
  omega

private theorem tailClock {C F : Type} (args : List Flapjack.Compiler.Backend.DataSem.Value)
    (ss : Option Nat) (s : Flapjack.Compiler.Backend.DataSem.State C F) (h : s.clock ≠ 0) :
    (DataSem.callEnv args ss (DataSem.decClock s)).clock < s.clock := by
  simp [DataSem.callEnv, DataSem.decClock]
  omega

/-- Every `data_compile_correct` case except `Assign` is ported; given the
`Assign` case, the evaluator induction yields the full correctness
proposition for every program and state. -/
theorem dataCompileCorrect_of_assign {width : Nat} [NeZero width] {C F : Type}
    (assignCase : ∀ (dest : Nat) (op : ClosLang.Op) (names : List Nat) (live : Option NumSet)
      (s : Flapjack.Compiler.Backend.DataSem.State C F),
      dataCompileCorrectInduction (width := width) (.assign dest op names live) s) :
    ∀ (prog : Flapjack.Compiler.Backend.DataLang.Prog) (s : Flapjack.Compiler.Backend.DataSem.State C F),
      dataCompileCorrectInduction (width := width) prog s := by
  refine clockWeightInduction (α := Flapjack.Compiler.Backend.DataLang.Prog)
    (σ := Flapjack.Compiler.Backend.DataSem.State C F) (·.clock) sizeOf
    (motive := fun prog s => dataCompileCorrectInduction (width := width) prog s) ?_
  intro prog s weightIH clockIH
  cases prog with
  | skip =>
    dcc_bridge (fun conf n l l1 l2 res s1 t locs =>
      dataCompileCorrect_skip s conf n l l1 l2 res s1 t locs)
  | move dest src =>
    dcc_bridge (fun conf n l l1 l2 res s1 t locs =>
      dataCompileCorrect_move s conf n l l1 l2 dest src res s1 t locs)
  | assign dest op names live => exact assignCase dest op names live s
  | tick =>
    dcc_bridge (fun conf n l l1 l2 res s1 t locs =>
      dataCompileCorrect_tick s conf n l l1 l2 res s1 t locs)
  | makeSpace amount names =>
    dcc_bridge (fun conf n l l1 l2 res s1 t locs =>
      dataCompileCorrect_makeSpace amount names s conf n l l1 l2 res s1 t locs)
  | raise name =>
    dcc_bridge (fun conf n l l1 l2 res s1 t locs =>
      dataCompileCorrect_raise s conf n l l1 l2 res s1 t locs name)
  | «return» names =>
    dcc_bridge (fun conf n l l1 l2 res s1 t locs =>
      dataCompileCorrect_return s conf n l l1 l2 res s1 t locs names)
  | seq first second =>
    dcc_bridge (fun conf n l l1 l2 res s1 t locs =>
      dataCompileCorrect_seq s conf n l l1 l2 res s1 t locs first second
        (weightIH first s (Nat.le_refl _) (by simp; omega))
        (fun r mid h => weightIH second mid
          (by
            have hc := DataSem.evaluate_clock_le first s
            rw [← h.1] at hc
            exact hc)
          (by simp)))
  | ifThenElse name yes no =>
    dcc_bridge (fun conf n l l1 l2 res s1 t locs =>
      dataCompileCorrect_if s conf n l l1 l2 res s1 t locs name yes no
        (fun _ _ _ _ => weightIH no s (Nat.le_refl _) (by simp))
        (fun _ _ _ => weightIH yes s (Nat.le_refl _) (by simp; omega)))
  | force ret loc src =>
    dcc_bridge (fun conf n l l1 l2 res s1 t locs =>
      dataCompileCorrect_force s conf n l l1 l2 res s1 t locs ret loc src
        (fun _ _ _ args1 prog ss _ _ env s1' h => by
          obtain ⟨_, _, _, _, _, _, rfl, hz⟩ := h
          exact clockIH prog _ (callClock args1 ss env false s hz))
        (fun _ _ _ args1 prog ss h => clockIH prog _ (tailClock args1 ss s h.2.2.2.2.2)))
  | call ret dest args handler =>
    dcc_bridge (fun conf n l l1 l2 res s1 t locs =>
      dataCompileCorrect_call s conf n l l1 l2 res s1 t locs ret dest args handler
        (fun _ args1 prog ss _ _ env s1' r s2 x hn h hyp => by
          obtain ⟨_, _, _, _, _, rfl, hz, hrun, _, _⟩ := hyp
          apply clockIH h
          have hc := DataSem.evaluate_clock_le prog
            (DataSem.callEnv args1 ss (DataSem.pushEnv env handler.isSome (DataSem.decClock s)))
          rw [hrun] at hc
          have := callClock args1 ss env handler.isSome s hz
          simp only [DataSem.setVar] at hc ⊢
          omega)
        (fun _ args1 prog ss _ _ env s1' hyp => by
          obtain ⟨_, _, _, _, _, rfl, hz⟩ := hyp
          exact clockIH prog _ (callClock args1 ss env handler.isSome s hz))
        (fun _ args1 prog ss hyp => clockIH prog _ (tailClock args1 ss s hyp.2.2.2.2)))

end Flapjack.Compiler.Backend.DataToWord.Proofs
