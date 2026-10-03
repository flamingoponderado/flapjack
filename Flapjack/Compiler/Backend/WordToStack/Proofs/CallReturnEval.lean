import Flapjack.Compiler.Backend.WordToStack.Proofs.CallDest
import Flapjack.Compiler.Backend.WordToStack.NativeLive
import Flapjack.Compiler.Backend.WordToStack.NativeReturn
import Flapjack.Compiler.Backend.StackRemove.Proofs.CopyLoop
import Flapjack.Compiler.Backend.Semantics.StackSem.EvaluateClock

/-!
# Word-to-Stack returning-call evaluation lemmas

Evaluation facts about the small StackLang programs emitted around a returning
call (`word_to_stackProofScript.sml`): `evaluate_call_dest_clock` (5234-5242),
`evaluate_wLive_clock` (5244-5258) and `evaluate_stack_move_seq` (5330-5348).
-/

namespace Flapjack.WordToStackProofs.CallReturnEval
open Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.WordToStack.Native
open Flapjack.Compiler.Backend.WordToStackRegFormat (wReg2)

/-- Canonical StackSem codec re-export for the evaluator's map translation;
no separate HOL original. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : StackSemStateBroad width C F) (h : state.FiniteSupport),
      (StackSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : StackSemStateFiniteExact width C F,
      StackSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  StackSemStateSupport.holFmapAsFiniteSupportWitness

/-- A program whose run does not depend on the clock and leaves it unchanged.
Flapjack infrastructure; no separate HOL original. -/
def ClockFree {width : Nat} [NeZero width] {C F : Type} (p : HolProg width) : Prop :=
  ∀ (t : StackSemStateFiniteExact width C F) (clk : Nat),
    StackSemEvaluate.evaluate (p, {t with clock := clk}) =
      Prod.map id (fun s => {s with clock := clk}) (StackSemEvaluate.evaluate (p, t))

theorem clockFree_skip {width : Nat} [NeZero width] {C F : Type} :
    ClockFree (C := C) (F := F) (.skip : HolProg width) := by
  intro t clk
  simp [StackSemEvaluate.evaluate_skip]

theorem clockFree_stackLoad {width : Nat} [NeZero width] {C F : Type} (r i : Nat) :
    ClockFree (C := C) (F := F) (.stackLoad r i : HolProg width) := by
  intro t clk
  rw [StackSemEvaluate.evaluate_stackLoad, StackSemEvaluate.evaluate_stackLoad]
  by_cases hu : t.useStack = true
  · by_cases hb : t.stackSpace + i < t.stack.length
    · simp [hu, hb, StackSemStateOps.setVar]
    · simp [hu, hb, StackSemStateOps.emptyEnv]
  · simp [hu]

theorem clockFree_stackStore {width : Nat} [NeZero width] {C F : Type} (r i : Nat) :
    ClockFree (C := C) (F := F) (.stackStore r i : HolProg width) := by
  intro t clk
  rw [StackSemEvaluate.evaluate_stackStore, StackSemEvaluate.evaluate_stackStore]
  by_cases hu : t.useStack = true
  · by_cases hb : t.stack.length ≤ t.stackSpace + i
    · simp [hu, hb, StackSemStateOps.emptyEnv]
    · rcases hg : StackSemStateOps.getVar r t with _ | v
      · simp [hu, hb, StackSemStateOps.getVar, StackSemStateOps.emptyEnv] at hg ⊢
        simp [hg]
      · simp [hu, hb, StackSemStateOps.getVar] at hg ⊢
        simp [hg]
  · simp [hu]

theorem clockFree_const {width : Nat} [NeZero width] {C F : Type} (r : Nat) (w : BitVec width) :
    ClockFree (C := C) (F := F) (.inst (.const r w) : HolProg width) := by
  intro t clk
  rw [StackSemEvaluate.evaluate_inst, StackSemEvaluate.evaluate_inst]
  simp [StackSemInst.instHOL, StackSemIntegerInstructions.instInteger,
    StackSemExpressions.assign, StackSemExpressions.wordExp, StackSemStateOps.setVar]

theorem clockFree_seq {width : Nat} [NeZero width] {C F : Type} (a b : HolProg width)
    (ha : ClockFree (C := C) (F := F) a) (hb : ClockFree (C := C) (F := F) b) :
    ClockFree (C := C) (F := F) (.seq a b) := by
  intro t clk
  rw [StackSemEvaluate.evaluate_seq, StackSemEvaluateClock.fixClockEvaluate,
    StackSemEvaluate.evaluate_seq, StackSemEvaluateClock.fixClockEvaluate, ha]
  rcases hrun : StackSemEvaluate.evaluate (a, t) with ⟨r, s⟩
  rcases r with _ | r
  · simp only [Prod.map_apply, id_eq]
    exact hb s clk
  · rfl

/-- Exact HOL `evaluate_call_dest_clock` (`word_to_stackProofScript.sml:5234-5242`).
HOL's free variables are explicit; `I ## (λt. t with clock := clk)` is
`Prod.map id`. -/
@[hol "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "evaluate_call_dest_clock"
  (fmap_as_finite_support := [regs, fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem evaluateCallDestClock {width : Nat} [NeZero width] {C F : Type}
    (dest : Option Nat) (args : List Nat) (k f f' : Nat) (q0 : HolProg width)
    (dest' : Sum Nat Nat) (t : StackSemStateFiniteExact width C F) (clk : Nat) :
    callDestNative dest args (k, f, f') = (q0, dest') →
      StackSemEvaluate.evaluate (q0, {t with clock := clk}) =
        Prod.map id (fun s => {s with clock := clk}) (StackSemEvaluate.evaluate (q0, t)) := by
  intro hcd
  suffices h : ClockFree (C := C) (F := F) q0 from h t clk
  rcases dest with _ | p
  · simp only [callDestNative] at hcd
    split at hcd
    · simp only [Prod.mk.injEq] at hcd; rw [← hcd.1]; exact clockFree_skip
    · simp only [Prod.mk.injEq] at hcd
      rw [← hcd.1]
      simp only [wReg2]
      split
      · exact clockFree_skip
      · exact clockFree_seq _ _ (clockFree_stackLoad _ _) clockFree_skip
  · simp only [callDestNative, Prod.mk.injEq] at hcd
    rw [← hcd.1]; exact clockFree_skip

/-- Exact HOL `evaluate_wLive_clock` (`word_to_stackProofScript.sml:5244-5258`).
HOL's free `kf` and `clk` are explicit. -/
@[hol "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "evaluate_wLive_clock"
  (fmap_as_finite_support := [regs, fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem evaluateWLiveClock {width : Nat} [NeZero width] {C F : Type}
    (kf : Nat × Nat × Nat) (clk : Nat) :
    ∀ (x : Spt Unit × Spt Unit) (t : StackSemStateFiniteExact width C F) (q : HolProg width)
      (bs bs' : AppList (BitVec width) × Nat),
      wLiveNative x bs kf = (q, bs') →
        StackSemEvaluate.evaluate (q, {t with clock := clk}) =
          ((StackSemEvaluate.evaluate (q, t)).1,
            {(StackSemEvaluate.evaluate (q, t)).2 with clock := clk}) := by
  intro x t q bs bs' hw
  suffices h : ClockFree (C := C) (F := F) q from h t clk
  simp only [wLiveNative] at hw
  split at hw
  · simp only [Prod.mk.injEq] at hw; rw [← hw.1]; exact clockFree_skip
  · simp only [Prod.mk.injEq] at hw
    rw [← hw.1]
    exact clockFree_seq _ _ (clockFree_const _ _) (clockFree_stackStore _ _)

/-- Exact HOL `evaluate_stack_move_seq` (`word_to_stackProofScript.sml:5330-5348`). -/
@[hol "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "evaluate_stack_move_seq"
  (fmap_as_finite_support := [regs, fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem evaluateStackMoveSeq {width : Nat} [NeZero width] {C F : Type} :
    ∀ (a b c d : Nat) (prog : HolProg width) (t : StackSemStateFiniteExact width C F),
      StackSemEvaluate.evaluate (stackMoveNative a b c d prog, t) =
        StackSemEvaluate.evaluate (.seq prog (stackMoveNative a b c d .skip), t) := by
  intro a
  induction a with
  | zero =>
      intro b c d prog t
      simp only [stackMoveNative]
      rw [StackSemEvaluate.evaluate_seq, StackSemEvaluateClock.fixClockEvaluate]
      rcases hrun : StackSemEvaluate.evaluate (prog, t) with ⟨r, s⟩
      rcases r with _ | r
      · simp [StackSemEvaluate.evaluate_skip]
      · rfl
  | succ n ih =>
      intro b c d prog t
      simp only [stackMoveNative]
      rw [Compiler.Backend.StackRemove.CopyLoopProof.sequenceAssoc prog,
        StackSemEvaluate.evaluate_seq (stackMoveNative n (b + 1) c d prog),
        StackSemEvaluate.evaluate_seq (.seq prog (stackMoveNative n (b + 1) c d .skip)), ih]

theorem seq_congr_right {width : Nat} [NeZero width] {C F : Type} (a b b' : HolProg width)
    (h : ∀ s : StackSemStateFiniteExact width C F,
      StackSemEvaluate.evaluate (b, s) = StackSemEvaluate.evaluate (b', s))
    (t : StackSemStateFiniteExact width C F) :
    StackSemEvaluate.evaluate (.seq a b, t) = StackSemEvaluate.evaluate (.seq a b', t) := by
  rw [StackSemEvaluate.evaluate_seq, StackSemEvaluate.evaluate_seq]
  rcases StackSemControl.fixClock t (StackSemEvaluate.evaluate (a, t)) with ⟨r, s1⟩
  rcases r with _ | r
  · exact h s1
  · rfl

theorem seq_skip_left {width : Nat} [NeZero width] {C F : Type} (b : HolProg width)
    (t : StackSemStateFiniteExact width C F) :
    StackSemEvaluate.evaluate (.seq .skip b, t) = StackSemEvaluate.evaluate (b, t) := by
  rw [StackSemEvaluate.evaluate_seq, StackSemEvaluate.evaluate_skip]
  simp only [StackSemControl.fixClock, Nat.min_self]

/-- Exact HOL `evaluate_copy_ret_aux_clock` (`word_to_stackProofScript.sml:7706-7718`).
HOL's free `k`, `f`, `n` and `clk` are explicit. -/
@[hol "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "evaluate_copy_ret_aux_clock"
  (fmap_as_finite_support := [regs, fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem evaluateCopyRetAuxClock {width : Nat} [NeZero width] {C F : Type}
    (k f n clk : Nat) :
    ∀ t : StackSemStateFiniteExact width C F,
      StackSemEvaluate.evaluate (copyRetAuxNative k f n, {t with clock := clk}) =
        Prod.map id (fun s => {s with clock := clk})
          (StackSemEvaluate.evaluate (copyRetAuxNative k f n, t)) := by
  intro t
  suffices h : ClockFree (C := C) (F := F) (copyRetAuxNative (width := width) k f n) from h t clk
  induction n with
  | zero => exact clockFree_skip
  | succ n ih =>
      simp only [copyRetAuxNative, listSeq]
      exact clockFree_seq _ _ (clockFree_stackLoad _ _)
        (clockFree_seq _ _ (clockFree_stackStore _ _) ih)

/-- Exact HOL `evaluate_copy_ret_Seq` (`word_to_stackProofScript.sml:7611-7641`).
HOL's free variables are explicit; the return-value and unused frame-component
carriers are independent, as in `copy_ret_def`. -/
@[hol "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "evaluate_copy_ret_Seq"
  (fmap_as_finite_support := [regs, fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem evaluateCopyRetSeq {width : Nat} [NeZero width] {C F β γ : Type}
    (perf b : Bool) (kf : Nat × Nat × γ) (vs : List β) (k0 : HolProg width)
    (t : StackSemStateFiniteExact width C F) :
    StackSemEvaluate.evaluate (copyRetNative perf b kf vs k0, t) =
      StackSemEvaluate.evaluate (.seq (copyRetNative perf b kf vs .skip) k0, t) := by
  by_cases hn : Compiler.Backend.WordToStack.numStackRet kf.1 vs = 0
  · simp only [copyRetNative, hn, if_true]
    rw [seq_skip_left]
  · simp only [copyRetNative, hn, if_false]
    rw [← Compiler.Backend.StackRemove.CopyLoopProof.sequenceAssoc]
    apply seq_congr_right
    intro s
    unfold seqStackFreeNative
    rw [if_neg hn, if_neg hn, ← Compiler.Backend.StackRemove.CopyLoopProof.sequenceAssoc]
    apply seq_congr_right
    intro s'
    rw [seq_skip_left]

end Flapjack.WordToStackProofs.CallReturnEval
