import Flapjack.Compiler.Backend.WordToStack.Proofs.CallDest
import Flapjack.Compiler.Backend.WordToStack.NativeLive
import Flapjack.Compiler.Backend.WordToStack.NativeReturn
import Flapjack.Compiler.Backend.StackRemove.Proofs.CopyLoop
import Flapjack.Compiler.Backend.Semantics.StackSem.EvaluateClock
import Flapjack.Compiler.Backend.WordGcFunctions
import Flapjack.Misc.ListEl

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

theorem getElem_of_drop_eq {α : Type} {l l' : List α} {m i : Nat}
    (h : l'.drop m = l.drop m) (hi : m ≤ i) (hl : i < l.length) (hl' : i < l'.length) :
    l'[i] = l[i] := by
  have h1 : (l'.drop m)[i - m]? = (l.drop m)[i - m]? := by rw [h]
  rw [List.getElem?_drop, List.getElem?_drop, show m + (i - m) = i by omega] at h1
  rw [List.getElem?_eq_getElem hl', List.getElem?_eq_getElem hl] at h1
  exact Option.some.inj h1

/-- Exact HOL `evaluate_stack_move` (`word_to_stackProofScript.sml:5270-5328`). HOL's
free `k` is explicit; its total `EL` is `holEl`. -/
@[hol "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "evaluate_stack_move"
  (fmap_as_finite_support := [regs, fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem evaluateStackMove {width : Nat} [NeZero width] {C F : Type} (k : Nat) :
    ∀ (n tar : Nat) (t : StackSemStateFiniteExact width C F) (offset : Nat),
      t.useStack = true ∧ t.stackSpace + tar + n + offset ≤ t.stack.length ∧ n ≤ offset →
      ∃ t' : StackSemStateFiniteExact width C F,
        StackSemEvaluate.evaluate (stackMoveNative n tar offset k .skip, t) = (none, t') ∧
        ∃ (tStack : List (WordLocW width)) (tRegs : HolFiniteMapExact Nat (WordLocW width)),
          t' = {t with stack := tStack, regs := tRegs} ∧
          (∀ i, i ≠ k → StackSemStateOps.getVar i t' = StackSemStateOps.getVar i t) ∧
          t.stack.length = tStack.length ∧ t'.stackSpace = t.stackSpace ∧
          tStack.drop (t'.stackSpace + tar + n) = t.stack.drop (t.stackSpace + tar + n) ∧
          (let stack' := tStack.drop (t'.stackSpace + tar)
           let stack := t.stack.drop (t.stackSpace + tar)
           ∀ x, x < n → holEl (x + offset) stack = holEl x stack') := by
  intro n
  induction n with
  | zero =>
      intro tar t offset _
      refine ⟨t, by simp [stackMoveNative, StackSemEvaluate.evaluate_skip], t.stack, t.regs,
        rfl, fun _ _ => rfl, rfl, rfl, rfl, fun x hx => absurd hx (Nat.not_lt_zero x)⟩
  | succ n ih =>
      intro tar t offset ⟨huse, hlen, hoff⟩
      obtain ⟨t1, hev1, S1, R1, rfl, hget1, hlen1, -, hdrop1, hel1⟩ :=
        ih (tar + 1) t offset ⟨huse, by omega, by omega⟩
      simp only at hdrop1 hel1
      have hb1 : t.stackSpace + (tar + offset) < S1.length := by omega
      have hv : S1[t.stackSpace + (tar + offset)] = t.stack[t.stackSpace + (tar + offset)]'(by omega) :=
        getElem_of_drop_eq hdrop1 (by omega) (by omega) hb1
      simp only [stackMoveNative]
      rw [StackSemEvaluate.evaluate_seq, StackSemEvaluateClock.fixClockEvaluate, hev1]
      simp only
      rw [StackSemEvaluate.evaluate_seq, StackSemEvaluateClock.fixClockEvaluate,
        StackSemEvaluate.evaluate_stackLoad, if_neg (by simp [huse]), dif_pos hb1]
      simp only
      rw [StackSemEvaluate.evaluate_stackStore, if_neg (by simp [StackSemStateOps.setVar, huse]),
        if_neg (by simp [StackSemStateOps.setVar]; omega)]
      simp only [StackSemStateOps.getVar, StackSemStateOps.setVar, HolFiniteMapExact.updateEq,
        FUPDATE_HOL, if_true]
      set v := S1[t.stackSpace + (tar + offset)] with hvdef
      refine ⟨_, rfl, S1.set (t.stackSpace + tar) v, R1.updateEq (k, v), rfl, ?_, ?_, rfl, ?_, ?_⟩
      · intro i hi
        have := hget1 i hi
        simp only [StackSemStateOps.getVar] at this ⊢
        simp [FUPDATE_HOL, hi, this]
      · simp [hlen1]
      · show (S1.set (t.stackSpace + tar) v).drop (t.stackSpace + tar + (n + 1)) =
          t.stack.drop (t.stackSpace + tar + (n + 1))
        rw [List.drop_set, if_pos (by omega), show t.stackSpace + tar + (n + 1) =
          t.stackSpace + (tar + 1) + n by omega]
        exact hdrop1
      · intro x hx
        show holEl (x + offset) (t.stack.drop (t.stackSpace + tar)) =
          holEl x ((S1.set (t.stackSpace + tar) v).drop (t.stackSpace + tar))
        rw [holEl_eq_getElem _ _ (by simp; omega), holEl_eq_getElem _ _ (by simp; omega),
          List.getElem_drop, List.getElem_drop, List.getElem_set]
        rcases x with _ | x
        · rw [if_pos (by omega), hv]
          simp only [show t.stackSpace + tar + (0 + offset) = t.stackSpace + (tar + offset) by omega]
        · rw [if_neg (by omega)]
          have h := hel1 x (by omega)
          rw [holEl_eq_getElem _ _ (by simp; omega), holEl_eq_getElem _ _ (by simp; omega),
            List.getElem_drop, List.getElem_drop] at h
          simp only [show t.stackSpace + tar + (x + 1 + offset) =
              t.stackSpace + (tar + 1) + (x + offset) by omega,
            show t.stackSpace + tar + (x + 1) = t.stackSpace + (tar + 1) + x by omega]
          exact h

theorem holEl_drop {α : Type} [Nonempty α] (l : List α) (m i : Nat) (h : m + i < l.length) :
    holEl i (l.drop m) = l[m + i] := by
  rw [holEl_eq_getElem _ _ (by simp; omega), List.getElem_drop]

/-- Exact HOL `evaluate_copy_ret_aux` (`word_to_stackProofScript.sml:7643-7704`).
HOL's total `EL` is `holEl`. -/
@[hol "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "evaluate_copy_ret_aux"
  (fmap_as_finite_support := [regs, fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem evaluateCopyRetAux {width : Nat} [NeZero width] {C F : Type} :
    ∀ (k f n : Nat) (t : StackSemStateFiniteExact width C F),
      t.useStack = true ∧ f ≠ 0 ∧ f ≤ t.stack.length - (t.stackSpace + n) →
      ∃ t' : StackSemStateFiniteExact width C F,
        StackSemEvaluate.evaluate (copyRetAuxNative k f n, t) = (none, t') ∧
        ∃ (tStack : List (WordLocW width)) (tRegs : HolFiniteMapExact Nat (WordLocW width)),
          t' = {t with stack := tStack, regs := tRegs} ∧
          tStack.length = t.stack.length ∧ t'.stackSpace = t.stackSpace ∧
          tStack.drop (f + n + t'.stackSpace) = t.stack.drop (f + n + t.stackSpace) ∧
          (∀ i, i ≠ k → StackSemStateOps.getVar i t' = StackSemStateOps.getVar i t) ∧
          (∀ m, m < f - n →
            holEl m (tStack.drop (n + t'.stackSpace)) = holEl m (t.stack.drop (n + t.stackSpace))) ∧
          (let stack' := tStack.drop t'.stackSpace
           let stack := t.stack.drop t.stackSpace
           ∀ x, x < n → holEl (x + f) stack' = holEl x stack) := by
  intro k f n
  induction n with
  | zero =>
      intro t _
      refine ⟨t, by simp [copyRetAuxNative, StackSemEvaluate.evaluate_skip], t.stack, t.regs,
        rfl, rfl, rfl, rfl, fun _ _ => rfl, fun _ _ => rfl, fun x hx => absurd hx (Nat.not_lt_zero x)⟩
  | succ n ih =>
      intro t ⟨huse, hf0, hlen⟩
      have hb1 : t.stackSpace + n < t.stack.length := by omega
      have hb2 : t.stackSpace + (n + f) < t.stack.length := by omega
      set v := t.stack[t.stackSpace + n] with hvdef
      simp only [copyRetAuxNative, listSeq]
      rw [StackSemEvaluate.evaluate_seq, StackSemEvaluateClock.fixClockEvaluate,
        StackSemEvaluate.evaluate_stackLoad, if_neg (by simp [huse]), dif_pos hb1]
      simp only
      rw [StackSemEvaluate.evaluate_seq, StackSemEvaluateClock.fixClockEvaluate,
        StackSemEvaluate.evaluate_stackStore, if_neg (by simp [StackSemStateOps.setVar, huse]),
        if_neg (by simp [StackSemStateOps.setVar]; omega)]
      simp only [StackSemStateOps.getVar, StackSemStateOps.setVar, HolFiniteMapExact.updateEq,
        FUPDATE_HOL, if_true]
      set t2 : StackSemStateFiniteExact width C F :=
        {t with regs := t.regs.updateEq (k, v), stack := t.stack.set (t.stackSpace + (n + f)) v}
        with ht2
      obtain ⟨t3, hev3, S3, R3, rfl, hlen3, -, hdrop3, hget3, hmid3, hcopy3⟩ :=
        ih t2 ⟨huse, hf0, by simp [t2]; omega⟩
      dsimp only at hcopy3
      have hsl : (t.stack.set (t.stackSpace + (n + f)) v).length = t.stack.length := by simp
      refine ⟨_, ?_, S3, R3, rfl, ?_, rfl, ?_, ?_, ?_, ?_⟩
      · exact hev3
      · rw [hlen3]; simp [t2]
      · show S3.drop (f + (n + 1) + t.stackSpace) = t.stack.drop (f + (n + 1) + t.stackSpace)
        apply List.ext_getElem?
        intro i
        have h := congrArg (fun l => l[i + 1]?) hdrop3
        simp only [List.getElem?_drop] at h ⊢
        rw [show f + (n + 1) + t.stackSpace + i = f + n + t.stackSpace + (i + 1) by omega]
        change S3[f + n + t.stackSpace + (i + 1)]? =
          (t.stack.set (t.stackSpace + (n + f)) v)[f + n + t.stackSpace + (i + 1)]? at h
        rw [h, List.getElem?_set_ne (by omega)]
      · intro i hi
        have := hget3 i hi
        simp only [StackSemStateOps.getVar] at this ⊢
        rw [this]
        simp [t2, FUPDATE_HOL, hi]
      · intro m hm
        have h := hmid3 (m + 1) (by omega)
        rw [holEl_drop _ _ _ (by rw [hlen3]; simp [t2]; omega),
          holEl_drop _ _ _ (by simp [t2]; omega)] at h
        rw [holEl_drop _ _ _ (by rw [hlen3]; simp [t2]; omega), holEl_drop _ _ _ (by omega)]
        simp only [t2, List.getElem_set] at h
        rw [if_neg (by omega)] at h
        simp only [show n + 1 + t.stackSpace + m = n + t.stackSpace + (m + 1) by omega]
        exact h
      · intro x hx
        rw [holEl_drop _ _ _ (by rw [hlen3]; simp [t2]; omega), holEl_drop _ _ _ (by omega)]
        by_cases hxn : x = n
        · subst hxn
          have hS : S3[t.stackSpace + (x + f)]'(by rw [hlen3]; simp [t2]; omega) =
              t2.stack[t.stackSpace + (x + f)]'(by simp [t2]; omega) := by
            have h1 : (S3.drop (f + x + t.stackSpace))[0]? =
                (t2.stack.drop (f + x + t.stackSpace))[0]? := by rw [hdrop3]
            rw [List.getElem?_drop, List.getElem?_drop] at h1
            rw [List.getElem?_eq_getElem (by rw [hlen3]; simp [t2]; omega),
              List.getElem?_eq_getElem (by simp [t2]; omega)] at h1
            simp only [show f + x + t.stackSpace + 0 = t.stackSpace + (x + f) by omega] at h1
            exact Option.some.inj h1
          rw [hS]
          simp [t2, hvdef]
        · have h := hcopy3 x (by omega)
          rw [holEl_drop _ _ _ (by rw [hlen3]; simp [t2]; omega),
            holEl_drop _ _ _ (by simp [t2]; omega)] at h
          rw [h]
          simp only [t2, List.getElem_set]
          rw [if_neg (by omega)]

end Flapjack.WordToStackProofs.CallReturnEval
