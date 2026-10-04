import Batteries.Tactic.PermuteGoals
import Flapjack.Compiler.Backend.StackAlloc.Proofs.GcSimple
import Flapjack.Compiler.Backend.StackAlloc.Proofs.CodeThm.GcMoveLoop
import Flapjack.Compiler.Backend.StackAlloc.Proofs.CodeThm.GcMoveRootsBitmaps
import Flapjack.Compiler.Backend.StackAlloc.Proofs.Submap
import Flapjack.Compiler.Backend.StackAlloc.Compile

/-!
# `stack_allocProof` `alloc_correct_lemma_Simple`

`alloc_correct_lemma_Simple` of
`cakeml/compiler/backend/proofs/stack_allocProofScript.sml` (1577-1713): with the
Simple collector, the StackSem `alloc` step is simulated by the stackLang
`word_gc_code` run by the exact StackSem `evaluate`. As in HOL, `gc_thm` unfolds
the collector, and the code runs `word_gc_move_code_thm`,
`word_gc_move_roots_bitmaps_code_thm` and `word_gc_move_loop_code_thm` between
straight-line store and register moves, composed through `evaluate_add_clock`.
-/

namespace Flapjack.Compiler.Backend.StackAlloc

open Flapjack Flapjack.StackSemEvaluate Flapjack.StackSemStateOps Flapjack.StackSemControl
open Flapjack.Compiler.Backend.StackLang Flapjack.Compiler.Encoders.Asm
open Flapjack.Compiler.Backend.DataToWord Flapjack.Compiler.Backend.WordGcFunctions
open Flapjack.Compiler.Backend.StackRemove (loadInst storeInst leftShiftInst rightShiftInst constInst)

theorem holHd_drop {α : Type} [Nonempty α] (l : List α) (n : Nat) (h : n < l.length) :
    holHd (l.drop n) = l[n] := by
  rw [List.drop_eq_getElem_cons h]
  rfl

theorem holFapply_updateEq_ne {α β : Type} [DecidableEq α] [Nonempty β]
    (f : HolFiniteMapExact α β) (k k' : α) (v : β) (h : k' ≠ k) :
    holFapply (f.updateEq (k, v)) k' = holFapply f k' := by
  simp [holFapply, HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL, h]

/-- Instructions and clock-free leaf clauses preserve the clock. -/
theorem evaluate_clock_of_leaf {width : Nat} [NeZero width] {C F : Type} (p : HolProg width)
    (hp : StackProps.EvaluateAddClock.clockFreeCtor p = true ∨ ∃ i, p = .inst i)
    (S : StackSemStateFiniteExact width C F) : (evaluate (p, S)).2.clock = S.clock := by
  rcases hp with hp | ⟨i, rfl⟩
  · exact (StackProps.EvaluateAddClock.clockFree_of_ctor p hp S 0).2
  · exact (StackProps.EvaluateAddClock.clockFree_inst i S 0).2

theorem listSeq_cons_cons {width : Nat} [NeZero width] (x y : HolProg width)
    (ys : List (HolProg width)) :
    listSeqHOL (x :: y :: ys) = .seq x (listSeqHOL (y :: ys)) := rfl

theorem listSeq_cons_append {width : Nat} [NeZero width] (x y : HolProg width)
    (ys zs : List (HolProg width)) :
    listSeqHOL (x :: ((y :: ys) ++ zs)) = .seq x (listSeqHOL ((y :: ys) ++ zs)) := rfl

/-- A normally completing prefix of clock-preserving programs of a `list_Seq`
passes its state to the rest. -/
theorem evaluate_listSeq_append_none {width : Nat} [NeZero width] {C F : Type} :
    ∀ (xs ys : List (HolProg width)) (S S1 : StackSemStateFiniteExact width C F),
      xs ≠ [] → ys ≠ [] →
      (∀ x ∈ xs, ∀ S' : StackSemStateFiniteExact width C F, (evaluate (x, S')).2.clock = S'.clock) →
      evaluate (listSeqHOL xs, S) = (none, S1) →
      evaluate (listSeqHOL (xs ++ ys), S) = evaluate (listSeqHOL ys, S1)
  | [], _, _, _, h, _, _, _ => absurd rfl h
  | [x], y :: ys, S, S1, _, _, hcl, h => by
      change evaluate (x, S) = (none, S1) at h
      have hc := hcl x (by simp) S
      rw [h] at hc
      exact evaluate_seq_none x (listSeqHOL (y :: ys)) S S1 h (by simp at hc; omega)
  | x :: x' :: xs, y :: ys, S, S1, _, _, hcl, h => by
      show evaluate (.seq x (listSeqHOL ((x' :: xs) ++ y :: ys)), S) = _
      rw [show listSeqHOL (x :: x' :: xs) = .seq x (listSeqHOL (x' :: xs)) from rfl,
        evaluate_seq] at h
      rw [evaluate_seq]
      have hc := hcl x (by simp) S
      rcases h1 : evaluate (x, S) with ⟨r1, T⟩
      rw [h1] at h hc
      simp only at hc
      have hfx : fixClock S (r1, T) = (r1, T) := by
        show (r1, { T with clock := min S.clock T.clock }) = (r1, T)
        rw [← hc, Nat.min_self]
      rw [hfx] at h ⊢
      cases r1 with
      | some e => simp at h
      | none =>
        exact evaluate_listSeq_append_none (x' :: xs) (y :: ys) T S1 (by simp) (by simp)
          (fun z hz => hcl z (by simp_all)) h
  | _ :: _, [], _, _, _, h, _, _ => absurd rfl h

namespace AllocSimpleSupport

/-- Canonical finite-support codec of the owning StackSem state carrier, required
by the `fmap_as_finite_support` qualifier of `alloc_correct_lemma_Simple`. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : StackSemStateBroad width C F) (h : state.FiniteSupport),
        (StackSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : StackSemStateFiniteExact width C F,
        StackSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  StackSemStateOps.holFmapAsFiniteSupportWitness

end AllocSimpleSupport

open Classical in
/-- Exact HOL `alloc_correct_lemma_Simple` (`stack_allocProofScript.sml:1577-1713`):
with the Simple collector, `alloc` is simulated by `word_gc_code`. HOL's free
`w s r t conf l ret c anything` are implicit; `fromAList`/`toAList` are
`sptFromAList`/`sptToAList`, `SUBMAP` is `HolFiniteMapExact.submap`, and
`dimword (:'a)` is `2 ^ width`. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem alloc_correct_lemma_Simple {width : Nat} [NeZero width] {C F : Type} {conf : Config}
    {c : DataToWord.Config} {w : BitVec width} {s t : StackSemStateFiniteExact width C F}
    {r : Option (StackSemResult width)} {l : HolFiniteMapExact Nat (WordLocW width)}
    {ret : WordLocW width} {anything : WordSemGcFun width} :
    StackSemAllocation.alloc w s = (r, t) ∧ r ≠ some .error ∧
      s.gcFun = wordGcFun conf ∧ conf.gcKind = .simple ∧
      s.bitmaps.length < 2 ^ width - 1 ∧
      s.stack.length * (width / 8) < 2 ^ width ∧
      l.lookup 0 = some ret ∧ l.lookup 1 = some (.word w) →
    ∃ ck l2,
      evaluate (wordGcCode conf, { s with
          useStore := true, useStack := true, useAlloc := false
          clock := s.clock + ck, regs := l, gcFun := anything
          code := sptFromAList (compile c (sptToAList s.code)) }) =
        (r, { t with
          useStore := true, useStack := true, useAlloc := false
          code := sptFromAList (compile c (sptToAList s.code))
          regs := l2, gcFun := anything }) ∧
      (r ≠ none → r = some (.halt (.word 1))) ∧
      t.regs.submap l2 ∧
      (r = none → l2.lookup 0 = some ret) := by
  rintro ⟨hA, hr, hgc, hk, hbl, hsl0, hl0, hl1⟩
  let s' : StackSemStateFiniteExact width C F := setStore .allocSize (.word w) s
  have hgc' : s'.gcFun = wordGcFun conf := hgc
  have hgcthm := gc_thm (s := s') ⟨hgc', hk⟩
  rw [StackSemAllocation.alloc] at hA
  change (match StackSemAllocation.gc s' with
    | none => (some .error, s)
    | some collected => _) = (r, t) at hA
  rw [hgcthm] at hA
  by_cases hsp : s'.stack.length < s'.stackSpace
  · simp only [hsp, if_true, Prod.mk.injEq] at hA
    exact absurd hA.1.symm hr
  simp only [hsp, if_false] at hA
  generalize hmv : wordGcMove conf (holFapply s'.store .globals, 0,
    wordSemTheWord (holFapply s'.store .otherHeap),
    wordSemTheWord (holFapply s'.store .currHeap), s'.memory, s'.mdomain) = R1 at hA
  obtain ⟨w1, i1, pa1, m1, c1⟩ := R1
  simp only at hA
  generalize hrb : wordGcMoveRootsBitmaps conf (s'.stack.drop s'.stackSpace, s'.bitmaps, i1, pa1,
    wordSemTheWord (holFapply s'.store .currHeap), m1, s'.mdomain) = R2 at hA
  obtain ⟨stack1, i2, pa2, m2, c2⟩ := R2
  simp only at hA
  generalize hlp : wordGcMoveLoop (2 ^ width) conf (wordSemTheWord (holFapply s'.store .otherHeap),
    i2, pa2, wordSemTheWord (holFapply s'.store .currHeap), m2, s'.mdomain, c1 && c2) = R3 at hA
  obtain ⟨i3, pa3, m3, c3⟩ := R3
  simp only at hA
  by_cases hP : wordGcFunAssum conf s'.store ∧ c3 = true
  swap
  · simp only [hP, if_false, Prod.mk.injEq] at hA
    exact absurd hA.1.symm hr
  simp only [hP] at hA
  obtain ⟨hassum, rfl⟩ := hP
  -- the collector's flags
  have hc12 : (c1 && c2) = true := wordGcMoveLoop_ok hlp rfl
  simp only [Bool.and_eq_true] at hc12
  obtain ⟨rfl, rfl⟩ := hc12
  -- the store facts of `word_gc_fun_assum`
  have hassum' := hassum
  obtain ⟨hdom, hwo, hwc, -, hwl, -, -, hwg, hg, hlen, hlen2, hsl⟩ := hassum'
  obtain ⟨other, hother⟩ := (isWord_thm _).1 hwo
  obtain ⟨curr, hcurr⟩ := (isWord_thm _).1 hwc
  obtain ⟨len, hlenw⟩ := (isWord_thm _).1 hwl
  obtain ⟨glob, hglob⟩ := (isWord_thm _).1 hwg
  have hlook : ∀ k : WordStoreHOL, k ∈ ([.globals, .currHeap, .otherHeap, .heapLength, .triggerGC,
      .genStart, .endOfHeap] : List WordStoreHOL) →
      s'.store.lookup k = some (holFapply s'.store k) := by
    intro k hk
    have := hdom k hk
    rcases h : s'.store.lookup k with _ | v
    · simp [h] at this
    · simp [holFapply, h]
  have hlo : s'.store.lookup .otherHeap = some (.word other) := by
    rw [hlook _ (by simp), hother]
  have hlc : s'.store.lookup .currHeap = some (.word curr) := by
    rw [hlook _ (by simp), hcurr]
  have hll : s'.store.lookup .heapLength = some (.word len) := by
    rw [hlook _ (by simp), hlenw]
  have hlg : s'.store.lookup .globals = some (.word glob) := by
    rw [hlook _ (by simp), hglob]
  rw [hother, hcurr, hlenw] at hA
  rw [hother, hcurr] at hlp
  rw [hcurr] at hrb
  rw [hglob, hother, hcurr] at hmv
  simp only [wordSemTheWord] at hA hlp hrb hmv
  -- the allocation's space test
  simp only [and_self, if_true] at hA
  have hspace : StackSemAllocation.hasSpace (.word w : WordLocW width)
      ((s'.store.updateListEq [(.currHeap, .word other), (.otherHeap, .word curr),
        (.nextFree, .word pa3), (.triggerGC, .word (other + len)), (.endOfHeap, .word (other + len)),
        (.globals, w1), (.globReal, globReal conf other w1)])) =
      some (decide (w.toNat ≤ (other + len - pa3).toNat)) := by
    simp [StackSemAllocation.hasSpace, HolFiniteMapExact.lookup_updateListEq, FUPDATE_LIST_HOL,
      FUPDATE_HOL]
  have hal : (s'.store.updateListEq [(.currHeap, .word other), (.otherHeap, .word curr),
        (.nextFree, .word pa3), (.triggerGC, .word (other + len)), (.endOfHeap, .word (other + len)),
        (.globals, w1), (.globReal, globReal conf other w1)]).lookup .allocSize =
      some (.word w) := by
    simp [s', setStore, HolFiniteMapExact.lookup_updateListEq, FUPDATE_LIST_HOL, FUPDATE_HOL,
      HolFiniteMapExact.lookup_updateEq]
  simp only [hal, hspace] at hA
  -- the moved globals root is a word
  obtain ⟨g1, rfl⟩ : ∃ g1, w1 = .word g1 := by
    have hw : ∃ g1, (wordGcMove conf (.word glob, 0, other, curr, s'.memory, s'.mdomain)).1 =
        .word g1 := by
      simp only [wordGcMove]
      split
      · exact ⟨_, rfl⟩
      · split <;> exact ⟨_, rfl⟩
    obtain ⟨g1, hg1⟩ := hw
    rw [hmv] at hg1
    exact ⟨g1, hg1⟩
  -- `word_gc_code` for the Simple collector, split around its three loops
  have hcode : (wordGcCode conf : HolProg width) =
      listSeqHOL ([.set .allocSize 1, .set .nextFree 0, constInst 1 0, moveHOL 2 1,
        .get 3 .otherHeap, moveHOL 4 1, .get 5 .globals, moveHOL 6 1, moveHOL 8 1] ++
      (wordGcMoveCode conf :: ([.set .globals 5, moveHOL 7 5, rightShiftInst 7 (shiftLength conf),
        leftShiftInst 7 (wordShiftAmount width), .get 9 .otherHeap, addInst 7 9, .set .globReal 7,
        constInst 7 0] ++ ([.stackLoadAny 9 8, moveHOL 8 7] ++
      (wordGcMoveRootsBitmapsCode conf :: .get 8 .otherHeap :: wordGcMoveLoopCode conf ::
        [.get 0 .currHeap, .get 1 .otherHeap, .get 2 .heapLength, addInst 2 1, .set .currHeap 1,
         .set .otherHeap 0, .get 0 .nextFree, .set .nextFree 8, .set .endOfHeap 2,
         .set .triggerGC 2, .get 1 .allocSize, subInst 2 8,
         .ite .lower 2 (.reg 1) (.seq (constInst 1 1) (.halt 1)) .skip]))))) := by
    simp only [wordGcCode, hk]
    rfl
  -- the state before `word_gc_move_code`
  let X := sptFromAList (compile c (sptToAList s.code))
  let S0 : StackSemStateFiniteExact width C F := { s with
    useStore := true, useStack := true, useAlloc := false, regs := l, gcFun := anything, code := X }
  let S1 : StackSemStateFiniteExact width C F :=
    setVar 8 (.word 0) (setVar 6 (.word 0) (setVar 5 (.word glob) (setVar 4 (.word 0)
      (setVar 3 (.word other) (setVar 2 (.word 0) (setVar 1 (.word 0)
        (setStore .nextFree ret (setStore .allocSize (.word w) S0))))))))
  have hlo' : s.store.lookup .otherHeap = some (.word other) := by
    simpa [s', setStore, HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL] using hlo
  have hlg' : s.store.lookup .globals = some (.word glob) := by
    simpa [s', setStore, HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL] using hlg
  have hlc' : s.store.lookup .currHeap = some (.word curr) := by
    simpa [s', setStore, HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL] using hlc
  have hll' : s.store.lookup .heapLength = some (.word len) := by
    simpa [s', setStore, HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL] using hll
  have hB1 : ∀ k, evaluate (listSeqHOL [.set .allocSize 1, .set .nextFree 0, constInst 1 0,
      moveHOL 2 1, .get 3 .otherHeap, moveHOL 4 1, .get 5 .globals, moveHOL 6 1, moveHOL 8 1],
      { S0 with clock := k }) = (none, { S1 with clock := k }) := by
    intro k
    simp [listSeqHOL, evaluate_seq, evaluate_set, evaluate_get, evaluate_inst, constInst, moveHOL,
      StackSemInst.instHOL, StackSemIntegerInstructions.instInteger, StackSemExpressions.assign,
      StackSemExpressions.wordExp, getVar, setVar, setStore, fixClock,
      StackSemRegisterTransfers.storeOfSyntax, HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL,
      hl0, hl1, hlo', hlg', S0, S1]
  -- word-dimension facts of `good_dimindex`
  have hws : wordShiftAmount width < width := by
    unfold wordShiftAmount
    rcases hg with h | h <;> simp [h]
  have hw2 : 2 < width := by
    rcases hg with h | h <;> omega
  have hshift : ∀ x : BitVec width, x <<< wordShiftAmount width = x * wordSemBytesInWord := by
    intro x
    rw [← bytesInWord_mul_eq_shift x hg, BitVec.mul_comm]
  -- `word_gc_move_code` on the globals root
  obtain ⟨ckG, q0, q1, q2, q6, hG⟩ := word_gc_move_code_thm (s := S1)
    ⟨hmv, hsl, hws, hw2, hlen, hshift,
      by simp [S1, S0, setVar, setStore, HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL, hlc'],
      rfl, rfl, rfl,
      by simp [S1, S0, setVar, setStore, HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL, hl0],
      by simp [S1, setVar, HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL],
      by simp [S1, setVar, HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL],
      by simp [S1, getVar, setVar, HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL],
      by simp [S1, getVar, setVar, HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL],
      by simp [S1, getVar, setVar, HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL],
      by simp [S1, setVar, HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL]⟩
  let SG : StackSemStateFiniteExact width C F := { S1 with
    memory := m1
    regs := S1.regs.updateListEq [(0, q0), (1, q1), (2, q2), (3, .word pa1), (4, .word i1),
      (5, .word g1), (6, q6)] }
  -- the straight-line block after it
  let gr : BitVec width := (g1 >>> shiftLength conf <<< wordShiftAmount width) + other
  let S2a : StackSemStateFiniteExact width C F :=
    setVar 7 (.word 0) (setStore .globReal (.word gr) (setVar 7 (.word gr) (setVar 9 (.word other)
      (setVar 7 (.word (g1 >>> shiftLength conf <<< wordShiftAmount width))
        (setVar 7 (.word (g1 >>> shiftLength conf)) (setVar 7 (.word g1)
          (setStore .globals (.word g1) SG)))))))
  have hpow : width < 2 ^ width := Nat.lt_two_pow_self
  have hslm : shiftLength conf % 2 ^ width = shiftLength conf := Nat.mod_eq_of_lt (by omega)
  have hwsm : wordShiftAmount width % 2 ^ width = wordShiftAmount width :=
    Nat.mod_eq_of_lt (by omega)
  have hsl_le : ¬ width ≤ shiftLength conf := by omega
  have hws_le : ¬ width ≤ wordShiftAmount width := by omega
  have hB2a : ∀ k, evaluate (listSeqHOL [.set .globals 5, moveHOL 7 5,
      rightShiftInst 7 (shiftLength conf), leftShiftInst 7 (wordShiftAmount width),
      .get 9 .otherHeap, addInst 7 9, .set .globReal 7, constInst 7 0],
      { SG with clock := k }) = (none, { S2a with clock := k }) := by
    intro k
    simp [listSeqHOL, evaluate_seq, evaluate_set, evaluate_get, evaluate_inst, constInst, moveHOL,
      rightShiftInst, leftShiftInst, addInst,
      StackSemInst.instHOL, StackSemIntegerInstructions.instInteger, StackSemExpressions.assign,
      StackSemExpressions.wordExp, wordOpHOL, wordOp, getVar, setVar, setStore, fixClock,
      StackSemRegisterTransfers.storeOfSyntax, HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL,
      HolFiniteMapExact.lookup_updateListEq, FUPDATE_LIST_HOL, wordShiftHOL, hslm, hwsm, hsl_le,
      hws_le, hlo', S0, S1, SG, S2a, gr]
  -- the stack has a frame above `stack_space`
  have hsplt : s.stackSpace < s.stack.length := by
    by_contra hc
    have hd : s'.stack.drop s'.stackSpace = [] :=
      List.drop_eq_nil_of_le (by simp only [s', setStore]; omega)
    rw [hd] at hrb
    have := wordGcMoveRootsBitmaps_unroll _ _ _ _ _ _ _ _ hrb
    rw [this] at hrb
    simp at hrb
  have hj : S2a.stackSpace + 0 < S2a.stack.length := hsplt
  have hv : S2a.stack[S2a.stackSpace + 0]'hj = holHd (s.stack.drop s.stackSpace) :=
    (holHd_drop _ _ hsplt).symm
  let S2 : StackSemStateFiniteExact width C F :=
    setVar 8 (.word 0) (setVar 9 (holHd (s.stack.drop s.stackSpace)) S2a)
  have hB2b : ∀ k, evaluate (.seq (.stackLoadAny 9 8) (listSeqHOL [moveHOL 8 7]),
      { S2a with clock := k }) = (none, { S2 with clock := k }) := by
    intro k
    rw [evaluate_seq_none _ _ _ _ (stackLoadAny_eval { S2a with clock := k } 9 8 0 rfl
        (by simp [S2a, SG, S1, setVar, setStore, HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL,
          HolFiniteMapExact.lookup_updateListEq, FUPDATE_LIST_HOL])
        hg (Nat.two_pow_pos width) hj) le_rfl]
    rw [show ({ S2a with clock := k } : StackSemStateFiniteExact width C F).stack[
        ({ S2a with clock := k } : StackSemStateFiniteExact width C F).stackSpace + 0]'hj =
        holHd (s.stack.drop s.stackSpace) from hv]
    rw [show listSeqHOL [moveHOL 8 7] = (moveHOL 8 7 : HolProg width) from rfl,
      moveHOL_eval _ 8 7 0 (by simp [S2a, setVar, HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL])]
    rfl
  -- `word_gc_move_roots_bitmaps_code` over the stack frames
  have hstk : S2.stack = s.stack.take s.stackSpace ++ [] ++ s.stack.drop s.stackSpace := by
    simp [S2, S2a, SG, S1, S0, setVar, setStore]
  obtain ⟨ckR, p0, p1, p2, p5, p6, p7, p8, _, hR⟩ :=
    word_gc_move_roots_bitmaps_code_thm (conf := conf) (init := s.stack.take s.stackSpace)
      (stack := s.stack.drop s.stackSpace) s.bitmaps S2 i1 pa1 curr m1 s.mdomain [] stack1 0
      i2 pa2 m2 []
      ⟨hrb, hbl, hg, hsl, hws, hw2, hlen, hg, hshift,
        by simp [S2, S2a, SG, S1, S0, setVar, setStore, HolFiniteMapExact.lookup_updateEq,
          FUPDATE_HOL, hlc'],
        rfl, rfl, rfl, rfl, rfl,
        by simp [S2, S2a, SG, setVar, setStore, HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL,
          HolFiniteMapExact.lookup_updateListEq, FUPDATE_LIST_HOL],
        by simp [S2, S2a, SG, setVar, setStore, HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL,
          HolFiniteMapExact.lookup_updateListEq, FUPDATE_LIST_HOL],
        by simp [S2, S2a, SG, setVar, setStore, HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL,
          HolFiniteMapExact.lookup_updateListEq, FUPDATE_LIST_HOL],
        by simp [S2, S2a, SG, getVar, setVar, setStore, HolFiniteMapExact.lookup_updateEq,
          FUPDATE_HOL, HolFiniteMapExact.lookup_updateListEq, FUPDATE_LIST_HOL],
        by simp [S2, S2a, SG, getVar, setVar, setStore, HolFiniteMapExact.lookup_updateEq,
          FUPDATE_HOL, HolFiniteMapExact.lookup_updateListEq, FUPDATE_LIST_HOL],
        by simp [S2, S2a, SG, setVar, setStore, HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL,
          HolFiniteMapExact.lookup_updateListEq, FUPDATE_LIST_HOL],
        by simp [S2, S2a, SG, setVar, setStore, HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL,
          HolFiniteMapExact.lookup_updateListEq, FUPDATE_LIST_HOL],
        by simp [S2, S2a, setVar, setStore, HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL],
        by simp [S2, getVar, setVar, HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL],
        by simp [S2, getVar, setVar, HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL],
        hstk,
        by simp [S2, S2a, SG, S1, S0, setVar, setStore]; omega,
        by simp only [S2, S2a, SG, S1, S0, setVar, setStore]; rw [Nat.mul_comm]; exact hsl0⟩
  let S2R : StackSemStateFiniteExact width C F := { S2 with
    memory := m2
    stack := s.stack.take s.stackSpace ++ [] ++ stack1
    clock := S2.clock
    regs := S2.regs.updateListEq [(0, p0), (1, p1), (2, p2), (3, .word pa2), (4, .word i2),
      (5, p5), (6, p6), (7, p7), (8, p8), (9, .word 0)] }
  have hlo2 : S2R.store.lookup .otherHeap = some (.word other) := by
    simp [S2R, S2, S2a, SG, S1, S0, setVar, setStore, HolFiniteMapExact.lookup_updateEq,
      FUPDATE_HOL, hlo']
  let S3 : StackSemStateFiniteExact width C F := setVar 8 (.word other) S2R
  have hB3 : ∀ k, evaluate (.get 8 .otherHeap, { S2R with clock := k }) =
      (none, { S3 with clock := k }) := by
    intro k
    rw [evaluate_get]
    simp [S3, S2R, S2, S2a, SG, S1, S0, setVar, setStore, StackSemRegisterTransfers.storeOfSyntax,
      HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL, hlo']
  -- `word_gc_move_loop_code` over the copied objects
  obtain ⟨ckL, u0, u1, u2, u5, u6, u7, hL⟩ :=
    word_gc_move_loop_code_thm (conf := conf) (2 ^ width) other i2 pa2 curr m2 s.mdomain true i3
      pa3 m3 S3
      ⟨by simpa [s', setStore] using hlp, hsl, hws, hw2, hlen, hlen2, hshift,
        by simp [S3, S2R, S2, S2a, SG, S1, S0, setVar, setStore, HolFiniteMapExact.lookup_updateEq,
          FUPDATE_HOL, hlc'],
        rfl, rfl, rfl,
        by simp [S3, S2R, setVar, HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL,
          HolFiniteMapExact.lookup_updateListEq, FUPDATE_LIST_HOL],
        by simp [S3, S2R, setVar, HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL,
          HolFiniteMapExact.lookup_updateListEq, FUPDATE_LIST_HOL],
        by simp [S3, S2R, setVar, HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL,
          HolFiniteMapExact.lookup_updateListEq, FUPDATE_LIST_HOL],
        by simp [S3, S2R, getVar, setVar, HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL,
          HolFiniteMapExact.lookup_updateListEq, FUPDATE_LIST_HOL],
        by simp [S3, S2R, getVar, setVar, HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL,
          HolFiniteMapExact.lookup_updateListEq, FUPDATE_LIST_HOL],
        by simp [S3, S2R, setVar, HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL,
          HolFiniteMapExact.lookup_updateListEq, FUPDATE_LIST_HOL]⟩
      (by simp [S3, S2R, setVar, HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL,
          HolFiniteMapExact.lookup_updateListEq, FUPDATE_LIST_HOL])
      (by simp [S3, S2R, setVar, HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL,
          HolFiniteMapExact.lookup_updateListEq, FUPDATE_LIST_HOL])
      ⟨by simp [S3, getVar, setVar, HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL], rfl⟩
  let S3L : StackSemStateFiniteExact width C F := { S3 with
    memory := m3
    regs := S3.regs.updateListEq [(0, u0), (1, u1), (2, u2), (3, .word pa3), (4, .word i3),
      (5, u5), (6, u6), (7, u7), (8, .word pa3)] }
  -- the closing block: swap the heaps, restore register 0, test the space
  let Sfin : StackSemStateFiniteExact width C F :=
    setVar 2 (.word (len + other - pa3)) (setVar 1 (.word w)
      (setStore .triggerGC (.word (len + other)) (setStore .endOfHeap (.word (len + other))
        (setStore .nextFree (.word pa3) (setVar 0 ret (setStore .otherHeap (.word curr)
          (setStore .currHeap (.word other) (setVar 2 (.word (len + other)) (setVar 2 (.word len)
            (setVar 1 (.word other) (setVar 0 (.word curr) S3L)))))))))))
  have hB4 : evaluate (listSeqHOL [.get 0 .currHeap, .get 1 .otherHeap, .get 2 .heapLength,
      addInst 2 1, .set .currHeap 1, .set .otherHeap 0, .get 0 .nextFree, .set .nextFree 8,
      .set .endOfHeap 2, .set .triggerGC 2, .get 1 .allocSize, subInst 2 8,
      .ite .lower 2 (.reg 1) (.seq (constInst 1 1) (.halt 1)) .skip], S3L) =
      if len + other - pa3 < w then (some (.halt (.word 1)), emptyEnv Sfin) else (none, Sfin) := by
    by_cases hlt : len + other - pa3 < w
    · simp [listSeqHOL, evaluate_seq, evaluate_set, evaluate_get, evaluate_inst, evaluate_ite,
        evaluate_halt, constInst, addInst, subInst,
        StackSemInst.instHOL, StackSemIntegerInstructions.instInteger, StackSemExpressions.assign,
        StackSemExpressions.wordExp, wordOpHOL, wordOp, getVar, setVar, setStore, fixClock,
        StackSemStateOps.getVarImm, HolRegImm.toWordRegImm, wordSemWordCmp, wordCmpHOL, emptyEnv,
        StackSemRegisterTransfers.storeOfSyntax, HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL,
        HolFiniteMapExact.lookup_updateListEq, FUPDATE_LIST_HOL, hlo', hlc', hll', hlt,
        S3L, S3, S2R, S2, S2a, SG, S1, S0, Sfin]
    · simp [listSeqHOL, evaluate_seq, evaluate_set, evaluate_get, evaluate_inst, evaluate_ite,
        evaluate_skip, constInst, addInst, subInst,
        StackSemInst.instHOL, StackSemIntegerInstructions.instInteger, StackSemExpressions.assign,
        StackSemExpressions.wordExp, wordOpHOL, wordOp, getVar, setVar, setStore, fixClock,
        StackSemStateOps.getVarImm, HolRegImm.toWordRegImm, wordSemWordCmp, wordCmpHOL,
        StackSemRegisterTransfers.storeOfSyntax, HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL,
        HolFiniteMapExact.lookup_updateListEq, FUPDATE_LIST_HOL, hlo', hlc', hll', hlt,
        S3L, S3, S2R, S2, S2a, SG, S1, S0, Sfin]
  -- the whole run, with the three collectors' clocks added up
  have hGk := StackProps.evaluateAddClock (ckR + ckL) _ _ _ _ ⟨hG, by simp⟩
  have hRk := StackProps.evaluateAddClock ckL _ _ _ _ ⟨hR, by simp⟩
  have hS1c : S1.clock = s.clock := rfl
  have hS2c : S2.clock = s.clock := rfl
  have hS3c : S3.clock = s.clock := rfl
  have hrun : evaluate (wordGcCode conf, { S0 with clock := s.clock + (ckG + ckR + ckL) }) =
      evaluate (listSeqHOL [.get 0 .currHeap, .get 1 .otherHeap, .get 2 .heapLength,
        addInst 2 1, .set .currHeap 1, .set .otherHeap 0, .get 0 .nextFree, .set .nextFree 8,
        .set .endOfHeap 2, .set .triggerGC 2, .get 1 .allocSize, subInst 2 8,
        .ite .lower 2 (.reg 1) (.seq (constInst 1 1) (.halt 1)) .skip], S3L) := by
    rw [hcode, evaluate_listSeq_append_none _ _ _ _ (by simp) (by simp)
      (by
        intro x hx S'
        simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
        rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
          first
            | exact evaluate_clock_of_leaf _ (Or.inl rfl) S'
            | exact evaluate_clock_of_leaf _ (Or.inr ⟨_, rfl⟩) S')
      (hB1 _)]
    have hGk' : evaluate (wordGcMoveCode conf, { S1 with clock := s.clock + (ckG + ckR + ckL) }) =
        (none, { SG with clock := s.clock + (ckR + ckL) }) := by
      have e1 : ({ S1 with clock := s.clock + (ckG + ckR + ckL) } :
          StackSemStateFiniteExact width C F) =
          { { S1 with clock := S1.clock + ckG } with
            clock := { S1 with clock := S1.clock + ckG }.clock + (ckR + ckL) } := by
        simp only [hS1c]
        congr 1
        omega
      rw [e1]
      exact hGk
    have hRk' : evaluate (wordGcMoveRootsBitmapsCode conf, { S2 with clock := s.clock + (ckR + ckL) }) =
        (none, { S2R with clock := s.clock + ckL }) := by
      have e2 : ({ S2 with clock := s.clock + (ckR + ckL) } : StackSemStateFiniteExact width C F) =
          { { S2 with clock := S2.clock + ckR } with
            clock := { S2 with clock := S2.clock + ckR }.clock + ckL } := by
        simp only [hS2c]
        congr 1
        omega
      rw [e2]
      exact hRk
    have hLk : evaluate (wordGcMoveLoopCode conf, { S3 with clock := s.clock + ckL }) =
        (none, S3L) := hL
    rw [listSeq_cons_append, evaluate_seq_none _ _ _ _ hGk' (by dsimp only; omega),
      evaluate_listSeq_append_none _ _ _ _ (by simp) (by simp)
        (by
          intro x hx S'
          simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
          rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
            first
              | exact evaluate_clock_of_leaf _ (Or.inl rfl) S'
              | exact evaluate_clock_of_leaf _ (Or.inr ⟨_, rfl⟩) S')
        (hB2a _),
      evaluate_listSeq_append_none _ _ _ _ (by simp) (by simp)
        (by
          intro x hx S'
          simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
          rcases hx with rfl | rfl <;>
            first
              | exact evaluate_clock_of_leaf _ (Or.inl rfl) S'
              | exact evaluate_clock_of_leaf _ (Or.inr ⟨_, rfl⟩) S')
        (show evaluate (listSeqHOL [.stackLoadAny 9 8, moveHOL 8 7],
            { S2a with clock := s.clock + (ckR + ckL) }) =
            (none, { S2 with clock := s.clock + (ckR + ckL) }) from hB2b _),
      listSeq_cons_cons, evaluate_seq_none _ _ _ _ hRk' (by dsimp only; omega),
      listSeq_cons_cons, evaluate_seq_none _ _ _ _ (hB3 _) le_rfl,
      listSeq_cons_cons, evaluate_seq_none _ _ _ _ hLk (by dsimp only [S3L]; omega)]
  -- the final store is the collector's store
  have hstore : Sfin.store = s'.store.updateListEq [(.currHeap, .word other),
      (.otherHeap, .word curr), (.nextFree, .word pa3), (.triggerGC, .word (other + len)),
      (.endOfHeap, .word (other + len)), (.globals, .word g1),
      (.globReal, globReal conf other (.word g1))] := by
    apply regs_ext
    intro k
    cases k <;> simp [Sfin, S3L, S3, S2R, S2, S2a, SG, S1, S0, s', gr, setVar, setStore, globReal,
      HolFiniteMapExact.lookup_updateEq, HolFiniteMapExact.lookup_updateListEq, FUPDATE_HOL,
      FUPDATE_LIST_HOL, BitVec.add_comm]
  have hlt_iff : (len + other - pa3 < w) ↔ ¬ w.toNat ≤ (other + len - pa3).toNat := by
    rw [BitVec.add_comm len other, BitVec.lt_def]
    omega
  by_cases hsp2 : w.toNat ≤ (other + len - pa3).toNat
  · simp only [hsp2, decide_true, Prod.mk.injEq] at hA
    obtain ⟨rfl, rfl⟩ := hA
    refine ⟨ckG + ckR + ckL, Sfin.regs, ?_, by simp, ?_, ?_⟩
    · change evaluate (wordGcCode conf, { S0 with clock := s.clock + (ckG + ckR + ckL) }) = _
      rw [hrun, hB4, if_neg (fun h => hlt_iff.1 h hsp2)]
      simp only [Prod.mk.injEq, true_and]
      rw [← hstore]
      simp [Sfin, S3L, S3, S2R, S2, S2a, SG, S1, S0, s', X, setVar, setStore]
    · intro k v hkv
      simp [HolFiniteMapExact.lookup_empty] at hkv
    · intro _
      simp [Sfin, setVar, setStore, HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL]
  · simp only [hsp2, decide_false, Prod.mk.injEq] at hA
    obtain ⟨rfl, rfl⟩ := hA
    refine ⟨ckG + ckR + ckL, HolFiniteMapExact.empty, ?_, fun _ => rfl, ?_, fun h => by cases h⟩
    · change evaluate (wordGcCode conf, { S0 with clock := s.clock + (ckG + ckR + ckL) }) = _
      rw [hrun, hB4, if_pos (hlt_iff.2 hsp2)]
      simp only [Prod.mk.injEq, true_and]
      simp only [emptyEnv]
      rw [hstore]
      simp [Sfin, S3L, S3, S2R, S2, S2a, SG, S1, S0, s', X, setVar, setStore]
    · intro k v hkv
      simp [emptyEnv, HolFiniteMapExact.lookup_empty] at hkv

end Flapjack.Compiler.Backend.StackAlloc
