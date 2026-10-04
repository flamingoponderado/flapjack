import Flapjack.Compiler.Backend.StackAlloc.GcCode
import Flapjack.Compiler.Backend.Semantics.StackSem.EvaluateDef
import Flapjack.Compiler.Backend.WordGcFunctions

/-!
# `stack_allocProof` `memcpy_code_thm`

The two `memcpy_code_thm` declarations of
`cakeml/compiler/backend/proofs/stack_allocProofScript.sml` (390, 444): the
stackLang `memcpy_code` loop, run by the exact StackSem `evaluate` with `n` extra
clock ticks, ends with memory `m1` and the four updated registers whenever the
shallow `word_gcFunctions` `memcpy` succeeds. `memcpyBody_eval` (one loop body)
and `memcpyCode_loop` (induction on the count) are Flapjack infrastructure.
-/

namespace Flapjack.Compiler.Backend.StackAlloc

open Flapjack Flapjack.StackSemEvaluate Flapjack.StackSemStateOps Flapjack.StackSemControl
open Flapjack.Compiler.Backend.StackLang Flapjack.Compiler.Encoders.Asm
open Flapjack.Compiler.Backend.StackRemove (loadInst storeInst)

/-- One `memcpy_code` loop body: load, advance source, count down, store,
advance destination. -/
theorem memcpyBody_eval {width : Nat} [NeZero width] {C F : Type}
    (s : StackSemStateFiniteExact width C F) (w a b : BitVec width)
    (h0 : getVar 0 s = some (.word w)) (h2 : getVar 2 s = some (.word a))
    (h3 : getVar 3 s = some (.word b)) (ha : s.mdomain a = true) (hb : s.mdomain b = true) :
    evaluate (listSeqHOL [loadInst 1 2, addBytesInWordInst 2, sub1Inst 0, storeInst 1 3,
      addBytesInWordInst 3], s) =
      (none, { s with
        regs := (((s.regs.updateEq (1, s.memory a)).updateEq (2, .word (a + wordSemBytesInWord))).updateEq
          (0, .word (w - 1))).updateEq (3, .word (b + wordSemBytesInWord))
        memory := fun key => if key = b then s.memory a else s.memory key }) := by
  have h0' : s.regs.lookup 0 = some (.word w) := by simpa [getVar] using h0
  have h2' : s.regs.lookup 2 = some (.word a) := by simpa [getVar] using h2
  have h3' : s.regs.lookup 3 = some (.word b) := by simpa [getVar] using h3
  simp [HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL, h0', h2', h3', listSeqHOL, evaluate_seq, evaluate_inst, loadInst, storeInst, addBytesInWordInst,
    sub1Inst, StackSemInst.instHOL, StackSemIntegerInstructions.instInteger,
    StackSemExpressions.assign, StackSemExpressions.wordExp, setVar, getVar, memLoad, memStore,
    wordOpHOL, wordOp, fixClock, ha, hb]

theorem regs_ext {α β : Type} {f g : HolFiniteMapExact α β}
    (h : ∀ k, f.lookup k = g.lookup k) : f = g := by
  obtain ⟨lf, pf⟩ := f
  obtain ⟨lg, pg⟩ := g
  have : lf = lg := funext h
  subst this
  rfl

/-- The `memcpy_code` loop entry: the `While` test on register 0. -/
theorem memcpyCode_eq {width : Nat} [NeZero width] :
    (memcpyCode : HolProg width) =
      .loop (.ite .notEqual 0 (.imm 0)
        (listSeqHOL [loadInst 1 2, addBytesInWordInst 2, sub1Inst 0, storeInst 1 3,
          addBytesInWordInst 3]) (.break 0)) := rfl

theorem memcpyCode_loop {width : Nat} [NeZero width] {C F : Type} :
    ∀ (n : Nat) (a b b1 : BitVec width) (m1 : BitVec width → WordLocW width)
      (s : StackSemStateFiniteExact width C F),
      WordGcFunctions.memcpy (BitVec.ofNat width n) a b s.memory s.mdomain = (b1, m1, true) →
      n < 2 ^ width →
      getVar 0 s = some (.word (BitVec.ofNat width n)) →
      (s.regs.lookup 1).isSome = true →
      getVar 2 s = some (.word a) → getVar 3 s = some (.word b) →
      ∃ r1, evaluate (memcpyCode, { s with clock := s.clock + n }) =
        (none, { s with
          memory := m1
          regs := s.regs.updateListEq [(0, .word 0), (1, r1),
            (2, .word (a + BitVec.ofNat width n * wordSemBytesInWord)), (3, .word b1)] }) := by
  intro n
  induction n with
  | zero =>
      intro a b b1 m1 s hm _ h0 h1 h2 h3
      rw [show BitVec.ofNat width 0 = 0#width from rfl, WordGcFunctions.memcpy_zero] at hm
      simp only [Prod.mk.injEq] at hm
      obtain ⟨rfl, rfl, -⟩ := hm
      obtain ⟨r1, hr1⟩ := Option.isSome_iff_exists.1 h1
      refine ⟨r1, ?_⟩
      have h0' : s.regs.lookup 0 = some (.word 0) := by simpa [getVar] using h0
      have h2' : s.regs.lookup 2 = some (.word a) := by simpa [getVar] using h2
      have h3' : s.regs.lookup 3 = some (.word b) := by simpa [getVar] using h3
      rw [memcpyCode_eq, evaluate_loop, evaluate_ite, evaluate_break]
      simp only [getVar, HolRegImm.toWordRegImm, Nat.add_zero, h0']
      simp [StackSemStateOps.getVarImm, wordSemWordCmp, wordCmpHOL, fixClock, contLoop,
        StackSemControl.exitLoop]
      apply regs_ext
      intro k
      simp only [HolFiniteMapExact.lookup_updateListEq, FUPDATE_LIST_HOL, List.foldl, FUPDATE_HOL]
      by_cases k0 : k = 0
      · subst k0; simp [h0']
      by_cases k1 : k = 1
      · subst k1; simp [hr1]
      by_cases k2 : k = 2
      · subst k2; simp [h2']
      by_cases k3 : k = 3
      · subst k3; simp [h3']
      simp [k0, k1, k2, k3]
  | succ n ih =>
      intro a b b1 m1 s hm hlt h0 h1 h2 h3
      have hne : BitVec.ofNat width (n + 1) ≠ 0 := by
        intro h
        have := congrArg BitVec.toNat h
        simp [Nat.mod_eq_of_lt hlt] at this
      have hpred : BitVec.ofNat width (n + 1) - 1 = BitVec.ofNat width n := by
        rw [BitVec.ofNat_add]; exact BitVec.add_sub_cancel _ _
      rw [WordGcFunctions.memcpy_of_ne hne, hpred] at hm
      generalize hrec : WordGcFunctions.memcpy (BitVec.ofNat width n) (a + wordSemBytesInWord)
        (b + wordSemBytesInWord) (WordGcFunctions.gcUpdate b (s.memory a) s.memory) s.mdomain = R at hm
      obtain ⟨b1', m1', c1⟩ := R
      simp only [Prod.mk.injEq, Bool.and_eq_true] at hm
      obtain ⟨rfl, rfl, hc1, ha, hb⟩ := hm
      subst hc1
      have h0' : s.regs.lookup 0 = some (.word (BitVec.ofNat width (n + 1))) := by
        simpa [getVar] using h0
      have hbody := memcpyBody_eval { s with clock := s.clock + (n + 1) }
        (BitVec.ofNat width (n + 1)) a b (by simpa [getVar] using h0) (by simpa [getVar] using h2)
        (by simpa [getVar] using h3) ha hb
      rw [memcpyCode_eq, evaluate_loop, evaluate_ite]
      simp only [getVar, HolRegImm.toWordRegImm, h0', StackSemStateOps.getVarImm, wordSemWordCmp,
        wordCmpHOL]
      have hcmp : (!(BitVec.ofNat width (n + 1) == 0)) = true := by simpa using hne
      simp only [hcmp]
      rw [hbody]
      have hck : s.clock + (n + 1) ≠ 0 := by omega
      simp only [fixClock, contLoop, Nat.min_self, if_true, hck, if_false, decClock,
        ← memcpyCode_eq]
      have hmem : (fun key => if key = b then s.memory a else s.memory key) =
          WordGcFunctions.gcUpdate b (s.memory a) s.memory := by
        funext key; simp [WordGcFunctions.gcUpdate, eq_comm]
      let t : StackSemStateFiniteExact width C F :=
        { s with
          regs := (((s.regs.updateEq (1, s.memory a)).updateEq
            (2, .word (a + wordSemBytesInWord))).updateEq
            (0, .word (BitVec.ofNat width n))).updateEq (3, .word (b + wordSemBytesInWord))
          memory := WordGcFunctions.gcUpdate b (s.memory a) s.memory }
      obtain ⟨r1, hr⟩ := ih (a + wordSemBytesInWord) (b + wordSemBytesInWord) b1' m1' t hrec
        (by omega) (by simp [t, getVar, FUPDATE_HOL]) (by simp [t, FUPDATE_HOL])
        (by simp [t, getVar, FUPDATE_HOL]) (by simp [t, getVar, FUPDATE_HOL])
      refine ⟨r1, ?_⟩
      have hst : ({ s with
            regs := (((s.regs.updateEq (1, s.memory a)).updateEq
              (2, .word (a + wordSemBytesInWord))).updateEq
              (0, .word (BitVec.ofNat width (n + 1) - 1))).updateEq
              (3, .word (b + wordSemBytesInWord))
            memory := fun key => if key = b then s.memory a else s.memory key
            clock := s.clock + (n + 1) - 1 } : StackSemStateFiniteExact width C F) =
          { t with clock := t.clock + n } := by
        simp only [t, hpred, hmem]
        congr 1
      rw [hst, hr]
      have harith : a + wordSemBytesInWord + BitVec.ofNat width n * wordSemBytesInWord =
          a + BitVec.ofNat width (n + 1) * wordSemBytesInWord := by
        rw [BitVec.ofNat_add, BitVec.add_mul, BitVec.one_mul, BitVec.add_assoc,
          BitVec.add_comm wordSemBytesInWord]
      simp only [t, harith, Prod.mk.injEq, true_and]
      congr 1
      apply regs_ext
      intro k
      simp only [HolFiniteMapExact.lookup_updateListEq, FUPDATE_LIST_HOL, List.foldl, FUPDATE_HOL,
        HolFiniteMapExact.lookup_updateEq]
      by_cases k0 : k = 0
      · subst k0; simp
      by_cases k1 : k = 1
      · subst k1; simp
      by_cases k2 : k = 2
      · subst k2; simp
      by_cases k3 : k = 3
      · subst k3; simp
      simp [k0, k1, k2, k3]

/-- Canonical finite-support codec of the owning StackSem state carrier, required
by the `fmap_as_finite_support` qualifier of the tagged theorems below. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : StackSemStateBroad width C F) (h : state.FiniteSupport),
        (StackSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : StackSemStateFiniteExact width C F,
        StackSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  StackSemStateOps.holFmapAsFiniteSupportWitness

/-- Exact HOL `memcpy_code_thm` (local, `stack_allocProofScript.sml:390-442`): the
`memcpy_code` loop simulates `memcpy (n2w n)` with `n` extra clock ticks. HOL
`1 IN FDOM s.regs` is `(s.regs.lookup 1).isSome`, `|++` is `updateListEq` and
`dimword (:'a)` is `2 ^ width`. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem memcpy_code_thm_n {width : Nat} [NeZero width] {C F : Type} :
    ∀ (n : Nat) (a b : BitVec width) (m : BitVec width → WordLocW width)
      (dm : BitVec width → Bool) (b1 : BitVec width) (m1 : BitVec width → WordLocW width)
      (s : StackSemStateFiniteExact width C F),
      WordGcFunctions.memcpy (BitVec.ofNat width n) a b m dm = (b1, m1, true) ∧
        n < 2 ^ width ∧ s.memory = m ∧ s.mdomain = dm ∧
        getVar 0 s = some (.word (BitVec.ofNat width n)) ∧ (s.regs.lookup 1).isSome = true ∧
        getVar 2 s = some (.word a) ∧ getVar 3 s = some (.word b) →
      ∃ r1, evaluate (memcpyCode, { s with clock := s.clock + n }) =
        (none, { s with
          memory := m1
          regs := s.regs.updateListEq [(0, .word 0), (1, r1),
            (2, .word (a + BitVec.ofNat width n * wordSemBytesInWord)), (3, .word b1)] }) := by
  rintro n a b m dm b1 m1 s ⟨hm, hlt, rfl, rfl, h0, h1, h2, h3⟩
  exact memcpyCode_loop n a b b1 m1 s hm hlt h0 h1 h2 h3

/-- Exact HOL `memcpy_code_thm` (`stack_allocProofScript.sml:444-463`): the
`memcpy_code` loop simulates `memcpy w` with `w2n w` extra clock ticks. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem memcpy_code_thm {width : Nat} [NeZero width] {C F : Type} :
    ∀ (w a b : BitVec width) (m : BitVec width → WordLocW width)
      (dm : BitVec width → Bool) (b1 : BitVec width) (m1 : BitVec width → WordLocW width)
      (s : StackSemStateFiniteExact width C F),
      WordGcFunctions.memcpy w a b m dm = (b1, m1, true) ∧
        s.memory = m ∧ s.mdomain = dm ∧
        getVar 0 s = some (.word w) ∧ (s.regs.lookup 1).isSome = true ∧
        getVar 2 s = some (.word a) ∧ getVar 3 s = some (.word b) →
      ∃ r1, evaluate (memcpyCode, { s with clock := s.clock + w.toNat }) =
        (none, { s with
          memory := m1
          regs := s.regs.updateListEq [(0, .word 0), (1, r1),
            (2, .word (a + w * wordSemBytesInWord)), (3, .word b1)] }) := by
  rintro w a b m dm b1 m1 s ⟨hm, hs, hd, h0, h1, h2, h3⟩
  have hw : BitVec.ofNat width w.toNat = w := by simp
  have := memcpy_code_thm_n w.toNat a b m dm b1 m1 s
    ⟨by rw [hw]; exact hm, w.isLt, hs, hd, by rw [hw]; exact h0, h1, h2, h3⟩
  rw [hw] at this
  exact this

end Flapjack.Compiler.Backend.StackAlloc
