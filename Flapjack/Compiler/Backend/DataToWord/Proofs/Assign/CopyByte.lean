module

public import Flapjack.Compiler.Backend.DataToWord.Proofs.Assign.InstallStubs
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.ByteCopy

@[expose] public section

/-! The byte-copy loops of `data_to_word_assignProofScript.sml`
(`CopyByteAdd_thm` and `CopyByteSub_thm`, lines 2977-3200). -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Assign
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.DataToWord
open Flapjack.Compiler.Backend.DataToWord.Proofs.Memory

namespace CopyByteWitness
/-- Canonical finite-map roundtrip for the target word state. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : WordSemStateBroad width C F) (h : state.FiniteSupport),
      (WordSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : WordSemStateFiniteExact width C F,
      WordSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  WordSemStateExact.holFmapAsFiniteSupportWitness
end CopyByteWitness

/-- Execute an instruction before its continuation. -/
private theorem copySeqInst {width : Nat} [NeZero width] {C F : Type}
    (s s' : WordSemStateFiniteExact width C F) (i : WordLangInst (BitVec width))
    (tail : WordLangProgHOL (BitVec width)) (h : WordSemStateFiniteExact.inst i s = some s')
    (clock : s'.clock = s.clock) (term : s'.termdep = s.termdep) :
    WordSemStateFiniteExact.evaluate (.seq (.inst i) tail) s =
      WordSemStateFiniteExact.evaluate tail s' := by
  simp [WordSemStateFiniteExact.evaluate, h, WordSemStateFiniteExact.fixClock, clock]
  rw [← term, ← clock]

/-- A byte load from a register plus offset. -/
private theorem copyLoad8 {width : Nat} [NeZero width] {C F : Type}
    (s : WordSemStateFiniteExact width C F) (r a : Nat) (off x : BitVec width) (b : BitVec 8)
    (ra : s.getVar a = some (.word x))
    (load : memLoadByteAuxExact s.memory s.mdomain s.be (x + off) = some b) :
    WordSemStateFiniteExact.inst (.mem .load8 r (.addr a off)) s =
      some (s.setVar r (.word (b.setWidth width))) := by
  simp [WordSemStateFiniteExact.inst, WordSemStateFiniteExact.wordExp, ra, theWords, wordOpHOL,
    wordOp, load]

/-- A byte store from a register to a register plus offset. -/
private theorem copyStore8 {width : Nat} [NeZero width] {C F : Type}
    (s : WordSemStateFiniteExact width C F) (r a : Nat) (off x w : BitVec width)
    (m' : BitVec width → WordLocW width)
    (ra : s.getVar a = some (.word x)) (rr : s.getVar r = some (.word w))
    (store : memStoreByteAuxExact s.memory s.mdomain s.be (x + off) (w.setWidth 8) = some m') :
    WordSemStateFiniteExact.inst (.mem .store8 r (.addr a off)) s = some { s with memory := m' } := by
  simp [WordSemStateFiniteExact.inst, WordSemStateFiniteExact.wordExp, ra, rr, theWords, wordOpHOL,
    wordOp, store]

/-- Branch on a comparison of a word register with an immediate. -/
private theorem copyEvalIteImm {width : Nat} [NeZero width] {C F : Type}
    (s : WordSemStateFiniteExact width C F) (cmp : Cmp) (r : Nat) (a c : BitVec width)
    (p q : WordLangProgHOL (BitVec width)) (ra : s.getVar r = some (.word a)) :
    WordSemStateFiniteExact.evaluate (.ite cmp r (.imm c) p q) s =
      if Compiler.Encoders.Asm.wordCmpHOL cmp a c then WordSemStateFiniteExact.evaluate p s
      else WordSemStateFiniteExact.evaluate q s := by
  simp [WordSemStateFiniteExact.evaluate, ra, WordSemStateFiniteExact.getVarImm, wordSemWordCmp]
  cases Compiler.Encoders.Asm.wordCmpHOL cmp a c <;> simp

/-- Return the value of register 8 to the location in register 0. -/
private theorem copyReturn {width : Nat} [NeZero width] {C F : Type}
    (s : WordSemStateFiniteExact width C F) (l1 l2 : Nat) (v : WordLocW width)
    (r0 : s.getVar 0 = some (.loc l1 l2)) (r8 : s.getVar 8 = some v) :
    WordSemStateFiniteExact.evaluate (.return 0 [8]) s =
      (some (.result (.loc l1 l2) [v]), WordSemStateFiniteExact.flushState false s) := by
  simp [WordSemStateFiniteExact.evaluate, r0, r8, WordSemStateFiniteExact.getVars]

/-- The expanded forward byte-copy stub. -/
private theorem byteCopyAddCode_eq {width : Nat} [NeZero width] :
    (byteCopyAddCode : WordLangProgHOL (BitVec width)) =
      let L (r k : Nat) : WordLangProgHOL (BitVec width) :=
        .inst (.mem .load8 r (.addr 4 (BitVec.ofNat width k)))
      let S (r k : Nat) : WordLangProgHOL (BitVec width) :=
        .inst (.mem .store8 r (.addr 6 (BitVec.ofNat width k)))
      .ite .lower 2 (.imm 4)
        (.ite .lower 2 (.imm 2)
          (.ite .equal 2 (.imm 0) (.return 0 [8]) (.seq (L 1 0) (.seq (S 1 0) (.return 0 [8]))))
          (.seq (L 1 0) (.seq (L 3 1)
            (.ite .equal 2 (.imm 2) (.seq (S 1 0) (.seq (S 3 1) (.return 0 [8])))
              (.seq (L 5 2) (.seq (S 1 0) (.seq (S 3 1) (.seq (S 5 2) (.return 0 [8])))))))))
        (.seq (L 1 0) (.seq (L 3 1) (.seq (L 5 2) (.seq (L 7 3) (.seq (S 1 0) (.seq (S 3 1)
          (.seq (S 5 2) (.seq (S 7 3) (.seq (.assign 9 (.op .sub [.var 2, .const 4]))
            (.seq (.assign 11 (.op .add [.var 4, .const 4]))
              (.seq (.assign 13 (.op .add [.var 6, .const 4]))
                (.call none (some byteCopyAddLocation) [0, 9, 11, 13, 8] none)))))))))))) := rfl

/-- The forward byte-copy stub implements `word_copy_fwd`. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_assignProofScript.sml" "CopyByteAdd_thm"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem copyByteAdd_correct {width : Nat} [NeZero width] {C F : Type}
    (be : Bool) (n a1 a2 : BitVec width) (m : BitVec width → WordLocW width)
    (dm : BitVec width → Bool) (retVal : WordLocW width) (l1 l2 : Nat)
    (s : WordSemStateFiniteExact width C F) (m1 : BitVec width → WordLocW width)
    (h : wordCopyFwd be n a1 a2 m dm = some m1 ∧ s.memory = m ∧ s.mdomain = dm ∧ s.be = be ∧
      goodDimindex width ∧ sptLookup byteCopyAddLocation s.code = some (5, byteCopyAddCode) ∧
      n.toNat / 4 ≤ s.clock ∧ s.getVar 0 = some (.loc l1 l2) ∧ s.getVar 2 = some (.word n) ∧
      s.getVar 4 = some (.word a1) ∧ s.getVar 6 = some (.word a2) ∧ s.getVar 8 = some retVal) :
    WordSemStateFiniteExact.evaluate byteCopyAddCode s =
      (some (.result (.loc l1 l2) [retVal]),
        { s with
          clock := s.clock - n.toNat / 4
          memory := m1
          locals := .ln
          localsSize := some 0
          stackMax := if n < 4#width then s.stackMax else
            Option.map₂ max s.stackMax (Option.map₂ (· + ·) (wordSemStackSize s.stack)
              (sptLookup byteCopyAddLocation s.stackSize)) }) := by
  induction hk : n.toNat using Nat.strong_induction_on generalizing n a1 a2 m s m1 with
  | _ k ih =>
  obtain ⟨run, hm, hdm, hbe, good, code, clock, r0, r2, r4, r6, r8⟩ := h
  subst hm hdm hbe
  have big : ¬ 2 ^ width ≤ 4 := by rcases good with rfl | rfl <;> decide
  rw [wordCopyFwd, dif_neg big] at run
  rw [byteCopyAddCode_eq]
  dsimp only
  rw [copyEvalIteImm s .lower 2 n 4 _ _ r2]
  by_cases lt4 : n < 4#width
  · have low : Compiler.Encoders.Asm.wordCmpHOL .lower n 4 = true := by
      simpa [Compiler.Encoders.Asm.wordCmpHOL] using lt4
    rw [if_pos low]
    rw [dif_pos lt4] at run
    have kq : k / 4 = 0 := by
      have : n.toNat < 4 := by
        rcases good with rfl | rfl <;> simpa [BitVec.lt_def] using lt4
      omega
    simp only [lt4, if_true, kq, Nat.sub_zero]
    rw [copyEvalIteImm s .lower 2 n 2 _ _ r2]
    by_cases lt2 : n < 2#width
    · rw [if_pos (by simpa [Compiler.Encoders.Asm.wordCmpHOL] using lt2)]
      rw [if_pos lt2] at run
      rw [copyEvalIteImm s .equal 2 n 0 _ _ r2]
      by_cases z : n = 0#width
      · rw [if_pos (by simp [Compiler.Encoders.Asm.wordCmpHOL, z])]
        rw [if_pos z] at run
        cases run
        rw [copyReturn s l1 l2 retVal r0 r8]
        simp [WordSemStateFiniteExact.flushState]
      · rw [if_neg (by simp [Compiler.Encoders.Asm.wordCmpHOL, z])]
        rw [if_neg z] at run
        obtain ⟨w, hl, hs⟩ := Option.bind_eq_some_iff.mp run
        rw [copySeqInst _ _ _ _ (copyLoad8 s 1 4 (BitVec.ofNat width 0) a1 w r4 (by simpa using hl)) rfl rfl]
        rw [copySeqInst _ _ _ _ (copyStore8 (s.setVar 1 (.word (w.setWidth width))) 1 6 (BitVec.ofNat width 0) a2 (w.setWidth width) m1 (by simpa [WordSemStateFiniteExact.setVar,
          WordSemStateFiniteExact.getVar, installLookupInsert] using r6)
          (by simp [WordSemStateFiniteExact.setVar, WordSemStateFiniteExact.getVar, installLookupInsert])
          (by simpa [WordSemStateFiniteExact.setVar, goodDimindex_w2w_byte w good] using hs)) rfl rfl]
        rw [copyReturn _ l1 l2 retVal (by simpa [WordSemStateFiniteExact.setVar,
          WordSemStateFiniteExact.getVar, installLookupInsert] using r0)
          (by simpa [WordSemStateFiniteExact.setVar, WordSemStateFiniteExact.getVar,
            installLookupInsert] using r8)]
        simp [WordSemStateFiniteExact.flushState, WordSemStateFiniteExact.setVar]
    · rw [if_neg (by simpa [Compiler.Encoders.Asm.wordCmpHOL] using lt2)]
      rw [if_neg lt2] at run
      obtain ⟨w1, hl1, run⟩ := Option.bind_eq_some_iff.mp run
      obtain ⟨w2, hl2, run⟩ := Option.bind_eq_some_iff.mp run
      let s1 := s.setVar 1 (.word (w1.setWidth width))
      let s2 := s1.setVar 3 (.word (w2.setWidth width))
      rw [copySeqInst _ s1 _ _ (copyLoad8 s 1 4 (BitVec.ofNat width 0) a1 w1 r4 (by simpa using hl1)) rfl rfl]
      rw [copySeqInst _ s2 _ _ (copyLoad8 s1 3 4 (BitVec.ofNat width 1) a1 w2 (by simpa [s1, s2, WordSemStateFiniteExact.setVar, WordSemStateFiniteExact.getVar, installLookupInsert] using r4) (by simpa [s1, WordSemStateFiniteExact.setVar] using hl2)) rfl rfl]
      rw [copyEvalIteImm s2 .equal 2 n 2 _ _ (by simpa [s1, s2, WordSemStateFiniteExact.setVar, WordSemStateFiniteExact.getVar, installLookupInsert] using r2)]
      by_cases e2 : n = 2#width
      · rw [if_pos (by simp [Compiler.Encoders.Asm.wordCmpHOL, e2])]
        rw [if_pos e2] at run
        obtain ⟨m2, hs1, run⟩ := Option.bind_eq_some_iff.mp run
        obtain ⟨m3, hs2, run⟩ := Option.bind_eq_some_iff.mp run
        have e := Option.some.inj run
        subst e
        rw [copySeqInst _ _ _ _ (copyStore8 s2 1 6 (BitVec.ofNat width 0) a2 (w1.setWidth width) m2 (by simpa [s1, s2, WordSemStateFiniteExact.setVar, WordSemStateFiniteExact.getVar, installLookupInsert] using r6) (by simp [s1, s2, WordSemStateFiniteExact.setVar, WordSemStateFiniteExact.getVar, installLookupInsert])
          (by simpa [s2, s1, WordSemStateFiniteExact.setVar, goodDimindex_w2w_byte w1 good] using hs1)) rfl rfl]
        rw [copySeqInst _ _ _ _ (copyStore8 { s2 with memory := m2 } 3 6 (BitVec.ofNat width 1) a2 (w2.setWidth width) m3 (by simpa [s1, s2, WordSemStateFiniteExact.setVar, WordSemStateFiniteExact.getVar, installLookupInsert] using r6) (by simp [s1, s2, WordSemStateFiniteExact.setVar, WordSemStateFiniteExact.getVar, installLookupInsert])
          (by simpa [s2, s1, WordSemStateFiniteExact.setVar, goodDimindex_w2w_byte w2 good] using hs2)) rfl rfl]
        rw [copyReturn _ l1 l2 retVal (by simpa [s1, s2, WordSemStateFiniteExact.setVar, WordSemStateFiniteExact.getVar, installLookupInsert] using r0) (by simpa [s1, s2, WordSemStateFiniteExact.setVar, WordSemStateFiniteExact.getVar, installLookupInsert] using r8)]
        simp [WordSemStateFiniteExact.flushState, s2, s1, WordSemStateFiniteExact.setVar]
      · rw [if_neg (by simp [Compiler.Encoders.Asm.wordCmpHOL, e2])]
        rw [if_neg e2] at run
        obtain ⟨w3, hl3, run⟩ := Option.bind_eq_some_iff.mp run
        obtain ⟨m2, hs1, run⟩ := Option.bind_eq_some_iff.mp run
        obtain ⟨m3, hs2, run⟩ := Option.bind_eq_some_iff.mp run
        obtain ⟨m4, hs3, run⟩ := Option.bind_eq_some_iff.mp run
        have e := Option.some.inj run
        subst e
        let s3 := s2.setVar 5 (.word (w3.setWidth width))
        rw [copySeqInst _ s3 _ _ (copyLoad8 s2 5 4 (BitVec.ofNat width 2) a1 w3 (by simpa [s1, s2, s3, WordSemStateFiniteExact.setVar, WordSemStateFiniteExact.getVar, installLookupInsert] using r4) (by simpa [s2, s1, WordSemStateFiniteExact.setVar] using hl3)) rfl rfl]
        rw [copySeqInst _ _ _ _ (copyStore8 s3 1 6 (BitVec.ofNat width 0) a2 (w1.setWidth width) m2 (by simpa [s1, s2, s3, WordSemStateFiniteExact.setVar, WordSemStateFiniteExact.getVar, installLookupInsert] using r6) (by simp [s1, s2, s3, WordSemStateFiniteExact.setVar, WordSemStateFiniteExact.getVar, installLookupInsert])
          (by simpa [s3, s2, s1, WordSemStateFiniteExact.setVar, goodDimindex_w2w_byte w1 good] using hs1)) rfl rfl]
        rw [copySeqInst _ _ _ _ (copyStore8 { s3 with memory := m2 } 3 6 (BitVec.ofNat width 1) a2 (w2.setWidth width) m3 (by simpa [s1, s2, s3, WordSemStateFiniteExact.setVar, WordSemStateFiniteExact.getVar, installLookupInsert] using r6) (by simp [s1, s2, s3, WordSemStateFiniteExact.setVar, WordSemStateFiniteExact.getVar, installLookupInsert])
          (by simpa [s3, s2, s1, WordSemStateFiniteExact.setVar, goodDimindex_w2w_byte w2 good] using hs2)) rfl rfl]
        rw [copySeqInst _ _ _ _ (copyStore8 { s3 with memory := m3 } 5 6 (BitVec.ofNat width 2) a2 (w3.setWidth width) m4 (by simpa [s1, s2, s3, WordSemStateFiniteExact.setVar, WordSemStateFiniteExact.getVar, installLookupInsert] using r6) (by simp [s1, s2, s3, WordSemStateFiniteExact.setVar, WordSemStateFiniteExact.getVar, installLookupInsert])
          (by simpa [s3, s2, s1, WordSemStateFiniteExact.setVar, goodDimindex_w2w_byte w3 good] using hs3)) rfl rfl]
        rw [copyReturn _ l1 l2 retVal (by simpa [s1, s2, s3, WordSemStateFiniteExact.setVar, WordSemStateFiniteExact.getVar, installLookupInsert] using r0) (by simpa [s1, s2, s3, WordSemStateFiniteExact.setVar, WordSemStateFiniteExact.getVar, installLookupInsert] using r8)]
        simp [WordSemStateFiniteExact.flushState, s3, s2, s1, WordSemStateFiniteExact.setVar]
  · rw [if_neg (by simpa [Compiler.Encoders.Asm.wordCmpHOL] using lt4)]
    rw [dif_neg lt4] at run
    obtain ⟨w1, hl1, run⟩ := Option.bind_eq_some_iff.mp run
    obtain ⟨w2, hl2, run⟩ := Option.bind_eq_some_iff.mp run
    obtain ⟨w3, hl3, run⟩ := Option.bind_eq_some_iff.mp run
    obtain ⟨w4, hl4, run⟩ := Option.bind_eq_some_iff.mp run
    obtain ⟨m2, hs1, run⟩ := Option.bind_eq_some_iff.mp run
    obtain ⟨m3, hs2, run⟩ := Option.bind_eq_some_iff.mp run
    obtain ⟨m4, hs3, run⟩ := Option.bind_eq_some_iff.mp run
    obtain ⟨m5, hs4, run⟩ := Option.bind_eq_some_iff.mp run
    let s1 := s.setVar 1 (.word (w1.setWidth width))
    let s2 := s1.setVar 3 (.word (w2.setWidth width))
    let s3 := s2.setVar 5 (.word (w3.setWidth width))
    let s4 := s3.setVar 7 (.word (w4.setWidth width))
    rw [copySeqInst _ s1 _ _ (copyLoad8 s 1 4 (BitVec.ofNat width 0) a1 w1 r4 (by simpa using hl1)) rfl rfl]
    rw [copySeqInst _ s2 _ _ (copyLoad8 s1 3 4 (BitVec.ofNat width 1) a1 w2 (by simpa [s1, s2, s3, s4, WordSemStateFiniteExact.setVar, WordSemStateFiniteExact.getVar, installLookupInsert] using r4)
      (by simpa [s1, WordSemStateFiniteExact.setVar] using hl2)) rfl rfl]
    rw [copySeqInst _ s3 _ _ (copyLoad8 s2 5 4 (BitVec.ofNat width 2) a1 w3 (by simpa [s1, s2, s3, s4, WordSemStateFiniteExact.setVar, WordSemStateFiniteExact.getVar, installLookupInsert] using r4)
      (by simpa [s2, s1, WordSemStateFiniteExact.setVar] using hl3)) rfl rfl]
    rw [copySeqInst _ s4 _ _ (copyLoad8 s3 7 4 (BitVec.ofNat width 3) a1 w4 (by simpa [s1, s2, s3, s4, WordSemStateFiniteExact.setVar, WordSemStateFiniteExact.getVar, installLookupInsert] using r4)
      (by simpa [s3, s2, s1, WordSemStateFiniteExact.setVar] using hl4)) rfl rfl]
    rw [copySeqInst _ _ _ _ (copyStore8 s4 1 6 (BitVec.ofNat width 0) a2 (w1.setWidth width) m2
      (by simpa [s1, s2, s3, s4, WordSemStateFiniteExact.setVar, WordSemStateFiniteExact.getVar, installLookupInsert] using r6) (by simp [s1, s2, s3, s4, WordSemStateFiniteExact.setVar, WordSemStateFiniteExact.getVar, installLookupInsert])
      (by simpa [s4, s3, s2, s1, WordSemStateFiniteExact.setVar, goodDimindex_w2w_byte w1 good] using hs1)) rfl rfl]
    rw [copySeqInst _ _ _ _ (copyStore8 { s4 with memory := m2 } 3 6 (BitVec.ofNat width 1) a2 (w2.setWidth width) m3
      (by simpa [s1, s2, s3, s4, WordSemStateFiniteExact.setVar, WordSemStateFiniteExact.getVar, installLookupInsert] using r6) (by simp [s1, s2, s3, s4, WordSemStateFiniteExact.setVar, WordSemStateFiniteExact.getVar, installLookupInsert])
      (by simpa [s4, s3, s2, s1, WordSemStateFiniteExact.setVar, goodDimindex_w2w_byte w2 good] using hs2)) rfl rfl]
    rw [copySeqInst _ _ _ _ (copyStore8 { s4 with memory := m3 } 5 6 (BitVec.ofNat width 2) a2 (w3.setWidth width) m4
      (by simpa [s1, s2, s3, s4, WordSemStateFiniteExact.setVar, WordSemStateFiniteExact.getVar, installLookupInsert] using r6) (by simp [s1, s2, s3, s4, WordSemStateFiniteExact.setVar, WordSemStateFiniteExact.getVar, installLookupInsert])
      (by simpa [s4, s3, s2, s1, WordSemStateFiniteExact.setVar, goodDimindex_w2w_byte w3 good] using hs3)) rfl rfl]
    rw [copySeqInst _ _ _ _ (copyStore8 { s4 with memory := m4 } 7 6 (BitVec.ofNat width 3) a2 (w4.setWidth width) m5
      (by simpa [s1, s2, s3, s4, WordSemStateFiniteExact.setVar, WordSemStateFiniteExact.getVar, installLookupInsert] using r6) (by simp [s1, s2, s3, s4, WordSemStateFiniteExact.setVar, WordSemStateFiniteExact.getVar, installLookupInsert])
      (by simpa [s4, s3, s2, s1, WordSemStateFiniteExact.setVar, goodDimindex_w2w_byte w4 good] using hs4)) rfl rfl]
    let s5 := { s4 with memory := m5 }
    have r2' := r2
    have r4' := r4
    have r6' := r6
    simp only [WordSemStateFiniteExact.getVar] at r2' r4' r6'
    rw [installSeqAssign s5 9 _ (.word (n - 4)) _ (by simp [s5, s4, s3, s2, s1, WordSemStateFiniteExact.wordExp, WordSemStateFiniteExact.getVar, WordSemStateFiniteExact.setVar, installLookupInsert, theWords, wordOpHOL, wordOp, r2'])]
    let s6 := s5.setVar 9 (.word (n - 4))
    rw [installSeqAssign s6 11 _ (.word (a1 + 4)) _ (by simp [s5, s4, s3, s2, s1, WordSemStateFiniteExact.wordExp, WordSemStateFiniteExact.getVar, WordSemStateFiniteExact.setVar, installLookupInsert, theWords, wordOpHOL, wordOp, r4', s6])]
    let s7 := s6.setVar 11 (.word (a1 + 4))
    rw [installSeqAssign s7 13 _ (.word (a2 + 4)) _ (by simp [s5, s4, s3, s2, s1, WordSemStateFiniteExact.wordExp, WordSemStateFiniteExact.getVar, WordSemStateFiniteExact.setVar, installLookupInsert, theWords, wordOpHOL, wordOp, r6', s7, s6])]
    let s8 := s7.setVar 13 (.word (a2 + 4))
    have ge4 : 4 ≤ n.toNat := by
      have := lt4
      rcases good with rfl | rfl <;> simp [BitVec.lt_def] at this <;> omega
    have n4 : (n - 4#width).toNat = n.toNat - 4 := by
      rw [BitVec.toNat_sub_of_le (by rcases good with rfl | rfl <;> simp [BitVec.le_def] <;> omega)]
      rcases good with rfl | rfl <;> simp
    have r0' := r0
    have r8' := r8
    simp only [WordSemStateFiniteExact.getVar] at r0' r8'
    rw [installTailCall s8 byteCopyAddLocation [0, 9, 11, 13, 8]
      [.loc l1 l2, .word (n - 4), .word (a1 + 4), .word (a2 + 4), retVal] byteCopyAddCode
      (by simp [s8, s7, s6, s5, s4, s3, s2, s1, WordSemStateFiniteExact.getVars, WordSemStateFiniteExact.getVar,
        WordSemStateFiniteExact.setVar, installLookupInsert, r0', r8'])
      code (by change s.clock ≠ 0; omega)]
    let s' := WordSemStateFiniteExact.callEnv [.loc l1 l2, .word (n - 4), .word (a1 + 4), .word (a2 + 4), retVal]
      (sptLookup byteCopyAddLocation s.stackSize) (WordSemStateFiniteExact.decClock s8)
    have ihr := ih (n - 4#width).toNat (by omega) (n - 4#width) (a1 + 4#width) (a2 + 4#width) m5 s' m1
      ⟨run, rfl, rfl, rfl, good, code, by change _ ≤ s.clock - 1; omega,
        by simp [s', WordSemStateFiniteExact.callEnv, WordSemStateFiniteExact.getVar, WordToStackProofs.fromList2Lookup],
        by simp [s', WordSemStateFiniteExact.callEnv, WordSemStateFiniteExact.getVar, WordToStackProofs.fromList2Lookup],
        by simp [s', WordSemStateFiniteExact.callEnv, WordSemStateFiniteExact.getVar, WordToStackProofs.fromList2Lookup],
        by simp [s', WordSemStateFiniteExact.callEnv, WordSemStateFiniteExact.getVar, WordToStackProofs.fromList2Lookup],
        by simp [s', WordSemStateFiniteExact.callEnv, WordSemStateFiniteExact.getVar, WordToStackProofs.fromList2Lookup]⟩ rfl
    change (match WordSemStateFiniteExact.evaluate byteCopyAddCode s' with
      | (res, s) => if wordSemBadFunReturn res then (some (WordSemResult.error : WordSemResult width), s) else (res, s)) = _
    rw [ihr]
    simp only [wordSemBadFunReturn, Bool.false_eq_true, if_false, lt4]
    have optMax (a b : Option Nat) : wordSemOptionMax a b = Option.map₂ max a b := by
      cases a <;> cases b <;> rfl
    have optAdd (a b : Option Nat) : wordSemOptionAdd a b = Option.map₂ (· + ·) a b := by
      cases a <;> cases b <;> rfl
    have idem (a b : Option Nat) : Option.map₂ max (Option.map₂ max a b) b = Option.map₂ max a b := by
      cases a <;> cases b <;> simp
    have clockEq : s.clock - 1 - (n - 4#width).toNat / 4 = s.clock - k / 4 := by
      rw [n4, ← hk]
      omega
    rw [show s'.clock = s.clock - 1 from rfl, clockEq]
    by_cases lt4' : n - 4#width < 4#width <;>
      simp [lt4', s', s8, s7, s6, s5, s4, s3, s2, s1, WordSemStateFiniteExact.callEnv,
        WordSemStateFiniteExact.decClock, WordSemStateFiniteExact.setVar, optMax, optAdd, idem]

/-- Adding a negated offset is subtraction. -/
private theorem copyAddNeg {width : Nat} (a b : BitVec width) : a + -b = a - b :=
  (BitVec.sub_eq_add_neg a b).symm

attribute [local simp] copyAddNeg in
/-- The expanded backward byte-copy stub. -/
private theorem byteCopySubCode_eq {width : Nat} [NeZero width] :
    (byteCopySubCode : WordLangProgHOL (BitVec width)) =
      let L (r k : Nat) : WordLangProgHOL (BitVec width) :=
        .inst (.mem .load8 r (.addr 4 (-(BitVec.ofNat width k))))
      let S (r k : Nat) : WordLangProgHOL (BitVec width) :=
        .inst (.mem .store8 r (.addr 6 (-(BitVec.ofNat width k))))
      .ite .lower 2 (.imm 4)
        (.ite .lower 2 (.imm 2)
          (.ite .equal 2 (.imm 0) (.return 0 [8]) (.seq (L 1 0) (.seq (S 1 0) (.return 0 [8]))))
          (.seq (L 1 0) (.seq (L 3 1)
            (.ite .equal 2 (.imm 2) (.seq (S 1 0) (.seq (S 3 1) (.return 0 [8])))
              (.seq (L 5 2) (.seq (S 1 0) (.seq (S 3 1) (.seq (S 5 2) (.return 0 [8])))))))))
        (.seq (L 1 0) (.seq (L 3 1) (.seq (L 5 2) (.seq (L 7 3) (.seq (S 1 0) (.seq (S 3 1)
          (.seq (S 5 2) (.seq (S 7 3) (.seq (.assign 9 (.op .sub [.var 2, .const 4]))
            (.seq (.assign 11 (.op .sub [.var 4, .const 4]))
              (.seq (.assign 13 (.op .sub [.var 6, .const 4]))
                (.call none (some byteCopySubLocation) [0, 9, 11, 13, 8] none)))))))))))) := rfl

attribute [local simp] copyAddNeg in
/-- The backward byte-copy stub implements `word_copy_bwd`. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_assignProofScript.sml" "CopyByteSub_thm"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem copyByteSub_correct {width : Nat} [NeZero width] {C F : Type}
    (be : Bool) (n a1 a2 : BitVec width) (m : BitVec width → WordLocW width)
    (dm : BitVec width → Bool) (retVal : WordLocW width) (l1 l2 : Nat)
    (s : WordSemStateFiniteExact width C F) (m1 : BitVec width → WordLocW width)
    (h : wordCopyBwd be n a1 a2 m dm = some m1 ∧ s.memory = m ∧ s.mdomain = dm ∧ s.be = be ∧
      goodDimindex width ∧ sptLookup byteCopySubLocation s.code = some (5, byteCopySubCode) ∧
      n.toNat / 4 ≤ s.clock ∧ s.getVar 0 = some (.loc l1 l2) ∧ s.getVar 2 = some (.word n) ∧
      s.getVar 4 = some (.word a1) ∧ s.getVar 6 = some (.word a2) ∧ s.getVar 8 = some retVal) :
    WordSemStateFiniteExact.evaluate byteCopySubCode s =
      (some (.result (.loc l1 l2) [retVal]),
        { s with
          clock := s.clock - n.toNat / 4
          memory := m1
          locals := .ln
          localsSize := some 0
          stackMax := if n < 4#width then s.stackMax else
            Option.map₂ max s.stackMax (Option.map₂ (· + ·) (wordSemStackSize s.stack)
              (sptLookup byteCopySubLocation s.stackSize)) }) := by
  induction hk : n.toNat using Nat.strong_induction_on generalizing n a1 a2 m s m1 with
  | _ k ih =>
  obtain ⟨run, hm, hdm, hbe, good, code, clock, r0, r2, r4, r6, r8⟩ := h
  subst hm hdm hbe
  have big : ¬ 2 ^ width ≤ 4 := by rcases good with rfl | rfl <;> decide
  rw [wordCopyBwd, dif_neg big] at run
  rw [byteCopySubCode_eq]
  dsimp only
  rw [copyEvalIteImm s .lower 2 n 4 _ _ r2]
  by_cases lt4 : n < 4#width
  · have low : Compiler.Encoders.Asm.wordCmpHOL .lower n 4 = true := by
      simpa [Compiler.Encoders.Asm.wordCmpHOL] using lt4
    rw [if_pos low]
    rw [dif_pos lt4] at run
    have kq : k / 4 = 0 := by
      have : n.toNat < 4 := by
        rcases good with rfl | rfl <;> simpa [BitVec.lt_def] using lt4
      omega
    simp only [lt4, if_true, kq, Nat.sub_zero]
    rw [copyEvalIteImm s .lower 2 n 2 _ _ r2]
    by_cases lt2 : n < 2#width
    · rw [if_pos (by simpa [Compiler.Encoders.Asm.wordCmpHOL] using lt2)]
      rw [if_pos lt2] at run
      rw [copyEvalIteImm s .equal 2 n 0 _ _ r2]
      by_cases z : n = 0#width
      · rw [if_pos (by simp [Compiler.Encoders.Asm.wordCmpHOL, z])]
        rw [if_pos z] at run
        cases run
        rw [copyReturn s l1 l2 retVal r0 r8]
        simp [WordSemStateFiniteExact.flushState]
      · rw [if_neg (by simp [Compiler.Encoders.Asm.wordCmpHOL, z])]
        rw [if_neg z] at run
        obtain ⟨w, hl, hs⟩ := Option.bind_eq_some_iff.mp run
        rw [copySeqInst _ _ _ _ (copyLoad8 s 1 4 (-(BitVec.ofNat width 0)) a1 w r4 (by simpa using hl)) rfl rfl]
        rw [copySeqInst _ _ _ _ (copyStore8 (s.setVar 1 (.word (w.setWidth width))) 1 6 (-(BitVec.ofNat width 0)) a2 (w.setWidth width) m1 (by simpa [WordSemStateFiniteExact.setVar,
          WordSemStateFiniteExact.getVar, installLookupInsert] using r6)
          (by simp [WordSemStateFiniteExact.setVar, WordSemStateFiniteExact.getVar, installLookupInsert])
          (by simpa [WordSemStateFiniteExact.setVar, goodDimindex_w2w_byte w good] using hs)) rfl rfl]
        rw [copyReturn _ l1 l2 retVal (by simpa [WordSemStateFiniteExact.setVar,
          WordSemStateFiniteExact.getVar, installLookupInsert] using r0)
          (by simpa [WordSemStateFiniteExact.setVar, WordSemStateFiniteExact.getVar,
            installLookupInsert] using r8)]
        simp [WordSemStateFiniteExact.flushState, WordSemStateFiniteExact.setVar]
    · rw [if_neg (by simpa [Compiler.Encoders.Asm.wordCmpHOL] using lt2)]
      rw [if_neg lt2] at run
      obtain ⟨w1, hl1, run⟩ := Option.bind_eq_some_iff.mp run
      obtain ⟨w2, hl2, run⟩ := Option.bind_eq_some_iff.mp run
      let s1 := s.setVar 1 (.word (w1.setWidth width))
      let s2 := s1.setVar 3 (.word (w2.setWidth width))
      rw [copySeqInst _ s1 _ _ (copyLoad8 s 1 4 (-(BitVec.ofNat width 0)) a1 w1 r4 (by simpa using hl1)) rfl rfl]
      rw [copySeqInst _ s2 _ _ (copyLoad8 s1 3 4 (-(BitVec.ofNat width 1)) a1 w2 (by simpa [s1, s2, WordSemStateFiniteExact.setVar, WordSemStateFiniteExact.getVar, installLookupInsert] using r4) (by simpa [s1, WordSemStateFiniteExact.setVar] using hl2)) rfl rfl]
      rw [copyEvalIteImm s2 .equal 2 n 2 _ _ (by simpa [s1, s2, WordSemStateFiniteExact.setVar, WordSemStateFiniteExact.getVar, installLookupInsert] using r2)]
      by_cases e2 : n = 2#width
      · rw [if_pos (by simp [Compiler.Encoders.Asm.wordCmpHOL, e2])]
        rw [if_pos e2] at run
        obtain ⟨m2, hs1, run⟩ := Option.bind_eq_some_iff.mp run
        obtain ⟨m3, hs2, run⟩ := Option.bind_eq_some_iff.mp run
        have e := Option.some.inj run
        subst e
        rw [copySeqInst _ _ _ _ (copyStore8 s2 1 6 (-(BitVec.ofNat width 0)) a2 (w1.setWidth width) m2 (by simpa [s1, s2, WordSemStateFiniteExact.setVar, WordSemStateFiniteExact.getVar, installLookupInsert] using r6) (by simp [s1, s2, WordSemStateFiniteExact.setVar, WordSemStateFiniteExact.getVar, installLookupInsert])
          (by simpa [s2, s1, WordSemStateFiniteExact.setVar, goodDimindex_w2w_byte w1 good] using hs1)) rfl rfl]
        rw [copySeqInst _ _ _ _ (copyStore8 { s2 with memory := m2 } 3 6 (-(BitVec.ofNat width 1)) a2 (w2.setWidth width) m3 (by simpa [s1, s2, WordSemStateFiniteExact.setVar, WordSemStateFiniteExact.getVar, installLookupInsert] using r6) (by simp [s1, s2, WordSemStateFiniteExact.setVar, WordSemStateFiniteExact.getVar, installLookupInsert])
          (by simpa [s2, s1, WordSemStateFiniteExact.setVar, goodDimindex_w2w_byte w2 good] using hs2)) rfl rfl]
        rw [copyReturn _ l1 l2 retVal (by simpa [s1, s2, WordSemStateFiniteExact.setVar, WordSemStateFiniteExact.getVar, installLookupInsert] using r0) (by simpa [s1, s2, WordSemStateFiniteExact.setVar, WordSemStateFiniteExact.getVar, installLookupInsert] using r8)]
        simp [WordSemStateFiniteExact.flushState, s2, s1, WordSemStateFiniteExact.setVar]
      · rw [if_neg (by simp [Compiler.Encoders.Asm.wordCmpHOL, e2])]
        rw [if_neg e2] at run
        obtain ⟨w3, hl3, run⟩ := Option.bind_eq_some_iff.mp run
        obtain ⟨m2, hs1, run⟩ := Option.bind_eq_some_iff.mp run
        obtain ⟨m3, hs2, run⟩ := Option.bind_eq_some_iff.mp run
        obtain ⟨m4, hs3, run⟩ := Option.bind_eq_some_iff.mp run
        have e := Option.some.inj run
        subst e
        let s3 := s2.setVar 5 (.word (w3.setWidth width))
        rw [copySeqInst _ s3 _ _ (copyLoad8 s2 5 4 (-(BitVec.ofNat width 2)) a1 w3 (by simpa [s1, s2, s3, WordSemStateFiniteExact.setVar, WordSemStateFiniteExact.getVar, installLookupInsert] using r4) (by simpa [s2, s1, WordSemStateFiniteExact.setVar] using hl3)) rfl rfl]
        rw [copySeqInst _ _ _ _ (copyStore8 s3 1 6 (-(BitVec.ofNat width 0)) a2 (w1.setWidth width) m2 (by simpa [s1, s2, s3, WordSemStateFiniteExact.setVar, WordSemStateFiniteExact.getVar, installLookupInsert] using r6) (by simp [s1, s2, s3, WordSemStateFiniteExact.setVar, WordSemStateFiniteExact.getVar, installLookupInsert])
          (by simpa [s3, s2, s1, WordSemStateFiniteExact.setVar, goodDimindex_w2w_byte w1 good] using hs1)) rfl rfl]
        rw [copySeqInst _ _ _ _ (copyStore8 { s3 with memory := m2 } 3 6 (-(BitVec.ofNat width 1)) a2 (w2.setWidth width) m3 (by simpa [s1, s2, s3, WordSemStateFiniteExact.setVar, WordSemStateFiniteExact.getVar, installLookupInsert] using r6) (by simp [s1, s2, s3, WordSemStateFiniteExact.setVar, WordSemStateFiniteExact.getVar, installLookupInsert])
          (by simpa [s3, s2, s1, WordSemStateFiniteExact.setVar, goodDimindex_w2w_byte w2 good] using hs2)) rfl rfl]
        rw [copySeqInst _ _ _ _ (copyStore8 { s3 with memory := m3 } 5 6 (-(BitVec.ofNat width 2)) a2 (w3.setWidth width) m4 (by simpa [s1, s2, s3, WordSemStateFiniteExact.setVar, WordSemStateFiniteExact.getVar, installLookupInsert] using r6) (by simp [s1, s2, s3, WordSemStateFiniteExact.setVar, WordSemStateFiniteExact.getVar, installLookupInsert])
          (by simpa [s3, s2, s1, WordSemStateFiniteExact.setVar, goodDimindex_w2w_byte w3 good] using hs3)) rfl rfl]
        rw [copyReturn _ l1 l2 retVal (by simpa [s1, s2, s3, WordSemStateFiniteExact.setVar, WordSemStateFiniteExact.getVar, installLookupInsert] using r0) (by simpa [s1, s2, s3, WordSemStateFiniteExact.setVar, WordSemStateFiniteExact.getVar, installLookupInsert] using r8)]
        simp [WordSemStateFiniteExact.flushState, s3, s2, s1, WordSemStateFiniteExact.setVar]
  · rw [if_neg (by simpa [Compiler.Encoders.Asm.wordCmpHOL] using lt4)]
    rw [dif_neg lt4] at run
    obtain ⟨w1, hl1, run⟩ := Option.bind_eq_some_iff.mp run
    obtain ⟨w2, hl2, run⟩ := Option.bind_eq_some_iff.mp run
    obtain ⟨w3, hl3, run⟩ := Option.bind_eq_some_iff.mp run
    obtain ⟨w4, hl4, run⟩ := Option.bind_eq_some_iff.mp run
    obtain ⟨m2, hs1, run⟩ := Option.bind_eq_some_iff.mp run
    obtain ⟨m3, hs2, run⟩ := Option.bind_eq_some_iff.mp run
    obtain ⟨m4, hs3, run⟩ := Option.bind_eq_some_iff.mp run
    obtain ⟨m5, hs4, run⟩ := Option.bind_eq_some_iff.mp run
    let s1 := s.setVar 1 (.word (w1.setWidth width))
    let s2 := s1.setVar 3 (.word (w2.setWidth width))
    let s3 := s2.setVar 5 (.word (w3.setWidth width))
    let s4 := s3.setVar 7 (.word (w4.setWidth width))
    rw [copySeqInst _ s1 _ _ (copyLoad8 s 1 4 (-(BitVec.ofNat width 0)) a1 w1 r4 (by simpa using hl1)) rfl rfl]
    rw [copySeqInst _ s2 _ _ (copyLoad8 s1 3 4 (-(BitVec.ofNat width 1)) a1 w2 (by simpa [s1, s2, s3, s4, WordSemStateFiniteExact.setVar, WordSemStateFiniteExact.getVar, installLookupInsert] using r4)
      (by simpa [s1, WordSemStateFiniteExact.setVar] using hl2)) rfl rfl]
    rw [copySeqInst _ s3 _ _ (copyLoad8 s2 5 4 (-(BitVec.ofNat width 2)) a1 w3 (by simpa [s1, s2, s3, s4, WordSemStateFiniteExact.setVar, WordSemStateFiniteExact.getVar, installLookupInsert] using r4)
      (by simpa [s2, s1, WordSemStateFiniteExact.setVar] using hl3)) rfl rfl]
    rw [copySeqInst _ s4 _ _ (copyLoad8 s3 7 4 (-(BitVec.ofNat width 3)) a1 w4 (by simpa [s1, s2, s3, s4, WordSemStateFiniteExact.setVar, WordSemStateFiniteExact.getVar, installLookupInsert] using r4)
      (by simpa [s3, s2, s1, WordSemStateFiniteExact.setVar] using hl4)) rfl rfl]
    rw [copySeqInst _ _ _ _ (copyStore8 s4 1 6 (-(BitVec.ofNat width 0)) a2 (w1.setWidth width) m2
      (by simpa [s1, s2, s3, s4, WordSemStateFiniteExact.setVar, WordSemStateFiniteExact.getVar, installLookupInsert] using r6) (by simp [s1, s2, s3, s4, WordSemStateFiniteExact.setVar, WordSemStateFiniteExact.getVar, installLookupInsert])
      (by simpa [s4, s3, s2, s1, WordSemStateFiniteExact.setVar, goodDimindex_w2w_byte w1 good] using hs1)) rfl rfl]
    rw [copySeqInst _ _ _ _ (copyStore8 { s4 with memory := m2 } 3 6 (-(BitVec.ofNat width 1)) a2 (w2.setWidth width) m3
      (by simpa [s1, s2, s3, s4, WordSemStateFiniteExact.setVar, WordSemStateFiniteExact.getVar, installLookupInsert] using r6) (by simp [s1, s2, s3, s4, WordSemStateFiniteExact.setVar, WordSemStateFiniteExact.getVar, installLookupInsert])
      (by simpa [s4, s3, s2, s1, WordSemStateFiniteExact.setVar, goodDimindex_w2w_byte w2 good] using hs2)) rfl rfl]
    rw [copySeqInst _ _ _ _ (copyStore8 { s4 with memory := m3 } 5 6 (-(BitVec.ofNat width 2)) a2 (w3.setWidth width) m4
      (by simpa [s1, s2, s3, s4, WordSemStateFiniteExact.setVar, WordSemStateFiniteExact.getVar, installLookupInsert] using r6) (by simp [s1, s2, s3, s4, WordSemStateFiniteExact.setVar, WordSemStateFiniteExact.getVar, installLookupInsert])
      (by simpa [s4, s3, s2, s1, WordSemStateFiniteExact.setVar, goodDimindex_w2w_byte w3 good] using hs3)) rfl rfl]
    rw [copySeqInst _ _ _ _ (copyStore8 { s4 with memory := m4 } 7 6 (-(BitVec.ofNat width 3)) a2 (w4.setWidth width) m5
      (by simpa [s1, s2, s3, s4, WordSemStateFiniteExact.setVar, WordSemStateFiniteExact.getVar, installLookupInsert] using r6) (by simp [s1, s2, s3, s4, WordSemStateFiniteExact.setVar, WordSemStateFiniteExact.getVar, installLookupInsert])
      (by simpa [s4, s3, s2, s1, WordSemStateFiniteExact.setVar, goodDimindex_w2w_byte w4 good] using hs4)) rfl rfl]
    let s5 := { s4 with memory := m5 }
    have r2' := r2
    have r4' := r4
    have r6' := r6
    simp only [WordSemStateFiniteExact.getVar] at r2' r4' r6'
    rw [installSeqAssign s5 9 _ (.word (n - 4)) _ (by simp [s5, s4, s3, s2, s1, WordSemStateFiniteExact.wordExp, WordSemStateFiniteExact.getVar, WordSemStateFiniteExact.setVar, installLookupInsert, theWords, wordOpHOL, wordOp, r2'])]
    let s6 := s5.setVar 9 (.word (n - 4))
    rw [installSeqAssign s6 11 _ (.word (a1 - 4)) _ (by simp [s5, s4, s3, s2, s1, WordSemStateFiniteExact.wordExp, WordSemStateFiniteExact.getVar, WordSemStateFiniteExact.setVar, installLookupInsert, theWords, wordOpHOL, wordOp, r4', s6])]
    let s7 := s6.setVar 11 (.word (a1 - 4))
    rw [installSeqAssign s7 13 _ (.word (a2 - 4)) _ (by simp [s5, s4, s3, s2, s1, WordSemStateFiniteExact.wordExp, WordSemStateFiniteExact.getVar, WordSemStateFiniteExact.setVar, installLookupInsert, theWords, wordOpHOL, wordOp, r6', s7, s6])]
    let s8 := s7.setVar 13 (.word (a2 - 4))
    have ge4 : 4 ≤ n.toNat := by
      have := lt4
      rcases good with rfl | rfl <;> simp [BitVec.lt_def] at this <;> omega
    have n4 : (n - 4#width).toNat = n.toNat - 4 := by
      rw [BitVec.toNat_sub_of_le (by rcases good with rfl | rfl <;> simp [BitVec.le_def] <;> omega)]
      rcases good with rfl | rfl <;> simp
    have r0' := r0
    have r8' := r8
    simp only [WordSemStateFiniteExact.getVar] at r0' r8'
    rw [installTailCall s8 byteCopySubLocation [0, 9, 11, 13, 8]
      [.loc l1 l2, .word (n - 4), .word (a1 - 4), .word (a2 - 4), retVal] byteCopySubCode
      (by simp [s8, s7, s6, s5, s4, s3, s2, s1, WordSemStateFiniteExact.getVars, WordSemStateFiniteExact.getVar,
        WordSemStateFiniteExact.setVar, installLookupInsert, r0', r8'])
      code (by change s.clock ≠ 0; omega)]
    let s' := WordSemStateFiniteExact.callEnv [.loc l1 l2, .word (n - 4), .word (a1 - 4), .word (a2 - 4), retVal]
      (sptLookup byteCopySubLocation s.stackSize) (WordSemStateFiniteExact.decClock s8)
    have ihr := ih (n - 4#width).toNat (by omega) (n - 4#width) (a1 - 4#width) (a2 - 4#width) m5 s' m1
      ⟨run, rfl, rfl, rfl, good, code, by change _ ≤ s.clock - 1; omega,
        by simp [s', WordSemStateFiniteExact.callEnv, WordSemStateFiniteExact.getVar, WordToStackProofs.fromList2Lookup],
        by simp [s', WordSemStateFiniteExact.callEnv, WordSemStateFiniteExact.getVar, WordToStackProofs.fromList2Lookup],
        by simp [s', WordSemStateFiniteExact.callEnv, WordSemStateFiniteExact.getVar, WordToStackProofs.fromList2Lookup],
        by simp [s', WordSemStateFiniteExact.callEnv, WordSemStateFiniteExact.getVar, WordToStackProofs.fromList2Lookup],
        by simp [s', WordSemStateFiniteExact.callEnv, WordSemStateFiniteExact.getVar, WordToStackProofs.fromList2Lookup]⟩ rfl
    change (match WordSemStateFiniteExact.evaluate byteCopySubCode s' with
      | (res, s) => if wordSemBadFunReturn res then (some (WordSemResult.error : WordSemResult width), s) else (res, s)) = _
    rw [ihr]
    simp only [wordSemBadFunReturn, Bool.false_eq_true, if_false, lt4]
    have optMax (a b : Option Nat) : wordSemOptionMax a b = Option.map₂ max a b := by
      cases a <;> cases b <;> rfl
    have optAdd (a b : Option Nat) : wordSemOptionAdd a b = Option.map₂ (· + ·) a b := by
      cases a <;> cases b <;> rfl
    have idem (a b : Option Nat) : Option.map₂ max (Option.map₂ max a b) b = Option.map₂ max a b := by
      cases a <;> cases b <;> simp
    have clockEq : s.clock - 1 - (n - 4#width).toNat / 4 = s.clock - k / 4 := by
      rw [n4, ← hk]
      omega
    rw [show s'.clock = s.clock - 1 from rfl, clockEq]
    by_cases lt4' : n - 4#width < 4#width <;>
      simp [lt4', s', s8, s7, s6, s5, s4, s3, s2, s1, WordSemStateFiniteExact.callEnv,
        WordSemStateFiniteExact.decClock, WordSemStateFiniteExact.setVar, optMax, optAdd, idem]

end Flapjack.Compiler.Backend.DataToWord.Proofs.Assign
