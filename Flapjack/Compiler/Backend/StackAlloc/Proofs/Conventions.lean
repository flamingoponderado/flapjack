import Flapjack.Compiler.Backend.StackAlloc.Compile
import Flapjack.Compiler.Backend.StackProps.ProgramNames
import Flapjack.Compiler.Backend.StackProps.RemoveNames
import Flapjack.Compiler.Backend.StackProps.RegisterBounds
import Flapjack.Compiler.Backend.StackProps.CallArgs
import Flapjack.Compiler.Backend.DataToWord.ConfOk
import Flapjack.Misc.GoodDimindex

/-!
# `stack_allocProof` syntactic convention lemmas

`stack_alloc_comp_stack_asm_name`, `stack_alloc_reg_bound` and
`stack_alloc_call_args` of
`cakeml/compiler/backend/proofs/stack_allocProofScript.sml` (6217-6331): `comp`
preserves the naming, register-bound and call-argument conventions, and the GC
stub satisfies the latter two.
-/

namespace Flapjack.Compiler.Backend.StackAlloc

open Flapjack Flapjack.Compiler.Backend.StackLang Flapjack.Compiler.Backend.StackProps
open Flapjack.Compiler.Encoders.Asm

/-- Exact HOL `stack_alloc_comp_stack_asm_name`
(`stack_allocProofScript.sml:6217-6237`). HOL's free `c` is implicit; its
`'a asm_config` shares the word dimension of the program, as in the source. -/
@[hol "cakeml/compiler/backend/proofs/stack_allocProofScript.sml"
  "stack_alloc_comp_stack_asm_name" (words_as_type_indexed_bitvec)]
theorem stack_alloc_comp_stack_asm_name {width : Nat} [NeZero width] {c : AsmConfigExact width} :
    ∀ (n m : Nat) (p : HolProg width),
      stackAsmName c p ∧ stackAsmRemove c p →
      stackAsmName c (comp n m p).1 ∧ stackAsmRemove c (comp n m p).1 := by
  intro n m p
  set_option tactic.fun_induction.unfolding false in
    fun_induction comp n m p with
    | _ => simp_all only [comp, stackAsmName, stackAsmRemove] <;> grind

namespace ConventionSupport

/-- `comp` preserves `reg_bound` when the bound is at least 10 (the inner
`comp_ind` induction of HOL's `stack_alloc_reg_bound`). -/
theorem comp_regBound {width : Nat} [NeZero width] {sp : Nat} (hsp : 10 ≤ sp) :
    ∀ (n m : Nat) (p : HolProg width), regBound p sp → regBound (comp n m p).1 sp := by
  intro n m p
  set_option tactic.fun_induction.unfolding false in
    fun_induction comp n m p with
    | _ => simp_all only [comp, regBound] <;> grind

/-- `comp` preserves `call_args p 1 2 3 4 0` (the inner `comp_ind` induction of
HOL's `stack_alloc_call_args`). -/
theorem comp_callArgs {width : Nat} [NeZero width] :
    ∀ (n m : Nat) (p : HolProg width), callArgs p 1 2 3 4 0 → callArgs (comp n m p).1 1 2 3 4 0 := by
  intro n m p
  set_option tactic.fun_induction.unfolding false in
    fun_induction comp n m p with
    | _ => simp_all only [comp, callArgs] <;> grind

set_option linter.unusedSimpArgs false in
/-- The GC stub is register-bounded by any bound of at least 10 (the
`EVAL_TAC` step of HOL's `stack_alloc_reg_bound`). -/
theorem stub_regBound {width : Nat} [NeZero width] (dc : DataToWord.Config) (sp : Nat)
    (hsp : 10 ≤ sp) : regBound (wordGcCode dc : HolProg width) sp := by
  unfold wordGcCode
  rcases dc.gcKind with _ | _ | gs
  · simp [memcpyCode, clearTopInst, wordGcMoveCode, wordGcMoveListCode, wordGcMoveLoopCode, wordGcMoveBitmapCode, wordGcMoveBitmapsCode, wordGcMoveRootsBitmapsCode, wordGenGcMoveCode, wordGenGcPartialMoveCode, wordGenGcMoveBitmapCode, wordGenGcPartialMoveBitmapCode, wordGenGcMoveBitmapsCode, wordGenGcPartialMoveBitmapsCode, wordGenGcMoveRootsBitmapsCode, wordGenGcPartialMoveRootsBitmapsCode, wordGenGcMoveListCode, wordGenGcPartialMoveListCode, wordGenGcMoveDataCode, wordGenGcPartialMoveRefListCode, wordGenGcPartialMoveDataCode, wordGenGcMoveRefsCode, wordGenGcMoveLoopCode, wordGcPartialOrFull, setNewTrigger, listSeqHOL, whileHOL, moveHOL, sub1Inst, subInst, addInst, andInst, xorInst, add1Inst, orInst, addBytesInWordInst, div2Inst, StackRemove.leftShiftInst, StackRemove.rightShiftInst, StackRemove.constInst, StackRemove.loadInst, StackRemove.storeInst, regBound, regBoundInst]; omega
  · simp [memcpyCode, clearTopInst, wordGcMoveCode, wordGcMoveListCode, wordGcMoveLoopCode, wordGcMoveBitmapCode, wordGcMoveBitmapsCode, wordGcMoveRootsBitmapsCode, wordGenGcMoveCode, wordGenGcPartialMoveCode, wordGenGcMoveBitmapCode, wordGenGcPartialMoveBitmapCode, wordGenGcMoveBitmapsCode, wordGenGcPartialMoveBitmapsCode, wordGenGcMoveRootsBitmapsCode, wordGenGcPartialMoveRootsBitmapsCode, wordGenGcMoveListCode, wordGenGcPartialMoveListCode, wordGenGcMoveDataCode, wordGenGcPartialMoveRefListCode, wordGenGcPartialMoveDataCode, wordGenGcMoveRefsCode, wordGenGcMoveLoopCode, wordGcPartialOrFull, setNewTrigger, listSeqHOL, whileHOL, moveHOL, sub1Inst, subInst, addInst, andInst, xorInst, add1Inst, orInst, addBytesInWordInst, div2Inst, StackRemove.leftShiftInst, StackRemove.rightShiftInst, StackRemove.constInst, StackRemove.loadInst, StackRemove.storeInst, regBound, regBoundInst]; omega
  · rcases gs with _ | ⟨g, gs⟩
    · simp [memcpyCode, clearTopInst, wordGcMoveCode, wordGcMoveListCode, wordGcMoveLoopCode, wordGcMoveBitmapCode, wordGcMoveBitmapsCode, wordGcMoveRootsBitmapsCode, wordGenGcMoveCode, wordGenGcPartialMoveCode, wordGenGcMoveBitmapCode, wordGenGcPartialMoveBitmapCode, wordGenGcMoveBitmapsCode, wordGenGcPartialMoveBitmapsCode, wordGenGcMoveRootsBitmapsCode, wordGenGcPartialMoveRootsBitmapsCode, wordGenGcMoveListCode, wordGenGcPartialMoveListCode, wordGenGcMoveDataCode, wordGenGcPartialMoveRefListCode, wordGenGcPartialMoveDataCode, wordGenGcMoveRefsCode, wordGenGcMoveLoopCode, wordGcPartialOrFull, setNewTrigger, listSeqHOL, whileHOL, moveHOL, sub1Inst, subInst, addInst, andInst, xorInst, add1Inst, orInst, addBytesInWordInst, div2Inst, StackRemove.leftShiftInst, StackRemove.rightShiftInst, StackRemove.constInst, StackRemove.loadInst, StackRemove.storeInst, regBound, regBoundInst]; omega
    · simp [memcpyCode, clearTopInst, wordGcMoveCode, wordGcMoveListCode, wordGcMoveLoopCode, wordGcMoveBitmapCode, wordGcMoveBitmapsCode, wordGcMoveRootsBitmapsCode, wordGenGcMoveCode, wordGenGcPartialMoveCode, wordGenGcMoveBitmapCode, wordGenGcPartialMoveBitmapCode, wordGenGcMoveBitmapsCode, wordGenGcPartialMoveBitmapsCode, wordGenGcMoveRootsBitmapsCode, wordGenGcPartialMoveRootsBitmapsCode, wordGenGcMoveListCode, wordGenGcPartialMoveListCode, wordGenGcMoveDataCode, wordGenGcPartialMoveRefListCode, wordGenGcPartialMoveDataCode, wordGenGcMoveRefsCode, wordGenGcMoveLoopCode, wordGcPartialOrFull, setNewTrigger, listSeqHOL, whileHOL, moveHOL, sub1Inst, subInst, addInst, andInst, xorInst, add1Inst, orInst, addBytesInWordInst, div2Inst, StackRemove.leftShiftInst, StackRemove.rightShiftInst, StackRemove.constInst, StackRemove.loadInst, StackRemove.storeInst, regBound, regBoundInst]; omega

set_option linter.unusedSimpArgs false in
/-- The GC stub satisfies `call_args _ 1 2 3 4 0` (the `EVAL_TAC` step of HOL's
`stack_alloc_call_args`). -/
theorem stub_callArgs {width : Nat} [NeZero width] (dc : DataToWord.Config) :
    callArgs (wordGcCode dc : HolProg width) 1 2 3 4 0 := by
  unfold wordGcCode
  rcases dc.gcKind with _ | _ | gs
  · simp [memcpyCode, clearTopInst, wordGcMoveCode, wordGcMoveListCode, wordGcMoveLoopCode, wordGcMoveBitmapCode, wordGcMoveBitmapsCode, wordGcMoveRootsBitmapsCode, wordGenGcMoveCode, wordGenGcPartialMoveCode, wordGenGcMoveBitmapCode, wordGenGcPartialMoveBitmapCode, wordGenGcMoveBitmapsCode, wordGenGcPartialMoveBitmapsCode, wordGenGcMoveRootsBitmapsCode, wordGenGcPartialMoveRootsBitmapsCode, wordGenGcMoveListCode, wordGenGcPartialMoveListCode, wordGenGcMoveDataCode, wordGenGcPartialMoveRefListCode, wordGenGcPartialMoveDataCode, wordGenGcMoveRefsCode, wordGenGcMoveLoopCode, wordGcPartialOrFull, setNewTrigger, listSeqHOL, whileHOL, moveHOL, sub1Inst, subInst, addInst, andInst, xorInst, add1Inst, orInst, addBytesInWordInst, div2Inst, StackRemove.leftShiftInst, StackRemove.rightShiftInst, StackRemove.constInst, StackRemove.loadInst, StackRemove.storeInst, callArgs]
  · simp [memcpyCode, clearTopInst, wordGcMoveCode, wordGcMoveListCode, wordGcMoveLoopCode, wordGcMoveBitmapCode, wordGcMoveBitmapsCode, wordGcMoveRootsBitmapsCode, wordGenGcMoveCode, wordGenGcPartialMoveCode, wordGenGcMoveBitmapCode, wordGenGcPartialMoveBitmapCode, wordGenGcMoveBitmapsCode, wordGenGcPartialMoveBitmapsCode, wordGenGcMoveRootsBitmapsCode, wordGenGcPartialMoveRootsBitmapsCode, wordGenGcMoveListCode, wordGenGcPartialMoveListCode, wordGenGcMoveDataCode, wordGenGcPartialMoveRefListCode, wordGenGcPartialMoveDataCode, wordGenGcMoveRefsCode, wordGenGcMoveLoopCode, wordGcPartialOrFull, setNewTrigger, listSeqHOL, whileHOL, moveHOL, sub1Inst, subInst, addInst, andInst, xorInst, add1Inst, orInst, addBytesInWordInst, div2Inst, StackRemove.leftShiftInst, StackRemove.rightShiftInst, StackRemove.constInst, StackRemove.loadInst, StackRemove.storeInst, callArgs]
  · rcases gs with _ | ⟨g, gs⟩
    · simp [memcpyCode, clearTopInst, wordGcMoveCode, wordGcMoveListCode, wordGcMoveLoopCode, wordGcMoveBitmapCode, wordGcMoveBitmapsCode, wordGcMoveRootsBitmapsCode, wordGenGcMoveCode, wordGenGcPartialMoveCode, wordGenGcMoveBitmapCode, wordGenGcPartialMoveBitmapCode, wordGenGcMoveBitmapsCode, wordGenGcPartialMoveBitmapsCode, wordGenGcMoveRootsBitmapsCode, wordGenGcPartialMoveRootsBitmapsCode, wordGenGcMoveListCode, wordGenGcPartialMoveListCode, wordGenGcMoveDataCode, wordGenGcPartialMoveRefListCode, wordGenGcPartialMoveDataCode, wordGenGcMoveRefsCode, wordGenGcMoveLoopCode, wordGcPartialOrFull, setNewTrigger, listSeqHOL, whileHOL, moveHOL, sub1Inst, subInst, addInst, andInst, xorInst, add1Inst, orInst, addBytesInWordInst, div2Inst, StackRemove.leftShiftInst, StackRemove.rightShiftInst, StackRemove.constInst, StackRemove.loadInst, StackRemove.storeInst, callArgs]
    · simp [memcpyCode, clearTopInst, wordGcMoveCode, wordGcMoveListCode, wordGcMoveLoopCode, wordGcMoveBitmapCode, wordGcMoveBitmapsCode, wordGcMoveRootsBitmapsCode, wordGenGcMoveCode, wordGenGcPartialMoveCode, wordGenGcMoveBitmapCode, wordGenGcPartialMoveBitmapCode, wordGenGcMoveBitmapsCode, wordGenGcPartialMoveBitmapsCode, wordGenGcMoveRootsBitmapsCode, wordGenGcPartialMoveRootsBitmapsCode, wordGenGcMoveListCode, wordGenGcPartialMoveListCode, wordGenGcMoveDataCode, wordGenGcPartialMoveRefListCode, wordGenGcPartialMoveDataCode, wordGenGcMoveRefsCode, wordGenGcMoveLoopCode, wordGcPartialOrFull, setNewTrigger, listSeqHOL, whileHOL, moveHOL, sub1Inst, subInst, addInst, andInst, xorInst, add1Inst, orInst, addBytesInWordInst, div2Inst, StackRemove.leftShiftInst, StackRemove.rightShiftInst, StackRemove.constInst, StackRemove.loadInst, StackRemove.storeInst, callArgs]

theorem ofNat_ne_zero_of_lt {width k : Nat} (h0 : k ≠ 0) (hk : k < width) :
    BitVec.ofNat width k ≠ 0 := by
  intro h
  have := congrArg BitVec.toNat h
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (Nat.lt_trans hk Nat.lt_two_pow_self)] at this
  simp at this
  exact h0 this

set_option linter.unusedSimpArgs false in
/-- The GC stub satisfies `stack_asm_name` under the source's configuration
hypotheses (the `EVAL_TAC` step of HOL's `stack_alloc_stack_asm_convs`). -/
theorem stub_asmName {width : Nat} [NeZero width] (conf : DataToWord.Config)
    (c : AsmConfigExact width) (hok : DataToWord.confOk width conf)
    (haddr : asmAddrOffsetOkExact c 0 = true) (hreg : regName 10 c)
    (hdim : goodDimindex width) (h8 : c.validImm (.inl .add) 8 = true)
    (h4 : c.validImm (.inl .add) 4 = true) (h1 : c.validImm (.inl .add) 1 = true)
    (hs1 : c.validImm (.inl .sub) 1 = true) :
    stackAsmName c (wordGcCode conf : HolProg width) := by
  simp only [regName] at hreg
  obtain ⟨hsl, hws, hlen0, hlen⟩ := hok
  have hwsa : 2 ≤ wordShiftAmount width := by
    unfold wordShiftAmount; split <;> omega
  have hw : 32 ≤ width := by rcases hdim with h | h <;> omega
  have hssl : DataToWord.smallShiftLength conf < width := by
    unfold DataToWord.shiftLength at hsl; unfold DataToWord.smallShiftLength; omega
  have hmod : ∀ k, k < width → k % 2 ^ width = k :=
    fun k hk => Nat.mod_eq_of_lt (Nat.lt_trans hk Nat.lt_two_pow_self)
  have hnz : ∀ k, k ≠ 0 → k < width → ¬ BitVec.ofNat width k = 0#width :=
    fun k h0 hk => ofNat_ne_zero_of_lt h0 hk
  have hbiw : c.validImm (.inl .add) wordSemBytesInWord = true := by
    rcases hdim with rfl | rfl
    · simpa [wordSemBytesInWord] using h4
    · simpa [wordSemBytesInWord] using h8
  have hsw : wordShiftAmount width < width := by unfold wordShiftAmount; split <;> omega
  have e1 := hmod _ hsl
  have e2 := hmod _ hsw
  have e3 := hmod 2 (by omega)
  have e4 := hmod (width - (DataToWord.smallShiftLength conf - 1) - 1) (by omega)
  have e5 := hmod (width - conf.lenSize) (by omega)
  have n1 := hnz _ (by omega) hsl
  have n3 := hnz 2 (by omega) (by omega)
  have n4 := hnz (width - (DataToWord.smallShiftLength conf - 1) - 1) (by omega) (by omega)
  have n5 := hnz (width - conf.lenSize) (by omega) (by omega)
  have n6 := hnz _ (by omega) hsw
  have e6 := hmod 1 (by omega)
  have e7 := hmod (width - 1) (by omega)
  have n7 := hnz (width - 1) (by omega) (by omega)
  have haddr' : asmAddrOffsetOkExact c (0#width) = true := haddr
  have h1' : c.validImm (.inl .add) (1#width) = true := h1
  have hs1' : c.validImm (.inl .sub) (1#width) = true := hs1
  unfold wordGcCode
  rcases conf.gcKind with _ | _ | gs
  · simp [memcpyCode, clearTopInst, wordGcMoveCode, wordGcMoveListCode, wordGcMoveLoopCode, wordGcMoveBitmapCode, wordGcMoveBitmapsCode, wordGcMoveRootsBitmapsCode, wordGenGcMoveCode, wordGenGcPartialMoveCode, wordGenGcMoveBitmapCode, wordGenGcPartialMoveBitmapCode, wordGenGcMoveBitmapsCode, wordGenGcPartialMoveBitmapsCode, wordGenGcMoveRootsBitmapsCode, wordGenGcPartialMoveRootsBitmapsCode, wordGenGcMoveListCode, wordGenGcPartialMoveListCode, wordGenGcMoveDataCode, wordGenGcPartialMoveRefListCode, wordGenGcPartialMoveDataCode, wordGenGcMoveRefsCode, wordGenGcMoveLoopCode, wordGcPartialOrFull, setNewTrigger, listSeqHOL, whileHOL, moveHOL, sub1Inst, subInst, addInst, andInst, xorInst, add1Inst, orInst, addBytesInWordInst, div2Inst, StackRemove.leftShiftInst, StackRemove.rightShiftInst, StackRemove.constInst, StackRemove.loadInst, StackRemove.storeInst, stackAsmName, instName, arithName, regImmName, regName, addrName, e1, e2, e3, e4, e5, n1, n3, n4, n5, n6, e6, e7, n7, haddr', h1', hs1', hbiw]
    omega
  · simp [memcpyCode, clearTopInst, wordGcMoveCode, wordGcMoveListCode, wordGcMoveLoopCode, wordGcMoveBitmapCode, wordGcMoveBitmapsCode, wordGcMoveRootsBitmapsCode, wordGenGcMoveCode, wordGenGcPartialMoveCode, wordGenGcMoveBitmapCode, wordGenGcPartialMoveBitmapCode, wordGenGcMoveBitmapsCode, wordGenGcPartialMoveBitmapsCode, wordGenGcMoveRootsBitmapsCode, wordGenGcPartialMoveRootsBitmapsCode, wordGenGcMoveListCode, wordGenGcPartialMoveListCode, wordGenGcMoveDataCode, wordGenGcPartialMoveRefListCode, wordGenGcPartialMoveDataCode, wordGenGcMoveRefsCode, wordGenGcMoveLoopCode, wordGcPartialOrFull, setNewTrigger, listSeqHOL, whileHOL, moveHOL, sub1Inst, subInst, addInst, andInst, xorInst, add1Inst, orInst, addBytesInWordInst, div2Inst, StackRemove.leftShiftInst, StackRemove.rightShiftInst, StackRemove.constInst, StackRemove.loadInst, StackRemove.storeInst, stackAsmName, instName, arithName, regImmName, regName, addrName, e1, e2, e3, e4, e5, n1, n3, n4, n5, n6, e6, e7, n7, haddr', h1', hs1', hbiw]
    omega
  · rcases gs with _ | ⟨g, gs⟩
    · simp [memcpyCode, clearTopInst, wordGcMoveCode, wordGcMoveListCode, wordGcMoveLoopCode, wordGcMoveBitmapCode, wordGcMoveBitmapsCode, wordGcMoveRootsBitmapsCode, wordGenGcMoveCode, wordGenGcPartialMoveCode, wordGenGcMoveBitmapCode, wordGenGcPartialMoveBitmapCode, wordGenGcMoveBitmapsCode, wordGenGcPartialMoveBitmapsCode, wordGenGcMoveRootsBitmapsCode, wordGenGcPartialMoveRootsBitmapsCode, wordGenGcMoveListCode, wordGenGcPartialMoveListCode, wordGenGcMoveDataCode, wordGenGcPartialMoveRefListCode, wordGenGcPartialMoveDataCode, wordGenGcMoveRefsCode, wordGenGcMoveLoopCode, wordGcPartialOrFull, setNewTrigger, listSeqHOL, whileHOL, moveHOL, sub1Inst, subInst, addInst, andInst, xorInst, add1Inst, orInst, addBytesInWordInst, div2Inst, StackRemove.leftShiftInst, StackRemove.rightShiftInst, StackRemove.constInst, StackRemove.loadInst, StackRemove.storeInst, stackAsmName, instName, arithName, regImmName, regName, addrName, e1, e2, e3, e4, e5, n1, n3, n4, n5, n6, e6, e7, n7, haddr', h1', hs1', hbiw]
      omega
    · simp [memcpyCode, clearTopInst, wordGcMoveCode, wordGcMoveListCode, wordGcMoveLoopCode, wordGcMoveBitmapCode, wordGcMoveBitmapsCode, wordGcMoveRootsBitmapsCode, wordGenGcMoveCode, wordGenGcPartialMoveCode, wordGenGcMoveBitmapCode, wordGenGcPartialMoveBitmapCode, wordGenGcMoveBitmapsCode, wordGenGcPartialMoveBitmapsCode, wordGenGcMoveRootsBitmapsCode, wordGenGcPartialMoveRootsBitmapsCode, wordGenGcMoveListCode, wordGenGcPartialMoveListCode, wordGenGcMoveDataCode, wordGenGcPartialMoveRefListCode, wordGenGcPartialMoveDataCode, wordGenGcMoveRefsCode, wordGenGcMoveLoopCode, wordGcPartialOrFull, setNewTrigger, listSeqHOL, whileHOL, moveHOL, sub1Inst, subInst, addInst, andInst, xorInst, add1Inst, orInst, addBytesInWordInst, div2Inst, StackRemove.leftShiftInst, StackRemove.rightShiftInst, StackRemove.constInst, StackRemove.loadInst, StackRemove.storeInst, stackAsmName, instName, arithName, regImmName, regName, addrName, e1, e2, e3, e4, e5, n1, n3, n4, n5, n6, e6, e7, n7, haddr', h1', hs1', hbiw]
      omega

set_option linter.unusedSimpArgs false in
/-- The GC stub satisfies `stack_asm_remove` when register 10 is a name (the
`EVAL_TAC` step of HOL's `stack_alloc_stack_asm_convs`). -/
theorem stub_asmRemove {width : Nat} [NeZero width] (conf : DataToWord.Config)
    (c : AsmConfigExact width) (hreg : regName 10 c) :
    stackAsmRemove c (wordGcCode conf : HolProg width) := by
  simp only [regName] at hreg
  unfold wordGcCode
  rcases conf.gcKind with _ | _ | gs
  · simp [memcpyCode, clearTopInst, wordGcMoveCode, wordGcMoveListCode, wordGcMoveLoopCode, wordGcMoveBitmapCode, wordGcMoveBitmapsCode, wordGcMoveRootsBitmapsCode, wordGenGcMoveCode, wordGenGcPartialMoveCode, wordGenGcMoveBitmapCode, wordGenGcPartialMoveBitmapCode, wordGenGcMoveBitmapsCode, wordGenGcPartialMoveBitmapsCode, wordGenGcMoveRootsBitmapsCode, wordGenGcPartialMoveRootsBitmapsCode, wordGenGcMoveListCode, wordGenGcPartialMoveListCode, wordGenGcMoveDataCode, wordGenGcPartialMoveRefListCode, wordGenGcPartialMoveDataCode, wordGenGcMoveRefsCode, wordGenGcMoveLoopCode, wordGcPartialOrFull, setNewTrigger, listSeqHOL, whileHOL, moveHOL, sub1Inst, subInst, addInst, andInst, xorInst, add1Inst, orInst, addBytesInWordInst, div2Inst, StackRemove.leftShiftInst, StackRemove.rightShiftInst, StackRemove.constInst, StackRemove.loadInst, StackRemove.storeInst, stackAsmRemove, regName]; omega
  · simp [memcpyCode, clearTopInst, wordGcMoveCode, wordGcMoveListCode, wordGcMoveLoopCode, wordGcMoveBitmapCode, wordGcMoveBitmapsCode, wordGcMoveRootsBitmapsCode, wordGenGcMoveCode, wordGenGcPartialMoveCode, wordGenGcMoveBitmapCode, wordGenGcPartialMoveBitmapCode, wordGenGcMoveBitmapsCode, wordGenGcPartialMoveBitmapsCode, wordGenGcMoveRootsBitmapsCode, wordGenGcPartialMoveRootsBitmapsCode, wordGenGcMoveListCode, wordGenGcPartialMoveListCode, wordGenGcMoveDataCode, wordGenGcPartialMoveRefListCode, wordGenGcPartialMoveDataCode, wordGenGcMoveRefsCode, wordGenGcMoveLoopCode, wordGcPartialOrFull, setNewTrigger, listSeqHOL, whileHOL, moveHOL, sub1Inst, subInst, addInst, andInst, xorInst, add1Inst, orInst, addBytesInWordInst, div2Inst, StackRemove.leftShiftInst, StackRemove.rightShiftInst, StackRemove.constInst, StackRemove.loadInst, StackRemove.storeInst, stackAsmRemove, regName]; omega
  · rcases gs with _ | ⟨g, gs⟩
    · simp [memcpyCode, clearTopInst, wordGcMoveCode, wordGcMoveListCode, wordGcMoveLoopCode, wordGcMoveBitmapCode, wordGcMoveBitmapsCode, wordGcMoveRootsBitmapsCode, wordGenGcMoveCode, wordGenGcPartialMoveCode, wordGenGcMoveBitmapCode, wordGenGcPartialMoveBitmapCode, wordGenGcMoveBitmapsCode, wordGenGcPartialMoveBitmapsCode, wordGenGcMoveRootsBitmapsCode, wordGenGcPartialMoveRootsBitmapsCode, wordGenGcMoveListCode, wordGenGcPartialMoveListCode, wordGenGcMoveDataCode, wordGenGcPartialMoveRefListCode, wordGenGcPartialMoveDataCode, wordGenGcMoveRefsCode, wordGenGcMoveLoopCode, wordGcPartialOrFull, setNewTrigger, listSeqHOL, whileHOL, moveHOL, sub1Inst, subInst, addInst, andInst, xorInst, add1Inst, orInst, addBytesInWordInst, div2Inst, StackRemove.leftShiftInst, StackRemove.rightShiftInst, StackRemove.constInst, StackRemove.loadInst, StackRemove.storeInst, stackAsmRemove, regName]; omega
    · simp [memcpyCode, clearTopInst, wordGcMoveCode, wordGcMoveListCode, wordGcMoveLoopCode, wordGcMoveBitmapCode, wordGcMoveBitmapsCode, wordGcMoveRootsBitmapsCode, wordGenGcMoveCode, wordGenGcPartialMoveCode, wordGenGcMoveBitmapCode, wordGenGcPartialMoveBitmapCode, wordGenGcMoveBitmapsCode, wordGenGcPartialMoveBitmapsCode, wordGenGcMoveRootsBitmapsCode, wordGenGcPartialMoveRootsBitmapsCode, wordGenGcMoveListCode, wordGenGcPartialMoveListCode, wordGenGcMoveDataCode, wordGenGcPartialMoveRefListCode, wordGenGcPartialMoveDataCode, wordGenGcMoveRefsCode, wordGenGcMoveLoopCode, wordGcPartialOrFull, setNewTrigger, listSeqHOL, whileHOL, moveHOL, sub1Inst, subInst, addInst, andInst, xorInst, add1Inst, orInst, addBytesInWordInst, div2Inst, StackRemove.leftShiftInst, StackRemove.rightShiftInst, StackRemove.constInst, StackRemove.loadInst, StackRemove.storeInst, stackAsmRemove, regName]; omega

end ConventionSupport

open ConventionSupport in
/-- Exact HOL `stack_alloc_reg_bound` (`stack_allocProofScript.sml:6270-6302`).
HOL's free `sp prog1 dc` are implicit; `EVERY P (MAP SND l)` is bounded
quantification over `l.map Prod.snd`. -/
@[hol "cakeml/compiler/backend/proofs/stack_allocProofScript.sml" "stack_alloc_reg_bound"
  (words_as_type_indexed_bitvec)]
theorem stack_alloc_reg_bound {width : Nat} [NeZero width] {sp : Nat}
    {prog1 : List (Nat × HolProg width)} {dc : DataToWord.Config} :
    10 ≤ sp ∧ (∀ p ∈ prog1.map Prod.snd, regBound p sp) →
    ∀ p ∈ (compile dc prog1).map Prod.snd, regBound p sp := by
  rintro ⟨hsp, h⟩ p hp
  simp only [compile, stubs, List.map_append, List.map_cons, List.map_nil, List.map_map,
    List.mem_append, List.mem_singleton, List.mem_map, Function.comp] at hp
  rcases hp with rfl | ⟨⟨k, q⟩, hq, rfl⟩
  · simp only [regBound]
    exact ⟨stub_regBound dc sp hsp, by omega⟩
  · exact comp_regBound hsp _ _ q (h q (List.mem_map.2 ⟨(k, q), hq, rfl⟩))

open ConventionSupport in
/-- Exact HOL `stack_alloc_call_args` (`stack_allocProofScript.sml:6304-6331`).
HOL's free `prog1 dc` are implicit. -/
@[hol "cakeml/compiler/backend/proofs/stack_allocProofScript.sml" "stack_alloc_call_args"
  (words_as_type_indexed_bitvec)]
theorem stack_alloc_call_args {width : Nat} [NeZero width]
    {prog1 : List (Nat × HolProg width)} {dc : DataToWord.Config} :
    (∀ p ∈ prog1.map Prod.snd, callArgs p 1 2 3 4 0) →
    ∀ p ∈ (compile dc prog1).map Prod.snd, callArgs p 1 2 3 4 0 := by
  intro h p hp
  simp only [compile, stubs, List.map_append, List.map_cons, List.map_nil, List.map_map,
    List.mem_append, List.mem_singleton, List.mem_map, Function.comp] at hp
  rcases hp with rfl | ⟨⟨k, q⟩, hq, rfl⟩
  · simp only [callArgs, and_true]
    exact stub_callArgs dc
  · exact comp_callArgs _ _ q (h q (List.mem_map.2 ⟨(k, q), hq, rfl⟩))

/-- Exact HOL `compile_has_fp_ops` (`stack_allocProofScript.sml:6333-6360`):
the GC stub, and hence `compile`, ignores the FP-capability flags of the
configuration. HOL's free `dconf b1 b2 code` are implicit. -/
@[hol "cakeml/compiler/backend/proofs/stack_allocProofScript.sml" "compile_has_fp_ops"
  (words_as_type_indexed_bitvec)]
theorem compile_has_fp_ops {width : Nat} [NeZero width] {dconf : DataToWord.Config}
    {b1 b2 : Bool} {code : List (Nat × HolProg width)} :
    compile { dconf with hasFpOps := b1, hasFpTern := b2 } code = compile dconf code := rfl

open ConventionSupport in
/-- Exact HOL `stack_alloc_stack_asm_convs` (`stack_allocProofScript.sml:6239-6268`).
HOL's free `c prog conf` are implicit; `EVERY (λ(n,p). P p) l` is bounded
quantification over the pairs of `l`, `conf_ok (:'a)` is `confOk width`,
`addr_offset_ok c 0w` is `asmAddrOffsetOkExact c 0`, `good_dimindex (:'a)` is
`goodDimindex width`, and the `INL Add`/`INL Sub` immediates are
`Sum.inl .add`/`Sum.inl .sub`. All ten source premises are kept; HOL's
`'a asm_config` shares the program word dimension. -/
@[hol "cakeml/compiler/backend/proofs/stack_allocProofScript.sml"
  "stack_alloc_stack_asm_convs" (words_as_type_indexed_bitvec)]
theorem stack_alloc_stack_asm_convs {width : Nat} [NeZero width] {c : AsmConfigExact width}
    {prog : List (Nat × HolProg width)} {conf : DataToWord.Config} :
    (∀ np ∈ prog, stackAsmName c np.2) ∧ (∀ np ∈ prog, stackAsmRemove c np.2) ∧
    DataToWord.confOk width conf ∧ asmAddrOffsetOkExact c 0 = true ∧ regName 10 c ∧
    goodDimindex width ∧ c.validImm (.inl .add) 8 = true ∧ c.validImm (.inl .add) 4 = true ∧
    c.validImm (.inl .add) 1 = true ∧ c.validImm (.inl .sub) 1 = true →
    (∀ np ∈ compile conf prog, stackAsmName c np.2) ∧
    (∀ np ∈ compile conf prog, stackAsmRemove c np.2) := by
  rintro ⟨hn, hr, hok, haddr, hreg, hdim, h8, h4, h1, hs1⟩
  have hreg0 : regName 0 c := by simp only [regName] at hreg ⊢; omega
  have key : ∀ np ∈ compile conf prog, stackAsmName c np.2 ∧ stackAsmRemove c np.2 := by
    intro np hnp
    simp only [compile, stubs, List.mem_append, List.mem_singleton, List.mem_map] at hnp
    rcases hnp with rfl | ⟨⟨k, q⟩, hq, rfl⟩
    · simp only [stackAsmName, stackAsmRemove, and_true]
      exact ⟨⟨stub_asmName conf c hok haddr hreg hdim h8 h4 h1 hs1, hreg0⟩,
        stub_asmRemove conf c hreg⟩
    · exact stack_alloc_comp_stack_asm_name k _ q ⟨hn _ hq, hr _ hq⟩
  exact ⟨fun np h => (key np h).1, fun np h => (key np h).2⟩

end Flapjack.Compiler.Backend.StackAlloc
