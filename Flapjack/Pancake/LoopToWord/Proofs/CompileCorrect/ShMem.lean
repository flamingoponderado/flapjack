import Flapjack.HolRef
import Flapjack.Pancake.LoopToWord.Proofs.CompileCorrect.Property
import Flapjack.Pancake.LoopToWord.Proofs.CompileCorrect.Arith
import Flapjack.Pancake.Proofs.LoopToWord.CompExpPreservesEval
import Flapjack.Pancake.Proofs.LoopToWord.WordToBytes
import Flapjack.Pancake.Semantics.LoopSemStateExact.ShMem
import Flapjack.Compiler.Backend.Semantics.WordSem.ShMem

/-!
# `ShMem` case of `loop_to_word`'s `compile_correct`

The exact `loopSem$evaluate_ind` case of HOL `compile_correct`
(`cakeml/pancake/proofs/loop_to_wordProofScript.sml:57-97`) for `ShMem`,
resumed at `:1455-1496`.  Bead `flapjack-pxn.18.5.9.26.1`.  The statement
takes the same form as the cases in `CompileCorrect/Base.lean`.  The source
`sh_mem_op` and the target `share_inst` make the same `call_FFI` on the same
FFI state and payload.  For byte stores the payload agrees by the tagged
`TAKE_1_word_to_bytes`.
-/

namespace Flapjack

open LoopToWord.CompileCorrect
open LoopToWordCompileCorrectArithSupport

namespace LoopToWordCompileCorrectShMemWitnesses

/-- Same-module roundtrip for the relation qualifier's loopSem state fields. -/
theorem holFmapAsFiniteSupportRelationWitness_LoopSemStateFiniteExact
    {width : Nat} [NeZero width] {F : Type} :
    (∀ (state : LoopSemStateBroad width F) (h : state.FiniteSupport),
        (LoopSemStateBroad.ofBroad state h).toBroad = state) ∧
      (∀ state : LoopSemStateFiniteExact width F,
        LoopSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  LoopSemStateFiniteExact.holFmapAsFiniteSupportWitness

/-- Same-module roundtrip for the relation qualifier's wordSem state fields. -/
theorem holFmapAsFiniteSupportRelationWitness_WordSemStateFiniteExact
    {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : WordSemStateBroad width C F) (h : state.FiniteSupport),
        (WordSemStateBroad.ofBroad state h).toBroad = state) ∧
      (∀ state : WordSemStateFiniteExact width C F,
        WordSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  WordSemStateExact.holFmapAsFiniteSupportWitness

end LoopToWordCompileCorrectShMemWitnesses

/-- Genuine `ShMem` case of HOL `compile_correct`
    (`loop_to_wordProofScript.sml:57-97`, resumed at `:1455-1496`). -/
@[hol "cakeml/pancake/proofs/loop_to_wordProofScript.sml" "compile_correct"
  (fmap_as_finite_support_relation :=
    [LoopSemStateFiniteExact.globals, WordSemStateFiniteExact.fpRegs,
      WordSemStateFiniteExact.store])
  (words_as_type_indexed_bitvec)]
theorem compileCorrect_ShMem {width : Nat} [NeZero width] {C F : Type}
    (op : WordMemOp) (v : Nat) (ad : HolLoopExp width) (s : LoopSemStateFiniteExact width F) :
    ∀ (res : Option (LoopSemStateFiniteExact.LoopResultExact width))
      (s1 : LoopSemStateFiniteExact width F) (t : WordSemStateFiniteExact width C F)
      (ctxt : Spt Nat) (retv : WordLocW width) (l : Nat × Nat),
      LoopSemStateFiniteExact.evaluate (.shMem op v ad) s = (res, s1) ∧ res ≠ some .error ∧
        loopToWordStateRelHOLExact s t ∧ LoopToWord.localsRelHOL ctxt s.locals t.locals ∧
        sptLookup 0 t.locals = some retv ∧
        goodDimindex width ∧
        ¬ wordSemIsWordLoc retv = true ∧
        (∀ n, sptMem n (accVarsHOL (width := width) (.shMem op v ad) .ln) → sptMem n ctxt) →
      ∃ t1 res1,
        WordSemStateFiniteExact.evaluate (LoopToWord.compHOL ctxt (.shMem op v ad) l).1 t = (res1, t1) ∧
          t1.ffi = s1.ffi ∧
          resultCase ctxt retv t res s1 res1 t1 := by
  rintro res s1 t ctxt retv l ⟨hEval, hNE, hState, hLocals, hRetv, hgd, -, hAcc⟩
  simp only [LoopSemStateFiniteExact.evaluate] at hEval
  have hget : ∀ n w, sptLookup n s.locals = some w →
      WordSemStateFiniteExact.getVar (LoopToWord.findVarHOL ctxt n) t = some w :=
    fun n w h => LoopToWord.localsRelHOLGetVar ctxt s.locals t n w ⟨hLocals, h⟩
  have hState' := hState
  obtain ⟨len, hm, hmd, hsmd, hclock, hbe, hffi, hcur, hlen, htop, hglob, hcode⟩ := hState'
  split at hEval
  · rename_i addr haddr
    have hexp := LoopToWord.compExpPreservesEval s ad _ t ctxt ⟨haddr, hgd, hState, hLocals⟩
    have hmv : sptMem v ctxt := hAcc v (by simp [accVarsHOL, sptMem_sptInsert])
    cases op <;> simp only [Flapjack.Compiler.Encoders.Asm.asmIsLoad, if_true, if_false, Bool.false_eq_true] at hEval
    all_goals
      split at hEval
      rotate_left
      · simp only [Prod.mk.injEq] at hEval
        exact absurd hEval.1.symm hNE
    all_goals
      simp only [LoopSemStateFiniteExact.shMemOp, LoopSemStateFiniteExact.shMemLoad,
        LoopSemStateFiniteExact.shMemStore] at hEval
    all_goals simp only [LoopToWord.compHOL]; rw [WordSemStateFiniteExact.evaluate, hexp]
    all_goals simp only [↓reduceIte, Nat.reduceEqDiff, WordSemStateFiniteExact.shareInst,
      WordSemStateFiniteExact.shMemSetVar, WordSemStateFiniteExact.shMemLoad,
      WordSemStateFiniteExact.shMemLoadByte, WordSemStateFiniteExact.shMemLoad16,
      WordSemStateFiniteExact.shMemLoad32, WordSemStateFiniteExact.shMemStore,
      WordSemStateFiniteExact.shMemStoreByte, WordSemStateFiniteExact.shMemStore16,
      WordSemStateFiniteExact.shMemStore32, hsmd, hffi] at hEval ⊢
    all_goals simp only [show BitVec.ofNat 8 0 = (0 : BitVec 8) from rfl,
      show BitVec.ofNat 8 1 = (1 : BitVec 8) from rfl, show BitVec.ofNat 8 2 = (2 : BitVec 8) from rfl,
      show BitVec.ofNat 8 4 = (4 : BitVec 8) from rfl] at hEval
    -- loads
    all_goals first
      | (
        split at hEval
        · rename_i hd
          rw [if_pos hd]
          split at hEval
          · rename_i o hc
            simp only [Prod.mk.injEq] at hEval
            obtain ⟨rfl, rfl⟩ := hEval
            simp only [hc]
            exact ⟨_, _, rfl, by simp [WordSemStateFiniteExact.flushState,
              LoopSemStateFiniteExact.callEnv, hffi], rfl⟩
          · rename_i nf nb hc
            simp only [Prod.mk.injEq] at hEval
            obtain ⟨rfl, rfl⟩ := hEval
            simp only [hc]
            obtain ⟨hl, h0⟩ := localsRel_retv_insert ctxt _ _ v
              (.word (panWordOfBytesHOL false 0 nb)) retv hLocals hmv hRetv
            exact ⟨_, _, rfl, rfl, ⟨len, hm, hmd, hsmd, hclock, hbe, rfl, hcur, hlen, htop, hglob,
              hcode⟩, rfl, h0, hl, rfl, rfl⟩
        · simp only [Prod.mk.injEq] at hEval
          exact absurd hEval.1.symm hNE
        done)
      | skip
    -- stores
    all_goals
      split at hEval
      · rename_i w hw
        simp only [hget v _ hw]
        try rw [takeOneWordToBytesHOL w hgd] at hEval
        split at hEval
        · rename_i hd
          rw [if_pos hd]
          split at hEval
          · rename_i o hc
            simp only [Prod.mk.injEq] at hEval
            obtain ⟨rfl, rfl⟩ := hEval
            simp only [hc]
            exact ⟨_, _, rfl, by simp [WordSemStateFiniteExact.flushState,
              LoopSemStateFiniteExact.callEnv, hffi], rfl⟩
          · rename_i nf nb hc
            simp only [Prod.mk.injEq] at hEval
            obtain ⟨rfl, rfl⟩ := hEval
            simp only [hc]
            refine ⟨_, _, rfl, rfl, ⟨len, ?_, ?_, ?_, ?_, ?_, rfl, ?_, ?_, ?_, ?_, ?_⟩, rfl, hRetv,
              hLocals, rfl, rfl⟩ <;> first | rfl | assumption
        · simp only [Prod.mk.injEq] at hEval
          exact absurd hEval.1.symm hNE
      · simp only [Prod.mk.injEq] at hEval
        exact absurd hEval.1.symm hNE
  · simp only [Prod.mk.injEq] at hEval
    exact absurd hEval.1.symm hNE

end Flapjack
