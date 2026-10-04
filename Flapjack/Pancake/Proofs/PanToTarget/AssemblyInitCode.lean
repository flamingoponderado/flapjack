import Flapjack.Compiler.Backend.StackToLab.Proofs.FullMakeInitSemantics
import Flapjack.Pancake.Proofs.PanToTarget.AssemblyResourceLimit

/-!
# `pan_to_target_compile_semantics` assembly, stage E (init code)

Intermediate step of the single HOL proof of `pan_to_target_compile_semantics`
(`pan_to_targetProofScript.sml:1756-1916`): taking `full_make_init` apart to expose
the stack initializer `init_code`, and instantiating `stack_removeProof$init_code_thm`
on its source state `s2`.  The premises are the `full_make_init_semantics`
hypotheses (`Assumptions`), which the top proof establishes from its own
hypotheses.  Not a HOL theorem, so untagged.
-/

namespace Flapjack.Pancake.Proofs.PanToTarget

open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.StackToLab.Proofs.FullMakeInitSemantics
open Flapjack.Compiler.Backend.StackRemove Flapjack.Compiler.Backend.StackRemove.Proofs

/-- Stage E core (HOL lines 1756-1916): under the `full_make_init_semantics`
hypotheses, `init_code` runs on the stack-names state `s2` without a result, and
`init_code_thm`'s pointer facts hold with `w2`/`w3`/`w4` the lab state's
`len`/`ptr2`/`len2` registers. -/
theorem panToTargetInitCodeRun {width : Nat} [NeZero width] {C F : Type}
    {stackConf : StackToLab.Config} {dataConf : DataToWord.Config} {maxHeap sp : Nat}
    {offset : BitVec width × BitVec width} {bitmaps : List (BitVec width)}
    {code : List (Nat × HolProg width)} {t : Flapjack.Compiler.Backend.LabSem.State width C F}
    {saveRegs : Nat → Bool} {dataSp : Nat}
    {coracle : Nat → C × List (Nat × HolProg width) × List (BitVec width)}
    (hA : Assumptions stackConf dataConf maxHeap sp offset bitmaps code t saveRegs dataSp
      coracle) :
    ∃ (t' : StackSemStateFiniteExact width C F) (w2 w3 w4 : BitVec width),
      StackSemEvaluate.evaluate (initCode (StackToLab.isGenGc dataConf.gcKind) maxHeap sp,
          s2 stackConf dataConf maxHeap sp offset code t saveRegs coracle) = (none, t') ∧
      t.regs t.lenReg = .word w2 ∧ t.regs t.ptr2Reg = .word w3 ∧
      t.regs t.len2Reg = .word w4 ∧
      holByteAligned w2 = true ∧ holByteAligned w4 = true ∧ w2 < w4 ∧
      t'.regs.lookup (sp + 2) = some (.word w2) ∧
      t'.regs.lookup sp = some (.word (w4 - bytesInWord width)) ∧
      (w2 + BitVec.ofNat width maxStackAlloc * bytesInWord width ≤ w3 ∧
        w3 ≤ w4 - BitVec.ofNat width maxStackAlloc * bytesInWord width ∧
        (-1 * w2 + w3).toNat ≤ maxHeap * (bytesInWord width).toNat ∧
        (bytesInWord width).toNat * maxHeap < 2 ^ width →
        t'.regs.lookup (sp + 1) =
          some (.word ((((w3 + -1 * w2) >>> (wordShiftAmount width + 1)) <<<
            (wordShiftAmount width + 1)) + w2 +
            bytesInWord width * BitVec.ofNat width storeList.length))) := by
  have hd := dischargeThese_s2 hA
  have hp := propagateThese_s2 (bitmaps := bitmaps) (dataSp := dataSp) hA
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, h4, h3, h2, -, -, hbij⟩ := id hA
  obtain ⟨every, oracleBound, oracleEq, codeEq, k8, entry1, save, noStack, noStore, noAlloc,
    maxOk⟩ := hd
  obtain ⟨good, ptr2, ptr3, ptr4, bp, r2, r3, r4, m0, m1, m2, m3, m4, cbEmpty, le, al2, al4,
    albp, big, heap⟩ := hp
  have sub : -1 * ptr2 + ptr4 = ptr4 - ptr2 := by
    rw [BitVec.neg_mul]; simp [BitVec.sub_eq_add_neg, BitVec.add_comm]
  rw [sub] at heap
  have main := InitCodeCorrect.initCodeThm (StackToLab.isGenGc dataConf.gcKind) maxHeap sp
    bitmaps dataSp (s2 stackConf dataConf maxHeap sp offset code t saveRegs coracle)
    stackConf.jump offset (sptFromAList (code1 dataConf code)) (coracle1 coracle)
    ⟨⟨ptr2, ptr3, ptr4, bp, good, k8, entry1, save, noStack, noStore, noAlloc, r2, r3, r4,
      m0, m1, m2, m3, m4, le, big, al2, al4, albp, cbEmpty, heap⟩,
     InitCodeRelation.impCodeRel stackConf.jump offset (StackToLab.isGenGc dataConf.gcKind)
       maxHeap sp BvlToBvi.initGlobalsLocation (code1 dataConf code) _ ⟨every, codeEq⟩,
     oracleEq, oracleBound,
     by rw [codeEq, sptLookup_sptFromAList]
        simp [compileHOL, initStubs, sptAListLookup, stackErrLab],
     maxOk⟩
  revert main
  rcases hev : StackSemEvaluate.evaluate (initCode (StackToLab.isGenGc dataConf.gcKind) maxHeap
      sp, s2 stackConf dataConf maxHeap sp offset code t saveRegs coracle) with ⟨_ | _, t'⟩
  · rintro ⟨⟨w2, w3, w4, s2r2, a2, t2, s2r4, a4, lt, tsp, bound, s2r3⟩, -⟩
    have lk : ∀ i, (i = 2 ∨ i = 3 ∨ i = 4) →
        (s2 stackConf dataConf maxHeap sp offset code t saveRegs coracle).regs.lookup i =
          some (t.regs (StackNames.findNameSpt stackConf.regNames i)) :=
      fun i hi => s2_regs_lookup hbij hi
    rw [lk 2 (.inl rfl), h2] at s2r2
    rw [lk 3 (.inr (.inl rfl)), h3] at s2r3
    rw [lk 4 (.inr (.inr rfl)), h4] at s2r4
    exact ⟨t', w2, w3, w4, rfl, Option.some.inj s2r2, Option.some.inj s2r3,
      Option.some.inj s2r4, a2, a4, lt, t2, tsp, bound⟩
  · simp

/-- A successful `full_make_init` (`opt = SOME x`, as `full_make_init_semantics`
gives) is `init_reduce` of the `init_code` result state, and the stack state it
returns has `x`'s stack (HOL lines 1756-1797 and 1924-1929). -/
theorem panToTargetFullMakeInitReduce {width : Nat} [NeZero width] {C F : Type}
    {stackConf : StackToLab.Config} {dataConf : DataToWord.Config} {maxHeap sp : Nat}
    {offset : BitVec width × BitVec width} {bitmaps : List (BitVec width)}
    {code : List (Nat × HolProg width)} {t : Flapjack.Compiler.Backend.LabSem.State width C F}
    {saveRegs : Nat → Bool} {dataSp : Nat}
    {coracle : Nat → C × List (Nat × HolProg width) × List (BitVec width)}
    {sst x t' : StackSemStateFiniteExact width C F}
    (hfmi : StackToLab.Proofs.FullMakeInit.fullMakeInit stackConf dataConf maxHeap sp offset bitmaps code t
      saveRegs dataSp coracle = (sst, some x))
    (hev : StackSemEvaluate.evaluate (initCode (StackToLab.isGenGc dataConf.gcKind) maxHeap sp,
      s2 stackConf dataConf maxHeap sp offset code t saveRegs coracle) = (none, t')) :
    x = InitReduce.initReduce (StackToLab.isGenGc dataConf.gcKind) stackConf.jump offset sp
        (sptFromAList (code1 dataConf code)) bitmaps dataSp (coracle1 coracle) t' ∧
      sst.stack = x.stack := by
  rw [fullMakeInit_eq] at hfmi
  simp only [Prod.mk.injEq] at hfmi
  obtain ⟨hs, hopt⟩ := hfmi
  have hx : x = InitReduce.initReduce (StackToLab.isGenGc dataConf.gcKind) stackConf.jump
      offset sp (sptFromAList (code1 dataConf code)) bitmaps dataSp (coracle1 coracle) t' := by
    unfold InitMake.makeInitOpt at hopt
    rw [hev] at hopt
    simp only at hopt
    split at hopt
    · exact (Option.some.inj hopt).symm
    · cases hopt
  refine ⟨hx, ?_⟩
  rw [← hs]
  simp only [StackAlloc.makeInit, InitMake.makeInitAny]
  unfold InitMake.makeInitOpt at hopt ⊢
  rw [hopt]

/-- Stage G meets stage E (HOL lines 2311-2335 and 1924-1929): for the lab state's
initial `len`/`ptr2`/`len2` registers `w2`/`w3`/`w4`, under the pointer bounds of
the top theorem's hypotheses, the stack limit `FST (get_stack_heap_limit max_heap
(w2, w3, w4))` is at most the length of the stack of the stack state that
`full_make_init` returns. -/
theorem panToTargetStackLimitLeInitStack {width : Nat} [NeZero width] {C F : Type}
    {stackConf : StackToLab.Config} {dataConf : DataToWord.Config} {maxHeap sp : Nat}
    {offset : BitVec width × BitVec width} {bitmaps : List (BitVec width)}
    {code : List (Nat × HolProg width)} {t : Flapjack.Compiler.Backend.LabSem.State width C F}
    {saveRegs : Nat → Bool} {dataSp : Nat}
    {coracle : Nat → C × List (Nat × HolProg width) × List (BitVec width)}
    {sst x : StackSemStateFiniteExact width C F} (w2 w3 w4 : BitVec width)
    (hA : Assumptions stackConf dataConf maxHeap sp offset bitmaps code t saveRegs dataSp
      coracle)
    (hfmi : StackToLab.Proofs.FullMakeInit.fullMakeInit stackConf dataConf maxHeap sp offset
      bitmaps code t saveRegs dataSp coracle = (sst, some x))
    (h2 : t.regs t.lenReg = .word w2) (h3 : t.regs t.ptr2Reg = .word w3)
    (h4 : t.regs t.len2Reg = .word w4)
    (hlo : w2 + BitVec.ofNat width maxStackAlloc * bytesInWord width ≤ w3)
    (hhi : w3 ≤ w4 - BitVec.ofNat width maxStackAlloc * bytesInWord width)
    (hheap : (-1 * w2 + w3).toNat ≤ maxHeap * (bytesInWord width).toNat)
    (hheapLt : (bytesInWord width).toNat * maxHeap < 2 ^ width)
    (halign : holAligned (wordShiftAmount width + 1) (w3 + -1 * w2) = true) :
    (InitLimits.getStackHeapLimit maxHeap (w2, w3, w4)).1 ≤ sst.stack.length := by
  obtain ⟨t', v2, v3, v4, hev, g2, g3, g4, a2, a4, -, tsp2, tsp, tsp1⟩ :=
    panToTargetInitCodeRun hA
  rw [h2] at g2; rw [h3] at g3; rw [h4] at g4
  cases g2; cases g3; cases g4
  obtain ⟨hx, hstack⟩ := panToTargetFullMakeInitReduce hfmi hev
  have hgood : goodDimindex width := hA.1
  rw [hstack, hx]
  simp only [InitReduce.initReduce, length_readMem]
  rw [holFapply_of_lookup tsp, holFapply_of_lookup (tsp1 ⟨hlo, hhi, hheap, hheapLt⟩)]
  exact panToTargetStackLimitLeLength hgood maxHeap w2 w3 w4 a2 a4 hlo hhi hheap hheapLt halign

end Flapjack.Pancake.Proofs.PanToTarget
