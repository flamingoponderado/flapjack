module

public import Flapjack.Compiler.Backend.StackToLab.Proofs.FullMakeInitSemantics
public import Flapjack.Compiler.Backend.BackendProps.Pure

@[expose] public section

/-! backendProofScript.sml 832-833: `full_make_init_semantics2`, stack_to_lab's
`full_make_init_semantics` with the compiler-oracle premise rewritten by
`compile_no_stubs_wrap_pure_co` into `pure_co` form. -/
namespace Flapjack.Compiler.Backend.BackendProof

open Flapjack Flapjack.Compiler.Backend.StackLang Flapjack.Compiler.Backend.LabLang
open Flapjack.Compiler.Backend.StackToLab.Proofs
open Flapjack.Compiler.Backend.StackToLab.Proofs.FullMakeInit

/-- Canonical owning-state roundtrip, re-exported from the stack_to_lab
counterpart; Flapjack representation infrastructure. -/
theorem holFmapAsFiniteSupportRelationWitness_StackSemStateFiniteExact
    {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : StackSemStateBroad width C F) (h : state.FiniteSupport),
      (StackSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : StackSemStateFiniteExact width C F,
      StackSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  FullMakeInitSemantics.holFmapAsFiniteSupportRelationWitness_StackSemStateFiniteExact

/-- Exact HOL `full_make_init_semantics2` (`backendProofScript.sml:832-833`),
derived as in HOL: `full_make_init_semantics` with its `t.compile_oracle`
premise in the `pure_co (compile_no_stubs ... o FST) o coracle` form. All other
premises and the conclusion are those of the reviewed
`fullMakeInitSemantics`. -/
@[hol "cakeml/compiler/backend/proofs/backendProofScript.sml" "full_make_init_semantics2"
  (fmap_as_finite_support_relation := [StackSemStateFiniteExact.regs,
    StackSemStateFiniteExact.fpRegs, StackSemStateFiniteExact.store])
  (words_as_type_indexed_bitvec)]
theorem fullMakeInitSemantics2 {width : Nat} [NeZero width] {C F : Type}
    {stackConf : StackToLab.Config} {dataConf : DataToWord.Config} {maxHeap sp : Nat}
    {offset : BitVec width × BitVec width} {bitmaps : List (BitVec width)}
    {code : List (Nat × HolProg width)} {t : Flapjack.Compiler.Backend.LabSem.State width C F}
    {saveRegs : Nat → Bool} {dataSp : Nat}
    {coracle : Nat → C × List (Nat × HolProg width) × List (BitVec width)}
    {s : StackSemStateFiniteExact width C F} {opt : Option (StackSemStateFiniteExact width C F)} :
    fullMakeInit stackConf dataConf maxHeap sp offset bitmaps code t saveRegs dataSp coracle =
      (s, opt) ∧
    goodDimindex width ∧
    t.code = StackToLab.compile stackConf dataConf maxHeap sp offset code ∧
    t.compileOracle = BackendProps.pureCo
      (StackToLab.compileNoStubs stackConf.regNames stackConf.jump offset sp ∘ Prod.fst) ∘
        coracle ∧
    ¬t.failed = true ∧
    MakeInit.memoryAssumption stackConf.regNames bitmaps dataSp t ∧
    StackRemove.maxStackAlloc ≤ maxHeap ∧
    ¬saveRegs t.linkReg = true ∧ t.pc = 0 ∧
    (∀ k i n, saveRegs k = true → t.ioRegs n i k = none) ∧
    (∀ k n, saveRegs k = true → t.ccRegs n k = none) ∧
    (∀ x : BitVec width, t.memDomain x = true → x.toNat % (width / 8) = 0) ∧
    (∀ x : BitVec width, t.sharedMemDomain x = true → x.toNat % (width / 8) = 0) ∧
    GoodCode.goodCode sp code ∧
    (∀ n, GoodCode.goodCode sp (coracle n).2.1) ∧
    10 ≤ sp ∧
    (∀ r ∈ [2, 3, 4], saveRegs (StackNames.findNameSpt stackConf.regNames (r + sp - 2)) = true) ∧
    StackNames.findNameSpt stackConf.regNames 4 = t.len2Reg ∧
    StackNames.findNameSpt stackConf.regNames 3 = t.ptr2Reg ∧
    StackNames.findNameSpt stackConf.regNames 2 = t.lenReg ∧
    StackNames.findNameSpt stackConf.regNames 1 = t.ptrReg ∧
    StackNames.findNameSpt stackConf.regNames 0 = t.linkReg ∧
    Function.Bijective (StackNames.findNameSpt stackConf.regNames) →
    opt ≠ none ∧
      (StackSemEvaluate.semantics BvlToBvi.initGlobalsLocation s ≠ .fail →
        Flapjack.Compiler.Backend.LabSem.semantics t =
          StackSemEvaluate.semantics BvlToBvi.initGlobalsLocation s) :=
  fun h => FullMakeInitSemantics.fullMakeInitSemantics h

end Flapjack.Compiler.Backend.BackendProof
