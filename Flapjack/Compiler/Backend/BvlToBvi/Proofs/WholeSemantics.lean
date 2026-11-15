module

public import Flapjack.Compiler.Backend.BvlToBvi.Proofs.Divergence
public import Flapjack.Compiler.Backend.BvlToBvi.Proofs.FullOracle
public import Flapjack.Compiler.Backend.BvlToBvi.Proofs.OracleConditions
public import Flapjack.Compiler.Backend.BvlInline.Proofs.WholeProgram
public import Flapjack.Compiler.Backend.BviInline.Proofs.Pipeline
@[expose] public section

/-! Whole-program correctness of the BVL-to-BVI pipeline. -/
open Flapjack Flapjack.Compiler.Backend Flapjack.SemanticPrimitivesHOL Flapjack.Basis.Pure.MlString
namespace Flapjack.Compiler.Backend.BvlToBvi.Proofs

/-- Complete pipeline preservation of non-failing source behavior. The
semantics inherit the real-model assumption documented in SOUNDNESS item 8. -/
@[hol "cakeml/compiler/backend/proofs/bvl_to_bviProofScript.sml" "compile_semantics"]
theorem compile_semantics {C F : Type} (start : Nat) (c : BvlToBvi.Config) (names namesOut : Spt MlString)
    (program : List (Nat × Nat × Bvl.Exp)) (targetStart : Nat) (output : List (Nat × Nat × Bvi.Exp))
    (inlines : Spt (Nat × Bvl.Exp)) (bviInlines : Spt (Nat × Bvi.Exp)) (n1 n2 n3 : Nat)
    (oracle : Nat → (Spt (Nat × Bvl.Exp) × Nat × Nat × Nat × Spt (Nat × Bvi.Exp) × C) × List (Nat × Nat × Bvl.Exp))
    (ffi : HolFfiState F) (compiler : BviSem.Compiler C)
    (h : compileSource start c names program = (targetStart, output, inlines, bviInlines, n1, n2, n3, namesOut) ∧
      (oracle 0).1.1 = inlines ∧ (oracle 0).1.2.1 = n1 ∧ (oracle 0).1.2.2.1 = n2 ∧
      (oracle 0).1.2.2.2.1 = n3 ∧ (oracle 0).1.2.2.2.2.1 = bviInlines ∧
      (∀ i, ((oracle i).2.map Prod.fst).Nodup ∧
        bvlNumStubs ≤ (oracle i).1.2.2.1 ∧ inNs 2 (oracle i).1.2.2.1 ∧
        bvlNumStubs ≤ (oracle i).1.2.2.2.1 ∧ inNs 3 (oracle i).1.2.2.2.1) ∧
      (program.map Prod.fst).Nodup)
    (nonfail : BvlSem.semantics ffi (sptFromAList program) oracle (fullCc c compiler) start ≠ .fail) :
    BviSem.semantics ffi (sptFromAList output) (fullCo c oracle) compiler targetStart =
      BvlSem.semantics ffi (sptFromAList program) oracle (fullCc c compiler) start := by
  obtain ⟨run, inline0, lower0, tail0, tmc0, bviInline0, oracleGood, distinct⟩ := h
  rcases hi : BvlInline.compileProg c.inlineSizeLimit c.splitMainAtSeq c.expCut program with ⟨ic, pi⟩
  rcases hl : compileProgSource start 0 pi with ⟨l, p, a⟩
  rcases ht : BviTailrec.compileProgSource c.doTailrec (bvlNumStubs + 2) p with ⟨b, pt⟩
  rcases hm : BviTmc.compileProgSource c.doTmc (bvlNumStubs + 3) pt with ⟨d, pm⟩
  rcases hb : BviInline.compileProgSource pm with ⟨bc, po⟩
  simp only [compileSource, hi, hl, ht, hm, hb, Prod.mk.injEq] at run
  rcases run with ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  have piDistinct : (pi.map Prod.fst).Nodup := by
    rw [BvlInline.Proofs.compileProg_names _ _ _ _ _ _ hi]
    exact distinct
  have piHandles := BvlInline.Proofs.compileProg_handleOk _ _ _ _ _ _ hi
  let co1 := BackendProps.stateCo (BvlInline.compileInc c.inlineSizeLimit c.splitMainAtSeq c.expCut) oracle
  let cc2 := BackendProps.stateCc (BviTailrec.compileProgSource c.doTailrec)
    (BackendProps.stateCc (BviTmc.compileProgSource c.doTmc)
      (BackendProps.stateCc BviInline.compileIncSource compiler))
  let cc1 := BackendProps.stateCc compileIncSource cc2
  have inlineSem := BvlInline.Proofs.compileProg_semantics c.inlineSizeLimit c.splitMainAtSeq c.expCut
    program ic pi oracle ffi cc1 start ⟨hi, inline0, distinct⟩ (by simpa [fullCc, cc1, cc2] using nonfail)
  have inlineNonfail : BvlSem.semantics ffi (sptFromAList pi) co1 cc1 start ≠ .fail := by
    rw [inlineSem]
    simpa [fullCc, cc1, cc2] using nonfail
  have oracleDistinct : ∀ i, ((co1 i).2.map Prod.fst).Nodup := by
    intro i
    change (((BackendProps.stateCo (BvlInline.compileInc c.inlineSizeLimit c.splitMainAtSeq c.expCut) oracle i).2).map Prod.fst).Nodup
    rw [inlineOracle_names]
    exact (oracleGood i).1
  have oracleHandles : ∀ i, ∀ entry ∈ (co1 i).2, BvlHandle.Proofs.handleOk [entry.2.2] :=
    inlineOracle_handleOk _ _ _ oracle
  have lowerBound : a ≤ (co1 0).1.1 := by simpa [co1, BackendProps.stateCo] using lower0.ge
  have lowerSem := compileProgSource_semantics start 0 l a pi p co1 cc2 ffi
    ⟨hl, piDistinct, piHandles, oracleHandles, lowerBound, inlineNonfail⟩
  let co2 := BackendProps.stateCo compileIncSource co1
  have lowerNonfail : BviSem.semantics ffi (sptFromAList p) co2 cc2 l ≠ .fail := by
    rw [lowerSem]
    exact inlineNonfail
  have tailCond : BviTailrec.inputCondition (bvlNumStubs + 2) p := by
    apply compileProgFuel_production_tailrec_inputCondition 0 0 start 0 l a pi p piDistinct
    simp [compileProgFuel, hl]
  have bounds2 : ∀ i, bvlNumStubs ≤ (co1 i).1.2.1 := by
    intro i
    simpa [co1, BackendProps.stateCo] using (oracleGood i).2.1
  have worker2 : ∀ i, BviTailrec.inWorkerNamespace (co1 i).1.2.1 := by
    intro i
    simpa [co1, BackendProps.stateCo, BviTailrec.inWorkerNamespace, inNs] using (oracleGood i).2.2.1
  have tailOracleCond : ∀ i, BviTailrec.inputCondition (co2 i).1.1 (co2 i).2 :=
    lowered_oracle_tailrec_inputCondition co1 oracleDistinct bounds2 worker2
  have tailFuel : BviTailrec.compileProgFuel 0 c.doTailrec (bvlNumStubs + 2) p = some (b, pt) := by
    simp [BviTailrec.compileProgFuel_eq_source, ht]
  have tailBound : ∀ name ∈ pt.map Prod.fst, BviTailrec.inWorkerNamespace name → name < (co2 0).1.1 := by
    intro name member worker
    have bound := tailrec_output_worker_below_counter c.doTailrec (bvlNumStubs + 2) b p pt tailCond ht name member worker
    simpa [co2, co1, BackendProps.stateCo] using tail0 ▸ bound
  have lowerFuel : compileProgFuel 0 0 start 0 pi = some (l, p, a) := by
    simp [compileProgFuel, hl]
  have tmcCond : BviTmc.inputCondition (bvlNumStubs + 3) pt :=
    lowered_tailrec_tmc_inputCondition_complete 0 0 start 0 l a c.doTailrec pi p pt b piDistinct lowerFuel tailFuel
  have originalDistinct : ∀ i, ((oracle i).2.map Prod.fst).Nodup := fun i => (oracleGood i).1
  have originalBounds2 : ∀ i, bvlNumStubs ≤ (oracle i).1.2.2.1 := fun i => (oracleGood i).2.1
  have originalWorker2 : ∀ i, BviTailrec.inWorkerNamespace (oracle i).1.2.2.1 := by
    intro i
    simpa [BviTailrec.inWorkerNamespace, inNs] using (oracleGood i).2.2.1
  have originalBounds3 : ∀ i, bvlNumStubs ≤ (oracle i).1.2.2.2.1 := fun i => (oracleGood i).2.2.2.1
  have originalWorker3 : ∀ i, BviTmc.inWorkerNamespace (oracle i).1.2.2.2.1 := by
    intro i
    simpa [BviTmc.inWorkerNamespace, inNs] using (oracleGood i).2.2.2.2
  have tmcOracleCond : ∀ i, BviTmc.inputCondition
      ((BackendProps.stateCo (BviTailrec.compileProgSource c.doTailrec) co2 i).1.1)
      ((BackendProps.stateCo (BviTailrec.compileProgSource c.doTailrec) co2 i).2) :=
    fullOracle_tmcCondition c.inlineSizeLimit c.splitMainAtSeq c.expCut c.doTailrec oracle
      originalDistinct originalBounds2 originalWorker2 originalBounds3 originalWorker3
  have tmcBound : ∀ name ∈ pm.map Prod.fst, BviTmc.inWorkerNamespace name →
      name < ((BackendProps.stateCo (BviTailrec.compileProgSource c.doTailrec) co2) 0).1.1 := by
    intro name member worker
    have bound := tmc_output_worker_below_counter c.doTmc (bvlNumStubs + 3) d pt pm tmcCond hm name member worker
    simpa [co2, co1, BackendProps.stateCo] using tmc0 ▸ bound
  have tmcFuel : BviTmc.compileProgFuel 0 c.doTmc (bvlNumStubs + 3) pt = some (d, pm) := by
    simp [BviTmc.compileProgFuel_eq_source, hm]
  have inlineFuel : BviInline.compileProgFuel 0 pm = some (bc, po) := by
    simpa [BviInline.compileProgSource] using (BviInline.compileProgFuel_eq_source 0 pm).trans (congrArg some hb)
  have inlineCache : ((BackendProps.stateCo (BviTmc.compileProgSource c.doTmc)
      (BackendProps.stateCo (BviTailrec.compileProgSource c.doTailrec) co2)) 0).1.1 = bc := by
    simpa [co2, co1, BackendProps.stateCo] using bviInline0
  have finalSem := BviInline.tailrec_tmc_inline_semantics 0 c.doTailrec c.doTmc
    (bvlNumStubs + 2) (bvlNumStubs + 3) l p pt pm po b d bc ffi co2 compiler
    tailCond tailOracleCond tailBound tailFuel tmcCond tmcOracleCond tmcBound tmcFuel inlineFuel inlineCache
    (by simpa [cc2] using lowerNonfail)
  simpa [fullCo, fullCc, co1, co2, cc1, cc2] using finalSem.trans (lowerSem.trans inlineSem)

end Flapjack.Compiler.Backend.BvlToBvi.Proofs
