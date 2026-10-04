import Flapjack.Compiler.Backend.WordToStack.Proofs.CompCorrect.Seq
import Flapjack.Compiler.Backend.WordToStack.Proofs.LoadRegisterTwo
import Flapjack.Compiler.Backend.WordToStack.Proofs.LoadContinuations
namespace Flapjack.WordToStackProofs.CompCorrect.CodeBufferWrite
open Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.WordToStack.Native
/-- Flapjack-only source case decomposition for the full buffer-write case.
No independent HOL declaration: this discharges the original nonerror premise. -/
theorem sourceSuccess {width : Nat} [NeZero width] {C F : Type}
    (r1 r2 : Nat) (source post : WordSemStateFiniteExact width (Nat × C) F)
    (result : Option (WordSemResult width))
    (execution : WordSemStateFiniteExact.evaluate (.codeBufferWrite r1 r2) source = (result,post))
    (notError : result ≠ some .error) :
    ∃ (w1 w2 : BitVec width), ∃ cb,
      WordSemStateFiniteExact.getVar r1 source = some (.word w1) ∧
      WordSemStateFiniteExact.getVar r2 source = some (.word w2) ∧
      wordSemBufferWrite source.codeBuffer w1 (w2.setWidth 8) = some cb ∧
      result = none ∧ post = {source with codeBuffer := cb} := by
  simp only [WordSemStateFiniteExact.evaluate] at execution
  cases h1 : WordSemStateFiniteExact.getVar r1 source with
  | none => simp [h1] at execution; obtain ⟨rfl,rfl⟩ := execution; contradiction
  | some v1 =>
    cases v1 with
    | loc a b =>
      cases h2 : WordSemStateFiniteExact.getVar r2 source <;>
        simp [h1,h2] at execution <;> obtain ⟨rfl,rfl⟩ := execution <;> contradiction
    | word w1 =>
      cases h2 : WordSemStateFiniteExact.getVar r2 source with
      | none => simp [h1,h2] at execution; obtain ⟨rfl,rfl⟩ := execution; contradiction
      | some v2 =>
        cases v2 with
        | loc a b => simp [h1,h2] at execution; obtain ⟨rfl,rfl⟩ := execution; contradiction
        | word w2 =>
          cases hw : wordSemBufferWrite source.codeBuffer w1 (w2.setWidth 8) with
          | none => simp [h1,h2,hw] at execution; obtain ⟨rfl,rfl⟩ := execution; contradiction
          | some cb =>
            simp only [h1,h2,hw,Prod.mk.injEq] at execution
            exact ⟨w1,w2,cb,rfl,rfl,hw,execution.1.symm,execution.2.symm⟩
/-- Flapjack-only preservation factoring for the actual buffer-write case;
there is no separate HOL declaration. Both sides receive the same code buffer. -/
theorem codeBufferRelation {width : Nat} [NeZero width] {C F : Type}
    {ac : AsmConfigExact width} {k f frame : Nat}
    {source : WordSemStateFiniteExact width (Nat × C) F}
    {target : StackSemStateFiniteExact width C F} {lens : List Nat}
    (cb : WordSemBuffer width 8)
    (related : stateRel ac k f frame source target lens 0) :
    stateRel ac k f frame {source with codeBuffer := cb}
      {target with codeBuffer := cb} lens 0 := by
  unfold stateRel at related ⊢
  obtain ⟨h1,h2,h3,h4,h5,h6,h7,h8,h9,h10,h11,h12,h13,h14,h15,h16,h17,h18,
    h19,h20,h21,h22,h23,h24,h25,h26,h27,h28,h29,h30,h31,h32,h33,h34,h35,h36,
    h37,h38⟩ := related
  exact ⟨h1,h2,h3,h4,h5,h6,h7,h8,h9,h10,h11,h12,h13,h14,h15,h16,h17,h18,
    h19,rfl,h21,h22,h23,h24,h25,h26,h27,h28,h29,h30,h31,h32,h33,h34,h35,h36,
    h37,h38⟩

/-- Genuine canonical source codec re-export for the relation qualifier. -/
theorem holFmapAsFiniteSupportRelationWitness_WordSemStateFiniteExact
    {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : WordSemStateBroad width C F) (h : state.FiniteSupport),
      (WordSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : WordSemStateFiniteExact width C F,
      WordSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  WordSemStateExact.holFmapAsFiniteSupportWitness

/-- Genuine canonical target codec re-export for the relation qualifier. -/
theorem holFmapAsFiniteSupportRelationWitness_StackSemStateFiniteExact
    {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : StackSemStateBroad width C F) (h : state.FiniteSupport),
      (StackSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : StackSemStateFiniteExact width C F,
      StackSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  StackSemStateSupport.holFmapAsFiniteSupportWitness



/-- Full original CodeBufferWrite constructor (7072–7096). All original
simulation premises and the full result/resource conclusion are retained.
Actual ordered source reads, native loads and target write are derived;
no targetrun, successful-buffer or postrelation premise is introduced.
Evaluator closure inherits reals_as_rational_cuts; no numerical FP claim. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem compCorrectCodeBufferWrite {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) (r1 r2 : Nat)
    (source : WordSemStateFiniteExact width (Nat × C) F) :
    Seq.Simulation ac (.codeBufferWrite r1 r2) source := by
  intro k f frame sourcePost target result bs bsPost n nPost compiled lens premises
  rcases premises with ⟨execution,notError,related,conventions,flat,compilation,
    lengthBound,bitmapBound,bitmapPrefix,labels,maxBound⟩
  obtain ⟨w1,w2,cb,read1,read2,writeEq,rfl,rfl⟩ :=
    sourceSuccess r1 r2 source sourcePost result execution notError
  have evens : r1%2=0 ∧ r2%2=0 := by
    simpa [postAllocConventionsHOL,everyVarHOL,everyStackVarHOL,
      callArgConventionHOL,isPhyVar] using conventions
  rcases fmt1 : Compiler.Backend.WordToStackRegFormat.wReg1 r1 (k,f,frame) with ⟨xs,reg1⟩
  rcases fmt2 : Compiler.Backend.WordToStackRegFormat.wReg2 r2 (k,f,frame) with ⟨ys,reg2⟩
  obtain ⟨t1,run1,clock1,rel1,_,_,_,_,regNe,loaded1⟩ :=
    LoadRegister.evaluateWStackLoadWReg1 ac k f frame r1 reg1 xs source target lens
      (.word w1) fmt1 evens.1 read1 related
  obtain ⟨t2,run2,clock2,_,rel2,_,_,otherReads,_,loaded2⟩ :=
    LoadRegisterTwo.evaluateWStackLoadWReg2 ac k f frame r2 reg2 ys source t1 lens
      (.word w2) fmt2 evens.2 read2 rel1
  have read1Final : StackSemStateOps.getVar reg1 t2 = some (.word w1) := by
    rw [otherReads reg1 regNe]
    exact loaded1
  have bufferEq : t2.codeBuffer = source.codeBuffer :=
    rel2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have programEq := congrArg Prod.fst compilation
  simp only [compNative,fmt1,fmt2] at programEq
  subst compiled
  refine ⟨0,{t2 with codeBuffer := cb},none,?_,?_⟩
  · simp only [Nat.add_zero,wStackLoadAppend,Function.comp_apply]
    rw [LoadRegister.evaluateWStackLoadSeq,StackSemEvaluate.evaluate_seq,run1]
    have fix1 : StackSemControl.fixClock target ((none : Option (StackSemResult width)),t1) = (none,t1) := by
      have le : t1.clock ≤ target.clock := by omega
      simp only [StackSemControl.fixClock,Nat.min_eq_right le]
    simp only [fix1]
    rw [LoadRegister.evaluateWStackLoadSeq,StackSemEvaluate.evaluate_seq,run2]
    have fix2 : StackSemControl.fixClock t1 ((none : Option (StackSemResult width)),t2) = (none,t2) := by
      have le : t2.clock ≤ t1.clock := by omega
      simp only [StackSemControl.fixClock,Nat.min_eq_right le]
    simp only [fix2]
    simp only [StackSemEvaluate.evaluate_codeBufferWrite,read1Final,loaded2,bufferEq,writeEq]
  · simpa only [compCorrectResult,Option.map_none,ne_eq,not_true_eq_false,
      ↓reduceIte] using codeBufferRelation cb rel2

end Flapjack.WordToStackProofs.CompCorrect.CodeBufferWrite
