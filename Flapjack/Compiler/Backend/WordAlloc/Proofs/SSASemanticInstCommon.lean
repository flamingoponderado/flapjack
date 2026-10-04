import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSASemanticRegisterWrites

namespace Flapjack.Compiler.Backend.WordAlloc

namespace SemanticInstInstCommonWitnesses

/-- Canonical imported native WordSem finite-map roundtrip. -/
theorem holFmapAsFiniteSupportRelationWitness_WordSemStateFiniteExact
    {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : WordSemStateBroad width C F) (h : state.FiniteSupport),
      (WordSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : WordSemStateFiniteExact width C F,
      WordSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  WordSemStateExact.holFmapAsFiniteSupportWitness

end SemanticInstInstCommonWitnesses

/-- Full original native Skip constructor case from the initial Inst split.
All six original premises and complete Error-exempt source-permutation
simulation are retained. Skip leaves the state, SSA and next unchanged;
unsupported16 instructions return NONE in both original and native inst,
so evaluation returns source Error and the original conclusion exempts it.
No target-run, successful-source or post-state premise is added. Inst/evaluator
inherits reals_as_rational_cuts (SOUNDNESS item 8). -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem ssaCcTransCorrectInstSkip {width : Nat} [NeZero width] {C F : Type}
    (source target : WordSemStateFiniteExact width C F)
    (ssa : Spt Nat) (next : Nat)
    (tables : List (Spt Nat × Spt Unit × Spt Unit))
    (h : Flapjack.WordAlloc.wordStateEqRel source target ∧
      ssaLocalsRel next ssa source.locals target.locals ∧ isAllocVar next ∧
      everyVarHOL (width := width) (fun x => decide (x < next)) (.inst .skip) = true ∧
      ssaMapOK next ssa ∧ ltOK tables) :
    ssaSimulation (.inst .skip) source target ssa next tables := by
  refine ⟨target.permute, ?_⟩
  simp_all [WordSemStateFiniteExact.evaluate, WordSemStateFiniteExact.inst,
    ssaCcTrans, ssaCcTransInst, Flapjack.WordAlloc.wordStateEqRel]

/-- Full original native Load16 constructor case from the initial Inst split.
All six original premises and complete Error-exempt source-permutation
simulation are retained. Skip leaves the state, SSA and next unchanged;
unsupported16 instructions return NONE in both original and native inst,
so evaluation returns source Error and the original conclusion exempts it.
No target-run, successful-source or post-state premise is added. Inst/evaluator
inherits reals_as_rational_cuts (SOUNDNESS item 8). -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem ssaCcTransCorrectInstLoad16 {width : Nat} [NeZero width] {C F : Type}
    (source target : WordSemStateFiniteExact width C F)
    (ssa : Spt Nat) (next : Nat)
    (data base : Nat) (offset : BitVec width)
    (tables : List (Spt Nat × Spt Unit × Spt Unit))
    (_h : Flapjack.WordAlloc.wordStateEqRel source target ∧
      ssaLocalsRel next ssa source.locals target.locals ∧ isAllocVar next ∧
      everyVarHOL (width := width) (fun x => decide (x < next)) (.inst (.mem .load16 data (.addr base offset))) = true ∧
      ssaMapOK next ssa ∧ ltOK tables) :
    ssaSimulation (.inst (.mem .load16 data (.addr base offset))) source target ssa next tables := by
  refine ⟨target.permute, ?_⟩
  simp [WordSemStateFiniteExact.evaluate, WordSemStateFiniteExact.inst]

/-- Full original native Store16 constructor case from the initial Inst split.
All six original premises and complete Error-exempt source-permutation
simulation are retained. Skip leaves the state, SSA and next unchanged;
unsupported16 instructions return NONE in both original and native inst,
so evaluation returns source Error and the original conclusion exempts it.
No target-run, successful-source or post-state premise is added. Inst/evaluator
inherits reals_as_rational_cuts (SOUNDNESS item 8). -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem ssaCcTransCorrectInstStore16 {width : Nat} [NeZero width] {C F : Type}
    (source target : WordSemStateFiniteExact width C F)
    (ssa : Spt Nat) (next : Nat)
    (data base : Nat) (offset : BitVec width)
    (tables : List (Spt Nat × Spt Unit × Spt Unit))
    (_h : Flapjack.WordAlloc.wordStateEqRel source target ∧
      ssaLocalsRel next ssa source.locals target.locals ∧ isAllocVar next ∧
      everyVarHOL (width := width) (fun x => decide (x < next)) (.inst (.mem .store16 data (.addr base offset))) = true ∧
      ssaMapOK next ssa ∧ ltOK tables) :
    ssaSimulation (.inst (.mem .store16 data (.addr base offset))) source target ssa next tables := by
  refine ⟨target.permute, ?_⟩
  simp [WordSemStateFiniteExact.evaluate, WordSemStateFiniteExact.inst]

end Flapjack.Compiler.Backend.WordAlloc
