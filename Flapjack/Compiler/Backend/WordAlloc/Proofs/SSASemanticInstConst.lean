import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSASemanticRegisterWrites

namespace Flapjack.Compiler.Backend.WordAlloc

namespace SemanticInstConstWitnesses

/-- Canonical imported native WordSem finite-map roundtrip. -/
theorem holFmapAsFiniteSupportRelationWitness_WordSemStateFiniteExact
    {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : WordSemStateBroad width C F) (h : state.FiniteSupport),
      (WordSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : WordSemStateFiniteExact width C F,
      WordSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  WordSemStateExact.holFmapAsFiniteSupportWitness

end SemanticInstConstWitnesses

/-- Genuine Const opcode case of the full original native SSA Inst semantic
case. All six original premises and the complete Error-exempt source-permutation,
result, frame, and result-sensitive locals conclusion are retained. The actual
native Const assignment and nextVarRename are used; fresh-destination locals
preservation follows from the original setVar relation. No target evaluation,
success, post-state relation, or induction hypothesis is assumed. The native
Inst/evaluator boundary inherits reals_as_rational_cuts (SOUNDNESS item 8). -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem ssaCcTransCorrectInstConst {width : Nat} [NeZero width] {C F : Type}
    (source target : WordSemStateFiniteExact width C F)
    (ssa : Spt Nat) (next name : Nat) (word : BitVec width)
    (tables : List (Spt Nat × Spt Unit × Spt Unit))
    (h : Flapjack.WordAlloc.wordStateEqRel source target ∧
      ssaLocalsRel next ssa source.locals target.locals ∧ isAllocVar next ∧
      everyVarHOL (fun x => decide (x < next)) (.inst (.const name word)) = true ∧
      ssaMapOK next ssa ∧ ltOK tables) :
    ssaSimulation (.inst (.const name word)) source target ssa next tables := by
  have bound : name < next := by
    simpa [everyVarHOL, everyVarInstHOL] using h.2.2.2.1
  have locals := ssaLocalsRelSetVar next ssa source.locals target.locals name (.word word)
    ⟨h.2.1, h.2.2.2.2.1, bound⟩
  refine ⟨target.permute, ?_⟩
  simp_all [WordSemStateFiniteExact.evaluate, WordSemStateFiniteExact.inst,
    WordSemStateFiniteExact.assign, WordSemStateFiniteExact.wordExp,
    WordSemStateFiniteExact.setVar, ssaCcTrans, ssaCcTransInst, nextVarRename,
    Flapjack.WordAlloc.wordStateEqRel]

end Flapjack.Compiler.Backend.WordAlloc
