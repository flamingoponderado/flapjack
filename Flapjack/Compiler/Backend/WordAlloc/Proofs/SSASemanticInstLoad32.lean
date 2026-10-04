import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSASemanticRegisterWrites

namespace Flapjack.Compiler.Backend.WordAlloc

namespace SemanticInstLoad32Witnesses

/-- Canonical imported native WordSem finite-map roundtrip. -/
theorem holFmapAsFiniteSupportRelationWitness_WordSemStateFiniteExact
    {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : WordSemStateBroad width C F) (h : state.FiniteSupport),
      (WordSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : WordSemStateFiniteExact width C F,
      WordSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  WordSemStateExact.holFmapAsFiniteSupportWitness

end SemanticInstLoad32Witnesses

/-- Full original native 32-bit Load32 opcode simulation, retaining all six
premises and the complete Error-exempt source-permutation conclusion. The
actual address expression is transported through the original SSA relation;
the original frame equates memory, its domain and endianness, so target memLoad32Exact follows
from the source read internally. Expression/type/domain errors retain the
source exemption; successful 32-bit-to-word fresh destination locals follow from the original
setVar relation. No target-run, source-success or post-state premise is added.
The Inst/evaluator boundary inherits reals_as_rational_cuts (SOUNDNESS item 8). -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem ssaCcTransCorrectInstLoad32 {width : Nat} [NeZero width] {C F : Type}
    (source target : WordSemStateFiniteExact width C F)
    (ssa : Spt Nat) (next dst base : Nat) (offset : BitVec width)
    (tables : List (Spt Nat × Spt Unit × Spt Unit))
    (h : Flapjack.WordAlloc.wordStateEqRel source target ∧
      ssaLocalsRel next ssa source.locals target.locals ∧ isAllocVar next ∧
      everyVarHOL (fun x => decide (x < next)) (.inst (.mem .load32 dst (.addr base offset))) = true ∧
      ssaMapOK next ssa ∧ ltOK tables) :
    ssaSimulation (.inst (.mem .load32 dst (.addr base offset))) source target ssa next tables := by
  have bound : dst < next := by
    have occurrences := h.2.2.2.1
    simp only [everyVarHOL, everyVarInstHOL, Bool.and_eq_true] at occurrences
    exact of_decide_eq_true occurrences.1
  let permuted := {source with permute := target.permute}
  have frame : Flapjack.WordAlloc.wordStateEqRel permuted target := by
    simpa [permuted, Flapjack.WordAlloc.wordStateEqRel] using h.1
  let expr : WordLangExpHOL (BitVec width) := .op .add [.var base, .const offset]
  refine ⟨target.permute, ?_⟩
  cases found : WordSemStateFiniteExact.wordExp permuted expr with
  | none =>
    have absent : WordSemStateFiniteExact.wordExp {source with permute := target.permute}
        (.op .add [.var base, .const offset]) = none := found
    simp [WordSemStateFiniteExact.evaluate, WordSemStateFiniteExact.inst, absent]
  | some address =>
    cases address with
    | loc label off =>
      have wrong : WordSemStateFiniteExact.wordExp {source with permute := target.permute}
          (.op .add [.var base, .const offset]) = some (.loc label off) := found
      simp [WordSemStateFiniteExact.evaluate, WordSemStateFiniteExact.inst, wrong]
    | word word =>
      have targetExpr := ssaCcTransExpCorrect permuted expr target ssa next (.word word) ⟨found, frame, h.2.1⟩
      have sameLoad : memLoad32Exact target.memory target.mdomain target.be word = memLoad32Exact permuted.memory permuted.mdomain permuted.be word := by
        simp_all [Flapjack.WordAlloc.wordStateEqRel]
      cases loaded : memLoad32Exact permuted.memory permuted.mdomain permuted.be word with
      | none =>
        have absent : memLoad32Exact source.memory source.mdomain source.be word = none := loaded
        have sourceExpr : WordSemStateFiniteExact.wordExp {source with permute := target.permute}
            (.op .add [.var base, .const offset]) = some (.word word) := found
        simp [WordSemStateFiniteExact.evaluate, WordSemStateFiniteExact.inst, sourceExpr, absent]
      | some value =>
        have locals := ssaLocalsRelSetVar next ssa source.locals target.locals dst (.word (value.setWidth width))
          ⟨h.2.1, h.2.2.2.2.1, bound⟩
        simp_all [WordSemStateFiniteExact.evaluate, WordSemStateFiniteExact.inst,
          WordSemStateFiniteExact.setVar, ssaCcTrans, ssaCcTransInst, nextVarRename,
          ssaCcTransExp, Flapjack.WordAlloc.wordStateEqRel, permuted, expr]

end Flapjack.Compiler.Backend.WordAlloc
