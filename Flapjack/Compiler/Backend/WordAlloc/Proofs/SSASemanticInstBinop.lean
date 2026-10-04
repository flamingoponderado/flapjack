import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSASemanticRegisterWrites

namespace Flapjack.Compiler.Backend.WordAlloc

namespace SemanticInstBinopWitnesses

/-- Canonical imported native WordSem finite-map roundtrip. -/
theorem holFmapAsFiniteSupportRelationWitness_WordSemStateFiniteExact
    {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : WordSemStateBroad width C F) (h : state.FiniteSupport),
      (WordSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : WordSemStateFiniteExact width C F,
      WordSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  WordSemStateExact.holFmapAsFiniteSupportWitness

end SemanticInstBinopWitnesses

/-- Genuine full Binop opcode case of the original native SSA Inst semantic
case, including register and immediate operands. All six original premises
and the complete Error-exempt source-permutation/result/frame/result-sensitive
locals conclusion are retained. Source expression errors preserve the original
exemption; successful target expressions and fresh destination locals are
proved using the original expression/setVar helpers. The literal compiler reads
operands from the original SSA map before extending it. No target evaluation,
success, post-state relation, or induction hypothesis is assumed. The native
Inst/evaluator boundary inherits reals_as_rational_cuts (SOUNDNESS item 8). -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem ssaCcTransCorrectInstBinop {width : Nat} [NeZero width] {C F : Type}
    (source target : WordSemStateFiniteExact width C F)
    (ssa : Spt Nat) (next dst src : Nat) (operator : BinOp)
    (immediate : WordRegImm (BitVec width))
    (tables : List (Spt Nat × Spt Unit × Spt Unit))
    (h : Flapjack.WordAlloc.wordStateEqRel source target ∧
      ssaLocalsRel next ssa source.locals target.locals ∧ isAllocVar next ∧
      everyVarHOL (fun x => decide (x < next)) (.inst (.arith (.binop operator dst src immediate))) = true ∧
      ssaMapOK next ssa ∧ ltOK tables) :
    ssaSimulation (.inst (.arith (.binop operator dst src immediate))) source target ssa next tables := by
  have bound : dst < next := by
    have occurrences := h.2.2.2.1
    simp only [everyVarHOL, everyVarInstHOL, Bool.and_eq_true] at occurrences
    exact of_decide_eq_true occurrences.1.1
  let permuted := {source with permute := target.permute}
  have frame : Flapjack.WordAlloc.wordStateEqRel permuted target := by
    simpa [permuted, Flapjack.WordAlloc.wordStateEqRel] using h.1
  cases immediate with
  | reg right =>
    let expr : WordLangExpHOL (BitVec width) := .op operator [.var src, .var right]
    refine ⟨target.permute, ?_⟩
    cases found : WordSemStateFiniteExact.wordExp permuted expr with
    | none =>
      have absent : WordSemStateFiniteExact.wordExp {source with permute := target.permute}
          (.op operator [.var src, .var right]) = none := found
      simp [WordSemStateFiniteExact.evaluate, WordSemStateFiniteExact.inst,
        WordSemStateFiniteExact.assign, absent]
    | some value =>
      have targetEval := ssaCcTransExpCorrect permuted expr target ssa next value ⟨found, frame, h.2.1⟩
      have locals := ssaLocalsRelSetVar next ssa source.locals target.locals dst value
        ⟨h.2.1, h.2.2.2.2.1, bound⟩
      simp_all [WordSemStateFiniteExact.evaluate, WordSemStateFiniteExact.inst,
        WordSemStateFiniteExact.assign, WordSemStateFiniteExact.setVar,
        ssaCcTrans, ssaCcTransInst, nextVarRename, ssaCcTransExp,
        Flapjack.WordAlloc.wordStateEqRel, permuted, expr]
  | imm word =>
    let expr : WordLangExpHOL (BitVec width) := .op operator [.var src, .const word]
    refine ⟨target.permute, ?_⟩
    cases found : WordSemStateFiniteExact.wordExp permuted expr with
    | none =>
      have absent : WordSemStateFiniteExact.wordExp {source with permute := target.permute}
          (.op operator [.var src, .const word]) = none := found
      simp [WordSemStateFiniteExact.evaluate, WordSemStateFiniteExact.inst,
        WordSemStateFiniteExact.assign, absent]
    | some value =>
      have targetEval := ssaCcTransExpCorrect permuted expr target ssa next value ⟨found, frame, h.2.1⟩
      have locals := ssaLocalsRelSetVar next ssa source.locals target.locals dst value
        ⟨h.2.1, h.2.2.2.2.1, bound⟩
      simp_all [WordSemStateFiniteExact.evaluate, WordSemStateFiniteExact.inst,
        WordSemStateFiniteExact.assign, WordSemStateFiniteExact.setVar,
        ssaCcTrans, ssaCcTransInst, nextVarRename, ssaCcTransExp,
        Flapjack.WordAlloc.wordStateEqRel, permuted, expr]

end Flapjack.Compiler.Backend.WordAlloc
