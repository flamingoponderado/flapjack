import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSASemanticControl
import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSALocalsInsert
import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSAExpressions

namespace Flapjack.Compiler.Backend.WordAlloc

namespace SemanticHeapWitnesses

/-- Canonical imported native WordSem finite-map roundtrip. -/
theorem holFmapAsFiniteSupportRelationWitness_WordSemStateFiniteExact
    {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : WordSemStateBroad width C F) (h : state.FiniteSupport),
      (WordSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : WordSemStateFiniteExact width C F,
      WordSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  WordSemStateExact.holFmapAsFiniteSupportWitness

end SemanticHeapWitnesses

/-- Full original native OpCurrHeap semantic case, with the six original
premises and complete Error-exempt source-permutation/result/frame/locals
conclusion. Actual word-expression success transport and fresh destination
locals preservation are derived internally. No desired target run or extra
success/post-state premise is assumed. The total evaluator inherits
reals_as_rational_cuts (SOUNDNESS item 8). -/
@[hol "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "ssa_cc_trans_correct"
  (fmap_as_finite_support_relation := [WordSemStateFiniteExact.fpRegs,
    WordSemStateFiniteExact.store]) (words_as_type_indexed_bitvec)]
theorem ssaCcTransCorrectOpCurrHeap {width : Nat} [NeZero width] {C F : Type}
    (source target : WordSemStateFiniteExact width C F)
    (ssa : Spt Nat) (next name : Nat) (operator : BinOp) (src : Nat)
    (tables : List (Spt Nat × Spt Unit × Spt Unit))
    (h : Flapjack.WordAlloc.wordStateEqRel source target ∧
      ssaLocalsRel next ssa source.locals target.locals ∧ isAllocVar next ∧
      everyVarHOL (fun x => decide (x < next)) (.opCurrHeap operator name src : WordLangProgHOL (BitVec width)) = true ∧
      ssaMapOK next ssa ∧ ltOK tables) :
    ssaSimulation (.opCurrHeap operator name src : WordLangProgHOL (BitVec width)) source target ssa next tables := by
  have bound : name < next := by
    have both : decide (name < next) = true ∧ decide (src < next) = true := by
      simpa [everyVarHOL] using h.2.2.2.1
    exact of_decide_eq_true both.1
  let expr : WordLangExpHOL (BitVec width) := .op operator [.var src, .lookup .currHeap]
  let permuted := {source with permute := target.permute}
  have frame : Flapjack.WordAlloc.wordStateEqRel permuted target := by
    simpa [permuted, Flapjack.WordAlloc.wordStateEqRel] using h.1
  refine ⟨target.permute, ?_⟩
  cases found : WordSemStateFiniteExact.wordExp permuted expr with
  | none =>
    have absent : WordSemStateFiniteExact.wordExp {source with permute := target.permute} expr = none := found
    simp only [expr] at absent
    simp [WordSemStateFiniteExact.evaluate, absent]
  | some value =>
    have targetEval := ssaCcTransExpCorrect permuted expr target ssa next value
      ⟨found, frame, h.2.1⟩
    have locals := ssaLocalsRelSetVar next ssa source.locals target.locals name value
      ⟨h.2.1, h.2.2.2.2.1, bound⟩
    simp_all [WordSemStateFiniteExact.evaluate, ssaCcTrans, nextVarRename,
      WordSemStateFiniteExact.setVar, Flapjack.WordAlloc.wordStateEqRel, permuted, expr, ssaCcTransExp]


end Flapjack.Compiler.Backend.WordAlloc
