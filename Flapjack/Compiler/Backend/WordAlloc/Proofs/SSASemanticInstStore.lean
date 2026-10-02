import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSASemanticRegisterWrites
import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSALocalsGetVar

namespace Flapjack.Compiler.Backend.WordAlloc

namespace SemanticInstStoreWitnesses

/-- Canonical imported native WordSem finite-map roundtrip. -/
theorem holFmapAsFiniteSupportRelationWitness_WordSemStateFiniteExact
    {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : WordSemStateBroad width C F) (h : state.FiniteSupport),
      (WordSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : WordSemStateFiniteExact width C F,
      WordSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  WordSemStateExact.holFmapAsFiniteSupportWitness

end SemanticInstStoreWitnesses

/-- Full original native Store opcode simulation with all six premises
and complete Error-exempt source-permutation conclusion. Address expression
and arbitrary WordLoc data reads transport through the original SSA relation.
Actual memory-domain branches and memory update preserve the original frame;
locals and the SSA map are unchanged. Expression/type/read/domain failures
retain the source Error exemption. No target-run, source-success or post-state
premise is assumed. The Inst/evaluator boundary inherits
reals_as_rational_cuts (SOUNDNESS item 8). -/
@[hol "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "ssa_cc_trans_correct"
  (fmap_as_finite_support_relation := [WordSemStateFiniteExact.fpRegs,
    WordSemStateFiniteExact.store]) (words_as_type_indexed_bitvec)]
theorem ssaCcTransCorrectInstStore {width : Nat} [NeZero width] {C F : Type}
    (source target : WordSemStateFiniteExact width C F)
    (ssa : Spt Nat) (next data base : Nat) (offset : BitVec width)
    (tables : List (Spt Nat × Spt Unit × Spt Unit))
    (h : Flapjack.WordAlloc.wordStateEqRel source target ∧
      ssaLocalsRel next ssa source.locals target.locals ∧ isAllocVar next ∧
      everyVarHOL (fun x => decide (x < next)) (.inst (.mem .store data (.addr base offset))) = true ∧
      ssaMapOK next ssa ∧ ltOK tables) :
    ssaSimulation (.inst (.mem .store data (.addr base offset))) source target ssa next tables := by
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
      cases read : WordSemStateFiniteExact.getVar data permuted with
      | none =>
        have sourceExpr : WordSemStateFiniteExact.wordExp {source with permute := target.permute}
            (.op .add [.var base, .const offset]) = some (.word word) := found
        have absent : WordSemStateFiniteExact.getVar data {source with permute := target.permute} = none := read
        simp [WordSemStateFiniteExact.evaluate, WordSemStateFiniteExact.inst, sourceExpr, absent]
      | some value =>
        have targetRead := ssaLocalsRelGetVar next ssa permuted target data value ⟨h.2.1, read⟩
        cases domain : permuted.mdomain word <;>
          simp_all [WordSemStateFiniteExact.evaluate, WordSemStateFiniteExact.inst,
            WordSemStateFiniteExact.memStore, ssaCcTrans, ssaCcTransInst,
            Flapjack.WordAlloc.wordStateEqRel, ssaCcTransExp, permuted, expr]

end Flapjack.Compiler.Backend.WordAlloc
