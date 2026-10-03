import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSASemanticRegisterWrites
import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSALocalsGetVar

namespace Flapjack.Compiler.Backend.WordAlloc

namespace SemanticInstStore32Witnesses

/-- Canonical imported native WordSem finite-map roundtrip. -/
theorem holFmapAsFiniteSupportRelationWitness_WordSemStateFiniteExact
    {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : WordSemStateBroad width C F) (h : state.FiniteSupport),
      (WordSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : WordSemStateFiniteExact width C F,
      WordSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  WordSemStateExact.holFmapAsFiniteSupportWitness

end SemanticInstStore32Witnesses

/-- Full original native Store32 opcode simulation with all six premises
and complete Error-exempt source-permutation conclusion. Address and word data
reads transport through the original SSA relation. Original frame equality
establishes the same native 32-bit-store memory/domain/endianness result; HOL
word-to-32-bit conversion is retained. The actual updated-memory frame and
unchanged locals are proved, without target-run, source-success or post-state
premises. Address/data-type/read/32-bit-store errors retain the source exemption.
The Inst/evaluator boundary inherits reals_as_rational_cuts (SOUNDNESS item 8). -/
@[hol "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "ssa_cc_trans_correct"
  (fmap_as_finite_support_relation := [WordSemStateFiniteExact.fpRegs,
    WordSemStateFiniteExact.store]) (words_as_type_indexed_bitvec)]
theorem ssaCcTransCorrectInstStore32 {width : Nat} [NeZero width] {C F : Type}
    (source target : WordSemStateFiniteExact width C F)
    (ssa : Spt Nat) (next data base : Nat) (offset : BitVec width)
    (tables : List (Spt Nat × Spt Unit × Spt Unit))
    (h : Flapjack.WordAlloc.wordStateEqRel source target ∧
      ssaLocalsRel next ssa source.locals target.locals ∧ isAllocVar next ∧
      everyVarHOL (fun x => decide (x < next)) (.inst (.mem .store32 data (.addr base offset))) = true ∧
      ssaMapOK next ssa ∧ ltOK tables) :
    ssaSimulation (.inst (.mem .store32 data (.addr base offset))) source target ssa next tables := by
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
        cases value with
        | loc label off =>
          have sourceExpr : WordSemStateFiniteExact.wordExp {source with permute := target.permute}
              (.op .add [.var base, .const offset]) = some (.word word) := found
          have wrong : WordSemStateFiniteExact.getVar data {source with permute := target.permute} = some (.loc label off) := read
          simp [WordSemStateFiniteExact.evaluate, WordSemStateFiniteExact.inst, sourceExpr, wrong]
        | word valueWord =>
          have targetRead := ssaLocalsRelGetVar next ssa permuted target data (.word valueWord) ⟨h.2.1, read⟩
          have sameStore : memStore32Exact target.memory target.mdomain target.be word (valueWord.setWidth 32) =
              memStore32Exact permuted.memory permuted.mdomain permuted.be word (valueWord.setWidth 32) := by
            simp_all [Flapjack.WordAlloc.wordStateEqRel]
          cases stored : memStore32Exact permuted.memory permuted.mdomain permuted.be word (valueWord.setWidth 32) <;>
            simp_all [WordSemStateFiniteExact.evaluate, WordSemStateFiniteExact.inst,
              ssaCcTrans, ssaCcTransInst, Flapjack.WordAlloc.wordStateEqRel,
              ssaCcTransExp, permuted, expr]

end Flapjack.Compiler.Backend.WordAlloc
