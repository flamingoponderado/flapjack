import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSASemanticRegisterWrites
import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSALocalsGetVar

namespace Flapjack.Compiler.Backend.WordAlloc

namespace SemanticStateWriteWitnesses

/-- Canonical imported native WordSem finite-map roundtrip. -/
theorem holFmapAsFiniteSupportRelationWitness_WordSemStateFiniteExact
    {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : WordSemStateBroad width C F) (h : state.FiniteSupport),
      (WordSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : WordSemStateFiniteExact width C F,
      WordSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  WordSemStateExact.holFmapAsFiniteSupportWitness

end SemanticStateWriteWitnesses

/-- Full original native SSA Set case, all six original premises and
complete source-permutation existential/result/frame/locals conclusion.
Every source failure and success branch is derived; no source-success,
target-execution or post-state premise. The full evaluator inherits
reals_as_rational_cuts (SOUNDNESS item 8). -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem ssaCcTransCorrectSet {width : Nat} [NeZero width] {C F : Type}
    (source target : WordSemStateFiniteExact width C F)
    (ssa : Spt Nat) (next : Nat) (name : WordStoreHOL) (expr : WordLangExpHOL (BitVec width))
    (tables : List (Spt Nat × Spt Unit × Spt Unit))
    (h : Flapjack.WordAlloc.wordStateEqRel source target ∧
      ssaLocalsRel next ssa source.locals target.locals ∧ isAllocVar next ∧
      everyVarHOL (fun x => decide (x < next)) (.set name expr : WordLangProgHOL (BitVec width)) = true ∧
      ssaMapOK next ssa ∧ ltOK tables) :
    ssaSimulation (.set name expr : WordLangProgHOL (BitVec width)) source target ssa next tables := by
  let permuted := {source with permute := target.permute}
  have frame : Flapjack.WordAlloc.wordStateEqRel permuted target := by
    simpa [permuted, Flapjack.WordAlloc.wordStateEqRel] using h.1
  refine ⟨target.permute, ?_⟩
  by_cases forbidden : name = .handler ∨ name = .bitmapBase
  · simp [WordSemStateFiniteExact.evaluate, forbidden]
  · cases found : WordSemStateFiniteExact.wordExp permuted expr with
    | none =>
      have absent : WordSemStateFiniteExact.wordExp {source with permute := target.permute} expr = none := found
      simp [WordSemStateFiniteExact.evaluate, absent, forbidden]
    | some value =>
      have targetEval := ssaCcTransExpCorrect permuted expr target ssa next value
        ⟨found, frame, h.2.1⟩
      simp_all [WordSemStateFiniteExact.evaluate, ssaCcTrans,
        WordSemStateFiniteExact.setStore, Flapjack.WordAlloc.wordStateEqRel, permuted]

/-- Full original native SSA Store case, all six original premises and
complete source-permutation existential/result/frame/locals conclusion.
Every source failure and success branch is derived; no source-success,
target-execution or post-state premise. The full evaluator inherits
reals_as_rational_cuts (SOUNDNESS item 8). -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem ssaCcTransCorrectStore {width : Nat} [NeZero width] {C F : Type}
    (source target : WordSemStateFiniteExact width C F)
    (ssa : Spt Nat) (next : Nat) (name : Nat) (expr : WordLangExpHOL (BitVec width))
    (tables : List (Spt Nat × Spt Unit × Spt Unit))
    (h : Flapjack.WordAlloc.wordStateEqRel source target ∧
      ssaLocalsRel next ssa source.locals target.locals ∧ isAllocVar next ∧
      everyVarHOL (fun x => decide (x < next)) (.store expr name : WordLangProgHOL (BitVec width)) = true ∧
      ssaMapOK next ssa ∧ ltOK tables) :
    ssaSimulation (.store expr name : WordLangProgHOL (BitVec width)) source target ssa next tables := by
  let permuted := {source with permute := target.permute}
  have frame : Flapjack.WordAlloc.wordStateEqRel permuted target := by
    simpa [permuted, Flapjack.WordAlloc.wordStateEqRel] using h.1
  refine ⟨target.permute, ?_⟩
  cases found : WordSemStateFiniteExact.wordExp permuted expr with
  | none =>
    have absent : WordSemStateFiniteExact.wordExp {source with permute := target.permute} expr = none := found
    simp [WordSemStateFiniteExact.evaluate, absent]
  | some address =>
    cases address with
    | loc label offset =>
      have nonword : WordSemStateFiniteExact.wordExp {source with permute := target.permute} expr = some (.loc label offset) := found
      simp [WordSemStateFiniteExact.evaluate, nonword]
    | word address =>
      cases valueFound : WordSemStateFiniteExact.getVar name permuted with
      | none =>
        have absent : WordSemStateFiniteExact.getVar name {source with permute := target.permute} = none := valueFound
        have exprFound : WordSemStateFiniteExact.wordExp {source with permute := target.permute} expr = some (.word address) := found
        simp [WordSemStateFiniteExact.evaluate, absent, exprFound]
      | some value =>
        have targetExpr := ssaCcTransExpCorrect permuted expr target ssa next (.word address)
          ⟨found, frame, h.2.1⟩
        have targetValue := ssaLocalsRelGetVar next ssa permuted target name value
          ⟨h.2.1, valueFound⟩
        by_cases domain : source.mdomain address
        · simp_all [WordSemStateFiniteExact.evaluate, ssaCcTrans,
            WordSemStateFiniteExact.memStore, WordSemStateFiniteExact.getVar,
            Flapjack.WordAlloc.wordStateEqRel, permuted]
        · simp_all [WordSemStateFiniteExact.evaluate,
            WordSemStateFiniteExact.memStore, WordSemStateFiniteExact.getVar,
            Flapjack.WordAlloc.wordStateEqRel, permuted]

end Flapjack.Compiler.Backend.WordAlloc
