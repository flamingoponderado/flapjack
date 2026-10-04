import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSALoopSemanticHelpers
import Flapjack.Compiler.Backend.WordAlloc.SSAFixInconsistencies

namespace Flapjack.Compiler.Backend.WordAlloc

namespace FakeConstChainWitnesses

/-- Canonical roundtrip of the imported native finite-map state carrier. -/
theorem holFmapAsFiniteSupportRelationWitness_WordSemStateFiniteExact
    {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : WordSemStateBroad width C F) (h : state.FiniteSupport),
      (WordSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : WordSemStateFiniteExact width C F,
      WordSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  WordSemStateExact.holFmapAsFiniteSupportWitness

end FakeConstChainWitnesses

/-- Original constant insertion commutation, retaining the word_loc payload. -/
@[hol "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "foldr_insert_const_swap"
  (words_as_type_indexed_bitvec)]
theorem foldrInsertConstSwap {width : Nat} [NeZero width]
    (names : List Nat) (name : Nat) (value : WordLocW width) (locals : Spt (WordLocW width)) :
    names.foldr (fun key tree => sptInsert key value tree) (sptInsert name value locals) =
      sptInsert name value (names.foldr (fun key tree => sptInsert key value tree) locals) := by
  induction names with
  | nil => rfl
  | cons key names ih =>
    simp only [List.foldr_cons,ih]
    by_cases equal : key = name
    · subst key
      rw [sptInsert_insert_shadow]
    · exact sptInsert_swap key name value value _ equal

/-- Full native evaluation of original fake constant chain, without distinctness,
register bounds or clock premises. Inherits evaluator reals_as_rational_cuts
(SOUNDNESS item 8). -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem evaluateFakeConstChain {width : Nat} [NeZero width] {C F : Type}
    (names : List Nat) (state : WordSemStateFiniteExact width C F) :
    WordSemStateFiniteExact.evaluate ((names.map (fakeMove (width := width))).foldr .seq .skip) state =
      (none,{state with locals := names.foldr (fun key locals => sptInsert key (.word 0) locals) state.locals}) := by
  induction names generalizing state with
  | nil => simp [WordSemStateFiniteExact.evaluate]
  | cons name names ih =>
    have first : WordSemStateFiniteExact.evaluate (fakeMove name) state =
        (none,WordSemStateFiniteExact.setVar name (.word 0) state) := by
      simp [fakeMove,WordSemStateFiniteExact.evaluate,WordSemStateFiniteExact.inst,
        WordSemStateFiniteExact.assign,WordSemStateFiniteExact.wordExp]
    simp only [List.map_cons,List.foldr_cons]
    rw [evaluateSeqCollapse _ _ _ _ first,ih]
    simp only [WordSemStateFiniteExact.setVar]
    rw [foldrInsertConstSwap]

-- Flapjack factoring of the common constant fold lookup, with no independent
-- HOL original. Duplicate registers are harmless because every payload agrees.
private theorem constFoldLookup {α : Type} (names : List Nat) (value : α)
    (locals : Spt α) (key : Nat) :
    sptLookup key (names.foldr (fun name tree => sptInsert name value tree) locals) =
      if key ∈ names then some value else sptLookup key locals := by
  induction names with
  | nil => simp
  | cons name names ih =>
    simp only [List.foldr_cons]
    by_cases equal : key = name
    · subst key
      simp [sptLookup_sptInsert_same]
    · rw [sptLookup_sptInsert_ne _ _ _ _ equal,ih]
      simp [equal]

/-- Full original fake-chain frame/domain/preserved outside reads/zero inside
reads result. No new membership, success or allocation hypotheses. Inherits
evaluator reals_as_rational_cuts (SOUNDNESS item 8). -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem evaluateFakeConstChainLocals {width : Nat} [NeZero width] {C F : Type}
    (names : List Nat) (state : WordSemStateFiniteExact width C F) :
    let after := (WordSemStateFiniteExact.evaluate
      ((names.map (fakeMove (width := width))).foldr .seq .skip) state).2
    Flapjack.WordAlloc.wordStateEqRel state after ∧
      sptDomain after.locals = (fun key => sptDomain state.locals key ∨ key ∈ names) ∧
      (∀ key, key ∉ names → sptLookup key after.locals = sptLookup key state.locals) ∧
      (∀ key, key ∈ names → sptLookup key after.locals = some (.word 0)) := by
  rw [evaluateFakeConstChain]
  dsimp only
  refine ⟨?_,?_,?_,?_⟩
  · simp [Flapjack.WordAlloc.wordStateEqRel]
  · funext key
    apply propext
    change sptMem key _ ↔ sptMem key state.locals ∨ key ∈ names
    rw [sptMem_iff_lookup]
    by_cases member : key ∈ names
    · simp [constFoldLookup,member]
    · simp only [constFoldLookup,member,if_false,or_false]
      exact (sptMem_iff_lookup key state.locals).symm
  · intro key member
    simp [constFoldLookup,member]
  · intro key member
    simp [constFoldLookup,member]

end Flapjack.Compiler.Backend.WordAlloc
