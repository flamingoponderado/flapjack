import Flapjack.Compiler.Backend.Semantics.WordSem.State
import Flapjack.Compiler.Backend.Semantics.StackSem.State
import Flapjack.Misc.GoodDimindex

namespace Flapjack.WordToStackProofs.CompCorrect

/-- Full original result translation. Every native source constructor is mapped
in original order, including NotEnoughSpace to target Halt (Word 1w). -/
@[hol "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "compile_result_def"
  (words_as_type_indexed_bitvec)]
def compileResult {width : Nat} [NeZero width] : WordSemResult width → StackSemResult width
  | .result value _ => .result value
  | .exception value _ => .exception value
  | .timeOut => .timeOut
  | .notEnoughSpace => .halt (.word 1)
  | .finalFfi event => .finalFFI event
  | .break label => .break label
  | .continue label => .continue label
  | .error => .error

/-- Full original two-part Halt characterization. The 1w equivalence is
unconditional; only the 2w exclusion carries the original good_dimindex guard. -/
@[hol "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "Halt_EQ_compile_result"
  (words_as_type_indexed_bitvec)]
theorem haltEqCompileResult {width : Nat} [NeZero width] (result : WordSemResult width) :
    ((StackSemResult.halt (.word (1 : BitVec width)) = compileResult result) ↔
      result = .notEnoughSpace) ∧
    (goodDimindex width → StackSemResult.halt (.word (2 : BitVec width)) ≠ compileResult result) := by
  constructor
  · cases result <;> simp [compileResult]
  · intro dimension
    rcases dimension with dimension | dimension <;> subst width <;>
      cases result <;> simp [compileResult, BitVec.ofNat_eq_ofNat]

/-- Genuine canonical source-state codec re-export, qualifier infrastructure
with no separate HOL declaration. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : WordSemStateBroad width C F) (h : state.FiniteSupport),
      (WordSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : WordSemStateFiniteExact width C F,
      WordSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  WordSemStateExact.holFmapAsFiniteSupportWitness

/-- Full original exception-unwinding local-frame constructor. Empty locals,
SOME 0 size and the frame holding the old size/both cutsets/absent handler are
updated together; every other actual native state field is unchanged. -/
@[hol "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "push_locals_def"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
def pushLocals {width : Nat} [NeZero width] {C F : Type}
    (nonGc gc : List (Nat × WordLocW width)) (source : WordSemStateFiniteExact width C F) :
    WordSemStateFiniteExact width C F :=
  { source with
      locals := .ln
      localsSize := some 0
      stack := .stackFrame source.localsSize nonGc gc none :: source.stack }

end Flapjack.WordToStackProofs.CompCorrect
