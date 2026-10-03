import Flapjack.RiscV.WordFuseConditions
import Flapjack.Compiler.Backend.WordToStack.ProductionConstantDomain
import Flapjack.Compiler.Backend.WordToStack.ProductionSelectorDomain
import Flapjack.RiscV.PipelineDiagnostics
import Flapjack.Pancake.LoopToWord.CompFuncCodecDomain

namespace Flapjack
open RiscV WordProgCarrierCodec

/-! Source audit: `word_simpScript.sml:393–499` has the same bounded search
and recursive Seq/If/Loop/MustTerminate/optional Call structure used here.
Successful candidates run `const_fp`; Seq candidates retain their prefix;
the hoister's terminating-Seq branch retains the untouched second program.
The proofs follow those actual production clauses and cover those retained
subprograms. `compile_exp` first reassociates, which production `wordConstFp`
already does. These lemmas concern the production carrier's partial codec,
which has no HOL declaration, and therefore deliberately carry no HOL tag. -/

/-- Structural carrier closure for the actual terminating-branch hoister.
The input acceptance premise excludes unsupported production instructions;
no output acceptance or successful compilation is assumed. This is
Flapjack-only codec infrastructure, not a HOL semantics theorem. -/
theorem supportsCodec_wordPushOutIfAux {α : Type u} (program : WordProg α)
    (accepted : supportsCodec program = true) :
    supportsCodec (wordPushOutIfAux program).1 = true := by
  fun_induction wordPushOutIfAux program
  all_goals try dsimp +zetaDelta only at *
  all_goals simp_all [supportsCodec]

/-- Acceptance of the public production hoisting wrapper, including unchanged
optional Call bodies. No cross-language semantic equivalence is asserted. -/
theorem supportsCodec_wordPushOutIf {α : Type u} (program : WordProg α)
    (accepted : supportsCodec program = true) :
    supportsCodec (wordPushOutIf program) = true :=
  supportsCodec_wordPushOutIfAux program accepted

section DuplicateIf
private theorem smartSeqDomain {α : Type u} (first second : WordProg α) :
    supportsCodec (wordSimpSmartSeq first second) =
      (supportsCodec first && supportsCodec second) := by
  unfold wordSimpSmartSeq
  split <;> simp_all [supportsCodec]

private theorem assocAccDomain {α : Type u} (before program : WordProg α)
    (beforeAccepted : supportsCodec before = true)
    (accepted : supportsCodec program = true) :
    supportsCodec (wordSimpSeqAssocAcc before program) = true := by
  fun_induction wordApplyColour (fun name => name) program generalizing before
  all_goals simp_all [wordSimpSeqAssocAcc, supportsCodec, smartSeqDomain]

private theorem assocDomain {α : Type u} (program : WordProg α)
    (accepted : supportsCodec program = true) :
    supportsCodec (wordSimpSeqAssoc program) = true :=
  assocAccDomain .skip program (by simp [supportsCodec]) accepted

variable {α : Type} [Add α] [Sub α] [AndOp α] [OrOp α]
    [HXor α α α] [Complement α] [OfNat α 1] [OfNat α 0] [DecidableEq α]
    [PanCmp α] [WordSimpShift α] [BEq α]

omit [BEq α] in
private theorem hoistConstDomain (program : WordProg α)
    (accepted : supportsCodec program = true) :
    supportsCodec (wordHoistConstFp program) = true :=
  supportsCodec_wordConstFpLoop program [] accepted

private theorem candidateDomain (operator : Cmp) (condition : Nat)
    (right : WordRegImm α) (dummy thenBranch elseBranch intermediate continuation result : WordProg α)
    (thenAccepted : supportsCodec thenBranch = true)
    (elseAccepted : supportsCodec elseBranch = true)
    (intermediateAccepted : supportsCodec intermediate = true)
    (continuationAccepted : supportsCodec continuation = true)
    (equation : wordHoistIfCandidate operator condition right dummy thenBranch
      elseBranch intermediate continuation = some result) :
    supportsCodec result = true := by
  unfold wordHoistIfCandidate at equation
  dsimp only at equation
  split at equation <;> try simp_all
  obtain ⟨_, equation⟩ := equation
  subst result
  apply hoistConstDomain
  simp [supportsCodec, thenAccepted, elseAccepted, intermediateAccepted, continuationAccepted]

private theorem tryHoistDomain (fuel : Nat)
    (program intermediate dummy continuation result : WordProg α)
    (accepted : supportsCodec program = true)
    (intermediateAccepted : supportsCodec intermediate = true)
    (continuationAccepted : supportsCodec continuation = true)
    (equation : wordTryIfHoist2 fuel program intermediate dummy continuation = some result) :
    supportsCodec result = true := by
  fun_induction wordTryIfHoist2 fuel program intermediate dummy continuation generalizing result
  all_goals simp_all [supportsCodec]
  case case2 =>
    apply candidateDomain (equation := equation)
    · exact accepted.1
    · exact accepted.2
    · exact intermediateAccepted
    · exact continuationAccepted
  case case3 =>
    subst result
    simp only [supportsCodec, Bool.and_eq_true]
    constructor
    · exact accepted.1
    · apply candidateDomain (equation := by assumption)
      · exact accepted.2.1
      · exact accepted.2.2
      · exact intermediateAccepted
      · exact continuationAccepted

private theorem tryHoistOneDomain (first second result : WordProg α)
    (left : supportsCodec first = true) (right : supportsCodec second = true)
    (equation : wordTryIfHoist1 first second = some result) :
    supportsCodec result = true := by
  unfold wordTryIfHoist1 at equation
  split at equation <;> try simp_all
  apply tryHoistDomain (equation := equation)
  · exact left
  · simp [supportsCodec]
  · simp_all [supportsCodec]

/-- Closure of the actual recursive duplicate-if pass, including both optional
Call bodies and the real bounded hoist search. Unsupported source instructions
are excluded by input codec acceptance alone. Flapjack-only infrastructure;
this does not assert HOL pass semantics or executed native routing. -/
theorem supportsCodec_wordSimpDuplicateIf (program : WordProg α)
    (accepted : supportsCodec program = true) :
    supportsCodec (wordSimpDuplicateIf program) = true := by
  fun_induction wordApplyColour (fun name => name) program
  all_goals simp_all [supportsCodec, wordSimpDuplicateIf]
  all_goals split <;> try simp_all [supportsCodec]
  all_goals apply assocDomain
  all_goals apply tryHoistOneDomain (equation := by assumption)
  all_goals assumption

end DuplicateIf

/-- Closure of actual pre-SSA preparation, in its executed order: constant
propagation, duplicate-if simplification, then branch hoisting. This is a
codec-domain result, not a pass simulation theorem. -/
theorem supportsCodec_wordToWordPreSsa {α : Type}
    [Add α] [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [Complement α] [OfNat α 1] [OfNat α 0] [DecidableEq α]
    [PanCmp α] [WordSimpShift α]
    (program : WordProg α) (accepted : supportsCodec program = true) :
    supportsCodec (wordToWordPreSsa program) = true :=
  supportsCodec_wordPushOutIf _
    (supportsCodec_wordSimpDuplicateIf _ (supportsCodec_wordConstFp _ accepted))

/-- The shared preparation actually supplied to full SSA accepts every input
accepted by the native codec. Covers arbitrary positive widths and whole
programs, without an output-codec or allocation-success premise. The identity
flatten wrapper and actual selector are composed, not duplicated. This is
Flapjack carrier infrastructure; native caller replacement remains separate. -/
theorem wordLangProgToHOL_wordBeforeSsaAllocatorBody_isSome
    {width : Nat} [NeZero width] (program : WordProg (BitVec width))
    (accepted : (wordLangProgToHOL program).isSome = true) :
    (wordLangProgToHOL (wordBeforeSsaAllocatorBody program)).isSome = true := by
  unfold wordBeforeSsaAllocatorBody
  rw [wordLangProgToHOL_wordInstSelectProgramFrom_isSome]
  rw [codecDomain] at accepted ⊢
  exact supportsCodec_wordToWordPreSsa program accepted

/-- Every actual routed source function reaches the native codec at the real
allocator boundary without any input-codec premise. This combines the full
source-output closure with preservation by the executed preparation stages.
It proves carrier acceptance only, not native limit wiring or HOL simulation. -/
theorem wordLangProgToHOL_sourceAllocatorInput_isSome
    {width : Nat} [NeZero width] (name : Nat) (parameters : List Nat)
    (body : LoopProg (BitVec width)) :
    (wordLangProgToHOL (wordBeforeSsaAllocatorBody
      (loopToWordCompFuncRouted name parameters body))).isSome = true :=
  wordLangProgToHOL_wordBeforeSsaAllocatorBody_isSome _
    (wordLangProgToHOL_loopToWordCompFuncRouted_isSome name parameters body)

/-- The executed allocation boundary uses native full-program limit for every
routed source function. There is no caller-supplied codec or successful
allocation premise: source closure discharges the native branch condition.
This establishes routing, not allocation/evaluation correctness. -/
theorem sourceAllocatorInput_usesNativeLimit
    {width : Nat} [NeZero width] (name : Nat) (parameters : List Nat)
    (body : LoopProg (BitVec width)) (wordParameters : List Nat) :
    CakeRegAlloc.cakeAllocateWordFunctionAfterDeadRoutedLimit name wordParameters
        (wordBeforeSsaAllocatorBody (loopToWordCompFuncRouted name parameters body)) =
      CakeRegAlloc.cakeAllocateWordFunctionAfterDeadNativeLimit name wordParameters
        (wordBeforeSsaAllocatorBody (loopToWordCompFuncRouted name parameters body)) :=
  CakeRegAlloc.cakeAllocateWordFunctionAfterDeadRoutedLimit_native _ _ _
    (wordLangProgToHOL_sourceAllocatorInput_isSome name parameters body)

/-- Every actual routed source input uses native full SSA, with its input
condition discharged by source compiler closure. This is routing infrastructure,
not allocation/evaluation correctness. -/
theorem sourceAllocatorInput_usesNativeSSA
    {width : Nat} [NeZero width] (name : Nat) (parameters : List Nat)
    (body : LoopProg (BitVec width)) (wordParameters : List Nat) :
    CakeRegAlloc.cakeAllocateWordFunctionAfterDeadRoutedSSA name wordParameters
        (wordBeforeSsaAllocatorBody (loopToWordCompFuncRouted name parameters body)) =
      CakeRegAlloc.cakeAllocateWordFunctionAfterDeadNativeSSA name wordParameters
        (wordBeforeSsaAllocatorBody (loopToWordCompFuncRouted name parameters body)) :=
  CakeRegAlloc.cakeAllocateWordFunctionAfterDeadRoutedSSA_native _ _ _
    (wordLangProgToHOL_sourceAllocatorInput_isSome name parameters body)


/-- The exact Loop-to-Word function used by PipelineDiagnostics reaches the
native input codec after executed pre-SSA preparation. Unlike the routed-source
variants above, this equation names LoopToWord.loopToWordCompFunc itself.
No successful compilation, encoding or allocation premise is supplied.
Arbitrary externally supplied Word bodies retain the codec rejection boundary;
this theorem asserts source provenance, not universal Word codec acceptance. -/
theorem executedSourceAllocatorInput_isSome
    {width : Nat} [NeZero width] (name : Nat) (parameters : List Nat)
    (body : LoopProg (BitVec width)) :
    (wordLangProgToHOL (wordBeforeSsaAllocatorBody
      (LoopToWord.loopToWordCompFunc name parameters body))).isSome = true :=
  wordLangProgToHOL_wordBeforeSsaAllocatorBody_isSome _
    (wordLangProgToHOL_loopToWordCompFunc_isSome name parameters body)

/-- Native full-program limit routing for the actual compatibility function
body consumed by production diagnostics. This is routing infrastructure,
without an independent HOL theorem, and makes no evaluation-correctness claim. -/
theorem executedSourceAllocatorInput_usesNativeLimit
    {width : Nat} [NeZero width] (name : Nat) (parameters : List Nat)
    (body : LoopProg (BitVec width)) (wordParameters : List Nat) :
    CakeRegAlloc.cakeAllocateWordFunctionAfterDeadRoutedLimit name wordParameters
        (wordBeforeSsaAllocatorBody (LoopToWord.loopToWordCompFunc name parameters body)) =
      CakeRegAlloc.cakeAllocateWordFunctionAfterDeadNativeLimit name wordParameters
        (wordBeforeSsaAllocatorBody (LoopToWord.loopToWordCompFunc name parameters body)) :=
  CakeRegAlloc.cakeAllocateWordFunctionAfterDeadRoutedLimit_native _ _ _
    (executedSourceAllocatorInput_isSome name parameters body)

/-- The exact source function input at the actual allocator caller executes
native SSA. Its input condition is proved from source syntax, not assumed;
allocation may still fail. Arbitrary Word extensions remain governed by
cakeAllocateWordFunctionAfterDeadRoutedSSA_rejected. Flapjack infrastructure. -/
theorem executedSourceAllocatorInput_usesNativeSSA
    {width : Nat} [NeZero width] (name : Nat) (parameters : List Nat)
    (body : LoopProg (BitVec width)) (wordParameters : List Nat) :
    CakeRegAlloc.cakeAllocateWordFunctionAfterDeadRoutedSSA name wordParameters
        (wordBeforeSsaAllocatorBody (LoopToWord.loopToWordCompFunc name parameters body)) =
      CakeRegAlloc.cakeAllocateWordFunctionAfterDeadNativeSSA name wordParameters
        (wordBeforeSsaAllocatorBody (LoopToWord.loopToWordCompFunc name parameters body)) :=
  CakeRegAlloc.cakeAllocateWordFunctionAfterDeadRoutedSSA_native _ _ _
    (executedSourceAllocatorInput_isSome name parameters body)

end Flapjack
