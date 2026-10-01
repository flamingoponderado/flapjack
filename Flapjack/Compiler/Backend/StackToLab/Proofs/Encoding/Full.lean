import Flapjack.Compiler.Backend.StackToLab.Proofs.Encoding.Nonrecursive
import Flapjack.Compiler.Backend.StackToLab.Proofs.Encoding.Recursive
namespace Flapjack.Compiler.Backend.StackToLab.Proofs
open Flapjack Flapjack.Compiler.Backend.StackToLab
open Flapjack.Compiler.Backend.StackLang Flapjack.Compiler.Backend.StackProps
open Flapjack.Compiler.Backend.LabSem Flapjack.Compiler.Backend.LabProps
open Flapjack.Compiler.Encoders.Asm

/-- Complete local HOL flatten validity theorem over the native carrier.
All subprogram induction hypotheses are discharged by well-founded recursion;
the public premises and EVERY conclusion are exactly the original statement. -/
@[hol "cakeml/compiler/backend/proofs/stack_to_labProofScript.sml" "flatten_line_ok_pre"
  (words_as_type_indexed_bitvec)]
theorem flattenLineOkPreHOL {width : Nat} [NeZero width]
    (tail : Bool) (program : HolProg width) (sectionId next : Nat)
    (conts breaks : List Nat) (lines : AppList (LabLineHOL width))
    (done : Bool) (nextAfter : Nat) (config : AsmConfigExact width)
    (zero : asmByteOffsetOkExact config 0 = true)
    (valid : stackAsmOkExact config program)
    (result : flattenHOL tail program sectionId next conts breaks =
      (lines, done, nextAfter)) :
    ∀ line ∈ appListAppend lines, lineOkPreHOL config line := by
  cases program with
  | inst instruction =>
    exact flattenLineOkPreInst tail instruction sectionId next conts breaks lines done nextAfter config zero valid result
  | raise register =>
    exact flattenLineOkPreRaise tail register sectionId next conts breaks lines done nextAfter config zero valid result
  | ret register =>
    exact flattenLineOkPreReturn tail register sectionId next conts breaks lines done nextAfter config zero valid result
  | codeBufferWrite left right =>
    exact flattenLineOkPreCodeBufferWrite tail left right sectionId next conts breaks lines done nextAfter config zero valid result
  | shMemOp operator register address =>
    exact flattenLineOkPreSharedMemory tail operator register address sectionId next conts breaks lines done nextAfter config zero valid result
  | tick =>
    exact flattenLineOkPreTick tail sectionId next conts breaks lines done nextAfter config zero valid result
  | halt register =>
    exact flattenLineOkPreHalt tail register sectionId next conts breaks lines done nextAfter config zero valid result
  | «break» index =>
    exact flattenLineOkPreBreak tail index sectionId next conts breaks lines done nextAfter config zero valid result
  | «continue» index =>
    exact flattenLineOkPreContinue tail index sectionId next conts breaks lines done nextAfter config zero valid result
  | rawCall target =>
    exact flattenLineOkPreRawCall tail target sectionId next conts breaks lines done nextAfter config zero valid result
  | jumpLower left right target =>
    exact flattenLineOkPreJumpLower tail left right target sectionId next conts breaks lines done nextAfter config zero valid result
  | ffi name a1 a2 a3 a4 link =>
    exact flattenLineOkPreFfi tail name a1 a2 a3 a4 link sectionId next conts breaks lines done nextAfter config zero valid result
  | locValue register label entry =>
    exact flattenLineOkPreLocValue tail register label entry sectionId next conts breaks lines done nextAfter config zero valid result
  | install a1 a2 a3 a4 link =>
    exact flattenLineOkPreInstall tail a1 a2 a3 a4 link sectionId next conts breaks lines done nextAfter config zero valid result
  | skip =>
    exact flattenLineOkPreSkip tail sectionId next conts breaks lines done nextAfter config zero valid result
  | get destination store =>
    exact flattenLineOkPreGet tail destination store sectionId next conts breaks lines done nextAfter config zero valid result
  | set store source =>
    exact flattenLineOkPreSet tail store source sectionId next conts breaks lines done nextAfter config zero valid result
  | opCurrHeap operator destination source =>
    exact flattenLineOkPreOpCurrHeap tail operator destination source sectionId next conts breaks lines done nextAfter config zero valid result
  | alloc words =>
    exact flattenLineOkPreAlloc tail words sectionId next conts breaks lines done nextAfter config zero valid result
  | storeConsts source bitmap stub =>
    exact flattenLineOkPreStoreConsts tail source bitmap stub sectionId next conts breaks lines done nextAfter config zero valid result
  | dataBufferWrite address value =>
    exact flattenLineOkPreDataBufferWrite tail address value sectionId next conts breaks lines done nextAfter config zero valid result
  | stackAlloc words =>
    exact flattenLineOkPreStackAlloc tail words sectionId next conts breaks lines done nextAfter config zero valid result
  | stackFree words =>
    exact flattenLineOkPreStackFree tail words sectionId next conts breaks lines done nextAfter config zero valid result
  | stackStore offset register =>
    exact flattenLineOkPreStackStore tail offset register sectionId next conts breaks lines done nextAfter config zero valid result
  | stackStoreAny register offsetRegister =>
    exact flattenLineOkPreStackStoreAny tail register offsetRegister sectionId next conts breaks lines done nextAfter config zero valid result
  | stackLoad offset register =>
    exact flattenLineOkPreStackLoad tail offset register sectionId next conts breaks lines done nextAfter config zero valid result
  | stackLoadAny register offsetRegister =>
    exact flattenLineOkPreStackLoadAny tail register offsetRegister sectionId next conts breaks lines done nextAfter config zero valid result
  | stackGetSize register =>
    exact flattenLineOkPreStackGetSize tail register sectionId next conts breaks lines done nextAfter config zero valid result
  | stackSetSize register =>
    exact flattenLineOkPreStackSetSize tail register sectionId next conts breaks lines done nextAfter config zero valid result
  | bitmapLoad destination address =>
    exact flattenLineOkPreBitmapLoad tail destination address sectionId next conts breaks lines done nextAfter config zero valid result
  | seq first second =>
    exact flattenLineOkPreSeq tail first second sectionId next conts breaks lines done nextAfter config zero valid result
      (fun t n m cs bs ls a b hz hv hr =>
      flattenLineOkPreHOL t first n m cs bs ls a b config hz hv hr)
      (fun t n m cs bs ls a b hz hv hr =>
      flattenLineOkPreHOL t second n m cs bs ls a b config hz hv hr)
  | ite operator condition right first second =>
    exact flattenLineOkPreIf tail operator condition right first second sectionId next conts breaks lines done nextAfter config zero valid result
      (fun t n m cs bs ls a b hz hv hr =>
      flattenLineOkPreHOL t first n m cs bs ls a b config hz hv hr)
      (fun t n m cs bs ls a b hz hv hr =>
      flattenLineOkPreHOL t second n m cs bs ls a b config hz hv hr)
  | loop body =>
    exact flattenLineOkPreLoop tail body sectionId next conts breaks lines done nextAfter config zero valid result
      (fun t n m cs bs ls a b hz hv hr =>
      flattenLineOkPreHOL t body n m cs bs ls a b config hz hv hr)
  | call returns target handler =>
    cases returns with
    | none =>
      exact flattenLineOkPreTailCall tail target handler sectionId next conts breaks lines done nextAfter config zero valid result
    | some ret =>
      rcases retEq : ret with ⟨body, link, returnSection, returnLabel⟩
      rw [retEq] at valid result
      cases handler with
      | none =>
        exact flattenLineOkPreReturnedCallNone tail body link returnSection returnLabel target
          sectionId next conts breaks lines done nextAfter config zero valid result
          (fun t n m cs bs ls a b hz hv hr =>
      flattenLineOkPreHOL t body n m cs bs ls a b config hz hv hr)
      | some h =>
        rcases handlerEq : h with ⟨handlerBody, handlerSection, handlerLabel⟩
        rw [handlerEq] at valid result
        exact flattenLineOkPreReturnedCallSome tail body link returnSection returnLabel target
          handlerBody handlerSection handlerLabel sectionId next conts breaks lines done nextAfter config zero valid result
          (fun t n m cs bs ls a b hz hv hr =>
      flattenLineOkPreHOL t body n m cs bs ls a b config hz hv hr)
          (fun t n m cs bs ls a b hz hv hr =>
      flattenLineOkPreHOL t handlerBody n m cs bs ls a b config hz hv hr)
termination_by sizeOf program
decreasing_by
  all_goals
    subst_vars
    decreasing_trivial

/-- Complete original compile_all_enc_ok_pre: source program validity and
zero byte-offset validity establish every emitted section's line precheck.
This precheck deliberately preserves HOL's acceptance of all LabAsm lines;
it is not the stronger all_enc_ok target-encoder theorem. -/
@[hol "cakeml/compiler/backend/proofs/stack_to_labProofScript.sml" "compile_all_enc_ok_pre"
  (words_as_type_indexed_bitvec)]
theorem compileAllEncOkPreHOL {width : Nat} [NeZero width]
    (config : AsmConfigExact width) (programs : List (Nat × HolProg width))
    (zero : asmByteOffsetOkExact config 0 = true)
    (valid : ∀ entry ∈ programs, stackAsmOkExact config entry.2) :
    allEncOkPreHOL config (programs.map progToSectionHOL) := by
  intro sectionData member
  rcases List.mem_map.mp member with ⟨⟨sectionId, program⟩, inPrograms, rfl⟩
  unfold secOkPreHOL
  cases flattened : flattenHOL true program sectionId
      (Flapjack.Compiler.Backend.StackAlloc.nextLab program 2) [] [] with
  | mk lines rest =>
    cases rest with
    | mk done next =>
      have safe := flattenLineOkPreHOL true program sectionId
        (Flapjack.Compiler.Backend.StackAlloc.nextLab program 2) [] []
        lines done next config zero (valid (sectionId, program) inPrograms) flattened
      simp only [progToSectionHOL, flattened]
      rw [(appListAppend_thm lines (.list [.label sectionId (if isSeqHOL program then next else 1) 0]) []).1]
      intro line inLines
      rcases List.mem_append.mp inLines with fromBody | fromLabel
      · exact safe line fromBody
      · simp [appListAppend, appendAux] at fromLabel
        subst line
        trivial
end Flapjack.Compiler.Backend.StackToLab.Proofs
