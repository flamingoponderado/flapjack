import Flapjack.Compiler.Backend.StackToLab.Native
import Flapjack.Compiler.Backend.LabProps.Native
import Flapjack.Compiler.Backend.StackProps.ProgramValidity
namespace Flapjack.Compiler.Backend.StackToLab.Proofs
open Flapjack Flapjack.Compiler.Backend.StackToLab
open Flapjack.Compiler.Backend.StackLang Flapjack.Compiler.Backend.StackProps
open Flapjack.Compiler.Backend.LabSem Flapjack.Compiler.Backend.LabProps
open Flapjack.Compiler.Backend.LabToTarget Flapjack.Compiler.Encoders.Asm
/-!
Nonrecursive constructor cases of the local `flatten_line_ok_pre` at
`stack_to_labProofScript.sml:3629-3661`. Each statement retains the original
zero byte-offset validity, source program assembly validity, actual flatten
result equality, and EVERY conclusion over the resulting app_list.

These are constructor specializations. Recursive.lean supplies Seq, If, Loop
and returned Call pieces under whole-statement structural motives; Full.lean
discharges those motives and assembles the complete original statements. Tail Call deliberately leaves its handler
arbitrary: the original NONE-return clauses ignore it. The original line
precheck accepts all LabAsm lines, including jumps; no stronger target validity
assumption is inserted here. FFI names use the exact MlString carrier.
-/
/-- Full original Inst constructor case; all original premises retained. -/
@[hol "cakeml/compiler/backend/proofs/stack_to_labProofScript.sml" "flatten_line_ok_pre"
  (words_as_type_indexed_bitvec)]
theorem flattenLineOkPreInst {width : Nat} [NeZero width]
    (tail : Bool) (instruction : HolInst width) (sectionId next : Nat)
    (conts breaks : List Nat) (lines : AppList (LabLineHOL width))
    (done : Bool) (nextAfter : Nat) (config : AsmConfigExact width)
    (_zero : asmByteOffsetOkExact config 0 = true)
    (valid : stackAsmOkExact config (.inst instruction))
    (result : flattenHOL tail (.inst instruction) sectionId next conts breaks =
      (lines, done, nextAfter)) :
    ∀ line ∈ appListAppend lines, lineOkPreHOL config line := by
  simp only [flattenHOL, Prod.mk.injEq] at result
  rcases result with ⟨hLines, _, _⟩
  subst lines
  simpa [appListAppend, appendAux, lineOkPreHOL, cbwToAsmHOL,
    asmOkExact, stackAsmOkExact] using valid
/-- Full original Raise constructor case; all original premises retained. -/
@[hol "cakeml/compiler/backend/proofs/stack_to_labProofScript.sml" "flatten_line_ok_pre"
  (words_as_type_indexed_bitvec)]
theorem flattenLineOkPreRaise {width : Nat} [NeZero width]
    (tail : Bool) (register : Nat) (sectionId next : Nat)
    (conts breaks : List Nat) (lines : AppList (LabLineHOL width))
    (done : Bool) (nextAfter : Nat) (config : AsmConfigExact width)
    (_zero : asmByteOffsetOkExact config 0 = true)
    (valid : stackAsmOkExact config (.raise register))
    (result : flattenHOL tail (.raise register) sectionId next conts breaks =
      (lines, done, nextAfter)) :
    ∀ line ∈ appListAppend lines, lineOkPreHOL config line := by
  simp only [flattenHOL, Prod.mk.injEq] at result
  rcases result with ⟨hLines, _, _⟩
  subst lines
  simpa [appListAppend, appendAux, lineOkPreHOL, cbwToAsmHOL, asmOkExact, stackAsmOkExact, asmRegOkExact] using valid

/-- Full original Return constructor case; all original premises retained. -/
@[hol "cakeml/compiler/backend/proofs/stack_to_labProofScript.sml" "flatten_line_ok_pre"
  (words_as_type_indexed_bitvec)]
theorem flattenLineOkPreReturn {width : Nat} [NeZero width]
    (tail : Bool) (register : Nat) (sectionId next : Nat)
    (conts breaks : List Nat) (lines : AppList (LabLineHOL width))
    (done : Bool) (nextAfter : Nat) (config : AsmConfigExact width)
    (_zero : asmByteOffsetOkExact config 0 = true)
    (valid : stackAsmOkExact config (.ret register))
    (result : flattenHOL tail (.ret register) sectionId next conts breaks =
      (lines, done, nextAfter)) :
    ∀ line ∈ appListAppend lines, lineOkPreHOL config line := by
  simp only [flattenHOL, Prod.mk.injEq] at result
  rcases result with ⟨hLines, _, _⟩
  subst lines
  simpa [appListAppend, appendAux, lineOkPreHOL, cbwToAsmHOL, asmOkExact, stackAsmOkExact, asmRegOkExact] using valid

/-- Full original CodeBufferWrite constructor case; all original premises retained. -/
@[hol "cakeml/compiler/backend/proofs/stack_to_labProofScript.sml" "flatten_line_ok_pre"
  (words_as_type_indexed_bitvec)]
theorem flattenLineOkPreCodeBufferWrite {width : Nat} [NeZero width]
    (tail : Bool) (left right : Nat) (sectionId next : Nat)
    (conts breaks : List Nat) (lines : AppList (LabLineHOL width))
    (done : Bool) (nextAfter : Nat) (config : AsmConfigExact width)
    (_zero : asmByteOffsetOkExact config 0 = true)
    (valid : stackAsmOkExact config (.codeBufferWrite left right))
    (result : flattenHOL tail (.codeBufferWrite left right) sectionId next conts breaks =
      (lines, done, nextAfter)) :
    ∀ line ∈ appListAppend lines, lineOkPreHOL config line := by
  simp only [flattenHOL, Prod.mk.injEq] at result
  rcases result with ⟨hLines, _, _⟩
  subst lines
  simp_all [appListAppend, appendAux, lineOkPreHOL, cbwToAsmHOL, asmOkExact, asmInstOkExact, stackAsmOkExact, asmRegOkExact]

/-- Full original SharedMemory constructor case; all original premises retained. -/
@[hol "cakeml/compiler/backend/proofs/stack_to_labProofScript.sml" "flatten_line_ok_pre"
  (words_as_type_indexed_bitvec)]
theorem flattenLineOkPreSharedMemory {width : Nat} [NeZero width]
    (tail : Bool) (operator : HolMemop) (register : Nat) (address : HolAddr width) (sectionId next : Nat)
    (conts breaks : List Nat) (lines : AppList (LabLineHOL width))
    (done : Bool) (nextAfter : Nat) (config : AsmConfigExact width)
    (_zero : asmByteOffsetOkExact config 0 = true)
    (valid : stackAsmOkExact config (.shMemOp operator register address))
    (result : flattenHOL tail (.shMemOp operator register address) sectionId next conts breaks =
      (lines, done, nextAfter)) :
    ∀ line ∈ appListAppend lines, lineOkPreHOL config line := by
  simp only [flattenHOL, Prod.mk.injEq] at result
  rcases result with ⟨hLines, _, _⟩
  subst lines
  cases address with
  | addr base offset =>
      cases operator <;> simp_all [appListAppend, appendAux, lineOkPreHOL, cbwToAsmHOL, asmOkExact, asmInstOkExact, stackAsmOkExact, asmRegOkExact, asmAddrOkExact]

/-- Full original Tick constructor case; all original premises retained. -/
@[hol "cakeml/compiler/backend/proofs/stack_to_labProofScript.sml" "flatten_line_ok_pre"
  (words_as_type_indexed_bitvec)]
theorem flattenLineOkPreTick {width : Nat} [NeZero width]
    (tail : Bool)  (sectionId next : Nat)
    (conts breaks : List Nat) (lines : AppList (LabLineHOL width))
    (done : Bool) (nextAfter : Nat) (config : AsmConfigExact width)
    (_zero : asmByteOffsetOkExact config 0 = true)
    (_valid : stackAsmOkExact config (.tick))
    (result : flattenHOL tail (.tick) sectionId next conts breaks =
      (lines, done, nextAfter)) :
    ∀ line ∈ appListAppend lines, lineOkPreHOL config line := by
  simp only [flattenHOL, Prod.mk.injEq] at result
  rcases result with ⟨hLines, _, _⟩
  subst lines
  simp [appListAppend, appendAux, lineOkPreHOL, cbwToAsmHOL, asmOkExact, asmInstOkExact]

/-- Full original Halt constructor case; all original premises retained. -/
@[hol "cakeml/compiler/backend/proofs/stack_to_labProofScript.sml" "flatten_line_ok_pre"
  (words_as_type_indexed_bitvec)]
theorem flattenLineOkPreHalt {width : Nat} [NeZero width]
    (tail : Bool) (register : Nat) (sectionId next : Nat)
    (conts breaks : List Nat) (lines : AppList (LabLineHOL width))
    (done : Bool) (nextAfter : Nat) (config : AsmConfigExact width)
    (_zero : asmByteOffsetOkExact config 0 = true)
    (_valid : stackAsmOkExact config (.halt register))
    (result : flattenHOL tail (.halt register) sectionId next conts breaks =
      (lines, done, nextAfter)) :
    ∀ line ∈ appListAppend lines, lineOkPreHOL config line := by
  simp only [flattenHOL, Prod.mk.injEq] at result
  rcases result with ⟨hLines, _, _⟩
  subst lines
  simp [appListAppend, appendAux, lineOkPreHOL]

/-- Full original Break constructor case; all original premises retained. -/
@[hol "cakeml/compiler/backend/proofs/stack_to_labProofScript.sml" "flatten_line_ok_pre"
  (words_as_type_indexed_bitvec)]
theorem flattenLineOkPreBreak {width : Nat} [NeZero width]
    (tail : Bool) (index : Nat) (sectionId next : Nat)
    (conts breaks : List Nat) (lines : AppList (LabLineHOL width))
    (done : Bool) (nextAfter : Nat) (config : AsmConfigExact width)
    (_zero : asmByteOffsetOkExact config 0 = true)
    (_valid : stackAsmOkExact config (.break index))
    (result : flattenHOL tail (.break index) sectionId next conts breaks =
      (lines, done, nextAfter)) :
    ∀ line ∈ appListAppend lines, lineOkPreHOL config line := by
  simp only [flattenHOL, Prod.mk.injEq] at result
  rcases result with ⟨hLines, _, _⟩
  subst lines
  simp [appListAppend, appendAux, lineOkPreHOL]

/-- Full original Continue constructor case; all original premises retained. -/
@[hol "cakeml/compiler/backend/proofs/stack_to_labProofScript.sml" "flatten_line_ok_pre"
  (words_as_type_indexed_bitvec)]
theorem flattenLineOkPreContinue {width : Nat} [NeZero width]
    (tail : Bool) (index : Nat) (sectionId next : Nat)
    (conts breaks : List Nat) (lines : AppList (LabLineHOL width))
    (done : Bool) (nextAfter : Nat) (config : AsmConfigExact width)
    (_zero : asmByteOffsetOkExact config 0 = true)
    (_valid : stackAsmOkExact config (.continue index))
    (result : flattenHOL tail (.continue index) sectionId next conts breaks =
      (lines, done, nextAfter)) :
    ∀ line ∈ appListAppend lines, lineOkPreHOL config line := by
  simp only [flattenHOL, Prod.mk.injEq] at result
  rcases result with ⟨hLines, _, _⟩
  subst lines
  simp [appListAppend, appendAux, lineOkPreHOL]

/-- Full original RawCall constructor case; all original premises retained. -/
@[hol "cakeml/compiler/backend/proofs/stack_to_labProofScript.sml" "flatten_line_ok_pre"
  (words_as_type_indexed_bitvec)]
theorem flattenLineOkPreRawCall {width : Nat} [NeZero width]
    (tail : Bool) (target : Nat) (sectionId next : Nat)
    (conts breaks : List Nat) (lines : AppList (LabLineHOL width))
    (done : Bool) (nextAfter : Nat) (config : AsmConfigExact width)
    (_zero : asmByteOffsetOkExact config 0 = true)
    (_valid : stackAsmOkExact config (.rawCall target))
    (result : flattenHOL tail (.rawCall target) sectionId next conts breaks =
      (lines, done, nextAfter)) :
    ∀ line ∈ appListAppend lines, lineOkPreHOL config line := by
  simp only [flattenHOL, Prod.mk.injEq] at result
  rcases result with ⟨hLines, _, _⟩
  subst lines
  simp [appListAppend, appendAux, lineOkPreHOL]

/-- Full original JumpLower constructor case; all original premises retained. -/
@[hol "cakeml/compiler/backend/proofs/stack_to_labProofScript.sml" "flatten_line_ok_pre"
  (words_as_type_indexed_bitvec)]
theorem flattenLineOkPreJumpLower {width : Nat} [NeZero width]
    (tail : Bool) (left right target : Nat) (sectionId next : Nat)
    (conts breaks : List Nat) (lines : AppList (LabLineHOL width))
    (done : Bool) (nextAfter : Nat) (config : AsmConfigExact width)
    (_zero : asmByteOffsetOkExact config 0 = true)
    (_valid : stackAsmOkExact config (.jumpLower left right target))
    (result : flattenHOL tail (.jumpLower left right target) sectionId next conts breaks =
      (lines, done, nextAfter)) :
    ∀ line ∈ appListAppend lines, lineOkPreHOL config line := by
  simp only [flattenHOL, Prod.mk.injEq] at result
  rcases result with ⟨hLines, _, _⟩
  subst lines
  simp [appListAppend, appendAux, lineOkPreHOL]

/-- Full original Ffi constructor case; all original premises retained. -/
@[hol "cakeml/compiler/backend/proofs/stack_to_labProofScript.sml" "flatten_line_ok_pre"
  (words_as_type_indexed_bitvec)]
theorem flattenLineOkPreFfi {width : Nat} [NeZero width]
    (tail : Bool) (name : Flapjack.Basis.Pure.MlString.MlString) (a1 a2 a3 a4 link : Nat) (sectionId next : Nat)
    (conts breaks : List Nat) (lines : AppList (LabLineHOL width))
    (done : Bool) (nextAfter : Nat) (config : AsmConfigExact width)
    (_zero : asmByteOffsetOkExact config 0 = true)
    (_valid : stackAsmOkExact config (.ffi name a1 a2 a3 a4 link))
    (result : flattenHOL tail (.ffi name a1 a2 a3 a4 link) sectionId next conts breaks =
      (lines, done, nextAfter)) :
    ∀ line ∈ appListAppend lines, lineOkPreHOL config line := by
  simp only [flattenHOL, Prod.mk.injEq] at result
  rcases result with ⟨hLines, _, _⟩
  subst lines
  simp [appListAppend, appendAux, lineOkPreHOL]

/-- Full original LocValue constructor case; all original premises retained. -/
@[hol "cakeml/compiler/backend/proofs/stack_to_labProofScript.sml" "flatten_line_ok_pre"
  (words_as_type_indexed_bitvec)]
theorem flattenLineOkPreLocValue {width : Nat} [NeZero width]
    (tail : Bool) (register label entry : Nat) (sectionId next : Nat)
    (conts breaks : List Nat) (lines : AppList (LabLineHOL width))
    (done : Bool) (nextAfter : Nat) (config : AsmConfigExact width)
    (_zero : asmByteOffsetOkExact config 0 = true)
    (_valid : stackAsmOkExact config (.locValue register label entry))
    (result : flattenHOL tail (.locValue register label entry) sectionId next conts breaks =
      (lines, done, nextAfter)) :
    ∀ line ∈ appListAppend lines, lineOkPreHOL config line := by
  simp only [flattenHOL, Prod.mk.injEq] at result
  rcases result with ⟨hLines, _, _⟩
  subst lines
  simp [appListAppend, appendAux, lineOkPreHOL]

/-- Full original Install constructor case; all original premises retained. -/
@[hol "cakeml/compiler/backend/proofs/stack_to_labProofScript.sml" "flatten_line_ok_pre"
  (words_as_type_indexed_bitvec)]
theorem flattenLineOkPreInstall {width : Nat} [NeZero width]
    (tail : Bool) (a1 a2 a3 a4 link : Nat) (sectionId next : Nat)
    (conts breaks : List Nat) (lines : AppList (LabLineHOL width))
    (done : Bool) (nextAfter : Nat) (config : AsmConfigExact width)
    (_zero : asmByteOffsetOkExact config 0 = true)
    (_valid : stackAsmOkExact config (.install a1 a2 a3 a4 link))
    (result : flattenHOL tail (.install a1 a2 a3 a4 link) sectionId next conts breaks =
      (lines, done, nextAfter)) :
    ∀ line ∈ appListAppend lines, lineOkPreHOL config line := by
  simp only [flattenHOL, Prod.mk.injEq] at result
  rcases result with ⟨hLines, _, _⟩
  subst lines
  simp [appListAppend, appendAux, lineOkPreHOL]

/-- Full original Skip constructor case; all original premises retained. -/
@[hol "cakeml/compiler/backend/proofs/stack_to_labProofScript.sml" "flatten_line_ok_pre"
  (words_as_type_indexed_bitvec)]
theorem flattenLineOkPreSkip {width : Nat} [NeZero width]
    (tail : Bool)  (sectionId next : Nat)
    (conts breaks : List Nat) (lines : AppList (LabLineHOL width))
    (done : Bool) (nextAfter : Nat) (config : AsmConfigExact width)
    (_zero : asmByteOffsetOkExact config 0 = true)
    (_valid : stackAsmOkExact config (.skip))
    (result : flattenHOL tail (.skip) sectionId next conts breaks =
      (lines, done, nextAfter)) :
    ∀ line ∈ appListAppend lines, lineOkPreHOL config line := by
  simp only [flattenHOL, Prod.mk.injEq] at result
  rcases result with ⟨hLines, _, _⟩
  subst lines
  simp [appListAppend, appendAux]

/-- Full original Get constructor case; all original premises retained. -/
@[hol "cakeml/compiler/backend/proofs/stack_to_labProofScript.sml" "flatten_line_ok_pre"
  (words_as_type_indexed_bitvec)]
theorem flattenLineOkPreGet {width : Nat} [NeZero width]
    (tail : Bool) (destination : Nat) (store : StoreName) (sectionId next : Nat)
    (conts breaks : List Nat) (lines : AppList (LabLineHOL width))
    (done : Bool) (nextAfter : Nat) (config : AsmConfigExact width)
    (_zero : asmByteOffsetOkExact config 0 = true)
    (_valid : stackAsmOkExact config (.get destination store))
    (result : flattenHOL tail (.get destination store) sectionId next conts breaks =
      (lines, done, nextAfter)) :
    ∀ line ∈ appListAppend lines, lineOkPreHOL config line := by
  simp only [flattenHOL, Prod.mk.injEq] at result
  rcases result with ⟨hLines, _, _⟩
  subst lines
  simp [appListAppend, appendAux]

/-- Full original Set constructor case; all original premises retained. -/
@[hol "cakeml/compiler/backend/proofs/stack_to_labProofScript.sml" "flatten_line_ok_pre"
  (words_as_type_indexed_bitvec)]
theorem flattenLineOkPreSet {width : Nat} [NeZero width]
    (tail : Bool) (store : StoreName) (source : Nat) (sectionId next : Nat)
    (conts breaks : List Nat) (lines : AppList (LabLineHOL width))
    (done : Bool) (nextAfter : Nat) (config : AsmConfigExact width)
    (_zero : asmByteOffsetOkExact config 0 = true)
    (_valid : stackAsmOkExact config (.set store source))
    (result : flattenHOL tail (.set store source) sectionId next conts breaks =
      (lines, done, nextAfter)) :
    ∀ line ∈ appListAppend lines, lineOkPreHOL config line := by
  simp only [flattenHOL, Prod.mk.injEq] at result
  rcases result with ⟨hLines, _, _⟩
  subst lines
  simp [appListAppend, appendAux]

/-- Full original OpCurrHeap constructor case; all original premises retained. -/
@[hol "cakeml/compiler/backend/proofs/stack_to_labProofScript.sml" "flatten_line_ok_pre"
  (words_as_type_indexed_bitvec)]
theorem flattenLineOkPreOpCurrHeap {width : Nat} [NeZero width]
    (tail : Bool) (operator : HolBinop) (destination source : Nat) (sectionId next : Nat)
    (conts breaks : List Nat) (lines : AppList (LabLineHOL width))
    (done : Bool) (nextAfter : Nat) (config : AsmConfigExact width)
    (_zero : asmByteOffsetOkExact config 0 = true)
    (_valid : stackAsmOkExact config (.opCurrHeap operator destination source))
    (result : flattenHOL tail (.opCurrHeap operator destination source) sectionId next conts breaks =
      (lines, done, nextAfter)) :
    ∀ line ∈ appListAppend lines, lineOkPreHOL config line := by
  simp only [flattenHOL, Prod.mk.injEq] at result
  rcases result with ⟨hLines, _, _⟩
  subst lines
  simp [appListAppend, appendAux]

/-- Full original Alloc constructor case; all original premises retained. -/
@[hol "cakeml/compiler/backend/proofs/stack_to_labProofScript.sml" "flatten_line_ok_pre"
  (words_as_type_indexed_bitvec)]
theorem flattenLineOkPreAlloc {width : Nat} [NeZero width]
    (tail : Bool) (words : Nat) (sectionId next : Nat)
    (conts breaks : List Nat) (lines : AppList (LabLineHOL width))
    (done : Bool) (nextAfter : Nat) (config : AsmConfigExact width)
    (_zero : asmByteOffsetOkExact config 0 = true)
    (_valid : stackAsmOkExact config (.alloc words))
    (result : flattenHOL tail (.alloc words) sectionId next conts breaks =
      (lines, done, nextAfter)) :
    ∀ line ∈ appListAppend lines, lineOkPreHOL config line := by
  simp only [flattenHOL, Prod.mk.injEq] at result
  rcases result with ⟨hLines, _, _⟩
  subst lines
  simp [appListAppend, appendAux]

/-- Full original StoreConsts constructor case; all original premises retained. -/
@[hol "cakeml/compiler/backend/proofs/stack_to_labProofScript.sml" "flatten_line_ok_pre"
  (words_as_type_indexed_bitvec)]
theorem flattenLineOkPreStoreConsts {width : Nat} [NeZero width]
    (tail : Bool) (source bitmap : Nat) (stub : Option Nat) (sectionId next : Nat)
    (conts breaks : List Nat) (lines : AppList (LabLineHOL width))
    (done : Bool) (nextAfter : Nat) (config : AsmConfigExact width)
    (_zero : asmByteOffsetOkExact config 0 = true)
    (_valid : stackAsmOkExact config (.storeConsts source bitmap stub))
    (result : flattenHOL tail (.storeConsts source bitmap stub) sectionId next conts breaks =
      (lines, done, nextAfter)) :
    ∀ line ∈ appListAppend lines, lineOkPreHOL config line := by
  simp only [flattenHOL, Prod.mk.injEq] at result
  rcases result with ⟨hLines, _, _⟩
  subst lines
  simp [appListAppend, appendAux]

/-- Full original DataBufferWrite constructor case; all original premises retained. -/
@[hol "cakeml/compiler/backend/proofs/stack_to_labProofScript.sml" "flatten_line_ok_pre"
  (words_as_type_indexed_bitvec)]
theorem flattenLineOkPreDataBufferWrite {width : Nat} [NeZero width]
    (tail : Bool) (address value : Nat) (sectionId next : Nat)
    (conts breaks : List Nat) (lines : AppList (LabLineHOL width))
    (done : Bool) (nextAfter : Nat) (config : AsmConfigExact width)
    (_zero : asmByteOffsetOkExact config 0 = true)
    (_valid : stackAsmOkExact config (.dataBufferWrite address value))
    (result : flattenHOL tail (.dataBufferWrite address value) sectionId next conts breaks =
      (lines, done, nextAfter)) :
    ∀ line ∈ appListAppend lines, lineOkPreHOL config line := by
  simp only [flattenHOL, Prod.mk.injEq] at result
  rcases result with ⟨hLines, _, _⟩
  subst lines
  simp [appListAppend, appendAux]

/-- Full original StackAlloc constructor case; all original premises retained. -/
@[hol "cakeml/compiler/backend/proofs/stack_to_labProofScript.sml" "flatten_line_ok_pre"
  (words_as_type_indexed_bitvec)]
theorem flattenLineOkPreStackAlloc {width : Nat} [NeZero width]
    (tail : Bool) (words : Nat) (sectionId next : Nat)
    (conts breaks : List Nat) (lines : AppList (LabLineHOL width))
    (done : Bool) (nextAfter : Nat) (config : AsmConfigExact width)
    (_zero : asmByteOffsetOkExact config 0 = true)
    (_valid : stackAsmOkExact config (.stackAlloc words))
    (result : flattenHOL tail (.stackAlloc words) sectionId next conts breaks =
      (lines, done, nextAfter)) :
    ∀ line ∈ appListAppend lines, lineOkPreHOL config line := by
  simp only [flattenHOL, Prod.mk.injEq] at result
  rcases result with ⟨hLines, _, _⟩
  subst lines
  simp [appListAppend, appendAux]

/-- Full original StackFree constructor case; all original premises retained. -/
@[hol "cakeml/compiler/backend/proofs/stack_to_labProofScript.sml" "flatten_line_ok_pre"
  (words_as_type_indexed_bitvec)]
theorem flattenLineOkPreStackFree {width : Nat} [NeZero width]
    (tail : Bool) (words : Nat) (sectionId next : Nat)
    (conts breaks : List Nat) (lines : AppList (LabLineHOL width))
    (done : Bool) (nextAfter : Nat) (config : AsmConfigExact width)
    (_zero : asmByteOffsetOkExact config 0 = true)
    (_valid : stackAsmOkExact config (.stackFree words))
    (result : flattenHOL tail (.stackFree words) sectionId next conts breaks =
      (lines, done, nextAfter)) :
    ∀ line ∈ appListAppend lines, lineOkPreHOL config line := by
  simp only [flattenHOL, Prod.mk.injEq] at result
  rcases result with ⟨hLines, _, _⟩
  subst lines
  simp [appListAppend, appendAux]

/-- Full original StackStore constructor case; all original premises retained. -/
@[hol "cakeml/compiler/backend/proofs/stack_to_labProofScript.sml" "flatten_line_ok_pre"
  (words_as_type_indexed_bitvec)]
theorem flattenLineOkPreStackStore {width : Nat} [NeZero width]
    (tail : Bool) (offset register : Nat) (sectionId next : Nat)
    (conts breaks : List Nat) (lines : AppList (LabLineHOL width))
    (done : Bool) (nextAfter : Nat) (config : AsmConfigExact width)
    (_zero : asmByteOffsetOkExact config 0 = true)
    (_valid : stackAsmOkExact config (.stackStore offset register))
    (result : flattenHOL tail (.stackStore offset register) sectionId next conts breaks =
      (lines, done, nextAfter)) :
    ∀ line ∈ appListAppend lines, lineOkPreHOL config line := by
  simp only [flattenHOL, Prod.mk.injEq] at result
  rcases result with ⟨hLines, _, _⟩
  subst lines
  simp [appListAppend, appendAux]

/-- Full original StackStoreAny constructor case; all original premises retained. -/
@[hol "cakeml/compiler/backend/proofs/stack_to_labProofScript.sml" "flatten_line_ok_pre"
  (words_as_type_indexed_bitvec)]
theorem flattenLineOkPreStackStoreAny {width : Nat} [NeZero width]
    (tail : Bool) (register offsetRegister : Nat) (sectionId next : Nat)
    (conts breaks : List Nat) (lines : AppList (LabLineHOL width))
    (done : Bool) (nextAfter : Nat) (config : AsmConfigExact width)
    (_zero : asmByteOffsetOkExact config 0 = true)
    (_valid : stackAsmOkExact config (.stackStoreAny register offsetRegister))
    (result : flattenHOL tail (.stackStoreAny register offsetRegister) sectionId next conts breaks =
      (lines, done, nextAfter)) :
    ∀ line ∈ appListAppend lines, lineOkPreHOL config line := by
  simp only [flattenHOL, Prod.mk.injEq] at result
  rcases result with ⟨hLines, _, _⟩
  subst lines
  simp [appListAppend, appendAux]

/-- Full original StackLoad constructor case; all original premises retained. -/
@[hol "cakeml/compiler/backend/proofs/stack_to_labProofScript.sml" "flatten_line_ok_pre"
  (words_as_type_indexed_bitvec)]
theorem flattenLineOkPreStackLoad {width : Nat} [NeZero width]
    (tail : Bool) (offset register : Nat) (sectionId next : Nat)
    (conts breaks : List Nat) (lines : AppList (LabLineHOL width))
    (done : Bool) (nextAfter : Nat) (config : AsmConfigExact width)
    (_zero : asmByteOffsetOkExact config 0 = true)
    (_valid : stackAsmOkExact config (.stackLoad offset register))
    (result : flattenHOL tail (.stackLoad offset register) sectionId next conts breaks =
      (lines, done, nextAfter)) :
    ∀ line ∈ appListAppend lines, lineOkPreHOL config line := by
  simp only [flattenHOL, Prod.mk.injEq] at result
  rcases result with ⟨hLines, _, _⟩
  subst lines
  simp [appListAppend, appendAux]

/-- Full original StackLoadAny constructor case; all original premises retained. -/
@[hol "cakeml/compiler/backend/proofs/stack_to_labProofScript.sml" "flatten_line_ok_pre"
  (words_as_type_indexed_bitvec)]
theorem flattenLineOkPreStackLoadAny {width : Nat} [NeZero width]
    (tail : Bool) (register offsetRegister : Nat) (sectionId next : Nat)
    (conts breaks : List Nat) (lines : AppList (LabLineHOL width))
    (done : Bool) (nextAfter : Nat) (config : AsmConfigExact width)
    (_zero : asmByteOffsetOkExact config 0 = true)
    (_valid : stackAsmOkExact config (.stackLoadAny register offsetRegister))
    (result : flattenHOL tail (.stackLoadAny register offsetRegister) sectionId next conts breaks =
      (lines, done, nextAfter)) :
    ∀ line ∈ appListAppend lines, lineOkPreHOL config line := by
  simp only [flattenHOL, Prod.mk.injEq] at result
  rcases result with ⟨hLines, _, _⟩
  subst lines
  simp [appListAppend, appendAux]

/-- Full original StackGetSize constructor case; all original premises retained. -/
@[hol "cakeml/compiler/backend/proofs/stack_to_labProofScript.sml" "flatten_line_ok_pre"
  (words_as_type_indexed_bitvec)]
theorem flattenLineOkPreStackGetSize {width : Nat} [NeZero width]
    (tail : Bool) (register : Nat) (sectionId next : Nat)
    (conts breaks : List Nat) (lines : AppList (LabLineHOL width))
    (done : Bool) (nextAfter : Nat) (config : AsmConfigExact width)
    (_zero : asmByteOffsetOkExact config 0 = true)
    (_valid : stackAsmOkExact config (.stackGetSize register))
    (result : flattenHOL tail (.stackGetSize register) sectionId next conts breaks =
      (lines, done, nextAfter)) :
    ∀ line ∈ appListAppend lines, lineOkPreHOL config line := by
  simp only [flattenHOL, Prod.mk.injEq] at result
  rcases result with ⟨hLines, _, _⟩
  subst lines
  simp [appListAppend, appendAux]

/-- Full original StackSetSize constructor case; all original premises retained. -/
@[hol "cakeml/compiler/backend/proofs/stack_to_labProofScript.sml" "flatten_line_ok_pre"
  (words_as_type_indexed_bitvec)]
theorem flattenLineOkPreStackSetSize {width : Nat} [NeZero width]
    (tail : Bool) (register : Nat) (sectionId next : Nat)
    (conts breaks : List Nat) (lines : AppList (LabLineHOL width))
    (done : Bool) (nextAfter : Nat) (config : AsmConfigExact width)
    (_zero : asmByteOffsetOkExact config 0 = true)
    (_valid : stackAsmOkExact config (.stackSetSize register))
    (result : flattenHOL tail (.stackSetSize register) sectionId next conts breaks =
      (lines, done, nextAfter)) :
    ∀ line ∈ appListAppend lines, lineOkPreHOL config line := by
  simp only [flattenHOL, Prod.mk.injEq] at result
  rcases result with ⟨hLines, _, _⟩
  subst lines
  simp [appListAppend, appendAux]

/-- Full original BitmapLoad constructor case; all original premises retained. -/
@[hol "cakeml/compiler/backend/proofs/stack_to_labProofScript.sml" "flatten_line_ok_pre"
  (words_as_type_indexed_bitvec)]
theorem flattenLineOkPreBitmapLoad {width : Nat} [NeZero width]
    (tail : Bool) (destination address : Nat) (sectionId next : Nat)
    (conts breaks : List Nat) (lines : AppList (LabLineHOL width))
    (done : Bool) (nextAfter : Nat) (config : AsmConfigExact width)
    (_zero : asmByteOffsetOkExact config 0 = true)
    (_valid : stackAsmOkExact config (.bitmapLoad destination address))
    (result : flattenHOL tail (.bitmapLoad destination address) sectionId next conts breaks =
      (lines, done, nextAfter)) :
    ∀ line ∈ appListAppend lines, lineOkPreHOL config line := by
  simp only [flattenHOL, Prod.mk.injEq] at result
  rcases result with ⟨hLines, _, _⟩
  subst lines
  simp [appListAppend, appendAux]

/-- Full original TailCall constructor case; all original premises retained. -/
@[hol "cakeml/compiler/backend/proofs/stack_to_labProofScript.sml" "flatten_line_ok_pre"
  (words_as_type_indexed_bitvec)]
theorem flattenLineOkPreTailCall {width : Nat} [NeZero width]
    (tail : Bool) (target : Sum Nat Nat)
    (handler : Option (HolProg width × Nat × Nat)) (sectionId next : Nat)
    (conts breaks : List Nat) (lines : AppList (LabLineHOL width))
    (done : Bool) (nextAfter : Nat) (config : AsmConfigExact width)
    (_zero : asmByteOffsetOkExact config 0 = true)
    (valid : stackAsmOkExact config (.call none target handler))
    (result : flattenHOL tail (.call none target handler) sectionId next conts breaks =
      (lines, done, nextAfter)) :
    ∀ line ∈ appListAppend lines, lineOkPreHOL config line := by
  cases target <;> simp only [flattenHOL, compileJumpHOL, Prod.mk.injEq] at result <;>
    rcases result with ⟨hLines, _, _⟩ <;> subst lines <;>
    simp_all [appListAppend, appendAux, lineOkPreHOL, cbwToAsmHOL,
      asmOkExact, stackAsmOkExact, asmRegOkExact]

end Flapjack.Compiler.Backend.StackToLab.Proofs
