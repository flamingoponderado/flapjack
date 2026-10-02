import Flapjack.Compiler.Backend.WordToStack.Proofs.AsmNameInstructions
import Flapjack.Compiler.Backend.WordToStack.Proofs.AsmNameHelpers

namespace Flapjack.WordToStackProofs.AsmNameFlat
open Flapjack Flapjack.Compiler.Backend.WordToStack.Native
open Flapjack.Compiler.Backend.StackLang Flapjack.Compiler.Backend.StackProps
open Flapjack.Compiler.Encoders.Asm
open Flapjack.Compiler.Backend.WordToStackRegFormat
open Flapjack.WordToStackProofs.AsmNameShare
open Flapjack.WordToStackProofs.AsmNameInstructions
open Flapjack.WordToStackProofs.AsmNameHelpers

/-- Internal naming calculation for arbitrary formatted move lists. HOL uses
this calculation inside the Move case and gives it no separate theorem name. -/
theorem formattedMovesName {width : Nat} [NeZero width] (conf : AsmConfigExact width)
    (moves : List (Option Nat × Option Nat)) (frame : Nat × Nat × Nat)
    (_room : frame.1 + 1 < conf.regCount - conf.avoidRegs.length) :
    stackAsmName conf (wMoveAuxNative
      (moves.map (fun xy => (formatVar frame.1 xy.1, formatVar frame.1 xy.2))) frame) := by
  have single (xy : Option Nat × Option Nat) :
      stackAsmName conf (wMoveSingleNative
        (formatVar frame.1 xy.1, formatVar frame.1 xy.2) frame) := by
    rcases xy with ⟨x,y⟩
    cases x <;> cases y <;> simp only [formatVar]
    all_goals try split_ifs
    all_goals simp_all [wMoveSingleNative, stackAsmName, instName,
      arithName, regImmName, regName]
    all_goals repeat' apply And.intro
    all_goals omega
  induction moves with
  | nil => trivial
  | cons xy rest ih =>
      cases rest with
      | nil => exact single xy
      | cons next tail =>
          simp only [List.map_cons, wMoveAuxNative, stackAsmName]
          exact ⟨single xy, ih⟩

/-- Complete original Skip naming case, with all seven source guards and
actual compiler output. Full naming assembly remains separate open work. -/
@[hol "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml"
  "word_to_stack_stack_asm_name_lem" (words_as_type_indexed_bitvec)]
theorem wordToStackStackAsmNameSkip {width : Nat} [NeZero width]
    (conf : AsmConfigExact width) (perf : Bool)
    (bs : AppList (BitVec width) × Nat) (frame : Nat × Nat × Nat)
    (plain : perf = false)
    (_conventions : @postAllocConventionsHOL width _ frame.1 (.skip) = true)
    (_valid : fullInstOkLessExact conf (.skip) = true)
    (_twoReg : conf.twoRegArith = true →
      everyInst (fun (i : WordLangInst (BitVec width)) => twoRegInstExact (HolInst.ofWordLangInst i)) (.skip) = true)
    (_noShare : noShareInstSubprogsHOL (width := width) (.skip) = true ∨ conf.isa ≠ .ag32)
    (_room : frame.1 + 1 < conf.regCount - conf.avoidRegs.length)
    (_minimum : 4 < frame.1) :
    stackAsmName conf (compNative conf perf (.skip) bs frame).1 := by
  subst perf
  simp only [compNative, stackAsmName]

/-- Complete original Move naming case, with all seven source guards and
actual compiler output. Full naming assembly remains separate open work. -/
@[hol "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml"
  "word_to_stack_stack_asm_name_lem" (words_as_type_indexed_bitvec)]
theorem wordToStackStackAsmNameMove {width : Nat} [NeZero width]
    (conf : AsmConfigExact width) (perf : Bool) (priority : Nat) (moves : List (Nat × Nat))
    (bs : AppList (BitVec width) × Nat) (frame : Nat × Nat × Nat)
    (plain : perf = false)
    (_conventions : @postAllocConventionsHOL width _ frame.1 (.move priority moves) = true)
    (_valid : fullInstOkLessExact conf (.move priority moves) = true)
    (_twoReg : conf.twoRegArith = true →
      everyInst (fun (i : WordLangInst (BitVec width)) => twoRegInstExact (HolInst.ofWordLangInst i)) (.move priority moves) = true)
    (_noShare : noShareInstSubprogsHOL (width := width) (.move priority moves) = true ∨ conf.isa ≠ .ag32)
    (_room : frame.1 + 1 < conf.regCount - conf.avoidRegs.length)
    (_minimum : 4 < frame.1) :
    stackAsmName conf (compNative conf perf (.move priority moves) bs frame).1 := by
  subst perf
  simp only [compNative, wMoveNative]
  exact formattedMovesName conf _ frame _room

/-- Complete original Assign naming case, with all seven source guards and
actual compiler output. Full naming assembly remains separate open work. -/
@[hol "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml"
  "word_to_stack_stack_asm_name_lem" (words_as_type_indexed_bitvec)]
theorem wordToStackStackAsmNameAssign {width : Nat} [NeZero width]
    (conf : AsmConfigExact width) (perf : Bool) (v : Nat) (exp : WordLangExpHOL (BitVec width))
    (bs : AppList (BitVec width) × Nat) (frame : Nat × Nat × Nat)
    (plain : perf = false)
    (_conventions : @postAllocConventionsHOL width _ frame.1 (.assign v exp) = true)
    (_valid : fullInstOkLessExact conf (.assign v exp) = true)
    (_twoReg : conf.twoRegArith = true →
      everyInst (fun (i : WordLangInst (BitVec width)) => twoRegInstExact (HolInst.ofWordLangInst i)) (.assign v exp) = true)
    (_noShare : noShareInstSubprogsHOL (width := width) (.assign v exp) = true ∨ conf.isa ≠ .ag32)
    (_room : frame.1 + 1 < conf.regCount - conf.avoidRegs.length)
    (_minimum : 4 < frame.1) :
    stackAsmName conf (compNative conf perf (.assign v exp) bs frame).1 := by
  subst perf
  simp only [compNative, stackAsmName]

/-- Complete original Get naming case, with all seven source guards and
actual compiler output. Full naming assembly remains separate open work. -/
@[hol "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml"
  "word_to_stack_stack_asm_name_lem" (words_as_type_indexed_bitvec)]
theorem wordToStackStackAsmNameGet {width : Nat} [NeZero width]
    (conf : AsmConfigExact width) (perf : Bool) (v : Nat) (name : WordStoreHOL)
    (bs : AppList (BitVec width) × Nat) (frame : Nat × Nat × Nat)
    (plain : perf = false)
    (_conventions : @postAllocConventionsHOL width _ frame.1 (.get v name) = true)
    (_valid : fullInstOkLessExact conf (.get v name) = true)
    (_twoReg : conf.twoRegArith = true →
      everyInst (fun (i : WordLangInst (BitVec width)) => twoRegInstExact (HolInst.ofWordLangInst i)) (.get v name) = true)
    (_noShare : noShareInstSubprogsHOL (width := width) (.get v name) = true ∨ conf.isa ≠ .ag32)
    (_room : frame.1 + 1 < conf.regCount - conf.avoidRegs.length)
    (_minimum : 4 < frame.1) :
    stackAsmName conf (compNative conf perf (.get v name) bs frame).1 := by
  subst perf
  simp only [compNative, writeNameEquation, stackAsmName]

/-- Complete original Set naming case, with all seven source guards and
actual compiler output. Full naming assembly remains separate open work. -/
@[hol "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml"
  "word_to_stack_stack_asm_name_lem" (words_as_type_indexed_bitvec)]
theorem wordToStackStackAsmNameSet {width : Nat} [NeZero width]
    (conf : AsmConfigExact width) (perf : Bool) (name : WordStoreHOL) (exp : WordLangExpHOL (BitVec width))
    (bs : AppList (BitVec width) × Nat) (frame : Nat × Nat × Nat)
    (plain : perf = false)
    (_conventions : @postAllocConventionsHOL width _ frame.1 (.set name exp) = true)
    (_valid : fullInstOkLessExact conf (.set name exp) = true)
    (_twoReg : conf.twoRegArith = true →
      everyInst (fun (i : WordLangInst (BitVec width)) => twoRegInstExact (HolInst.ofWordLangInst i)) (.set name exp) = true)
    (_noShare : noShareInstSubprogsHOL (width := width) (.set name exp) = true ∨ conf.isa ≠ .ag32)
    (_room : frame.1 + 1 < conf.regCount - conf.avoidRegs.length)
    (_minimum : 4 < frame.1) :
    stackAsmName conf (compNative conf perf (.set name exp) bs frame).1 := by
  subst perf
  cases name <;> cases exp
  all_goals simp only [compNative, wReg1, stackAsmName]
  all_goals try split_ifs
  all_goals try simp only [loadName, stackAsmName, storeNameOfWord]

/-- Complete original Store naming case, with all seven source guards and
actual compiler output. Full naming assembly remains separate open work. -/
@[hol "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml"
  "word_to_stack_stack_asm_name_lem" (words_as_type_indexed_bitvec)]
theorem wordToStackStackAsmNameStore {width : Nat} [NeZero width]
    (conf : AsmConfigExact width) (perf : Bool) (exp : WordLangExpHOL (BitVec width)) (v : Nat)
    (bs : AppList (BitVec width) × Nat) (frame : Nat × Nat × Nat)
    (plain : perf = false)
    (_conventions : @postAllocConventionsHOL width _ frame.1 (.store exp v) = true)
    (_valid : fullInstOkLessExact conf (.store exp v) = true)
    (_twoReg : conf.twoRegArith = true →
      everyInst (fun (i : WordLangInst (BitVec width)) => twoRegInstExact (HolInst.ofWordLangInst i)) (.store exp v) = true)
    (_noShare : noShareInstSubprogsHOL (width := width) (.store exp v) = true ∨ conf.isa ≠ .ag32)
    (_room : frame.1 + 1 < conf.regCount - conf.avoidRegs.length)
    (_minimum : 4 < frame.1) :
    stackAsmName conf (compNative conf perf (.store exp v) bs frame).1 := by
  subst perf
  simp only [compNative, stackAsmName]

/-- Complete original Alloc naming case, with all seven source guards and
actual compiler output. Full naming assembly remains separate open work. -/
@[hol "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml"
  "word_to_stack_stack_asm_name_lem" (words_as_type_indexed_bitvec)]
theorem wordToStackStackAsmNameAlloc {width : Nat} [NeZero width]
    (conf : AsmConfigExact width) (perf : Bool) (v : Nat) (live : WordLangCutsetsHOL)
    (bs : AppList (BitVec width) × Nat) (frame : Nat × Nat × Nat)
    (plain : perf = false)
    (_conventions : @postAllocConventionsHOL width _ frame.1 (.alloc v live) = true)
    (_valid : fullInstOkLessExact conf (.alloc v live) = true)
    (_twoReg : conf.twoRegArith = true →
      everyInst (fun (i : WordLangInst (BitVec width)) => twoRegInstExact (HolInst.ofWordLangInst i)) (.alloc v live) = true)
    (_noShare : noShareInstSubprogsHOL (width := width) (.alloc v live) = true ∨ conf.isa ≠ .ag32)
    (_room : frame.1 + 1 < conf.regCount - conf.avoidRegs.length)
    (_minimum : 4 < frame.1) :
    stackAsmName conf (compNative conf perf (.alloc v live) bs frame).1 := by
  subst perf
  simp only [compNative, stackAsmName]
  exact ⟨wLiveStackAsmName conf live bs frame _ _ _room rfl, trivial⟩

/-- Complete original StoreConsts naming case, with all seven source guards and
actual compiler output. Full naming assembly remains separate open work. -/
@[hol "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml"
  "word_to_stack_stack_asm_name_lem" (words_as_type_indexed_bitvec)]
theorem wordToStackStackAsmNameStoreConsts {width : Nat} [NeZero width]
    (conf : AsmConfigExact width) (perf : Bool) (r1 r2 r3 r4 : Nat) (ws : List (Bool × BitVec width))
    (bs : AppList (BitVec width) × Nat) (frame : Nat × Nat × Nat)
    (plain : perf = false)
    (_conventions : @postAllocConventionsHOL width _ frame.1 (.storeConsts r1 r2 r3 r4 ws) = true)
    (_valid : fullInstOkLessExact conf (.storeConsts r1 r2 r3 r4 ws) = true)
    (_twoReg : conf.twoRegArith = true →
      everyInst (fun (i : WordLangInst (BitVec width)) => twoRegInstExact (HolInst.ofWordLangInst i)) (.storeConsts r1 r2 r3 r4 ws) = true)
    (_noShare : noShareInstSubprogsHOL (width := width) (.storeConsts r1 r2 r3 r4 ws) = true ∨ conf.isa ≠ .ag32)
    (_room : frame.1 + 1 < conf.regCount - conf.avoidRegs.length)
    (_minimum : 4 < frame.1) :
    stackAsmName conf (compNative conf perf (.storeConsts r1 r2 r3 r4 ws) bs frame).1 := by
  subst perf
  simp only [compNative, stackAsmName, instName, regName]
  repeat' apply And.intro
  all_goals first | trivial | omega

/-- Complete original Raise naming case, with all seven source guards and
actual compiler output. Full naming assembly remains separate open work. -/
@[hol "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml"
  "word_to_stack_stack_asm_name_lem" (words_as_type_indexed_bitvec)]
theorem wordToStackStackAsmNameRaise {width : Nat} [NeZero width]
    (conf : AsmConfigExact width) (perf : Bool) (v : Nat)
    (bs : AppList (BitVec width) × Nat) (frame : Nat × Nat × Nat)
    (plain : perf = false)
    (_conventions : @postAllocConventionsHOL width _ frame.1 (.raise v) = true)
    (_valid : fullInstOkLessExact conf (.raise v) = true)
    (_twoReg : conf.twoRegArith = true →
      everyInst (fun (i : WordLangInst (BitVec width)) => twoRegInstExact (HolInst.ofWordLangInst i)) (.raise v) = true)
    (_noShare : noShareInstSubprogsHOL (width := width) (.raise v) = true ∨ conf.isa ≠ .ag32)
    (_room : frame.1 + 1 < conf.regCount - conf.avoidRegs.length)
    (_minimum : 4 < frame.1) :
    stackAsmName conf (compNative conf perf (.raise v) bs frame).1 := by
  subst perf
  simp only [compNative, stackAsmName, and_true]

/-- Complete original Return naming case, with all seven source guards and
actual compiler output. Full naming assembly remains separate open work. -/
@[hol "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml"
  "word_to_stack_stack_asm_name_lem" (words_as_type_indexed_bitvec)]
theorem wordToStackStackAsmNameReturn {width : Nat} [NeZero width]
    (conf : AsmConfigExact width) (perf : Bool) (v : Nat) (vs : List Nat)
    (bs : AppList (BitVec width) × Nat) (frame : Nat × Nat × Nat)
    (plain : perf = false)
    (_conventions : @postAllocConventionsHOL width _ frame.1 (.return v vs) = true)
    (_valid : fullInstOkLessExact conf (.return v vs) = true)
    (_twoReg : conf.twoRegArith = true →
      everyInst (fun (i : WordLangInst (BitVec width)) => twoRegInstExact (HolInst.ofWordLangInst i)) (.return v vs) = true)
    (_noShare : noShareInstSubprogsHOL (width := width) (.return v vs) = true ∨ conf.isa ≠ .ag32)
    (_room : frame.1 + 1 < conf.regCount - conf.avoidRegs.length)
    (_minimum : 4 < frame.1) :
    stackAsmName conf (compNative conf perf (.return v vs) bs frame).1 := by
  subst perf
  all_goals simp only [compNative, wReg1, seqStackFreeNative]
  all_goals try split_ifs
  all_goals try simp only [loadName, stackAsmName, regName]
  all_goals repeat' apply And.intro
  all_goals first | trivial | omega

/-- Complete original Break naming case, with all seven source guards and
actual compiler output. Full naming assembly remains separate open work. -/
@[hol "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml"
  "word_to_stack_stack_asm_name_lem" (words_as_type_indexed_bitvec)]
theorem wordToStackStackAsmNameBreak {width : Nat} [NeZero width]
    (conf : AsmConfigExact width) (perf : Bool) (label : Nat)
    (bs : AppList (BitVec width) × Nat) (frame : Nat × Nat × Nat)
    (plain : perf = false)
    (_conventions : @postAllocConventionsHOL width _ frame.1 (.break label) = true)
    (_valid : fullInstOkLessExact conf (.break label) = true)
    (_twoReg : conf.twoRegArith = true →
      everyInst (fun (i : WordLangInst (BitVec width)) => twoRegInstExact (HolInst.ofWordLangInst i)) (.break label) = true)
    (_noShare : noShareInstSubprogsHOL (width := width) (.break label) = true ∨ conf.isa ≠ .ag32)
    (_room : frame.1 + 1 < conf.regCount - conf.avoidRegs.length)
    (_minimum : 4 < frame.1) :
    stackAsmName conf (compNative conf perf (.break label) bs frame).1 := by
  subst perf
  simp only [compNative, stackAsmName]

/-- Complete original Continue naming case, with all seven source guards and
actual compiler output. Full naming assembly remains separate open work. -/
@[hol "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml"
  "word_to_stack_stack_asm_name_lem" (words_as_type_indexed_bitvec)]
theorem wordToStackStackAsmNameContinue {width : Nat} [NeZero width]
    (conf : AsmConfigExact width) (perf : Bool) (label : Nat)
    (bs : AppList (BitVec width) × Nat) (frame : Nat × Nat × Nat)
    (plain : perf = false)
    (_conventions : @postAllocConventionsHOL width _ frame.1 (.continue label) = true)
    (_valid : fullInstOkLessExact conf (.continue label) = true)
    (_twoReg : conf.twoRegArith = true →
      everyInst (fun (i : WordLangInst (BitVec width)) => twoRegInstExact (HolInst.ofWordLangInst i)) (.continue label) = true)
    (_noShare : noShareInstSubprogsHOL (width := width) (.continue label) = true ∨ conf.isa ≠ .ag32)
    (_room : frame.1 + 1 < conf.regCount - conf.avoidRegs.length)
    (_minimum : 4 < frame.1) :
    stackAsmName conf (compNative conf perf (.continue label) bs frame).1 := by
  subst perf
  simp only [compNative, stackAsmName]

/-- Complete original Tick naming case, with all seven source guards and
actual compiler output. Full naming assembly remains separate open work. -/
@[hol "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml"
  "word_to_stack_stack_asm_name_lem" (words_as_type_indexed_bitvec)]
theorem wordToStackStackAsmNameTick {width : Nat} [NeZero width]
    (conf : AsmConfigExact width) (perf : Bool)
    (bs : AppList (BitVec width) × Nat) (frame : Nat × Nat × Nat)
    (plain : perf = false)
    (_conventions : @postAllocConventionsHOL width _ frame.1 (.tick) = true)
    (_valid : fullInstOkLessExact conf (.tick) = true)
    (_twoReg : conf.twoRegArith = true →
      everyInst (fun (i : WordLangInst (BitVec width)) => twoRegInstExact (HolInst.ofWordLangInst i)) (.tick) = true)
    (_noShare : noShareInstSubprogsHOL (width := width) (.tick) = true ∨ conf.isa ≠ .ag32)
    (_room : frame.1 + 1 < conf.regCount - conf.avoidRegs.length)
    (_minimum : 4 < frame.1) :
    stackAsmName conf (compNative conf perf (.tick) bs frame).1 := by
  subst perf
  simp only [compNative, stackAsmName]

/-- Complete original OpCurrHeap naming case, with all seven source guards and
actual compiler output. Full naming assembly remains separate open work. -/
@[hol "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml"
  "word_to_stack_stack_asm_name_lem" (words_as_type_indexed_bitvec)]
theorem wordToStackStackAsmNameOpCurrHeap {width : Nat} [NeZero width]
    (conf : AsmConfigExact width) (perf : Bool) (op : BinOp) (v src : Nat)
    (bs : AppList (BitVec width) × Nat) (frame : Nat × Nat × Nat)
    (plain : perf = false)
    (_conventions : @postAllocConventionsHOL width _ frame.1 (.opCurrHeap op v src) = true)
    (_valid : fullInstOkLessExact conf (.opCurrHeap op v src) = true)
    (_twoReg : conf.twoRegArith = true →
      everyInst (fun (i : WordLangInst (BitVec width)) => twoRegInstExact (HolInst.ofWordLangInst i)) (.opCurrHeap op v src) = true)
    (_noShare : noShareInstSubprogsHOL (width := width) (.opCurrHeap op v src) = true ∨ conf.isa ≠ .ag32)
    (_room : frame.1 + 1 < conf.regCount - conf.avoidRegs.length)
    (_minimum : 4 < frame.1) :
    stackAsmName conf (compNative conf perf (.opCurrHeap op v src) bs frame).1 := by
  subst perf
  have rawConstraint : conf.twoRegArith = true → v = src := by
    simpa [everyInst, twoRegInstExact, HolInst.ofWordLangInst,
      HolArith.ofWordLangArith, HolRegImm.ofWordRegImm] using _twoReg
  all_goals simp only [compNative, wRegWrite1Native, wReg1]
  all_goals try split_ifs
  all_goals try simp only [loadName, stackAsmName, regName]
  all_goals simp_all []
  all_goals repeat' first | apply And.intro | intro
  all_goals first | trivial | omega | (have equal := rawConstraint ‹conf.twoRegArith = true›; omega)

/-- Complete original LocValue naming case, with all seven source guards and
actual compiler output. Full naming assembly remains separate open work. -/
@[hol "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml"
  "word_to_stack_stack_asm_name_lem" (words_as_type_indexed_bitvec)]
theorem wordToStackStackAsmNameLocValue {width : Nat} [NeZero width]
    (conf : AsmConfigExact width) (perf : Bool) (v label : Nat)
    (bs : AppList (BitVec width) × Nat) (frame : Nat × Nat × Nat)
    (plain : perf = false)
    (_conventions : @postAllocConventionsHOL width _ frame.1 (.locValue v label) = true)
    (_valid : fullInstOkLessExact conf (.locValue v label) = true)
    (_twoReg : conf.twoRegArith = true →
      everyInst (fun (i : WordLangInst (BitVec width)) => twoRegInstExact (HolInst.ofWordLangInst i)) (.locValue v label) = true)
    (_noShare : noShareInstSubprogsHOL (width := width) (.locValue v label) = true ∨ conf.isa ≠ .ag32)
    (_room : frame.1 + 1 < conf.regCount - conf.avoidRegs.length)
    (_minimum : 4 < frame.1) :
    stackAsmName conf (compNative conf perf (.locValue v label) bs frame).1 := by
  subst perf
  simp only [compNative, writeNameEquation, stackAsmName]

/-- Complete original Install naming case, with all seven source guards and
actual compiler output. Full naming assembly remains separate open work. -/
@[hol "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml"
  "word_to_stack_stack_asm_name_lem" (words_as_type_indexed_bitvec)]
theorem wordToStackStackAsmNameInstall {width : Nat} [NeZero width]
    (conf : AsmConfigExact width) (perf : Bool) (r1 r2 r3 r4 : Nat) (live : WordLangCutsetsHOL)
    (bs : AppList (BitVec width) × Nat) (frame : Nat × Nat × Nat)
    (plain : perf = false)
    (_conventions : @postAllocConventionsHOL width _ frame.1 (.install r1 r2 r3 r4 live) = true)
    (_valid : fullInstOkLessExact conf (.install r1 r2 r3 r4 live) = true)
    (_twoReg : conf.twoRegArith = true →
      everyInst (fun (i : WordLangInst (BitVec width)) => twoRegInstExact (HolInst.ofWordLangInst i)) (.install r1 r2 r3 r4 live) = true)
    (_noShare : noShareInstSubprogsHOL (width := width) (.install r1 r2 r3 r4 live) = true ∨ conf.isa ≠ .ag32)
    (_room : frame.1 + 1 < conf.regCount - conf.avoidRegs.length)
    (_minimum : 4 < frame.1) :
    stackAsmName conf (compNative conf perf (.install r1 r2 r3 r4 live) bs frame).1 := by
  subst perf
  have convention := _conventions
  simp only [postAllocConventionsHOL, Bool.and_eq_true] at convention
  have calls := convention.2.2
  simp only [callArgConventionHOL, Bool.and_eq_true, beq_iff_eq] at calls
  all_goals simp only [compNative, wReg1, wReg2]
  all_goals try split_ifs
  all_goals try simp only [loadName, stackAsmName, List.append_nil, List.nil_append, List.cons_append]

/-- Complete original CodeBufferWrite naming case, with all seven source guards and
actual compiler output. Full naming assembly remains separate open work. -/
@[hol "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml"
  "word_to_stack_stack_asm_name_lem" (words_as_type_indexed_bitvec)]
theorem wordToStackStackAsmNameCodeBufferWrite {width : Nat} [NeZero width]
    (conf : AsmConfigExact width) (perf : Bool) (r1 r2 : Nat)
    (bs : AppList (BitVec width) × Nat) (frame : Nat × Nat × Nat)
    (plain : perf = false)
    (_conventions : @postAllocConventionsHOL width _ frame.1 (.codeBufferWrite r1 r2) = true)
    (_valid : fullInstOkLessExact conf (.codeBufferWrite r1 r2) = true)
    (_twoReg : conf.twoRegArith = true →
      everyInst (fun (i : WordLangInst (BitVec width)) => twoRegInstExact (HolInst.ofWordLangInst i)) (.codeBufferWrite r1 r2) = true)
    (_noShare : noShareInstSubprogsHOL (width := width) (.codeBufferWrite r1 r2) = true ∨ conf.isa ≠ .ag32)
    (_room : frame.1 + 1 < conf.regCount - conf.avoidRegs.length)
    (_minimum : 4 < frame.1) :
    stackAsmName conf (compNative conf perf (.codeBufferWrite r1 r2) bs frame).1 := by
  subst perf
  all_goals simp only [compNative, wReg1, wReg2]
  all_goals try split_ifs
  all_goals try simp only [loadName, stackAsmName, regName, List.append_nil, List.nil_append, List.cons_append]
  all_goals repeat' apply And.intro
  all_goals first | trivial | omega

/-- Complete original DataBufferWrite naming case, with all seven source guards and
actual compiler output. Full naming assembly remains separate open work. -/
@[hol "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml"
  "word_to_stack_stack_asm_name_lem" (words_as_type_indexed_bitvec)]
theorem wordToStackStackAsmNameDataBufferWrite {width : Nat} [NeZero width]
    (conf : AsmConfigExact width) (perf : Bool) (r1 r2 : Nat)
    (bs : AppList (BitVec width) × Nat) (frame : Nat × Nat × Nat)
    (plain : perf = false)
    (_conventions : @postAllocConventionsHOL width _ frame.1 (.dataBufferWrite r1 r2) = true)
    (_valid : fullInstOkLessExact conf (.dataBufferWrite r1 r2) = true)
    (_twoReg : conf.twoRegArith = true →
      everyInst (fun (i : WordLangInst (BitVec width)) => twoRegInstExact (HolInst.ofWordLangInst i)) (.dataBufferWrite r1 r2) = true)
    (_noShare : noShareInstSubprogsHOL (width := width) (.dataBufferWrite r1 r2) = true ∨ conf.isa ≠ .ag32)
    (_room : frame.1 + 1 < conf.regCount - conf.avoidRegs.length)
    (_minimum : 4 < frame.1) :
    stackAsmName conf (compNative conf perf (.dataBufferWrite r1 r2) bs frame).1 := by
  subst perf
  all_goals simp only [compNative, wReg1, wReg2]
  all_goals try split_ifs
  all_goals try simp only [loadName, stackAsmName, regName, List.append_nil, List.nil_append, List.cons_append]
  all_goals repeat' apply And.intro
  all_goals first | trivial | omega

/-- Complete original Ffi naming case, with all seven source guards and
actual compiler output. Full naming assembly remains separate open work. -/
@[hol "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml"
  "word_to_stack_stack_asm_name_lem" (words_as_type_indexed_bitvec)]
theorem wordToStackStackAsmNameFfi {width : Nat} [NeZero width]
    (conf : AsmConfigExact width) (perf : Bool) (name : Basis.Pure.MlString.MlString) (r1 r2 r3 r4 : Nat) (live : WordLangCutsetsHOL)
    (bs : AppList (BitVec width) × Nat) (frame : Nat × Nat × Nat)
    (plain : perf = false)
    (_conventions : @postAllocConventionsHOL width _ frame.1 (.ffi name r1 r2 r3 r4 live) = true)
    (_valid : fullInstOkLessExact conf (.ffi name r1 r2 r3 r4 live) = true)
    (_twoReg : conf.twoRegArith = true →
      everyInst (fun (i : WordLangInst (BitVec width)) => twoRegInstExact (HolInst.ofWordLangInst i)) (.ffi name r1 r2 r3 r4 live) = true)
    (_noShare : noShareInstSubprogsHOL (width := width) (.ffi name r1 r2 r3 r4 live) = true ∨ conf.isa ≠ .ag32)
    (_room : frame.1 + 1 < conf.regCount - conf.avoidRegs.length)
    (_minimum : 4 < frame.1) :
    stackAsmName conf (compNative conf perf (.ffi name r1 r2 r3 r4 live) bs frame).1 := by
  subst perf
  simp only [compNative, stackAsmName]

end Flapjack.WordToStackProofs.AsmNameFlat
