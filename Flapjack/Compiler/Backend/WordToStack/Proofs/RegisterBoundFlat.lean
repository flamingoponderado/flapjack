import Flapjack.Compiler.Backend.WordToStack.Proofs.RegisterBoundInstructions

namespace Flapjack.WordToStackProofs.RegisterBoundFlat
open Flapjack Flapjack.Compiler.Backend.WordToStack.Native
open Flapjack.Compiler.Backend.StackLang Flapjack.Compiler.Backend.StackProps
open Flapjack.Compiler.Encoders.Asm
open Flapjack.Compiler.Backend.WordToStackRegFormat

/-- Internal source Move-case calculation on arbitrary formatted lists;
no standalone HOL theorem names this intermediate. -/
theorem formattedMovesBound {width : Nat} [NeZero width]
    (moves : List (Option Nat × Option Nat)) (frame : Nat × Nat × Nat) :
    regBound (wMoveAuxNative
      (moves.map (fun xy => (formatVar frame.1 xy.1, formatVar frame.1 xy.2))) frame :
      HolProg width) (frame.1 + 2) := by
  have single (xy : Option Nat × Option Nat) :
      regBound (wMoveSingleNative (formatVar frame.1 xy.1, formatVar frame.1 xy.2)
        frame : HolProg width) (frame.1 + 2) := by
    rcases xy with ⟨x,y⟩
    cases x <;> cases y <;> simp only [formatVar]
    all_goals try split_ifs
    all_goals simp only [wMoveSingleNative, regBound, regBoundInst]
    all_goals repeat' apply And.intro
    all_goals omega
  induction moves with
  | nil => trivial
  | cons xy rest ih =>
      cases rest with
      | nil => exact single xy
      | cons next tail =>
          simp only [List.map_cons, wMoveAuxNative, regBound]
          exact ⟨single xy, ih⟩

/-- Internal bitmap insertion bound from the original Alloc/Call calculation;
no separately named HOL theorem is claimed. -/
theorem liveBound {width : Nat} [NeZero width] (live : WordLangCutsetsHOL)
    (bs : AppList (BitVec width) × Nat) (frame : Nat × Nat × Nat) :
    regBound (wLiveNative live bs frame).1 (frame.1 + 2) := by
  simp only [wLiveNative]
  split <;> simp only [regBound, regBoundInst]
  all_goals constructor <;> omega

/-- Full original Skip case: all fields and all original guards retained. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem wordToStackRegBoundSkip {width : Nat} [NeZero width]
    (conf : AsmConfigExact width) (perf : Bool)
    (bs : AppList (BitVec width) × Nat) (frame : Nat × Nat × Nat)
    (_conventions : @postAllocConventionsHOL width _ frame.1 (.skip) = true)
    (_room : 4 ≤ frame.1) (plain : perf = false) :
    regBound (compNative conf perf (.skip) bs frame).1 (frame.1 + 2) := by
  subst perf
  simp only [compNative, regBound]

/-- Full original Move case: all fields and all original guards retained. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem wordToStackRegBoundMove {width : Nat} [NeZero width]
    (conf : AsmConfigExact width) (perf : Bool) (priority : Nat) (moves : List (Nat × Nat))
    (bs : AppList (BitVec width) × Nat) (frame : Nat × Nat × Nat)
    (_conventions : @postAllocConventionsHOL width _ frame.1 (.move priority moves) = true)
    (_room : 4 ≤ frame.1) (plain : perf = false) :
    regBound (compNative conf perf (.move priority moves) bs frame).1 (frame.1 + 2) := by
  subst perf
  simp only [compNative, wMoveNative]
  exact formattedMovesBound (width := width) _ frame

/-- Full original Assign case: all fields and all original guards retained. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem wordToStackRegBoundAssign {width : Nat} [NeZero width]
    (conf : AsmConfigExact width) (perf : Bool) (v : Nat) (exp : WordLangExpHOL (BitVec width))
    (bs : AppList (BitVec width) × Nat) (frame : Nat × Nat × Nat)
    (_conventions : @postAllocConventionsHOL width _ frame.1 (.assign v exp) = true)
    (_room : 4 ≤ frame.1) (plain : perf = false) :
    regBound (compNative conf perf (.assign v exp) bs frame).1 (frame.1 + 2) := by
  subst perf
  simp only [compNative, regBound]

/-- Full original Get case: all fields and all original guards retained. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem wordToStackRegBoundGet {width : Nat} [NeZero width]
    (conf : AsmConfigExact width) (perf : Bool) (v : Nat) (name : WordStoreHOL)
    (bs : AppList (BitVec width) × Nat) (frame : Nat × Nat × Nat)
    (_conventions : @postAllocConventionsHOL width _ frame.1 (.get v name) = true)
    (_room : 4 ≤ frame.1) (plain : perf = false) :
    regBound (compNative conf perf (.get v name) bs frame).1 (frame.1 + 2) := by
  subst perf
  all_goals simp only [compNative, wRegWrite1Native]
  all_goals try split_ifs
  all_goals try simp only [regBound]
  all_goals repeat' apply And.intro
  all_goals first | trivial | omega

/-- Full original Set case: all fields and all original guards retained. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem wordToStackRegBoundSet {width : Nat} [NeZero width]
    (conf : AsmConfigExact width) (perf : Bool) (name : WordStoreHOL) (exp : WordLangExpHOL (BitVec width))
    (bs : AppList (BitVec width) × Nat) (frame : Nat × Nat × Nat)
    (_conventions : @postAllocConventionsHOL width _ frame.1 (.set name exp) = true)
    (_room : 4 ≤ frame.1) (plain : perf = false) :
    regBound (compNative conf perf (.set name exp) bs frame).1 (frame.1 + 2) := by
  subst perf
  cases name <;> cases exp
  all_goals simp only [compNative, wReg1, regBound]
  all_goals try split_ifs
  all_goals try simp only [wStackLoadNative, regBound, storeNameOfWord]
  all_goals try simp only [ne_eq, reduceCtorEq, not_false_eq_true, and_true]
  all_goals repeat' apply And.intro
  all_goals first | trivial | omega

/-- Full original Store case: all fields and all original guards retained. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem wordToStackRegBoundStore {width : Nat} [NeZero width]
    (conf : AsmConfigExact width) (perf : Bool) (exp : WordLangExpHOL (BitVec width)) (v : Nat)
    (bs : AppList (BitVec width) × Nat) (frame : Nat × Nat × Nat)
    (_conventions : @postAllocConventionsHOL width _ frame.1 (.store exp v) = true)
    (_room : 4 ≤ frame.1) (plain : perf = false) :
    regBound (compNative conf perf (.store exp v) bs frame).1 (frame.1 + 2) := by
  subst perf
  simp only [compNative, regBound]

/-- Full original Alloc case: all fields and all original guards retained. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem wordToStackRegBoundAlloc {width : Nat} [NeZero width]
    (conf : AsmConfigExact width) (perf : Bool) (v : Nat) (live : WordLangCutsetsHOL)
    (bs : AppList (BitVec width) × Nat) (frame : Nat × Nat × Nat)
    (_conventions : @postAllocConventionsHOL width _ frame.1 (.alloc v live) = true)
    (_room : 4 ≤ frame.1) (plain : perf = false) :
    regBound (compNative conf perf (.alloc v live) bs frame).1 (frame.1 + 2) := by
  subst perf
  simp only [compNative, regBound]
  exact ⟨liveBound live bs frame, by trivial⟩

/-- Full original StoreConsts case: all fields and all original guards retained. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem wordToStackRegBoundStoreConsts {width : Nat} [NeZero width]
    (conf : AsmConfigExact width) (perf : Bool) (r1 r2 r3 r4 : Nat) (ws : List (Bool × BitVec width))
    (bs : AppList (BitVec width) × Nat) (frame : Nat × Nat × Nat)
    (_conventions : @postAllocConventionsHOL width _ frame.1 (.storeConsts r1 r2 r3 r4 ws) = true)
    (_room : 4 ≤ frame.1) (plain : perf = false) :
    regBound (compNative conf perf (.storeConsts r1 r2 r3 r4 ws) bs frame).1 (frame.1 + 2) := by
  subst perf
  simp only [compNative, regBound, regBoundInst]
  all_goals first | trivial | (constructor <;> omega)

/-- Full original Raise case: all fields and all original guards retained. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem wordToStackRegBoundRaise {width : Nat} [NeZero width]
    (conf : AsmConfigExact width) (perf : Bool) (v : Nat)
    (bs : AppList (BitVec width) × Nat) (frame : Nat × Nat × Nat)
    (_conventions : @postAllocConventionsHOL width _ frame.1 (.raise v) = true)
    (_room : 4 ≤ frame.1) (plain : perf = false) :
    regBound (compNative conf perf (.raise v) bs frame).1 (frame.1 + 2) := by
  subst perf
  simp only [compNative, regBound]
  all_goals first | trivial

/-- Full original Return case: all fields and all original guards retained. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem wordToStackRegBoundReturn {width : Nat} [NeZero width]
    (conf : AsmConfigExact width) (perf : Bool) (v : Nat) (vs : List Nat)
    (bs : AppList (BitVec width) × Nat) (frame : Nat × Nat × Nat)
    (_conventions : @postAllocConventionsHOL width _ frame.1 (.return v vs) = true)
    (_room : 4 ≤ frame.1) (plain : perf = false) :
    regBound (compNative conf perf (.return v vs) bs frame).1 (frame.1 + 2) := by
  subst perf
  all_goals simp only [compNative, wReg1, seqStackFreeNative]
  all_goals try split_ifs
  all_goals try simp only [wStackLoadNative, regBound]
  all_goals repeat' apply And.intro
  all_goals first | trivial | omega

/-- Full original Break case: all fields and all original guards retained. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem wordToStackRegBoundBreak {width : Nat} [NeZero width]
    (conf : AsmConfigExact width) (perf : Bool) (label : Nat)
    (bs : AppList (BitVec width) × Nat) (frame : Nat × Nat × Nat)
    (_conventions : @postAllocConventionsHOL width _ frame.1 (.break label) = true)
    (_room : 4 ≤ frame.1) (plain : perf = false) :
    regBound (compNative conf perf (.break label) bs frame).1 (frame.1 + 2) := by
  subst perf
  simp only [compNative, regBound]

/-- Full original Continue case: all fields and all original guards retained. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem wordToStackRegBoundContinue {width : Nat} [NeZero width]
    (conf : AsmConfigExact width) (perf : Bool) (label : Nat)
    (bs : AppList (BitVec width) × Nat) (frame : Nat × Nat × Nat)
    (_conventions : @postAllocConventionsHOL width _ frame.1 (.continue label) = true)
    (_room : 4 ≤ frame.1) (plain : perf = false) :
    regBound (compNative conf perf (.continue label) bs frame).1 (frame.1 + 2) := by
  subst perf
  simp only [compNative, regBound]

/-- Full original Tick case: all fields and all original guards retained. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem wordToStackRegBoundTick {width : Nat} [NeZero width]
    (conf : AsmConfigExact width) (perf : Bool)
    (bs : AppList (BitVec width) × Nat) (frame : Nat × Nat × Nat)
    (_conventions : @postAllocConventionsHOL width _ frame.1 (.tick) = true)
    (_room : 4 ≤ frame.1) (plain : perf = false) :
    regBound (compNative conf perf (.tick) bs frame).1 (frame.1 + 2) := by
  subst perf
  simp only [compNative, regBound]

/-- Full original OpCurrHeap case: all fields and all original guards retained. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem wordToStackRegBoundOpCurrHeap {width : Nat} [NeZero width]
    (conf : AsmConfigExact width) (perf : Bool) (op : BinOp) (v src : Nat)
    (bs : AppList (BitVec width) × Nat) (frame : Nat × Nat × Nat)
    (_conventions : @postAllocConventionsHOL width _ frame.1 (.opCurrHeap op v src) = true)
    (_room : 4 ≤ frame.1) (plain : perf = false) :
    regBound (compNative conf perf (.opCurrHeap op v src) bs frame).1 (frame.1 + 2) := by
  subst perf
  all_goals simp only [compNative, wRegWrite1Native, wReg1]
  all_goals try split_ifs
  all_goals try simp only [wStackLoadNative, regBound]
  all_goals repeat' apply And.intro
  all_goals first | trivial | omega

/-- Full original LocValue case: all fields and all original guards retained. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem wordToStackRegBoundLocValue {width : Nat} [NeZero width]
    (conf : AsmConfigExact width) (perf : Bool) (v label : Nat)
    (bs : AppList (BitVec width) × Nat) (frame : Nat × Nat × Nat)
    (_conventions : @postAllocConventionsHOL width _ frame.1 (.locValue v label) = true)
    (_room : 4 ≤ frame.1) (plain : perf = false) :
    regBound (compNative conf perf (.locValue v label) bs frame).1 (frame.1 + 2) := by
  subst perf
  all_goals simp only [compNative, wRegWrite1Native]
  all_goals try split_ifs
  all_goals try simp only [regBound]
  all_goals repeat' apply And.intro
  all_goals first | trivial | omega

/-- Full original Install case: all fields and all original guards retained. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem wordToStackRegBoundInstall {width : Nat} [NeZero width]
    (conf : AsmConfigExact width) (perf : Bool) (r1 r2 r3 r4 : Nat) (live : WordLangCutsetsHOL)
    (bs : AppList (BitVec width) × Nat) (frame : Nat × Nat × Nat)
    (_conventions : @postAllocConventionsHOL width _ frame.1 (.install r1 r2 r3 r4 live) = true)
    (_room : 4 ≤ frame.1) (plain : perf = false) :
    regBound (compNative conf perf (.install r1 r2 r3 r4 live) bs frame).1 (frame.1 + 2) := by
  subst perf
  have convention := _conventions
  simp only [postAllocConventionsHOL, Bool.and_eq_true] at convention
  have calls := convention.2.2
  simp only [callArgConventionHOL, Bool.and_eq_true, beq_iff_eq] at calls
  all_goals simp only [compNative, wReg1, wReg2]
  all_goals try split_ifs
  all_goals try simp only [wStackLoadNative, regBound, List.append_nil, List.nil_append, List.cons_append]
  all_goals repeat' apply And.intro
  all_goals first | trivial | omega

/-- Full original CodeBufferWrite case: all fields and all original guards retained. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem wordToStackRegBoundCodeBufferWrite {width : Nat} [NeZero width]
    (conf : AsmConfigExact width) (perf : Bool) (r1 r2 : Nat)
    (bs : AppList (BitVec width) × Nat) (frame : Nat × Nat × Nat)
    (_conventions : @postAllocConventionsHOL width _ frame.1 (.codeBufferWrite r1 r2) = true)
    (_room : 4 ≤ frame.1) (plain : perf = false) :
    regBound (compNative conf perf (.codeBufferWrite r1 r2) bs frame).1 (frame.1 + 2) := by
  subst perf
  all_goals simp only [compNative, wReg1, wReg2]
  all_goals try split_ifs
  all_goals try simp only [wStackLoadNative, regBound, List.append_nil, List.nil_append, List.cons_append]
  all_goals repeat' apply And.intro
  all_goals first | trivial | omega

/-- Full original DataBufferWrite case: all fields and all original guards retained. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem wordToStackRegBoundDataBufferWrite {width : Nat} [NeZero width]
    (conf : AsmConfigExact width) (perf : Bool) (r1 r2 : Nat)
    (bs : AppList (BitVec width) × Nat) (frame : Nat × Nat × Nat)
    (_conventions : @postAllocConventionsHOL width _ frame.1 (.dataBufferWrite r1 r2) = true)
    (_room : 4 ≤ frame.1) (plain : perf = false) :
    regBound (compNative conf perf (.dataBufferWrite r1 r2) bs frame).1 (frame.1 + 2) := by
  subst perf
  all_goals simp only [compNative, wReg1, wReg2]
  all_goals try split_ifs
  all_goals try simp only [wStackLoadNative, regBound, List.append_nil, List.nil_append, List.cons_append]
  all_goals repeat' apply And.intro
  all_goals first | trivial | omega

/-- Full original Ffi case: all fields and all original guards retained. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem wordToStackRegBoundFfi {width : Nat} [NeZero width]
    (conf : AsmConfigExact width) (perf : Bool) (name : Basis.Pure.MlString.MlString) (r1 r2 r3 r4 : Nat) (live : WordLangCutsetsHOL)
    (bs : AppList (BitVec width) × Nat) (frame : Nat × Nat × Nat)
    (_conventions : @postAllocConventionsHOL width _ frame.1 (.ffi name r1 r2 r3 r4 live) = true)
    (_room : 4 ≤ frame.1) (plain : perf = false) :
    regBound (compNative conf perf (.ffi name r1 r2 r3 r4 live) bs frame).1 (frame.1 + 2) := by
  subst perf
  have convention := _conventions
  simp only [postAllocConventionsHOL, Bool.and_eq_true] at convention
  have calls := convention.2.2
  simp only [callArgConventionHOL, Bool.and_eq_true, beq_iff_eq] at calls
  all_goals simp only [compNative, regBound]
  all_goals repeat' apply And.intro
  all_goals first | trivial | omega

end Flapjack.WordToStackProofs.RegisterBoundFlat
