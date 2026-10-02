import Flapjack.Compiler.Backend.StackProps.AllocationConstants

/-! Actual operation regressions paired with the full original 47-row
StackProps allocation-constants source probe. Generic untouched state fields
and arbitrary configuration/FFI hosts remain quantified. -/
namespace Flapjack.Test.StackPropsAllocationConstantsParity
set_option maxRecDepth 4096
open Flapjack StackSemAllocation StackSemStoreConsts StackPropsAllocationConstants

private def allocation {C F : Type} (s : StackSemStateFiniteExact 8 C F)
    (callback : WordSemGcFun 8) : StackSemStateFiniteExact 8 C F :=
  { s with
    stack := [.word 0]
    stackSpace := 0
    bitmaps := []
    regs := HolFiniteMapExact.empty.updateEq (9,.word 2)
    memory := fun _ => .word 0
    mdomain := fun _ => true
    store := ((HolFiniteMapExact.empty.updateEq (.allocSize,.word 4)).updateEq
      (.nextFree,.word 5)).updateEq (.triggerGC,.word 20)
    gcFun := callback }

private def copy {C F : Type} (s : StackSemStateFiniteExact 64 C F) :
    StackSemStateFiniteExact 64 C F :=
  { s with
    regs := (((((HolFiniteMapExact.empty.updateEq (0,.word 0xAA)).updateEq
      (1,.word 0)).updateEq (2,.word 0x100)).updateEq (3,.word 0x10)).updateEq
      (4,.word 0xDEAD)).updateEq (5,.word 0xBEEF)
    memory := fun _ => .word 0
    mdomain := fun _ => true
    bitmaps := [3,0x55]
    useAlloc := true }

/-- Flapjack regression abbreviation for the full original allocation fields. -/
private def AllocFrame {width : Nat} [NeZero width] {C F : Type}
    (s t : StackSemStateFiniteExact width C F) : Prop :=
    t.ffi=s.ffi ∧
    t.clock=s.clock ∧
    t.useAlloc=s.useAlloc ∧
    t.useStore=s.useStore ∧
    t.useStack=s.useStack ∧
    t.code=s.code ∧
    t.be=s.be ∧
    t.gcFun=s.gcFun ∧
    t.mdomain=s.mdomain ∧
    t.shMdomain=s.shMdomain ∧
    t.bitmaps=s.bitmaps ∧
    t.compile=s.compile ∧
    t.dataBuffer=s.dataBuffer ∧
    t.codeBuffer=s.codeBuffer ∧
    t.compileOracle=s.compileOracle
/-- Flapjack regression abbreviation for the full original constant-store fields. -/
private def StoreFrame {width : Nat} [NeZero width] {C F : Type}
    (s t : StackSemStateFiniteExact width C F) : Prop :=
    t.ffi=s.ffi ∧
    t.clock=s.clock ∧
    t.useAlloc=s.useAlloc ∧
    t.useStore=s.useStore ∧
    t.useStack=s.useStack ∧
    t.code=s.code ∧
    t.be=s.be ∧
    t.gcFun=s.gcFun ∧
    t.mdomain=s.mdomain ∧
    t.shMdomain=s.shMdomain ∧
    t.bitmaps=s.bitmaps ∧
    t.compile=s.compile ∧
    t.store=s.store ∧
    t.dataBuffer=s.dataBuffer ∧
    t.codeBuffer=s.codeBuffer ∧
    t.compileOracle=s.compileOracle

private def concreteCopyBase : StackSemStateFiniteExact 64 Nat Nat where
  regs := HolFiniteMapExact.empty
  fpRegs := HolFiniteMapExact.empty
  store := HolFiniteMapExact.empty
  stack := []
  stackSpace := 0
  memory := fun _ => .word 0
  mdomain := fun _ => true
  shMdomain := fun _ => false
  bitmaps := []
  compile := fun _ _ => none
  compileOracle := fun _ => (0, [], [])
  codeBuffer := { position := 0, buffer := [], spaceLeft := 0 }
  dataBuffer := { position := 0, buffer := [], spaceLeft := 0 }
  gcFun := fun _ => none
  useStack := false
  useStore := false
  useAlloc := true
  clock := 5
  code := .ln
  ffi := { oracle := fun _ _ _ _ => .final .diverged, ffiState := 0, ioEvents := [] }
  ffiSaveRegs := fun _ => false
  be := false

variable {C F : Type}
private def alloc_success_state (s : StackSemStateFiniteExact 8 C F) := allocation s (fun (wl,m,_,st) => some (wl,m,st))
example (s : StackSemStateFiniteExact 8 C F) : AllocFrame (alloc_success_state s) (alloc 10 (alloc_success_state s)).2 :=
  allocConst 10 (alloc_success_state s) (alloc 10 (alloc_success_state s)).2 (alloc 10 (alloc_success_state s)).1 rfl
example (s : StackSemStateFiniteExact 8 C F) : alloc 10 {alloc_success_state s with clock := 37} =
  Prod.map id (fun t => {t with clock := 37}) (alloc 10 (alloc_success_state s)) := allocWithClock 10 (alloc_success_state s) 37
example (s : StackSemStateFiniteExact 8 C F) : (alloc 10 (alloc_success_state s)).1 = none := by
  cbv
private def alloc_halt_state (s : StackSemStateFiniteExact 8 C F) := allocation s (fun (wl,m,_,st) => some (wl,m,st))
example (s : StackSemStateFiniteExact 8 C F) : AllocFrame (alloc_halt_state s) (alloc 16 (alloc_halt_state s)).2 :=
  allocConst 16 (alloc_halt_state s) (alloc 16 (alloc_halt_state s)).2 (alloc 16 (alloc_halt_state s)).1 rfl
example (s : StackSemStateFiniteExact 8 C F) : alloc 16 {alloc_halt_state s with clock := 37} =
  Prod.map id (fun t => {t with clock := 37}) (alloc 16 (alloc_halt_state s)) := allocWithClock 16 (alloc_halt_state s) 37
example (s : StackSemStateFiniteExact 8 C F) : (alloc 16 (alloc_halt_state s)).1 = some (.halt (.word 1)) := by cbv
private def alloc_gc_failure_state (s : StackSemStateFiniteExact 8 C F) := allocation s (fun _ => none)
example (s : StackSemStateFiniteExact 8 C F) : AllocFrame (alloc_gc_failure_state s) (alloc 10 (alloc_gc_failure_state s)).2 :=
  allocConst 10 (alloc_gc_failure_state s) (alloc 10 (alloc_gc_failure_state s)).2 (alloc 10 (alloc_gc_failure_state s)).1 rfl
example (s : StackSemStateFiniteExact 8 C F) : alloc 10 {alloc_gc_failure_state s with clock := 37} =
  Prod.map id (fun t => {t with clock := 37}) (alloc 10 (alloc_gc_failure_state s)) := allocWithClock 10 (alloc_gc_failure_state s) 37
example (s : StackSemStateFiniteExact 8 C F) : (alloc 10 (alloc_gc_failure_state s)).1 = some .error := by cbv
private def alloc_missing_state (s : StackSemStateFiniteExact 8 C F) := allocation s (fun (wl,m,_,_) => some (wl,m,HolFiniteMapExact.empty))
example (s : StackSemStateFiniteExact 8 C F) : AllocFrame (alloc_missing_state s) (alloc 10 (alloc_missing_state s)).2 :=
  allocConst 10 (alloc_missing_state s) (alloc 10 (alloc_missing_state s)).2 (alloc 10 (alloc_missing_state s)).1 rfl
example (s : StackSemStateFiniteExact 8 C F) : alloc 10 {alloc_missing_state s with clock := 37} =
  Prod.map id (fun t => {t with clock := 37}) (alloc 10 (alloc_missing_state s)) := allocWithClock 10 (alloc_missing_state s) 37
example (s : StackSemStateFiniteExact 8 C F) : (alloc 10 (alloc_missing_state s)).1 = some .error := by cbv
private def alloc_bad_amount_state (s : StackSemStateFiniteExact 8 C F) := allocation s (fun (wl,m,_,st) => some (wl,m,st.updateEq (.allocSize,.loc 1 0)))
example (s : StackSemStateFiniteExact 8 C F) : AllocFrame (alloc_bad_amount_state s) (alloc 10 (alloc_bad_amount_state s)).2 :=
  allocConst 10 (alloc_bad_amount_state s) (alloc 10 (alloc_bad_amount_state s)).2 (alloc 10 (alloc_bad_amount_state s)).1 rfl
example (s : StackSemStateFiniteExact 8 C F) : alloc 10 {alloc_bad_amount_state s with clock := 37} =
  Prod.map id (fun t => {t with clock := 37}) (alloc 10 (alloc_bad_amount_state s)) := allocWithClock 10 (alloc_bad_amount_state s) 37
example (s : StackSemStateFiniteExact 8 C F) : (alloc 10 (alloc_bad_amount_state s)).1 = some .error := by cbv
private def alloc_bad_space_state (s : StackSemStateFiniteExact 8 C F) := allocation s (fun (wl,m,_,_) => some (wl,m,(HolFiniteMapExact.empty.updateEq (.allocSize,.word 10)).updateEq (.triggerGC,.word 20)))
example (s : StackSemStateFiniteExact 8 C F) : AllocFrame (alloc_bad_space_state s) (alloc 10 (alloc_bad_space_state s)).2 :=
  allocConst 10 (alloc_bad_space_state s) (alloc 10 (alloc_bad_space_state s)).2 (alloc 10 (alloc_bad_space_state s)).1 rfl
example (s : StackSemStateFiniteExact 8 C F) : alloc 10 {alloc_bad_space_state s with clock := 37} =
  Prod.map id (fun t => {t with clock := 37}) (alloc 10 (alloc_bad_space_state s)) := allocWithClock 10 (alloc_bad_space_state s) 37
example (s : StackSemStateFiniteExact 8 C F) : (alloc 10 (alloc_bad_space_state s)).1 = some .error := by cbv
private def store_duplicate_state (s : StackSemStateFiniteExact 64 C F) := copy s
example (s : StackSemStateFiniteExact 64 C F) : StoreFrame (store_duplicate_state s) (storeConstSem (resultWidth := 8) 1 5 (store_duplicate_state s)).2 :=
  storeConstSemConst (resultWidth := 8) 1 5 (store_duplicate_state s) (storeConstSem (resultWidth := 8) 1 5 (store_duplicate_state s)).2 (storeConstSem (resultWidth := 8) 1 5 (store_duplicate_state s)).1 rfl
example (s : StackSemStateFiniteExact 64 C F) : storeConstSem (resultWidth := 8) 1 5 {store_duplicate_state s with clock := 37} =
  Prod.map id (fun t => {t with clock := 37}) (storeConstSem (resultWidth := 8) 1 5 (store_duplicate_state s)) := storeConstSemWithClock (resultWidth := 8) 1 5 (store_duplicate_state s) 37
example (s : StackSemStateFiniteExact 64 C F) : (storeConstSem (resultWidth := 8) 1 5 (store_duplicate_state s)).1 = some .error := by cbv
private def store_nonword_state (s : StackSemStateFiniteExact 64 C F) := {copy s with regs := (copy s).regs.updateEq (1,.loc 9 9)}
example (s : StackSemStateFiniteExact 64 C F) : StoreFrame (store_nonword_state s) (storeConstSem (resultWidth := 8) 4 5 (store_nonword_state s)).2 :=
  storeConstSemConst (resultWidth := 8) 4 5 (store_nonword_state s) (storeConstSem (resultWidth := 8) 4 5 (store_nonword_state s)).2 (storeConstSem (resultWidth := 8) 4 5 (store_nonword_state s)).1 rfl
example (s : StackSemStateFiniteExact 64 C F) : storeConstSem (resultWidth := 8) 4 5 {store_nonword_state s with clock := 37} =
  Prod.map id (fun t => {t with clock := 37}) (storeConstSem (resultWidth := 8) 4 5 (store_nonword_state s)) := storeConstSemWithClock (resultWidth := 8) 4 5 (store_nonword_state s) 37
example (s : StackSemStateFiniteExact 64 C F) : (storeConstSem (resultWidth := 8) 4 5 (store_nonword_state s)).1 = some .error := by cbv
private def store_copy_failure_state (s : StackSemStateFiniteExact 64 C F) := {copy s with bitmaps := []}
example (s : StackSemStateFiniteExact 64 C F) : StoreFrame (store_copy_failure_state s) (storeConstSem (resultWidth := 8) 4 5 (store_copy_failure_state s)).2 :=
  storeConstSemConst (resultWidth := 8) 4 5 (store_copy_failure_state s) (storeConstSem (resultWidth := 8) 4 5 (store_copy_failure_state s)).2 (storeConstSem (resultWidth := 8) 4 5 (store_copy_failure_state s)).1 rfl
example (s : StackSemStateFiniteExact 64 C F) : storeConstSem (resultWidth := 8) 4 5 {store_copy_failure_state s with clock := 37} =
  Prod.map id (fun t => {t with clock := 37}) (storeConstSem (resultWidth := 8) 4 5 (store_copy_failure_state s)) := storeConstSemWithClock (resultWidth := 8) 4 5 (store_copy_failure_state s) 37
example (s : StackSemStateFiniteExact 64 C F) : (storeConstSem (resultWidth := 8) 4 5 (store_copy_failure_state s)).1 = some .error := by cbv
private def store_success_alloc_state (s : StackSemStateFiniteExact 64 C F) := copy s
example (s : StackSemStateFiniteExact 64 C F) : StoreFrame (store_success_alloc_state s) (storeConstSem (resultWidth := 8) 4 5 (store_success_alloc_state s)).2 :=
  storeConstSemConst (resultWidth := 8) 4 5 (store_success_alloc_state s) (storeConstSem (resultWidth := 8) 4 5 (store_success_alloc_state s)).2 (storeConstSem (resultWidth := 8) 4 5 (store_success_alloc_state s)).1 rfl
example (s : StackSemStateFiniteExact 64 C F) : storeConstSem (resultWidth := 8) 4 5 {store_success_alloc_state s with clock := 37} =
  Prod.map id (fun t => {t with clock := 37}) (storeConstSem (resultWidth := 8) 4 5 (store_success_alloc_state s)) := storeConstSemWithClock (resultWidth := 8) 4 5 (store_success_alloc_state s) 37
example : (storeConstSem (resultWidth := 8) 4 5 (store_success_alloc_state concreteCopyBase)).1 = none := by decide +kernel
private def store_success_noalloc_state (s : StackSemStateFiniteExact 64 C F) := {copy s with useAlloc := false}
example (s : StackSemStateFiniteExact 64 C F) : StoreFrame (store_success_noalloc_state s) (storeConstSem (resultWidth := 8) 4 5 (store_success_noalloc_state s)).2 :=
  storeConstSemConst (resultWidth := 8) 4 5 (store_success_noalloc_state s) (storeConstSem (resultWidth := 8) 4 5 (store_success_noalloc_state s)).2 (storeConstSem (resultWidth := 8) 4 5 (store_success_noalloc_state s)).1 rfl
example (s : StackSemStateFiniteExact 64 C F) : storeConstSem (resultWidth := 8) 4 5 {store_success_noalloc_state s with clock := 37} =
  Prod.map id (fun t => {t with clock := 37}) (storeConstSem (resultWidth := 8) 4 5 (store_success_noalloc_state s)) := storeConstSemWithClock (resultWidth := 8) 4 5 (store_success_noalloc_state s) 37
example : (storeConstSem (resultWidth := 8) 4 5 (store_success_noalloc_state concreteCopyBase)).1 = none := by decide +kernel
example (s : StackSemStateFiniteExact 8 C F) : gc {alloc_success_state s with clock := 37} =
  (gc (alloc_success_state s)).map (fun t => {t with clock := 37}) := gcWithClock (alloc_success_state s) 37
example (s : StackSemStateFiniteExact 8 C F) : gc {alloc_gc_failure_state s with clock := 37} =
  (gc (alloc_gc_failure_state s)).map (fun t => {t with clock := 37}) := gcWithClock (alloc_gc_failure_state s) 37
example (s : StackSemStateFiniteExact 8 C F) : gc {alloc_missing_state s with clock := 37} =
  (gc (alloc_missing_state s)).map (fun t => {t with clock := 37}) := gcWithClock (alloc_missing_state s) 37
example (s : StackSemStateFiniteExact 8 C F) : gc {alloc_bad_amount_state s with clock := 37} =
  (gc (alloc_bad_amount_state s)).map (fun t => {t with clock := 37}) := gcWithClock (alloc_bad_amount_state s) 37

/-- Flapjack actual-operation regression with independent result/state dimensions. -/
example (s : StackSemStateFiniteExact 1 C F) :
    storeConstSem (resultWidth := 80) 1 5 s = (some .error,s) := by
  simp [storeConstSem]
/-- Flapjack actual-operation regression at the reversed dimensions. -/
example (s : StackSemStateFiniteExact 80 C F) :
    storeConstSem (resultWidth := 1) 1 5 s = (some .error,s) := by
  simp [storeConstSem]

def runChecks : IO Bool := do
  IO.println "PASS original allocation/constant-store full fields and clock (39 kernel applications/outcomes)"
  pure true
end Flapjack.Test.StackPropsAllocationConstantsParity
