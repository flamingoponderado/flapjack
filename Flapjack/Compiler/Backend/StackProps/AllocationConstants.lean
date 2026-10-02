import Flapjack.Compiler.Backend.Semantics.StackSem.Allocation
import Flapjack.Compiler.Backend.Semantics.StackSem.StoreConsts

/-! Full original allocation and bitmap-copy state preservation and clock
commutation. No successful-GC or memory-domain hypothesis is introduced. -/
namespace Flapjack.StackPropsAllocationConstants
open StackSemAllocation StackSemStoreConsts StackSemStateOps

/-- Canonical imported state roundtrip; Flapjack representation infrastructure. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : StackSemStateBroad width C F) (h : state.FiniteSupport),
        (StackSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : StackSemStateFiniteExact width C F,
        StackSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  StackSemStateSupport.holFmapAsFiniteSupportWitness

/-- Full original Option-map clock commutation, including every GC failure. -/
@[hol "cakeml/compiler/backend/semantics/stackPropsScript.sml" "gc_with_const"
  (fmap_as_finite_support := [regs, fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem gcWithClock {width : Nat} [NeZero width] {C F : Type}
    (s : StackSemStateFiniteExact width C F) (k : Nat) :
    gc { s with clock := k } = (gc s).map (fun s => { s with clock := k }) := by
  simp only [gc]
  repeat' first | split | simp_all

/-- Flapjack decomposition lemma for the actual GC record updates; no
separate original HOL theorem is claimed. Its returned-state premise is used
only to establish the original allocation preservation theorem below. -/
private theorem gcConst {width : Nat} [NeZero width] {C F : Type}
    (s t : StackSemStateFiniteExact width C F) (h : gc s = some t) :
    t.ffi = s.ffi ∧
    t.clock = s.clock ∧
    t.useAlloc = s.useAlloc ∧
    t.useStore = s.useStore ∧
    t.useStack = s.useStack ∧
    t.code = s.code ∧
    t.be = s.be ∧
    t.gcFun = s.gcFun ∧
    t.mdomain = s.mdomain ∧
    t.shMdomain = s.shMdomain ∧
    t.bitmaps = s.bitmaps ∧
    t.compile = s.compile ∧
    t.dataBuffer = s.dataBuffer ∧
    t.codeBuffer = s.codeBuffer ∧
    t.compileOracle = s.compileOracle := by
  simp only [gc] at h
  repeat' first | split at h | cases h | simp_all

/-- Full original fifteen-field allocation preservation, with the sole
original returned-pair equality premise. -/
@[hol "cakeml/compiler/backend/semantics/stackPropsScript.sml" "alloc_const"
  (fmap_as_finite_support := [regs, fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem allocConst {width : Nat} [NeZero width] {C F : Type}
    (w : BitVec width) (s t : StackSemStateFiniteExact width C F)
    (result : Option (StackSemResult width)) (h : alloc w s = (result,t)) :
    t.ffi = s.ffi ∧
    t.clock = s.clock ∧
    t.useAlloc = s.useAlloc ∧
    t.useStore = s.useStore ∧
    t.useStack = s.useStack ∧
    t.code = s.code ∧
    t.be = s.be ∧
    t.gcFun = s.gcFun ∧
    t.mdomain = s.mdomain ∧
    t.shMdomain = s.shMdomain ∧
    t.bitmaps = s.bitmaps ∧
    t.compile = s.compile ∧
    t.dataBuffer = s.dataBuffer ∧
    t.codeBuffer = s.codeBuffer ∧
    t.compileOracle = s.compileOracle := by
  cases hg : gc (setStore .allocSize (.word w) s) with
  | none =>
      simp only [alloc, hg, Prod.mk.injEq] at h
      rcases h with ⟨_, rfl⟩
      simp
  | some collected =>
      have frame := gcConst (setStore .allocSize (.word w) s) collected hg
      simp only [setStore] at frame
      simp only [alloc, hg] at h
      repeat' first | split at h | (simp only [Prod.mk.injEq] at h; rcases h with ⟨_, rfl⟩; simpa [emptyEnv] using frame)

/-- Full original sixteen-field constant-store preservation, including
all error outcomes and the optional register-zero removal. -/
@[hol "cakeml/compiler/backend/semantics/stackPropsScript.sml" "store_const_sem_const"
  (fmap_as_finite_support := [regs, fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem storeConstSemConst {width : Nat} {resultWidth : Nat}
    [NeZero width] [NeZero resultWidth] {C F : Type}
    (t1 t2 : Nat) (s t : StackSemStateFiniteExact width C F)
    (result : Option (StackSemResult resultWidth)) (h : storeConstSem t1 t2 s = (result,t)) :
    t.ffi = s.ffi ∧
    t.clock = s.clock ∧
    t.useAlloc = s.useAlloc ∧
    t.useStore = s.useStore ∧
    t.useStack = s.useStack ∧
    t.code = s.code ∧
    t.be = s.be ∧
    t.gcFun = s.gcFun ∧
    t.mdomain = s.mdomain ∧
    t.shMdomain = s.shMdomain ∧
    t.bitmaps = s.bitmaps ∧
    t.compile = s.compile ∧
    t.store = s.store ∧
    t.dataBuffer = s.dataBuffer ∧
    t.codeBuffer = s.codeBuffer ∧
    t.compileOracle = s.compileOracle := by
  simp only [storeConstSem] at h
  repeat' first | split at h | (simp only [Prod.mk.injEq] at h; rcases h with ⟨_, rfl⟩; simp [unsetVarZero, setVar])

/-- Full original allocation clock commutation, retaining result and state. -/
@[hol "cakeml/compiler/backend/semantics/stackPropsScript.sml" "alloc_with_const"
  (fmap_as_finite_support := [regs, fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem allocWithClock {width : Nat} [NeZero width] {C F : Type}
    (w : BitVec width) (s : StackSemStateFiniteExact width C F) (k : Nat) :
    alloc w { s with clock := k } =
      Prod.map id (fun s => { s with clock := k }) (alloc w s) := by
  simp only [alloc]
  rw [show setStore .allocSize (.word w) { s with clock := k } =
    { setStore .allocSize (.word w) s with clock := k } from rfl, gcWithClock]
  cases hg : gc (setStore .allocSize (.word w) s) <;> simp only [Option.map]
  · rfl
  · repeat' first | split | simp_all [emptyEnv]

/-- Full original constant-store clock commutation, without domain or
successful-copy assumptions. -/
@[hol "cakeml/compiler/backend/semantics/stackPropsScript.sml" "store_const_sem_with_const"
  (fmap_as_finite_support := [regs, fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem storeConstSemWithClock {width : Nat} {resultWidth : Nat}
    [NeZero width] [NeZero resultWidth] {C F : Type}
    (t1 t2 : Nat) (s : StackSemStateFiniteExact width C F) (k : Nat) :
    storeConstSem (resultWidth := resultWidth) t1 t2 { s with clock := k } =
      Prod.map id (fun s => { s with clock := k }) (storeConstSem t1 t2 s) := by
  simp only [storeConstSem, getVar]
  repeat' first | split | simp_all [unsetVarZero, setVar]

end Flapjack.StackPropsAllocationConstants
