import Flapjack.Compiler.Backend.Semantics.StackSem.ShMem

/-! Full original StackProps shared-memory clock commutation. Every result
and state is retained, including errors, terminal FFI and successful loads.
There is no successful-execution or domain premise. -/
namespace Flapjack.StackPropsSharedMemoryClock
open StackSemShMem StackSemStateOps

/-- Canonical imported-state roundtrip; Flapjack representation infrastructure. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : StackSemStateBroad width C F) (h : state.FiniteSupport),
        (StackSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : StackSemStateFiniteExact width C F,
        StackSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  StackSemShMemSupport.holFmapAsFiniteSupportWitness

/-- Full original clock-update commutation, with arbitrary native state. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem shMemLoadWithClock {width : Nat} [NeZero width] {C F : Type}
    (r : Nat) (a : BitVec width) (s : StackSemStateFiniteExact width C F) (k : Nat) :
    shMemLoad r a { s with clock := k } =
      Prod.map id (fun s => { s with clock := k }) (shMemLoad r a s) := by
  simp only [shMemLoad]
  repeat' first | split | simp_all

/-- Full original clock-update commutation, with arbitrary native state. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem shMemStoreWithClock {width : Nat} [NeZero width] {C F : Type}
    (r : Nat) (a : BitVec width) (s : StackSemStateFiniteExact width C F) (k : Nat) :
    shMemStore r a { s with clock := k } =
      Prod.map id (fun s => { s with clock := k }) (shMemStore r a s) := by
  simp only [shMemStore, getVar]
  repeat' first | split | simp_all

/-- Full original clock-update commutation, with arbitrary native state. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem shMemLoad32WithClock {width : Nat} [NeZero width] {C F : Type}
    (r : Nat) (a : BitVec width) (s : StackSemStateFiniteExact width C F) (k : Nat) :
    shMemLoad32 r a { s with clock := k } =
      Prod.map id (fun s => { s with clock := k }) (shMemLoad32 r a s) := by
  simp only [shMemLoad32]
  repeat' first | split | simp_all

/-- Full original clock-update commutation, with arbitrary native state. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem shMemStore32WithClock {width : Nat} [NeZero width] {C F : Type}
    (r : Nat) (a : BitVec width) (s : StackSemStateFiniteExact width C F) (k : Nat) :
    shMemStore32 r a { s with clock := k } =
      Prod.map id (fun s => { s with clock := k }) (shMemStore32 r a s) := by
  simp only [shMemStore32, getVar]
  repeat' first | split | simp_all

/-- Full original clock-update commutation, with arbitrary native state. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem shMemLoad16WithClock {width : Nat} [NeZero width] {C F : Type}
    (r : Nat) (a : BitVec width) (s : StackSemStateFiniteExact width C F) (k : Nat) :
    shMemLoad16 r a { s with clock := k } =
      Prod.map id (fun s => { s with clock := k }) (shMemLoad16 r a s) := by
  simp only [shMemLoad16]
  repeat' first | split | simp_all

/-- Full original clock-update commutation, with arbitrary native state. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem shMemStore16WithClock {width : Nat} [NeZero width] {C F : Type}
    (r : Nat) (a : BitVec width) (s : StackSemStateFiniteExact width C F) (k : Nat) :
    shMemStore16 r a { s with clock := k } =
      Prod.map id (fun s => { s with clock := k }) (shMemStore16 r a s) := by
  simp only [shMemStore16, getVar]
  repeat' first | split | simp_all

/-- Full original clock-update commutation, with arbitrary native state. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem shMemLoadByteWithClock {width : Nat} [NeZero width] {C F : Type}
    (r : Nat) (a : BitVec width) (s : StackSemStateFiniteExact width C F) (k : Nat) :
    shMemLoadByte r a { s with clock := k } =
      Prod.map id (fun s => { s with clock := k }) (shMemLoadByte r a s) := by
  simp only [shMemLoadByte]
  repeat' first | split | simp_all

/-- Full original clock-update commutation, with arbitrary native state. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem shMemStoreByteWithClock {width : Nat} [NeZero width] {C F : Type}
    (r : Nat) (a : BitVec width) (s : StackSemStateFiniteExact width C F) (k : Nat) :
    shMemStoreByte r a { s with clock := k } =
      Prod.map id (fun s => { s with clock := k }) (shMemStoreByte r a s) := by
  simp only [shMemStoreByte, getVar]
  repeat' first | split | simp_all

/-- Full original eight-operator dispatch clock commutation. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem shMemOpWithClock {width : Nat} [NeZero width] {C F : Type}
    (op : WordMemOp) (r : Nat) (a : BitVec width)
    (s : StackSemStateFiniteExact width C F) (k : Nat) :
    shMemOp op r a { s with clock := k } =
      Prod.map id (fun s => { s with clock := k }) (shMemOp op r a s) := by
  cases op <;> simp only [shMemOp, shMemLoadWithClock, shMemStoreWithClock,
    shMemLoadByteWithClock, shMemStoreByteWithClock, shMemLoad16WithClock,
    shMemStore16WithClock, shMemLoad32WithClock, shMemStore32WithClock]

/-- Full original sh_mem_op_const: all twelve preserved fields, including
arbitrary memory-domain/compile/GC functions. The only premise is the original
input helper evaluation, and every success, final or error result is allowed. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem shMemOpConst {width : Nat} [NeZero width] {C F : Type}
    (op : WordMemOp) (r : Nat) (a : BitVec width)
    (s t : StackSemStateFiniteExact width C F) (res : Option (StackSemResult width))
    (h : shMemOp op r a s = (res, t)) :
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
    t.compileOracle = s.compileOracle := by
  cases op <;> simp only [shMemOp, shMemLoad, shMemStore, shMemLoadByte,
    shMemStoreByte, shMemLoad16, shMemStore16, shMemLoad32, shMemStore32, getVar] at h
  all_goals repeat' first | split at h | simp_all
  all_goals rcases h with ⟨_, rfl⟩ <;> simp

end Flapjack.StackPropsSharedMemoryClock
