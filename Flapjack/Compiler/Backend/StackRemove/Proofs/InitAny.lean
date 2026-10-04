import Flapjack.Compiler.Backend.StackRemove.Proofs.InitMake

/-! Field laws of the total initialized state, `stack_removeProofScript.sml`
(4100-4157).
-/

namespace Flapjack.Compiler.Backend.StackRemove.Proofs.InitAny
open Flapjack Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.StackRemove.Proofs.InitMake

/-- Canonical roundtrip for the imported actual state carrier; representation
infrastructure rather than an assumption about any initializer input. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : StackSemStateBroad width C F) (h : state.FiniteSupport),
      (StackSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : StackSemStateFiniteExact width C F,
      StackSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  Flapjack.StackSemStateOps.holFmapAsFiniteSupportWitness

/-- Flapjack proof factoring: a present optional initialized state is the
actual reduction of the initializer's normal post-state that satisfies the
original `init_prop`. No separate HOL declaration. -/
theorem makeInitOpt_eq_some {width : Nat} [NeZero width] {C F : Type}
    {generateGc : Bool} {maxHeap : Nat} {bitmaps : List (BitVec width)} {dataSpace : Nat}
    {oracle : Nat → C × List (Nat × HolProg width) × List (BitVec width)}
    {jump : Bool} {bounds : BitVec width × BitVec width} {pointer : Nat}
    {code : Spt (HolProg width)} {s t : StackSemStateFiniteExact width C F}
    (h : makeInitOpt generateGc maxHeap bitmaps dataSpace oracle jump bounds pointer code s =
      some t) :
    ∃ post, t = InitReduce.initReduce generateGc jump bounds pointer code bitmaps dataSpace
        oracle post ∧
      InitProp.initProp generateGc maxHeap dataSpace
        (InitLimits.getStackHeapLimit maxHeap (InitLimits.readPointers s)) t := by
  unfold makeInitOpt at h
  split at h
  · cases h
  · split at h
    · cases h
      exact ⟨_, rfl, by assumption⟩
    · cases h

/-- Complete original bitmap law: the supplied bitmaps on success and the
fallback `[4w]` otherwise. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem makeInitAnyBitmaps {width : Nat} [NeZero width] {C F : Type}
    (generateGc : Bool) (maxHeap : Nat) (bitmaps : List (BitVec width)) (dataSpace : Nat)
    (oracle : Nat → C × List (Nat × HolProg width) × List (BitVec width))
    (jump : Bool) (bounds : BitVec width × BitVec width) (pointer : Nat)
    (code : Spt (HolProg width)) (s : StackSemStateFiniteExact width C F) :
    (makeInitAny generateGc maxHeap bitmaps dataSpace oracle jump bounds pointer code s).bitmaps =
      if (makeInitOpt generateGc maxHeap bitmaps dataSpace oracle jump bounds pointer code
          s).isSome
      then bitmaps else [4] := by
  unfold makeInitAny
  cases h : makeInitOpt generateGc maxHeap bitmaps dataSpace oracle jump bounds pointer code s with
  | none => rfl
  | some t =>
    obtain ⟨post, rfl, _⟩ := makeInitOpt_eq_some h
    rfl

/-- Complete original law: the total initialized state uses the stack. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem makeInitAnyUseStack {width : Nat} [NeZero width] {C F : Type}
    (generateGc : Bool) (maxHeap : Nat) (bitmaps : List (BitVec width)) (dataSpace : Nat)
    (oracle : Nat → C × List (Nat × HolProg width) × List (BitVec width))
    (jump : Bool) (bounds : BitVec width × BitVec width) (pointer : Nat)
    (code : Spt (HolProg width)) (s : StackSemStateFiniteExact width C F) :
    (makeInitAny generateGc maxHeap bitmaps dataSpace oracle jump bounds pointer code
      s).useStack = true := by
  unfold makeInitAny
  cases h : makeInitOpt generateGc maxHeap bitmaps dataSpace oracle jump bounds pointer code s with
  | none => rfl
  | some t =>
    obtain ⟨post, rfl, _⟩ := makeInitOpt_eq_some h
    rfl

/-- Complete original law: the total initialized state uses the store. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem makeInitAnyUseStore {width : Nat} [NeZero width] {C F : Type}
    (generateGc : Bool) (maxHeap : Nat) (bitmaps : List (BitVec width)) (dataSpace : Nat)
    (oracle : Nat → C × List (Nat × HolProg width) × List (BitVec width))
    (jump : Bool) (bounds : BitVec width × BitVec width) (pointer : Nat)
    (code : Spt (HolProg width)) (s : StackSemStateFiniteExact width C F) :
    (makeInitAny generateGc maxHeap bitmaps dataSpace oracle jump bounds pointer code
      s).useStore = true := by
  unfold makeInitAny
  cases h : makeInitOpt generateGc maxHeap bitmaps dataSpace oracle jump bounds pointer code s with
  | none => rfl
  | some t =>
    obtain ⟨post, rfl, _⟩ := makeInitOpt_eq_some h
    rfl

/-- Complete original law: the total initialized state disables allocation. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem makeInitAnyUseAlloc {width : Nat} [NeZero width] {C F : Type}
    (generateGc : Bool) (maxHeap : Nat) (bitmaps : List (BitVec width)) (dataSpace : Nat)
    (oracle : Nat → C × List (Nat × HolProg width) × List (BitVec width))
    (jump : Bool) (bounds : BitVec width × BitVec width) (pointer : Nat)
    (code : Spt (HolProg width)) (s : StackSemStateFiniteExact width C F) :
    ¬ (makeInitAny generateGc maxHeap bitmaps dataSpace oracle jump bounds pointer code
      s).useAlloc = true := by
  unfold makeInitAny
  cases h : makeInitOpt generateGc maxHeap bitmaps dataSpace oracle jump bounds pointer code s with
  | none => simp
  | some t =>
    obtain ⟨post, rfl, _⟩ := makeInitOpt_eq_some h
    simp [InitReduce.initReduce]

/-- Complete original law: the total initialized state carries the supplied
code. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem makeInitAnyCode {width : Nat} [NeZero width] {C F : Type}
    (generateGc : Bool) (maxHeap : Nat) (bitmaps : List (BitVec width)) (dataSpace : Nat)
    (oracle : Nat → C × List (Nat × HolProg width) × List (BitVec width))
    (jump : Bool) (bounds : BitVec width × BitVec width) (pointer : Nat)
    (code : Spt (HolProg width)) (s : StackSemStateFiniteExact width C F) :
    (makeInitAny generateGc maxHeap bitmaps dataSpace oracle jump bounds pointer code
      s).code = code := by
  unfold makeInitAny
  cases h : makeInitOpt generateGc maxHeap bitmaps dataSpace oracle jump bounds pointer code s with
  | none => rfl
  | some t =>
    obtain ⟨post, rfl, _⟩ := makeInitOpt_eq_some h
    rfl

/-- Complete original law: the total initialized state carries the supplied
compile oracle. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem makeInitAnyCompileOracle {width : Nat} [NeZero width] {C F : Type}
    (ggc : Bool) (maxHeap : Nat) (bitmaps : List (BitVec width)) (dataSpace : Nat)
    (oracle : Nat → C × List (Nat × HolProg width) × List (BitVec width))
    (jump : Bool) (bounds : BitVec width × BitVec width) (pointer : Nat)
    (code : Spt (HolProg width)) (s : StackSemStateFiniteExact width C F) :
    (makeInitAny ggc maxHeap bitmaps dataSpace oracle jump bounds pointer code
      s).compileOracle = oracle := by
  unfold makeInitAny
  cases h : makeInitOpt ggc maxHeap bitmaps dataSpace oracle jump bounds pointer code s with
  | none => rfl
  | some t =>
    obtain ⟨post, rfl, _⟩ := makeInitOpt_eq_some h
    rfl

/-- Complete original stack bound of the total initialized state: on success
it is the original `init_prop` conjunct, and the fallback stack has one word. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem makeInitAnyStackLimit {width : Nat} [NeZero width] {C F : Type}
    (generateGc : Bool) (maxHeap : Nat) (bitmaps : List (BitVec width)) (dataSpace : Nat)
    (oracle : Nat → C × List (Nat × HolProg width) × List (BitVec width))
    (jump : Bool) (bounds : BitVec width × BitVec width) (pointer : Nat)
    (code : Spt (HolProg width)) (s : StackSemStateFiniteExact width C F) :
    (makeInitAny generateGc maxHeap bitmaps dataSpace oracle jump bounds pointer code
      s).stack.length * (width / 8) < 2 ^ width := by
  unfold makeInitAny
  cases h : makeInitOpt generateGc maxHeap bitmaps dataSpace oracle jump bounds pointer code s with
  | none =>
    show 1 * (width / 8) < 2 ^ width
    have : width < 2 ^ width := Nat.lt_two_pow_self
    omega
  | some t =>
    obtain ⟨_, _, prop⟩ := makeInitOpt_eq_some h
    obtain ⟨_, _, _, _, rest⟩ := prop
    show t.stack.length * (width / 8) < 2 ^ width
    repeat (first | exact rest.1 | replace rest := rest.2)

end Flapjack.Compiler.Backend.StackRemove.Proofs.InitAny
