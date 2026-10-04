import Flapjack.Compiler.Backend.Semantics.StackSem.StateOps
import Flapjack.Compiler.Backend.Semantics.WordSem.Env
import Flapjack.Misc.Option
import Mathlib.Tactic.SplitIfs

namespace Flapjack.WordToStackProofs
open Flapjack
namespace NativeStackAccessors
/-- Canonical roundtrip for the imported native StackSem carrier. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} [NeZero width] {C F : Type} :
    (∀ (s : StackSemStateBroad width C F) (h : s.FiniteSupport),
      (StackSemStateBroad.ofBroad s h).toBroad = s) ∧
    (∀ s : StackSemStateFiniteExact width C F,
      StackSemStateBroad.ofBroad s.toBroad s.toBroad_finiteSupport = s) :=
  StackSemStateSupport.holFmapAsFiniteSupportWitness

/-- Flapjack infrastructure: equality of canonical finite-support maps is
lookup extensionality; support proofs carry no observable information. -/
private theorem finiteMapEq {α β : Type} (m m' : HolFiniteMapExact α β)
    (h : ∀ k, m.lookup k = m'.lookup k) : m = m' := by
  cases m with
  | mk f hf =>
    cases m' with
    | mk g hg =>
      have he : f = g := funext h
      cases he
      rfl

/-- Flapjack infrastructure: canonical finite-support updates at distinct Nat
keys commute as whole maps, including arbitrary prior lookup functions. -/
private theorem updateSwap {α : Type} (m : HolFiniteMapExact Nat α)
    (a b : Nat) (x y : α) (h : a ≠ b) :
    (m.updateEq (b,y)).updateEq (a,x) = (m.updateEq (a,x)).updateEq (b,y) := by
  apply finiteMapEq
  intro k
  simp only [HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL]
  split_ifs <;> simp_all

/-- Flapjack infrastructure: a second canonical update at one Nat key shadows
the first as a whole finite-support map. -/
private theorem updateCancel {α : Type} (m : HolFiniteMapExact Nat α)
    (a : Nat) (x y : α) : (m.updateEq (a,y)).updateEq (a,x) = m.updateEq (a,x) := by
  apply finiteMapEq
  intro k
  simp only [HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL]
  split_ifs <;> rfl

/-- Full original StackSem distinct-key update commutation, as state equality. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem setVarSwap {width : Nat} [NeZero width] {C F : Type}
    (a a' : Nat) (b b' : WordLocW width) (s : StackSemStateFiniteExact width C F)
    (h : a ≠ a') :
    StackSemStateOps.setVar a b (StackSemStateOps.setVar a' b' s) =
      StackSemStateOps.setVar a' b' (StackSemStateOps.setVar a b s) := by
  simp only [StackSemStateOps.setVar, updateSwap _ _ _ _ _ h]

/-- Full original StackSem same-key shadowing, with no state premise. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem setVarCancel {width : Nat} [NeZero width] {C F : Type}
    (a : Nat) (b b' : WordLocW width) (s : StackSemStateFiniteExact width C F) :
    StackSemStateOps.setVar a b (StackSemStateOps.setVar a b' s) =
      StackSemStateOps.setVar a b s := by
  simp only [StackSemStateOps.setVar, updateCancel]

/-- Full original StackSem read after update at the same key. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem getVarSetVar {width : Nat} [NeZero width] {C F : Type}
    (k : Nat) (v : WordLocW width) (s : StackSemStateFiniteExact width C F) :
    StackSemStateOps.getVar k (StackSemStateOps.setVar k v s) = some v := by
  simp [StackSemStateOps.getVar, StackSemStateOps.setVar, FUPDATE_HOL]

/-- Full original clock self-update equality, preserving the whole state. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem stateWithConst {width : Nat} [NeZero width] {C F : Type}
    (s : StackSemStateFiniteExact width C F) : { s with clock := s.clock } = s := rfl

/-- Full original store/register update commutation, as whole state equality. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem setStoreSetVar {width : Nat} [NeZero width] {C F : Type}
    (a : WordStoreHOL) (b : WordLocW width) (c : Nat) (d : WordLocW width)
    (s : StackSemStateFiniteExact width C F) :
    StackSemStateOps.setStore a b (StackSemStateOps.setVar c d s) =
      StackSemStateOps.setVar c d (StackSemStateOps.setStore a b s) := rfl
end NativeStackAccessors

namespace NativeWordAccessors
open WordSemStateFiniteExact
/-- Every HOL type is inhabited. The native word constructor supplies that
logical fact for the existing option THE; this is neither a new NONE default
nor an executable choice, and all THE observations below are proved SOME. -/
local instance wordLocNonempty {width : Nat} [NeZero width] : Nonempty (WordLocW width) :=
  ⟨.word 0⟩
/-- Canonical roundtrip for the imported native WordSem carrier. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} [NeZero width] {C F : Type} :
    (∀ (s : WordSemStateBroad width C F) (h : s.FiniteSupport),
      (WordSemStateBroad.ofBroad s h).toBroad = s) ∧
    (∀ s : WordSemStateFiniteExact width C F,
      WordSemStateBroad.ofBroad s.toBroad s.toBroad_finiteSupport = s) :=
  WordSemStateExact.holFmapAsFiniteSupportWitness

/-- Full original WordSem distinct-key update commutation as whole state equality. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem setVarSwapWord {width : Nat} [NeZero width] {C F : Type}
    (a a' : Nat) (b b' : WordLocW width) (s : WordSemStateFiniteExact width C F)
    (h : a ≠ a') :
    setVar a b (setVar a' b' s) = setVar a' b' (setVar a b s) := by
  simp only [setVar, sptInsert_swap _ _ _ _ _ h]

/-- Full original WordSem same-key shadowing as whole state equality. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem setVarCancelWord {width : Nat} [NeZero width] {C F : Type}
    (a : Nat) (b b' : WordLocW width) (s : WordSemStateFiniteExact width C F) :
    setVar a b (setVar a b' s) = setVar a b s := by
  simp only [setVar, sptInsert_insert_shadow]

/-- Full original EVERY/read-success equivalence for arbitrary native states
and name lists, including duplicate names and empty reads. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem isSomeGetVarsEvery {width : Nat} [NeZero width] {C F : Type}
    (xs : List Nat) (s : WordSemStateFiniteExact width C F) :
    (WordSemStateFiniteExact.getVars xs s).isSome = true ↔
      ∀ x, x ∈ xs → (getVar x s).isSome = true := by
  induction xs with
  | nil => simp [WordSemStateFiniteExact.getVars]
  | cons n ns ih =>
    cases hv : getVar n s <;> cases ht : WordSemStateFiniteExact.getVars ns s <;>
      simp_all [WordSemStateFiniteExact.getVars]

/-- Full original read-success preservation after any native variable update.
No desired output values or environment relation is assumed. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem isSomeGetVarsSetVar {width : Nat} [NeZero width] {C F : Type}
    (ls : List Nat) (s : WordSemStateFiniteExact width C F) (k : Nat) (v : WordLocW width)
    (h : (WordSemStateFiniteExact.getVars ls s).isSome = true) :
    (WordSemStateFiniteExact.getVars ls (setVar k v s)).isSome = true := by
  rw [isSomeGetVarsEvery] at h ⊢
  intro x hx
  by_cases he : x = k
  · subst x
    simp [getVar, setVar, sptLookup_sptInsert_same]
  · simpa [getVar, setVar, sptLookup_sptInsert_ne _ _ _ _ he] using h x hx

/-- Full original successful-read decomposition: every lookup succeeds and
all returned values equal MAP THE of those actual lookups. The existing
option THE is only rewritten on SOME, never evaluated at NONE. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem getVarsEq {width : Nat} [NeZero width] {C F : Type}
    (ls : List Nat) (st : WordSemStateFiniteExact width C F) (z : List (WordLocW width))
    (h : WordSemStateFiniteExact.getVars ls st = some z) :
    let lookups := ls.map (fun x => sptLookup x st.locals)
    (∀ v, v ∈ lookups → v.isSome = true) ∧ z = lookups.map holThe := by
  induction ls generalizing z with
  | nil => simp [WordSemStateFiniteExact.getVars] at h; subst z; simp
  | cons n ns ih =>
    cases hv : getVar n st with
    | none => simp [WordSemStateFiniteExact.getVars, hv] at h
    | some v =>
      cases ht : WordSemStateFiniteExact.getVars ns st with
      | none => simp [WordSemStateFiniteExact.getVars, hv, ht] at h
      | some vs =>
        simp only [WordSemStateFiniteExact.getVars, hv, ht, Option.some.injEq] at h
        subst z
        have hi := ih vs ht
        simp only [getVar] at hv
        simpa [hv, holThe] using hi

/-- Full original successful pop preserves the entire FFI field, for both
plain and handler frames. Source/target state success is the sole premise. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem popEnvFfi {width : Nat} [NeZero width] {C F : Type}
    (s s' : WordSemStateFiniteExact width C F) (h : popEnv s = some s') :
    s.ffi = s'.ffi := by
  unfold popEnv at h
  split at h
  · cases h; rfl
  · cases h; rfl
  · cases h
end NativeWordAccessors
end Flapjack.WordToStackProofs
