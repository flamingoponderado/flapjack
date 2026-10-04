import Flapjack.Compiler.Backend.Semantics.StackSem.State

/-! HOL StackSem state primitives. All operations use the accepted owning state
carrier; finite-support maps have canonical lookup/update semantics. No local
state duplicate, evaluator, or executed compiler refinement is introduced. -/

namespace Flapjack.StackSemStateOps

/-- Same-module re-export of the canonical state roundtrip; infrastructure. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : StackSemStateBroad width C F) (h : state.FiniteSupport),
        (StackSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : StackSemStateFiniteExact width C F,
        StackSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  StackSemStateSupport.holFmapAsFiniteSupportWitness

/-- Flapjack-only shared restriction of canonical finite-support maps by the
    executable Bool mask used by StackSem's saved-register field. Its lookup
    equation follows the original FLOOKUP_DRESTRICT1127-1131, but this is
    infrastructure for the two untagged clause fragments, not a tagged port
    of generic HOL set restriction. The result keeps the original support
    witness because every surviving binding was already in the input map. -/
def restrictIn {α β : Type} (m : HolFiniteMapExact α β) (keep : α → Bool) :
    HolFiniteMapExact α β where
  lookup key := if keep key then m.lookup key else none
  finiteSupport := by
    obtain ⟨keys, hkeys⟩ := m.finiteSupport
    refine ⟨keys, ?_⟩
    intro key hkey
    apply hkeys key
    by_cases h : keep key
    · simpa [h] using hkey
    · simp [h] at hkey

/-- Flapjack lookup equation for the shared saved-register mask operation. -/
theorem restrictIn_lookup {α β : Type} (m : HolFiniteMapExact α β)
    (keep : α → Bool) (key : α) :
    (restrictIn m keep).lookup key = if keep key then m.lookup key else none := rfl

/-- HOL domain-checked memory update. Equality implements addr =+ value;
    the update preserves the domain and every other state field. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
def memStore {width : Nat} [NeZero width] {C F : Type}
    (addr : BitVec width) (value : WordLocW width) (s : StackSemStateFiniteExact width C F) : Option (StackSemStateFiniteExact width C F) :=
  if s.mdomain addr then some { s with memory := fun key => if key = addr then value else s.memory key } else none

/-- HOL state operation, preserving all fields except the source update. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
def memLoad {width : Nat} [NeZero width] {C F : Type}
    (addr : BitVec width) (s : StackSemStateFiniteExact width C F) : Option (WordLocW width) :=
  if s.mdomain addr then some (s.memory addr) else none

/-- HOL state operation, preserving all fields except the source update. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
def decClock {width : Nat} [NeZero width] {C F : Type}
    (s : StackSemStateFiniteExact width C F) : StackSemStateFiniteExact width C F :=
  { s with clock := s.clock - 1 }

/-- HOL state operation, preserving all fields except the source update. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
def getVar {width : Nat} [NeZero width] {C F : Type}
    (v : Nat) (s : StackSemStateFiniteExact width C F) : Option (WordLocW width) :=
  s.regs.lookup v

/-- HOL register/immediate lookup. Register lookup preserves Word and Loc
payloads; an immediate always becomes a Word without inspecting the state. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
def getVarImm {width : Nat} [NeZero width] {C F : Type}
    (value : WordRegImm (BitVec width))
    (s : StackSemStateFiniteExact width C F) : Option (WordLocW width) :=
  match value with
  | .reg name => getVar name s
  | .imm word => some (.word word)

/-- HOL state operation, preserving all fields except the source update. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
def getFpVar {width : Nat} [NeZero width] {C F : Type}
    (v : Nat) (s : StackSemStateFiniteExact width C F) : Option (BitVec 64) :=
  s.fpRegs.lookup v

/-- HOL state operation, preserving all fields except the source update. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
def setVar {width : Nat} [NeZero width] {C F : Type}
    (v : Nat) (x : WordLocW width) (s : StackSemStateFiniteExact width C F) : StackSemStateFiniteExact width C F :=
  { s with regs := s.regs.updateEq (v, x) }

/-- HOL state operation, preserving all fields except the source update. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
def setFpVar {width : Nat} [NeZero width] {C F : Type}
    (v : Nat) (x : BitVec 64) (s : StackSemStateFiniteExact width C F) : StackSemStateFiniteExact width C F :=
  { s with fpRegs := s.fpRegs.updateEq (v, x) }

/-- HOL state operation, preserving all fields except the source update. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
def setStore {width : Nat} [NeZero width] {C F : Type}
    (v : WordStoreHOL) (x : WordLocW width) (s : StackSemStateFiniteExact width C F) : StackSemStateFiniteExact width C F :=
  { s with store := s.store.updateEq (v, x) }

/-- HOL state operation, preserving all fields except the source update. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
def emptyEnv {width : Nat} [NeZero width] {C F : Type}
    (s : StackSemStateFiniteExact width C F) : StackSemStateFiniteExact width C F :=
  { s with regs := HolFiniteMapExact.empty, stack := [] }

/-- HOL register-list lookup: retain order and fail at the first missing key. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
def getVars {width : Nat} [NeZero width] {C F : Type}
    (vars : List Nat) (s : StackSemStateFiniteExact width C F) : Option (List (WordLocW width)) :=
  match vars with
  | [] => some []
  | v :: vs =>
      match getVar v s with
      | none => none
      | some x =>
          match getVars vs s with
          | none => none
          | some xs => some (x :: xs)

end Flapjack.StackSemStateOps
