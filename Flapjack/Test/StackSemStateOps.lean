import Flapjack.Compiler.Backend.Semantics.StackSem.StateOps

/-! Flapjack-specific kernel checks of the ported state primitives, including
non-Word values, missing registers and preservation of unrelated state fields.
These are infrastructure checks, not separate HOL theorem ports. -/
open Flapjack Flapjack.StackSemStateOps
variable {width : Nat} [NeZero width] {C F : Type}
variable (s : StackSemStateFiniteExact width C F)

example (addr : BitVec width) (h : s.mdomain addr = false) : memLoad addr s = none := by
  simp [memLoad, h]
example (addr : BitVec width) (h : s.mdomain addr = true) : memLoad addr s = some (s.memory addr) := by
  simp [memLoad, h]
example (addr : BitVec width) (x : WordLocW width) (h : s.mdomain addr = false) : memStore addr x s = none := by
  simp [memStore, h]
example (addr : BitVec width) (x : WordLocW width) (h : s.mdomain addr = true) :
    (memStore addr x s).map (fun t => (t.memory addr, t.mdomain, t.regs, t.clock)) =
      some (x, s.mdomain, s.regs, s.clock) := by
  simp [memStore, h]
example (v : Nat) (x : WordLocW width) : getVar v (setVar v x s) = some x := by
  simp [getVar, setVar, HolFiniteMapExact.updateEq, FUPDATE_HOL]
example (v : Nat) (x : BitVec 64) : getFpVar v (setFpVar v x s) = some x := by
  simp [getFpVar, setFpVar, HolFiniteMapExact.updateEq, FUPDATE_HOL]
example (v : WordStoreHOL) (x : WordLocW width) : (setStore v x s).store.lookup v = some x := by
  simp [setStore, HolFiniteMapExact.updateEq, FUPDATE_HOL]
example : getVars [] s = some [] := rfl
example (v : Nat) (vs : List Nat) (h : getVar v s = none) : getVars (v :: vs) s = none := by
  simp [getVars, h]
example (v : Nat) (x : WordLocW width) : getVars [v,v] (setVar v x s) = some [x,x] := by
  simp [getVars, getVar, setVar, HolFiniteMapExact.updateEq, FUPDATE_HOL]
example : (emptyEnv s).stack = [] ∧ (emptyEnv s).fpRegs = s.fpRegs ∧ (emptyEnv s).store = s.store := by
  exact ⟨rfl,rfl,rfl⟩
example (v : Nat) : getVar v (emptyEnv s) = none := rfl
example : (decClock s).clock = s.clock - 1 ∧ (decClock s).regs = s.regs := by
  exact ⟨rfl,rfl⟩
