import Flapjack.Compiler.Backend.Semantics.StackSem.Control

/-! Flapjack-specific kernel checks of code lookup rejection and clock-state
preservation. These are infrastructure checks, not additional HOL theorem ports. -/
open Flapjack Flapjack.StackSemControl
variable {width : Nat} [NeZero width] {α C F R : Type}
variable (code : Spt α) (regs : HolFiniteMapExact Nat (WordLocW width))
example (label : Nat) : findCode (.inl label) regs code = sptLookup label code := rfl
example (reg : Nat) (h : regs.lookup reg = none) : findCode (.inr reg) regs code = none := by
  simp [findCode,h]
example (reg : Nat) (word : BitVec width) (h : regs.lookup reg = some (.word word)) :
    findCode (.inr reg) regs code = none := by simp [findCode,h]
example (reg label offset : Nat) (h : regs.lookup reg = some (.loc label (offset+1))) :
    findCode (.inr reg) regs code = none := by simp [findCode,h]
example (reg label : Nat) (h : regs.lookup reg = some (.loc label 0)) :
    findCode (.inr reg) regs code = sptLookup label code := by simp [findCode,h]
example (reg label : Nat) :
    findCode (.inr reg) ((HolFiniteMapExact.empty : HolFiniteMapExact Nat (WordLocW width)).updateEq
      (reg,.loc label 0)) code = sptLookup label code := by
  simp [findCode,HolFiniteMapExact.updateEq,FUPDATE_HOL]
variable (s t : StackSemStateFiniteExact width C F) (res : R)
example : (fixClock s (res,t)).1 = res := rfl
example : (fixClock s (res,t)).2.regs = t.regs ∧ (fixClock s (res,t)).2.stack = t.stack ∧
    (fixClock s (res,t)).2.ffi = t.ffi := by exact ⟨rfl,rfl,rfl⟩
example : (fixClock { s with clock := 3 } (res,{ t with clock := 12 })).2.clock = 3 := rfl
example : (fixClock { s with clock := 12 } (res,{ t with clock := 3 })).2.clock = 3 := rfl
example : (fixClock { s with clock := 0 } (res,t)).2.clock = 0 := by simp [fixClock]
example : (fixClock s (res,t)).2.clock ≤ s.clock :=
  fixClockImp s (res,t) res (fixClock s (res,t)).2 rfl
