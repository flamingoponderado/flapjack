import Flapjack.RiscV.L3.Defs.Reservation
namespace Flapjack.Test.L3ReservationParity
open Flapjack.RiscV.L3

/-- Full-state regression of the literal reservation writer. No standalone HOL
original: arbitrary native state, core and optional virtual address are retained. -/
theorem fullWrite (s : riscv_state) (value : Option (BitVec 64)) :
    «write'ReserveLoad» value s =
      { s with c_ReserveLoad := holUpdate s.procID value s.c_ReserveLoad } := by
  rfl

/-- Derived read-after-write and complete indexed frame, no separate HOL
original. No valid-core or existing-reservation restriction is required. -/
theorem readAfterWrite (s : riscv_state) (value : Option (BitVec 64)) :
    ReserveLoad («write'ReserveLoad» value s) = value := by
  simp [ReserveLoad, fullWrite, holUpdate]

theorem indexedFrame (s : riscv_state) (value : Option (BitVec 64)) (id : BitVec 8) :
    («write'ReserveLoad» value s).c_ReserveLoad id =
      if s.procID = id then value else s.c_ReserveLoad id := by
  rfl

/-- Derived observation shape, no separate HOL original. THE NONE is not given
a chosen value; the original IsSome conjunction masks it. -/
theorem fullMatch (s : riscv_state) (v : BitVec 64) :
    matchLoadReservation v s =
      (match s.c_ReserveLoad s.procID with | none => false | some w => w == v) := by
  cases h : s.c_ReserveLoad s.procID <;> simp [matchLoadReservation, ReserveLoad, h, holThe]

private def fixture (base : riscv_state) (core : BitVec 8) (old : Option (BitVec 64)) : riscv_state :=
  { base with procID := core, totalCore := 1, c_ReserveLoad := (fun id => if id = core then old else some 77) }

private noncomputable def observation (s : riscv_state) (new : Option (BitVec 64)) (query : BitVec 64) := by
  classical
  exact
    let r := «write'ReserveLoad» new s
    ((ReserveLoad s).map BitVec.toNat, (ReserveLoad r).map BitVec.toNat,
      matchLoadReservation query s, matchLoadReservation query r,
      (r.c_ReserveLoad (s.procID + 1)).map BitVec.toNat,
      decide (r = { s with c_ReserveLoad := holUpdate s.procID new s.c_ReserveLoad }),
      r.totalCore,r.procID.toNat)

-- Original l3_reservation_probe.out: none_none.
example (base : riscv_state) :
    observation (fixture base (BitVec.ofNat 8 7) none) none (BitVec.ofNat 64 0) =
      (none,none,false,false,some 77,true,1,7) := by
  simp [observation, fixture, fullWrite, fullMatch, ReserveLoad, holUpdate]

-- Original l3_reservation_probe.out: none_zero.
example (base : riscv_state) :
    observation (fixture base (BitVec.ofNat 8 7) none) (some (BitVec.ofNat 64 0)) (BitVec.ofNat 64 0) =
      (none,(some 0),false,true,some 77,true,1,7) := by
  simp [observation, fixture, fullWrite, fullMatch, ReserveLoad, holUpdate]

-- Original l3_reservation_probe.out: clear_zero.
example (base : riscv_state) :
    observation (fixture base (BitVec.ofNat 8 7) (some (BitVec.ofNat 64 0))) none (BitVec.ofNat 64 0) =
      ((some 0),none,true,false,some 77,true,1,7) := by
  simp [observation, fixture, fullWrite, fullMatch, ReserveLoad, holUpdate]

-- Original l3_reservation_probe.out: replace_match.
example (base : riscv_state) :
    observation (fixture base (BitVec.ofNat 8 7) (some (BitVec.ofNat 64 21))) (some (BitVec.ofNat 64 123)) (BitVec.ofNat 64 123) =
      ((some 21),(some 123),false,true,some 77,true,1,7) := by
  simp [observation, fixture, fullWrite, fullMatch, ReserveLoad, holUpdate]

-- Original l3_reservation_probe.out: max_mismatch.
example (base : riscv_state) :
    observation (fixture base (BitVec.ofNat 8 7) (some (BitVec.ofNat 64 18446744073709551615))) (some (BitVec.ofNat 64 18446744073709551615)) (BitVec.ofNat 64 0) =
      ((some 18446744073709551615),(some 18446744073709551615),false,false,some 77,true,1,7) := by
  simp [observation, fixture, fullWrite, fullMatch, ReserveLoad, holUpdate]

-- Original l3_reservation_probe.out: present_mismatch.
example (base : riscv_state) :
    observation (fixture base (BitVec.ofNat 8 7) (some (BitVec.ofNat 64 21))) (some (BitVec.ofNat 64 21)) (BitVec.ofNat 64 22) =
      ((some 21),(some 21),false,false,some 77,true,1,7) := by
  simp [observation, fixture, fullWrite, fullMatch, ReserveLoad, holUpdate]

-- Original l3_reservation_probe.out: core_zero.
example (base : riscv_state) :
    observation (fixture base (BitVec.ofNat 8 0) none) (some (BitVec.ofNat 64 18446744073709551615)) (BitVec.ofNat 64 18446744073709551615) =
      (none,(some 18446744073709551615),false,true,some 77,true,1,0) := by
  simp [observation, fixture, fullWrite, fullMatch, ReserveLoad, holUpdate]

-- Original l3_reservation_probe.out: core_wrap.
example (base : riscv_state) :
    observation (fixture base (BitVec.ofNat 8 255) (some (BitVec.ofNat 64 21))) (some (BitVec.ofNat 64 0)) (BitVec.ofNat 64 0) =
      ((some 21),(some 0),false,true,some 77,true,1,255) := by
  simp [observation, fixture, fullWrite, fullMatch, ReserveLoad, holUpdate]

end Flapjack.Test.L3ReservationParity
