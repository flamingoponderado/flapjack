import Flapjack.RiscV.L3.Defs.AddressException
namespace Flapjack.Test.L3AddressExceptionParity
open Flapjack.RiscV.L3

/-- Flapjack regression infrastructure: no separate HOL original. This full-state
normal form checks the complete signalAddressException update for arbitrary
exception/address/core/state, without assuming a valid core or address. -/
theorem fullState (s : riscv_state) (e : ExceptionType) (v : BitVec 64) :
    signalAddressException (e,v) s =
      { s with c_NextFetch := (holUpdate s.procID
          (some (TransferControl.Trap { trap := e, badaddr := some v })) s.c_NextFetch) } := by
  rfl


private def observation (e : ExceptionType) (core : BitVec 8) (r : riscv_state) :=
  ((match r.c_NextFetch core with
    | some (.Trap t) => (t.trap == e, t.badaddr.map BitVec.toNat)
    | _ => (false, none)),
   r.c_NextFetch (core + 1) == none, r.exception == .NoException,
   r.totalCore, r.procID.toNat)

-- Original l3_address_exception_probe.out: load_zero.
example (base : riscv_state) :
    let s := { base with procID := BitVec.ofNat 8 0, totalCore := 1, c_NextFetch := (fun _ => none), exception := .NoException }
    observation .Load_Fault (BitVec.ofNat 8 0)
      (signalAddressException (.Load_Fault, BitVec.ofNat 64 0) s) =
      ((true, some 0),true,true,1,0) := by
  simp [observation, fullState, holUpdate]

-- Original l3_address_exception_probe.out: store_max.
example (base : riscv_state) :
    let s := { base with procID := BitVec.ofNat 8 255, totalCore := 1, c_NextFetch := (fun _ => none), exception := .NoException }
    observation .Store_AMO_Fault (BitVec.ofNat 8 255)
      (signalAddressException (.Store_AMO_Fault, BitVec.ofNat 64 18446744073709551615) s) =
      ((true, some 18446744073709551615),true,true,1,255) := by
  simp [observation, fullState, holUpdate]

-- Original l3_address_exception_probe.out: misaligned.
example (base : riscv_state) :
    let s := { base with procID := BitVec.ofNat 8 7, totalCore := 1, c_NextFetch := (fun _ => none), exception := .NoException }
    observation .AMO_Misaligned (BitVec.ofNat 8 7)
      (signalAddressException (.AMO_Misaligned, BitVec.ofNat 64 3) s) =
      ((true, some 3),true,true,1,7) := by
  simp [observation, fullState, holUpdate]

-- Original l3_address_exception_probe.out: arbitrary_exception.
example (base : riscv_state) :
    let s := { base with procID := BitVec.ofNat 8 7, totalCore := 1, c_NextFetch := (fun _ => none), exception := .NoException }
    observation .Illegal_Instr (BitVec.ofNat 8 7)
      (signalAddressException (.Illegal_Instr, BitVec.ofNat 64 1234) s) =
      ((true, some 1234),true,true,1,7) := by
  simp [observation, fullState, holUpdate]
end Flapjack.Test.L3AddressExceptionParity
