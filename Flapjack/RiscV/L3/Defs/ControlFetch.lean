import Flapjack.RiscV.L3.Defs.AddressException
namespace Flapjack.RiscV.L3

noncomputable def «dfn'FETCH_MISALIGNED» (addr : (BitVec 64)) : (riscv_state → riscv_state) :=
  (fun (state : riscv_state) => (signalAddressException (ExceptionType.Fetch_Misaligned, addr) state))

noncomputable def «dfn'FETCH_FAULT» (addr : (BitVec 64)) : (riscv_state → riscv_state) :=
  (fun (state : riscv_state) => (signalAddressException (ExceptionType.Fetch_Fault, addr) state))

end Flapjack.RiscV.L3
