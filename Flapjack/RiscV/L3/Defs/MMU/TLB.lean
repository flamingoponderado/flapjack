import Flapjack.RiscV.L3.Defs.MMU.Primitives
set_option maxRecDepth 200000
namespace Flapjack.RiscV.L3
open Flapjack.Basis.Pure.MlString

/-- Source review: Full original arbitrary-level mask and arithmetic physical-address alignment; current-core cycle age, all nine fields replace canonical ARB entry. No bound on level or procID. -/
@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "mkTLBEntry_def"]
noncomputable def mkTLBEntry (arg0 : ((BitVec 6) × (Bool × ((BitVec 64) × ((BitVec 64) × (SV_PTE × (Nat × (BitVec 64)))))))) : (riscv_state → TLBEntry) :=
  match arg0 with
  | (asid, (global, (vAddr, (pAddr, (pte, (i, pteAddr)))))) =>
  (fun (state : riscv_state) => (let s0 : TLBEntry := (let r := ((let r := ((let r := ((let r := ((let r := (Flapjack.holArb TLBEntry); { r with asid := ((fun (_eta1 : (BitVec 6)) => asid)) r.asid })); { r with global := ((fun (_eta1 : Bool) => global)) r.global })); { r with pte := ((fun (_eta1 : SV_PTE) => pte)) r.pte })); { r with pteAddr := ((fun (_eta1 : (BitVec 64)) => pteAddr)) r.pteAddr })); { r with vAddrMask := ((fun (_eta1 : (BitVec 64)) => (((((BitVec.ofNat 64 1) <<< (((LEVEL_BITS * i) + PAGESIZE_BITS)))) - (BitVec.ofNat 64 1))))) r.vAddrMask }); (let s0_1 : TLBEntry := (let r := s0; { r with vMatchMask := ((fun (_eta1 : (BitVec 64)) => ((((BitVec.signExtend 64 (BitVec.ofNat 1 1))) ^^^ s0.vAddrMask)))) r.vMatchMask }); (let r := ((let r := ((let r := s0_1; { r with vAddr := ((fun (_eta1 : (BitVec 64)) => (vAddr &&& s0_1.vMatchMask))) r.vAddr })); { r with pAddr := ((fun (_eta1 : (BitVec 64)) => ((((BitVec.sshiftRight pAddr ((PAGESIZE_BITS + (LEVEL_BITS * i))))) <<< ((PAGESIZE_BITS + (LEVEL_BITS * i))))))) r.pAddr })); { r with age := ((fun (_eta1 : (BitVec 64)) => (state.c_cycles state.procID))) r.age }))))

/-- Source review: Full original inclusive FOR scan0..15, retains the first hit, with global-or-ASID and masked virtual-address equality guards. No hit premise or table narrowing. -/
@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "lookupTLB_def"]
def lookupTLB (arg0 : ((BitVec 6) × ((BitVec 64) × ((BitVec 4) → (Option TLBEntry))))) : (Option (TLBEntry × (BitVec 4))) :=
  match arg0 with
  | (asid, (vAddr, tlb)) =>
  ((((holFor ((0, (((TLBEntries - 1), ((fun (i : Nat) => (fun (state : ((Option (TLBEntry × (BitVec 4))) × Unit)) => (match (tlb (BitVec.ofNat 4 i)) with | none => ((), state) | some e => ((), ((if ((((state.1 == ((none : (Option (TLBEntry × (BitVec 4))))))) && ((((e.global || (e.asid == asid))) && ((e.vAddr == (vAddr &&& e.vMatchMask))))))) then ((((some ((e, (BitVec.ofNat 4 i))))), ())) else state)))))))))))) ((((none : (Option (TLBEntry × (BitVec 4))))), ())))).2).1

end Flapjack.RiscV.L3
