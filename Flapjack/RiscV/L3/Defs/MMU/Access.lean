import Flapjack.RiscV.L3.Defs
import Flapjack.RiscV.L3.Defs.MMU.Primitives
namespace Flapjack.RiscV.L3

/-- Compatibility selector for integer proof simplifiers; only physical memory
exists on this branch, regardless of the retained HOL configuration value. -/
def vmType (_vm : BitVec 5) (state : riscv_state) : VM_Mode × riscv_state :=
  (.Mbare, state)

/-- Source review: Full arbitrary Nat byte counts;64-bit mask (1 shifted nbytes*8)-1, aligned/single-word/cross-word branches and higher-word then lower-word state updates. No nbytes bound or alignment premise. -/
def rawWriteData (arg0 : ((BitVec 64) × ((BitVec 64) × Nat))) : (riscv_state → riscv_state) :=
  match arg0 with
  | (pAddr, (data, nbytes)) =>
  (fun (state : riscv_state) => (let mask : (BitVec 64) := (((((BitVec.setWidth 64 (BitVec.ofNat 1 1))) <<< (nbytes * 8))) - (BitVec.ofNat 64 1)); (let pAddrIdx : (BitVec 61) := (holWordExtract 61 63 3 pAddr); (let align : Nat := (holWordExtract 3 2 0 pAddr).toNat; (let v : (BitVec 64) := (MEM pAddrIdx state); (if (align == 0) then ((«write'MEM» ((((((v &&& (~~~mask))) ||| (data &&& mask))), pAddrIdx)) state)) else ((if ((decide ((align + nbytes) ≤ (64 / 8)))) then ((«write'MEM» ((((((v &&& ((~~~((mask <<< (align * 8))))))) ||| (((data &&& mask) <<< (align * 8))))), pAddrIdx)) state)) else ((let dw_mask : (BitVec 128) := ((BitVec.setWidth 128 mask) <<< (align * 8)); (let dw_new : (BitVec 128) := (((((BitVec.setWidth 128 (((MEM ((pAddrIdx + (BitVec.ofNat 61 1))) state)) ++ v))) &&& (~~~dw_mask))) ||| (((((BitVec.setWidth 128 data) <<< (align * 8))) &&& dw_mask))); («write'MEM» ((((holWordExtract 64 (64 - 1) 0 dw_new)), pAddrIdx)) ((«write'MEM» ((((holWordExtract 64 (((2 * 64) - 1)) 64 dw_new)), ((pAddrIdx + (BitVec.ofNat 61 1))))) state))))))))))))))

/-- Source review: Full aligned/un-aligned branches,61-bit wrapping word index,128-bit arithmetic shift followed by low64 extraction. -/
def rawReadData (pAddr : (BitVec 64)) : (riscv_state → (BitVec 64)) :=
  (fun (state : riscv_state) => (let pAddrIdx : (BitVec 61) := (holWordExtract 61 63 3 pAddr); (let align : Nat := (holWordExtract 3 2 0 pAddr).toNat; (if (align == 0) then (MEM pAddrIdx state) else ((holWordExtract 64 63 0 ((BitVec.sshiftRight ((BitVec.setWidth 128 (((MEM ((pAddrIdx + (BitVec.ofNat 61 1))) state)) ++ (MEM pAddrIdx state)))) (align * 8)))))))))

/-- Flapjack-specific frame consequence of the literal rawWriteData equation.
There is no separately named HOL theorem; the original generic proof is captured
in l3_mmu_write_frame_probe.out. Every non-memory field is preserved, without
address/alignment/byte-count premises. -/
theorem rawWriteDataPreservesNonMemory (a d : BitVec 64) (n : Nat) (s : riscv_state) :
 rawWriteData (a,d,n) s = { s with MEM8 := (rawWriteData (a,d,n) s).MEM8 } := by
 simp only [rawWriteData]
 dsimp
 split <;> (try split) <;> simp_all [«write'MEM»]

end Flapjack.RiscV.L3
