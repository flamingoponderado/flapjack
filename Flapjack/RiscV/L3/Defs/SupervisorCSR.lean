import Flapjack.RiscV.L3.Defs.MachineCSRCodec
import Flapjack.RiscV.L3.Defs.CSRAccess
namespace Flapjack.RiscV.L3

/-! Complete literal supervisor CSR codecs and lift/lower section. Original
fixed fields/reserved slices, MPRV1 supervisor projection, dirty extension
summary and VM whitelist are preserved. update_mstatus retains original
reserved fields and rejected VM; no validity premise or modern-ISA repair. -/

@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "rec'sip_def"]
def «rec'sip» (x : (BitVec 64)) : sip :=
  (sip.mk (x.getLsbD 1) (x.getLsbD 5) ((BitVec.setWidth 62 ((holWordExtract 1 0 0 x) ++ ((BitVec.setWidth 61 ((holWordExtract 3 4 2 x) ++ (holWordExtract 58 63 6 x))))))))

@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "lift_mip_sip_def"]
def lift_mip_sip (mip : mip) : sip :=
  (let r := ((let r := ((«rec'sip» (BitVec.ofNat 64 0))); { r with STIP := ((fun (_eta1 : Bool) => mip.STIP)) r.STIP })); { r with SSIP := ((fun (_eta1 : Bool) => mip.SSIP)) r.SSIP })

@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "reg'sip_def"]
def «reg'sip» (x : sip) : (BitVec 64) :=
  (match x with | ⟨SSIP, STIP, sip_rst⟩ => (BitVec.setWidth 64 ((holWordExtract 58 57 0 sip_rst) ++ ((BitVec.setWidth 6 (((holV2w 1 ((STIP :: (([] : (List Bool))))))) ++ ((BitVec.setWidth 5 ((holWordExtract 3 60 58 sip_rst) ++ ((BitVec.setWidth 2 (((holV2w 1 ((SSIP :: (([] : (List Bool))))))) ++ (holWordExtract 1 61 61 sip_rst)))))))))))))

@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "rec'sie_def"]
def «rec'sie» (x : (BitVec 64)) : sie :=
  (sie.mk (x.getLsbD 1) (x.getLsbD 5) ((BitVec.setWidth 62 ((holWordExtract 1 0 0 x) ++ ((BitVec.setWidth 61 ((holWordExtract 3 4 2 x) ++ (holWordExtract 58 63 6 x))))))))

@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "lift_mie_sie_def"]
def lift_mie_sie (mie : mie) : sie :=
  (let r := ((let r := ((«rec'sie» (BitVec.ofNat 64 0))); { r with STIE := ((fun (_eta1 : Bool) => mie.STIE)) r.STIE })); { r with SSIE := ((fun (_eta1 : Bool) => mie.SSIE)) r.SSIE })

@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "reg'sie_def"]
def «reg'sie» (x : sie) : (BitVec 64) :=
  (match x with | ⟨SSIE, STIE, sie_rst⟩ => (BitVec.setWidth 64 ((holWordExtract 58 57 0 sie_rst) ++ ((BitVec.setWidth 6 (((holV2w 1 ((STIE :: (([] : (List Bool))))))) ++ ((BitVec.setWidth 5 ((holWordExtract 3 60 58 sie_rst) ++ ((BitVec.setWidth 2 (((holV2w 1 ((SSIE :: (([] : (List Bool))))))) ++ (holWordExtract 1 61 61 sie_rst)))))))))))))

@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "rec'sstatus_def"]
def «rec'sstatus» (x : (BitVec 64)) : sstatus :=
  (sstatus.mk (holWordExtract 2 13 12 x) (x.getLsbD 0) (x.getLsbD 16) (x.getLsbD 3) (x.getLsbD 4) (x.getLsbD 63) (holWordExtract 2 15 14 x) ((BitVec.setWidth 55 ((holWordExtract 2 2 1 x) ++ ((BitVec.setWidth 53 ((holWordExtract 7 11 5 x) ++ (holWordExtract 46 62 17 x))))))))

@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "extStatus_def"]
noncomputable def extStatus (e : (BitVec 2)) : ExtStatus :=
  (((fun (v : (BitVec 2)) => (if ((v == (BitVec.ofNat 2 0))) then ExtStatus.Off else ((if ((v == (BitVec.ofNat 2 1))) then ExtStatus.Initial else ((if ((v == (BitVec.ofNat 2 2))) then ExtStatus.Clean else ((if ((v == (BitVec.ofNat 2 3))) then ExtStatus.Dirty else (Flapjack.holArb ExtStatus)))))))))) e)

@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "lift_mstatus_sstatus_def"]
noncomputable def lift_mstatus_sstatus (mst : mstatus) : sstatus :=
  (let r := ((let r := ((let r := ((let r := ((let r := ((let r := ((let r := ((«rec'sstatus» (BitVec.ofNat 64 0))); { r with SMPRV := ((fun (_eta1 : Bool) => mst.MMPRV)) r.SMPRV })); { r with SXS := ((fun (_eta1 : (BitVec 2)) => mst.MXS)) r.SXS })); { r with SFS := ((fun (_eta1 : (BitVec 2)) => mst.MFS)) r.SFS })); { r with SSD := ((fun (_eta1 : Bool) => (((((extStatus mst.MXS) == ExtStatus.Dirty)) || (((extStatus mst.MFS) == ExtStatus.Dirty)))))) r.SSD })); { r with SPS := ((fun (_eta1 : Bool) => ((!(((privilege mst.MPRV1) == Privilege.User)))))) r.SPS })); { r with SPIE := ((fun (_eta1 : Bool) => mst.MIE1)) r.SPIE })); { r with SIE := ((fun (_eta1 : Bool) => mst.MIE)) r.SIE })

@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "reg'sstatus_def"]
def «reg'sstatus» (x : sstatus) : (BitVec 64) :=
  (match x with | ⟨SFS, SIE, SMPRV, SPIE, SPS, SSD, SXS, sstatus_rst⟩ => (BitVec.setWidth 64 (((holV2w 1 ((SSD :: (([] : (List Bool))))))) ++ ((BitVec.setWidth 63 ((holWordExtract 46 45 0 sstatus_rst) ++ ((BitVec.setWidth 17 (((holV2w 1 ((SMPRV :: (([] : (List Bool))))))) ++ ((BitVec.setWidth 16 (SXS ++ ((BitVec.setWidth 14 (SFS ++ ((BitVec.setWidth 12 ((holWordExtract 7 52 46 sstatus_rst) ++ ((BitVec.setWidth 5 (((holV2w 1 ((SPS :: (([] : (List Bool))))))) ++ ((BitVec.setWidth 4 (((holV2w 1 ((SPIE :: (([] : (List Bool))))))) ++ ((BitVec.setWidth 3 ((holWordExtract 2 54 53 sstatus_rst) ++ ((holV2w 1 ((SIE :: (([] : (List Bool))))))))))))))))))))))))))))))))))

@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "isValidVM_def"]
def isValidVM (vm : (BitVec 5)) : Bool :=
  (((fun (v : (BitVec 5)) => (if ((v == (BitVec.ofNat 5 0))) then true else ((if ((v == (BitVec.ofNat 5 1))) then true else ((if ((v == (BitVec.ofNat 5 2))) then true else ((if ((v == (BitVec.ofNat 5 8))) then true else ((if ((v == (BitVec.ofNat 5 9))) then true else ((if ((v == (BitVec.ofNat 5 10))) then true else ((if ((v == (BitVec.ofNat 5 11))) then true else ((if ((v == (BitVec.ofNat 5 12))) then true else false))))))))))))))))) vm)


end Flapjack.RiscV.L3
