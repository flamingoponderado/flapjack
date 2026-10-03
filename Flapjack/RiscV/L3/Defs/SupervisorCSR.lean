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

@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "update_mstatus_def"]
noncomputable def update_mstatus (arg0 : (mstatus × mstatus)) : mstatus :=
  match arg0 with
  | (orig, v) =>
  (let s0 : mstatus := (let r := ((let r := ((let r := ((let r := ((let r := ((let r := ((let r := ((let r := orig; { r with MIE := ((fun (_eta1 : Bool) => v.MIE)) r.MIE })); { r with MPRV := ((fun (_eta1 : (BitVec 2)) => v.MPRV)) r.MPRV })); { r with MIE1 := ((fun (_eta1 : Bool) => v.MIE1)) r.MIE1 })); { r with MPRV1 := ((fun (_eta1 : (BitVec 2)) => v.MPRV1)) r.MPRV1 })); { r with MIE2 := ((fun (_eta1 : Bool) => v.MIE2)) r.MIE2 })); { r with MPRV2 := ((fun (_eta1 : (BitVec 2)) => v.MPRV2)) r.MPRV2 })); { r with MIE3 := ((fun (_eta1 : Bool) => v.MIE3)) r.MIE3 })); { r with MPRV3 := ((fun (_eta1 : (BitVec 2)) => v.MPRV3)) r.MPRV3 }); (let r := ((let r := ((let r := ((let r := ((if (isValidVM v.VM) then ((let r := s0; { r with VM := ((fun (_eta1 : (BitVec 5)) => v.VM)) r.VM })) else s0)); { r with MMPRV := ((fun (_eta1 : Bool) => v.MMPRV)) r.MMPRV })); { r with MFS := ((fun (_eta1 : (BitVec 2)) => v.MFS)) r.MFS })); { r with MXS := ((fun (_eta1 : (BitVec 2)) => v.MXS)) r.MXS })); { r with MSD := ((fun (_eta1 : Bool) => (((((extStatus v.MXS) == ExtStatus.Dirty)) || (((extStatus v.MFS) == ExtStatus.Dirty)))))) r.MSD }))

@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "lower_sip_mip_def"]
def lower_sip_mip (arg0 : (sip × mip)) : mip :=
  match arg0 with
  | (sip, mip) =>
  (let r := ((let r := mip; { r with STIP := ((fun (_eta1 : Bool) => sip.STIP)) r.STIP })); { r with SSIP := ((fun (_eta1 : Bool) => sip.SSIP)) r.SSIP })

@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "lower_sie_mie_def"]
def lower_sie_mie (arg0 : (sie × mie)) : mie :=
  match arg0 with
  | (sie, mie) =>
  (let r := ((let r := mie; { r with STIE := ((fun (_eta1 : Bool) => sie.STIE)) r.STIE })); { r with SSIE := ((fun (_eta1 : Bool) => sie.SSIE)) r.SSIE })

@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "lower_sstatus_mstatus_def"]
noncomputable def lower_sstatus_mstatus (arg0 : (sstatus × mstatus)) : mstatus :=
  match arg0 with
  | (sst, mst) =>
  (update_mstatus ((mst, ((let r := ((let r := ((let r := ((let r := ((let r := ((let r := ((«rec'mstatus» («reg'mstatus» mst))); { r with MMPRV := ((fun (_eta1 : Bool) => sst.SMPRV)) r.MMPRV })); { r with MXS := ((fun (_eta1 : (BitVec 2)) => sst.SXS)) r.MXS })); { r with MFS := ((fun (_eta1 : (BitVec 2)) => sst.SFS)) r.MFS })); { r with MPRV1 := ((fun (_eta1 : (BitVec 2)) => ((privLevel (if sst.SPS then Privilege.Supervisor else Privilege.User))))) r.MPRV1 })); { r with MIE1 := ((fun (_eta1 : Bool) => sst.SPIE)) r.MIE1 })); { r with MIE := ((fun (_eta1 : Bool) => sst.SIE)) r.MIE })))))

/-- Flapjack-only unconditional frame: interrupt lowering changes only SSIP/STIP. -/
theorem lowerSipFrame (sst : sip) (mst : mip) :
    { lower_sip_mip (sst,mst) with SSIP := mst.SSIP, STIP := mst.STIP } = mst := by rfl

/-- Flapjack-only unconditional frame: interrupt lowering changes only SSIE/STIE. -/
theorem lowerSieFrame (sst : sie) (mst : mie) :
    { lower_sie_mie (sst,mst) with SSIE := mst.SSIE, STIE := mst.STIE } = mst := by rfl

/-- Flapjack-only unconditional reserved-field frame; no separate HOL original. -/
theorem updateMstatusReserved (orig v : mstatus) :
    (update_mstatus (orig,v)).«mstatus'rst» = orig.«mstatus'rst» := by
  simp only [update_mstatus]
  split <;> rfl

end Flapjack.RiscV.L3
