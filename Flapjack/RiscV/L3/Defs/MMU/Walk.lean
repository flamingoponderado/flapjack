import Flapjack.RiscV.L3.Defs.MMU.Access
set_option maxRecDepth 200000
namespace Flapjack.RiscV.L3

/-- Source review: riscvScript4745-4960 complete recursive tDef. The original
measure is level, retained directly for termination. PTE address uses the
36-bit VPN shifted by level*9, its low nine bits widened and shifted by three.
Invalid PTE and level-zero pointer return None with unchanged state. Other
pointers recur at level-1 with the PPN shifted within 38 bits before widening.
Leaves retain permission-returned state, set R and set D only for Write, and
write eight bytes only when either bit changes. Superpage PPN/VPN mixing keeps
38-bit and 36-bit operations before concatenation with the 12-bit offset; no
alignment rejection or global-bit accumulation is added. The whole returned
option, updated PTE, level, global bit, PTE address and native state are retained. -/
@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "walk64_def"]
noncomputable def walk64 (arg0 : ((BitVec 64) × (fetchType × (accessType × (Privilege × ((BitVec 64) × Nat)))))) (state : riscv_state) : ((Option ((BitVec 64) × (SV_PTE × (Nat × (Bool × (BitVec 64)))))) × riscv_state) :=
  match arg0 with
  | (vAddr, (ft, (ac, (priv, (ptb, level))))) =>
  (let va : SV_Vaddr := («rec'SV_Vaddr» vAddr); (let pte_addr : (BitVec 64) := (ptb + ((((BitVec.setWidth 64 ((holWordExtract 9 (LEVEL_BITS - 1) 0 ((va.Sv_VPNi >>> (level * LEVEL_BITS))))))) <<< 3))); (let v : SV_PTE := («rec'SV_PTE» (rawReadData pte_addr state)); (if (!v.PTE_V) then ((((none : (Option ((BitVec 64) × (SV_PTE × (Nat × (Bool × (BitVec 64)))))))), state)) else ((if ((((v.PTE_T == (BitVec.ofNat 4 0))) || ((v.PTE_T == (BitVec.ofNat 4 1))))) then ((if (level == 0) then ((((none : (Option ((BitVec 64) × (SV_PTE × (Nat × (Bool × (BitVec 64)))))))), state)) else ((walk64 ((vAddr, ((ft, ((ac, ((priv, ((((BitVec.setWidth 64 (v.PTE_PPNi <<< PAGESIZE_BITS))), (level - 1))))))))))) state)))) else ((match (checkMemPermission ((ft, ((ac, (priv, v.PTE_T))))) state) with | (v0, s) => (if (!v0) then ((((none : (Option ((BitVec 64) × (SV_PTE × (Nat × (Bool × (BitVec 64)))))))), s)) else ((match (let s0 : SV_PTE := (let r := v; { r with PTE_R := ((fun (_eta1 : Bool) => true)) r.PTE_R }); (let s0_1 : SV_PTE := (if (ac == accessType.Write) then ((let r := s0; { r with PTE_D := ((fun (_eta1 : Bool) => true)) r.PTE_D })) else s0); (((some ((((BitVec.setWidth 64 ((BitVec.setWidth 50 (((if ((decide (level > 0))) then ((((BitVec.setWidth 38 ((((v.PTE_PPNi >>> (level * LEVEL_BITS))) <<< (level * LEVEL_BITS))))) ||| ((BitVec.setWidth 38 ((va.Sv_VPNi &&& (((((BitVec.ofNat 36 1) <<< (level * LEVEL_BITS))) - (BitVec.ofNat 36 1))))))))) else v.PTE_PPNi)) ++ va.Sv_PgOfs))))), ((s0_1, ((level, (((isGlobal v.PTE_T), pte_addr)))))))))), ((s0_1, ((if ((((!(v.PTE_R == s0_1.PTE_R))) || ((!(v.PTE_D == s0_1.PTE_D))))) then ((rawWriteData ((pte_addr, (((«reg'SV_PTE» s0_1), 8)))) s)) else s))))))) with | (r, s1) => (r, s1.2))))))))))))
termination_by arg0.2.2.2.2.2
decreasing_by simp_wf; simp_all only [beq_iff_eq]; omega

end Flapjack.RiscV.L3
