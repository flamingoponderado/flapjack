import Flapjack.RiscV.L3.Defs.CSRAccess
namespace Flapjack.Test.L3CSRAccessParity
open Flapjack.RiscV.L3
private def fixture (base : riscv_state) (mode p core : Nat) : riscv_state :=
  { base with procID := BitVec.ofNat 8 core, totalCore := 1, c_MCSR := fun id => { base.c_MCSR id with mcpuid := { (base.c_MCSR id).mcpuid with ArchBase := BitVec.ofNat 2 mode }, mstatus := { (base.c_MCSR id).mstatus with MPRV := BitVec.ofNat 2 p } } }
private noncomputable def observation (base : riscv_state) (csr : BitVec 12) (mode core : Nat) := by
  classical
  exact let s := fixture base mode 0 core
    let r := is_CSR_defined csr s
    (r.1,decide (r.2=s),csrRW csr,csrPR csr,
      ([0,1,2,3] : List Nat).flatMap (fun p =>
        [.Read,.Write].map (fun a => (checkCSROp (csr,31,a) (fixture base mode p core)).1)))
-- Original csr0_mode0; independently derived signed-range/permission result.
example (base : riscv_state) : observation base 0 0 7 = (true,true,0,0,[true,true,true,true,true,true,true,true]) := by
  simp [observation,fixture,is_CSR_defined,csrRW,csrPR,checkCSROp,check_CSR_access,
    curPrivilege,privLevel,privilege,in32BitMode,curArch,architecture,MCSR,holWordExtract]

-- Original csr1_mode0; independently derived signed-range/permission result.
example (base : riscv_state) : observation base 1 0 255 = (true,true,0,0,[true,true,true,true,true,true,true,true]) := by
  simp [observation,fixture,is_CSR_defined,csrRW,csrPR,checkCSROp,check_CSR_access,
    curPrivilege,privLevel,privilege,in32BitMode,curArch,architecture,MCSR,holWordExtract]

-- Original csr3_mode0; independently derived signed-range/permission result.
example (base : riscv_state) : observation base 3 0 255 = (true,true,0,0,[true,true,true,true,true,true,true,true]) := by
  simp [observation,fixture,is_CSR_defined,csrRW,csrPR,checkCSROp,check_CSR_access,
    curPrivilege,privLevel,privilege,in32BitMode,curArch,architecture,MCSR,holWordExtract]

-- Original csr4_mode0; independently derived signed-range/permission result.
example (base : riscv_state) : observation base 4 0 7 = (true,true,0,0,[true,true,true,true,true,true,true,true]) := by
  simp [observation,fixture,is_CSR_defined,csrRW,csrPR,checkCSROp,check_CSR_access,
    curPrivilege,privLevel,privilege,in32BitMode,curArch,architecture,MCSR,holWordExtract]

-- Original csr255_mode0; independently derived signed-range/permission result.
example (base : riscv_state) : observation base 255 0 255 = (true,true,0,0,[true,true,true,true,true,true,true,true]) := by
  simp [observation,fixture,is_CSR_defined,csrRW,csrPR,checkCSROp,check_CSR_access,
    curPrivilege,privLevel,privilege,in32BitMode,curArch,architecture,MCSR,holWordExtract]

-- Original csr256_mode0; independently derived signed-range/permission result.
example (base : riscv_state) : observation base 256 0 7 = (true,true,0,1,[false,false,true,true,true,true,true,true]) := by
  simp [observation,fixture,is_CSR_defined,csrRW,csrPR,checkCSROp,check_CSR_access,
    curPrivilege,privLevel,privilege,in32BitMode,curArch,architecture,MCSR,holWordExtract]

-- Original csr257_mode0; independently derived signed-range/permission result.
example (base : riscv_state) : observation base 257 0 255 = (true,true,0,1,[false,false,true,true,true,true,true,true]) := by
  simp [observation,fixture,is_CSR_defined,csrRW,csrPR,checkCSROp,check_CSR_access,
    curPrivilege,privLevel,privilege,in32BitMode,curArch,architecture,MCSR,holWordExtract]

-- Original csr258_mode0; independently derived signed-range/permission result.
example (base : riscv_state) : observation base 258 0 7 = (true,true,0,1,[false,false,true,true,true,true,true,true]) := by
  simp [observation,fixture,is_CSR_defined,csrRW,csrPR,checkCSROp,check_CSR_access,
    curPrivilege,privLevel,privilege,in32BitMode,curArch,architecture,MCSR,holWordExtract]

-- Original csr259_mode0; independently derived signed-range/permission result.
example (base : riscv_state) : observation base 259 0 255 = (true,true,0,1,[false,false,true,true,true,true,true,true]) := by
  simp [observation,fixture,is_CSR_defined,csrRW,csrPR,checkCSROp,check_CSR_access,
    curPrivilege,privLevel,privilege,in32BitMode,curArch,architecture,MCSR,holWordExtract]

-- Original csr260_mode0; independently derived signed-range/permission result.
example (base : riscv_state) : observation base 260 0 7 = (true,true,0,1,[false,false,true,true,true,true,true,true]) := by
  simp [observation,fixture,is_CSR_defined,csrRW,csrPR,checkCSROp,check_CSR_access,
    curPrivilege,privLevel,privilege,in32BitMode,curArch,architecture,MCSR,holWordExtract]

-- Original csr261_mode0; independently derived signed-range/permission result.
example (base : riscv_state) : observation base 261 0 255 = (true,true,0,1,[false,false,true,true,true,true,true,true]) := by
  simp [observation,fixture,is_CSR_defined,csrRW,csrPR,checkCSROp,check_CSR_access,
    curPrivilege,privLevel,privilege,in32BitMode,curArch,architecture,MCSR,holWordExtract]

-- Original csr288_mode0; independently derived signed-range/permission result.
example (base : riscv_state) : observation base 288 0 7 = (true,true,0,1,[false,false,true,true,true,true,true,true]) := by
  simp [observation,fixture,is_CSR_defined,csrRW,csrPR,checkCSROp,check_CSR_access,
    curPrivilege,privLevel,privilege,in32BitMode,curArch,architecture,MCSR,holWordExtract]

-- Original csr289_mode0; independently derived signed-range/permission result.
example (base : riscv_state) : observation base 289 0 255 = (true,true,0,1,[false,false,true,true,true,true,true,true]) := by
  simp [observation,fixture,is_CSR_defined,csrRW,csrPR,checkCSROp,check_CSR_access,
    curPrivilege,privLevel,privilege,in32BitMode,curArch,architecture,MCSR,holWordExtract]

-- Original csr290_mode0; independently derived signed-range/permission result.
example (base : riscv_state) : observation base 290 0 7 = (true,true,0,1,[false,false,true,true,true,true,true,true]) := by
  simp [observation,fixture,is_CSR_defined,csrRW,csrPR,checkCSROp,check_CSR_access,
    curPrivilege,privLevel,privilege,in32BitMode,curArch,architecture,MCSR,holWordExtract]

-- Original csr319_mode0; independently derived signed-range/permission result.
example (base : riscv_state) : observation base 319 0 255 = (true,true,0,1,[false,false,true,true,true,true,true,true]) := by
  simp [observation,fixture,is_CSR_defined,csrRW,csrPR,checkCSROp,check_CSR_access,
    curPrivilege,privLevel,privilege,in32BitMode,curArch,architecture,MCSR,holWordExtract]

-- Original csr320_mode0; independently derived signed-range/permission result.
example (base : riscv_state) : observation base 320 0 7 = (true,true,0,1,[false,false,true,true,true,true,true,true]) := by
  simp [observation,fixture,is_CSR_defined,csrRW,csrPR,checkCSROp,check_CSR_access,
    curPrivilege,privLevel,privilege,in32BitMode,curArch,architecture,MCSR,holWordExtract]

-- Original csr321_mode0; independently derived signed-range/permission result.
example (base : riscv_state) : observation base 321 0 255 = (true,true,0,1,[false,false,true,true,true,true,true,true]) := by
  simp [observation,fixture,is_CSR_defined,csrRW,csrPR,checkCSROp,check_CSR_access,
    curPrivilege,privLevel,privilege,in32BitMode,curArch,architecture,MCSR,holWordExtract]

-- Original csr322_mode0; independently derived signed-range/permission result.
example (base : riscv_state) : observation base 322 0 7 = (true,true,0,1,[false,false,true,true,true,true,true,true]) := by
  simp [observation,fixture,is_CSR_defined,csrRW,csrPR,checkCSROp,check_CSR_access,
    curPrivilege,privLevel,privilege,in32BitMode,curArch,architecture,MCSR,holWordExtract]

-- Original csr323_mode0; independently derived signed-range/permission result.
example (base : riscv_state) : observation base 323 0 255 = (true,true,0,1,[false,false,true,true,true,true,true,true]) := by
  simp [observation,fixture,is_CSR_defined,csrRW,csrPR,checkCSROp,check_CSR_access,
    curPrivilege,privLevel,privilege,in32BitMode,curArch,architecture,MCSR,holWordExtract]

-- Original csr324_mode0; independently derived signed-range/permission result.
example (base : riscv_state) : observation base 324 0 7 = (true,true,0,1,[false,false,true,true,true,true,true,true]) := by
  simp [observation,fixture,is_CSR_defined,csrRW,csrPR,checkCSROp,check_CSR_access,
    curPrivilege,privLevel,privilege,in32BitMode,curArch,architecture,MCSR,holWordExtract]

-- Original csr325_mode0; independently derived signed-range/permission result.
example (base : riscv_state) : observation base 325 0 255 = (true,true,0,1,[false,false,true,true,true,true,true,true]) := by
  simp [observation,fixture,is_CSR_defined,csrRW,csrPR,checkCSROp,check_CSR_access,
    curPrivilege,privLevel,privilege,in32BitMode,curArch,architecture,MCSR,holWordExtract]

-- Original csr383_mode0; independently derived signed-range/permission result.
example (base : riscv_state) : observation base 383 0 255 = (true,true,0,1,[false,false,true,true,true,true,true,true]) := by
  simp [observation,fixture,is_CSR_defined,csrRW,csrPR,checkCSROp,check_CSR_access,
    curPrivilege,privLevel,privilege,in32BitMode,curArch,architecture,MCSR,holWordExtract]

-- Original csr384_mode0; independently derived signed-range/permission result.
example (base : riscv_state) : observation base 384 0 7 = (true,true,0,1,[false,false,true,true,true,true,true,true]) := by
  simp [observation,fixture,is_CSR_defined,csrRW,csrPR,checkCSROp,check_CSR_access,
    curPrivilege,privLevel,privilege,in32BitMode,curArch,architecture,MCSR,holWordExtract]

-- Original csr385_mode0; independently derived signed-range/permission result.
example (base : riscv_state) : observation base 385 0 255 = (true,true,0,1,[false,false,true,true,true,true,true,true]) := by
  simp [observation,fixture,is_CSR_defined,csrRW,csrPR,checkCSROp,check_CSR_access,
    curPrivilege,privLevel,privilege,in32BitMode,curArch,architecture,MCSR,holWordExtract]

-- Original csr386_mode0; independently derived signed-range/permission result.
example (base : riscv_state) : observation base 386 0 7 = (true,true,0,1,[false,false,true,true,true,true,true,true]) := by
  simp [observation,fixture,is_CSR_defined,csrRW,csrPR,checkCSROp,check_CSR_access,
    curPrivilege,privLevel,privilege,in32BitMode,curArch,architecture,MCSR,holWordExtract]

-- Original csr767_mode0; independently derived signed-range/permission result.
example (base : riscv_state) : observation base 767 0 255 = (true,true,0,2,[false,false,false,false,true,true,true,true]) := by
  simp [observation,fixture,is_CSR_defined,csrRW,csrPR,checkCSROp,check_CSR_access,
    curPrivilege,privLevel,privilege,in32BitMode,curArch,architecture,MCSR,holWordExtract]

-- Original csr768_mode0; independently derived signed-range/permission result.
example (base : riscv_state) : observation base 768 0 7 = (true,true,0,3,[false,false,false,false,false,false,true,true]) := by
  simp [observation,fixture,is_CSR_defined,csrRW,csrPR,checkCSROp,check_CSR_access,
    curPrivilege,privLevel,privilege,in32BitMode,curArch,architecture,MCSR,holWordExtract]

-- Original csr770_mode0; independently derived signed-range/permission result.
example (base : riscv_state) : observation base 770 0 7 = (true,true,0,3,[false,false,false,false,false,false,true,true]) := by
  simp [observation,fixture,is_CSR_defined,csrRW,csrPR,checkCSROp,check_CSR_access,
    curPrivilege,privLevel,privilege,in32BitMode,curArch,architecture,MCSR,holWordExtract]

-- Original csr771_mode0; independently derived signed-range/permission result.
example (base : riscv_state) : observation base 771 0 255 = (true,true,0,3,[false,false,false,false,false,false,true,true]) := by
  simp [observation,fixture,is_CSR_defined,csrRW,csrPR,checkCSROp,check_CSR_access,
    curPrivilege,privLevel,privilege,in32BitMode,curArch,architecture,MCSR,holWordExtract]

-- Original csr772_mode0; independently derived signed-range/permission result.
example (base : riscv_state) : observation base 772 0 7 = (true,true,0,3,[false,false,false,false,false,false,true,true]) := by
  simp [observation,fixture,is_CSR_defined,csrRW,csrPR,checkCSROp,check_CSR_access,
    curPrivilege,privLevel,privilege,in32BitMode,curArch,architecture,MCSR,holWordExtract]

-- Original csr773_mode0; independently derived signed-range/permission result.
example (base : riscv_state) : observation base 773 0 255 = (true,true,0,3,[false,false,false,false,false,false,true,true]) := by
  simp [observation,fixture,is_CSR_defined,csrRW,csrPR,checkCSROp,check_CSR_access,
    curPrivilege,privLevel,privilege,in32BitMode,curArch,architecture,MCSR,holWordExtract]

-- Original csr800_mode0; independently derived signed-range/permission result.
example (base : riscv_state) : observation base 800 0 7 = (true,true,0,3,[false,false,false,false,false,false,true,true]) := by
  simp [observation,fixture,is_CSR_defined,csrRW,csrPR,checkCSROp,check_CSR_access,
    curPrivilege,privLevel,privilege,in32BitMode,curArch,architecture,MCSR,holWordExtract]

-- Original csr801_mode0; independently derived signed-range/permission result.
example (base : riscv_state) : observation base 801 0 255 = (true,true,0,3,[false,false,false,false,false,false,true,true]) := by
  simp [observation,fixture,is_CSR_defined,csrRW,csrPR,checkCSROp,check_CSR_access,
    curPrivilege,privLevel,privilege,in32BitMode,curArch,architecture,MCSR,holWordExtract]

-- Original csr802_mode0; independently derived signed-range/permission result.
example (base : riscv_state) : observation base 802 0 7 = (true,true,0,3,[false,false,false,false,false,false,true,true]) := by
  simp [observation,fixture,is_CSR_defined,csrRW,csrPR,checkCSROp,check_CSR_access,
    curPrivilege,privLevel,privilege,in32BitMode,curArch,architecture,MCSR,holWordExtract]

-- Original csr831_mode0; independently derived signed-range/permission result.
example (base : riscv_state) : observation base 831 0 255 = (true,true,0,3,[false,false,false,false,false,false,true,true]) := by
  simp [observation,fixture,is_CSR_defined,csrRW,csrPR,checkCSROp,check_CSR_access,
    curPrivilege,privLevel,privilege,in32BitMode,curArch,architecture,MCSR,holWordExtract]

-- Original csr832_mode0; independently derived signed-range/permission result.
example (base : riscv_state) : observation base 832 0 7 = (true,true,0,3,[false,false,false,false,false,false,true,true]) := by
  simp [observation,fixture,is_CSR_defined,csrRW,csrPR,checkCSROp,check_CSR_access,
    curPrivilege,privLevel,privilege,in32BitMode,curArch,architecture,MCSR,holWordExtract]

-- Original csr836_mode0; independently derived signed-range/permission result.
example (base : riscv_state) : observation base 836 0 7 = (true,true,0,3,[false,false,false,false,false,false,true,true]) := by
  simp [observation,fixture,is_CSR_defined,csrRW,csrPR,checkCSROp,check_CSR_access,
    curPrivilege,privLevel,privilege,in32BitMode,curArch,architecture,MCSR,holWordExtract]

-- Original csr837_mode0; independently derived signed-range/permission result.
example (base : riscv_state) : observation base 837 0 255 = (true,true,0,3,[false,false,false,false,false,false,true,true]) := by
  simp [observation,fixture,is_CSR_defined,csrRW,csrPR,checkCSROp,check_CSR_access,
    curPrivilege,privLevel,privilege,in32BitMode,curArch,architecture,MCSR,holWordExtract]

-- Original csr895_mode0; independently derived signed-range/permission result.
example (base : riscv_state) : observation base 895 0 255 = (true,true,0,3,[false,false,false,false,false,false,true,true]) := by
  simp [observation,fixture,is_CSR_defined,csrRW,csrPR,checkCSROp,check_CSR_access,
    curPrivilege,privLevel,privilege,in32BitMode,curArch,architecture,MCSR,holWordExtract]

-- Original csr896_mode0; independently derived signed-range/permission result.
example (base : riscv_state) : observation base 896 0 7 = (true,true,0,3,[false,false,false,false,false,false,true,true]) := by
  simp [observation,fixture,is_CSR_defined,csrRW,csrPR,checkCSROp,check_CSR_access,
    curPrivilege,privLevel,privilege,in32BitMode,curArch,architecture,MCSR,holWordExtract]

-- Original csr901_mode0; independently derived signed-range/permission result.
example (base : riscv_state) : observation base 901 0 255 = (true,true,0,3,[false,false,false,false,false,false,true,true]) := by
  simp [observation,fixture,is_CSR_defined,csrRW,csrPR,checkCSROp,check_CSR_access,
    curPrivilege,privLevel,privilege,in32BitMode,curArch,architecture,MCSR,holWordExtract]

-- Original csr902_mode0; independently derived signed-range/permission result.
example (base : riscv_state) : observation base 902 0 7 = (true,true,0,3,[false,false,false,false,false,false,true,true]) := by
  simp [observation,fixture,is_CSR_defined,csrRW,csrPR,checkCSROp,check_CSR_access,
    curPrivilege,privLevel,privilege,in32BitMode,curArch,architecture,MCSR,holWordExtract]

-- Original csr1792_mode0; independently derived signed-range/permission result.
example (base : riscv_state) : observation base 1792 0 7 = (true,true,1,3,[false,false,false,false,false,false,true,true]) := by
  simp [observation,fixture,is_CSR_defined,csrRW,csrPR,checkCSROp,check_CSR_access,
    curPrivilege,privLevel,privilege,in32BitMode,curArch,architecture,MCSR,holWordExtract]

-- Original csr1793_mode0; independently derived signed-range/permission result.
example (base : riscv_state) : observation base 1793 0 255 = (true,true,1,3,[false,false,false,false,false,false,true,true]) := by
  simp [observation,fixture,is_CSR_defined,csrRW,csrPR,checkCSROp,check_CSR_access,
    curPrivilege,privLevel,privilege,in32BitMode,curArch,architecture,MCSR,holWordExtract]

-- Original csr1794_mode0; independently derived signed-range/permission result.
example (base : riscv_state) : observation base 1794 0 7 = (true,true,1,3,[false,false,false,false,false,false,true,true]) := by
  simp [observation,fixture,is_CSR_defined,csrRW,csrPR,checkCSROp,check_CSR_access,
    curPrivilege,privLevel,privilege,in32BitMode,curArch,architecture,MCSR,holWordExtract]

-- Original csr1856_mode0; independently derived signed-range/permission result.
example (base : riscv_state) : observation base 1856 0 7 = (true,true,1,3,[false,false,false,false,false,false,true,true]) := by
  simp [observation,fixture,is_CSR_defined,csrRW,csrPR,checkCSROp,check_CSR_access,
    curPrivilege,privLevel,privilege,in32BitMode,curArch,architecture,MCSR,holWordExtract]

-- Original csr1857_mode0; independently derived signed-range/permission result.
example (base : riscv_state) : observation base 1857 0 255 = (true,true,1,3,[false,false,false,false,false,false,true,true]) := by
  simp [observation,fixture,is_CSR_defined,csrRW,csrPR,checkCSROp,check_CSR_access,
    curPrivilege,privLevel,privilege,in32BitMode,curArch,architecture,MCSR,holWordExtract]

-- Original csr1858_mode0; independently derived signed-range/permission result.
example (base : riscv_state) : observation base 1858 0 7 = (true,true,1,3,[false,false,false,false,false,false,true,true]) := by
  simp [observation,fixture,is_CSR_defined,csrRW,csrPR,checkCSROp,check_CSR_access,
    curPrivilege,privLevel,privilege,in32BitMode,curArch,architecture,MCSR,holWordExtract]

-- Original csr1919_mode0; independently derived signed-range/permission result.
example (base : riscv_state) : observation base 1919 0 255 = (true,true,1,3,[false,false,false,false,false,false,true,true]) := by
  simp [observation,fixture,is_CSR_defined,csrRW,csrPR,checkCSROp,check_CSR_access,
    curPrivilege,privLevel,privilege,in32BitMode,curArch,architecture,MCSR,holWordExtract]

-- Original csr1920_mode0; independently derived signed-range/permission result.
example (base : riscv_state) : observation base 1920 0 7 = (true,true,1,3,[false,false,false,false,false,false,true,true]) := by
  simp [observation,fixture,is_CSR_defined,csrRW,csrPR,checkCSROp,check_CSR_access,
    curPrivilege,privLevel,privilege,in32BitMode,curArch,architecture,MCSR,holWordExtract]

-- Original csr1922_mode0; independently derived signed-range/permission result.
example (base : riscv_state) : observation base 1922 0 7 = (true,true,1,3,[false,false,false,false,false,false,true,true]) := by
  simp [observation,fixture,is_CSR_defined,csrRW,csrPR,checkCSROp,check_CSR_access,
    curPrivilege,privLevel,privilege,in32BitMode,curArch,architecture,MCSR,holWordExtract]

-- Original csr1923_mode0; independently derived signed-range/permission result.
example (base : riscv_state) : observation base 1923 0 255 = (true,true,1,3,[false,false,false,false,false,false,true,true]) := by
  simp [observation,fixture,is_CSR_defined,csrRW,csrPR,checkCSROp,check_CSR_access,
    curPrivilege,privLevel,privilege,in32BitMode,curArch,architecture,MCSR,holWordExtract]

-- Original csr1924_mode0; independently derived signed-range/permission result.
example (base : riscv_state) : observation base 1924 0 7 = (true,true,1,3,[false,false,false,false,false,false,true,true]) := by
  simp [observation,fixture,is_CSR_defined,csrRW,csrPR,checkCSROp,check_CSR_access,
    curPrivilege,privLevel,privilege,in32BitMode,curArch,architecture,MCSR,holWordExtract]

-- Original csr2047_mode0; independently derived signed-range/permission result.
example (base : riscv_state) : observation base 2047 0 255 = (true,true,1,3,[false,false,false,false,false,false,true,true]) := by
  simp [observation,fixture,is_CSR_defined,csrRW,csrPR,checkCSROp,check_CSR_access,
    curPrivilege,privLevel,privilege,in32BitMode,curArch,architecture,MCSR,holWordExtract]

-- Original csr2048_mode0; independently derived signed-range/permission result.
example (base : riscv_state) : observation base 2048 0 7 = (false,true,2,0,[false,false,false,false,false,false,false,false]) := by
  simp [observation,fixture,is_CSR_defined,csrRW,csrPR,checkCSROp,check_CSR_access,
    curPrivilege,privLevel,privilege,in32BitMode,curArch,architecture,MCSR,holWordExtract]

-- Original csr2303_mode0; independently derived signed-range/permission result.
example (base : riscv_state) : observation base 2303 0 255 = (false,true,2,0,[false,false,false,false,false,false,false,false]) := by
  simp [observation,fixture,is_CSR_defined,csrRW,csrPR,checkCSROp,check_CSR_access,
    curPrivilege,privLevel,privilege,in32BitMode,curArch,architecture,MCSR,holWordExtract]

-- Original csr2304_mode0; independently derived signed-range/permission result.
example (base : riscv_state) : observation base 2304 0 7 = (true,true,2,1,[false,false,true,true,true,true,true,true]) := by
  simp [observation,fixture,is_CSR_defined,csrRW,csrPR,checkCSROp,check_CSR_access,
    curPrivilege,privLevel,privilege,in32BitMode,curArch,architecture,MCSR,holWordExtract]

-- Original csr2306_mode0; independently derived signed-range/permission result.
example (base : riscv_state) : observation base 2306 0 7 = (true,true,2,1,[false,false,true,true,true,true,true,true]) := by
  simp [observation,fixture,is_CSR_defined,csrRW,csrPR,checkCSROp,check_CSR_access,
    curPrivilege,privLevel,privilege,in32BitMode,curArch,architecture,MCSR,holWordExtract]

-- Original csr2307_mode0; independently derived signed-range/permission result.
example (base : riscv_state) : observation base 2307 0 255 = (false,true,2,1,[false,false,false,false,false,false,false,false]) := by
  simp [observation,fixture,is_CSR_defined,csrRW,csrPR,checkCSROp,check_CSR_access,
    curPrivilege,privLevel,privilege,in32BitMode,curArch,architecture,MCSR,holWordExtract]

-- Original csr2431_mode0; independently derived signed-range/permission result.
example (base : riscv_state) : observation base 2431 0 255 = (false,true,2,1,[false,false,false,false,false,false,false,false]) := by
  simp [observation,fixture,is_CSR_defined,csrRW,csrPR,checkCSROp,check_CSR_access,
    curPrivilege,privLevel,privilege,in32BitMode,curArch,architecture,MCSR,holWordExtract]

-- Original csr2432_mode0; independently derived signed-range/permission result.
example (base : riscv_state) : observation base 2432 0 7 = (true,true,2,1,[false,false,true,true,true,true,true,true]) := by
  simp [observation,fixture,is_CSR_defined,csrRW,csrPR,checkCSROp,check_CSR_access,
    curPrivilege,privLevel,privilege,in32BitMode,curArch,architecture,MCSR,holWordExtract]

-- Original csr2434_mode0; independently derived signed-range/permission result.
example (base : riscv_state) : observation base 2434 0 7 = (true,true,2,1,[false,false,true,true,true,true,true,true]) := by
  simp [observation,fixture,is_CSR_defined,csrRW,csrPR,checkCSROp,check_CSR_access,
    curPrivilege,privLevel,privilege,in32BitMode,curArch,architecture,MCSR,holWordExtract]

-- Original csr2435_mode0; independently derived signed-range/permission result.
example (base : riscv_state) : observation base 2435 0 255 = (false,true,2,1,[false,false,false,false,false,false,false,false]) := by
  simp [observation,fixture,is_CSR_defined,csrRW,csrPR,checkCSROp,check_CSR_access,
    curPrivilege,privLevel,privilege,in32BitMode,curArch,architecture,MCSR,holWordExtract]

-- Original csr2816_mode0; independently derived signed-range/permission result.
example (base : riscv_state) : observation base 2816 0 7 = (false,true,2,3,[false,false,false,false,false,false,false,false]) := by
  simp [observation,fixture,is_CSR_defined,csrRW,csrPR,checkCSROp,check_CSR_access,
    curPrivilege,privLevel,privilege,in32BitMode,curArch,architecture,MCSR,holWordExtract]

-- Original csr2817_mode0; independently derived signed-range/permission result.
example (base : riscv_state) : observation base 2817 0 255 = (true,true,2,3,[false,false,false,false,false,false,true,true]) := by
  simp [observation,fixture,is_CSR_defined,csrRW,csrPR,checkCSROp,check_CSR_access,
    curPrivilege,privLevel,privilege,in32BitMode,curArch,architecture,MCSR,holWordExtract]

-- Original csr2818_mode0; independently derived signed-range/permission result.
example (base : riscv_state) : observation base 2818 0 7 = (true,true,2,3,[false,false,false,false,false,false,true,true]) := by
  simp [observation,fixture,is_CSR_defined,csrRW,csrPR,checkCSROp,check_CSR_access,
    curPrivilege,privLevel,privilege,in32BitMode,curArch,architecture,MCSR,holWordExtract]

-- Original csr2944_mode0; independently derived signed-range/permission result.
example (base : riscv_state) : observation base 2944 0 7 = (true,true,2,3,[false,false,false,false,false,false,true,true]) := by
  simp [observation,fixture,is_CSR_defined,csrRW,csrPR,checkCSROp,check_CSR_access,
    curPrivilege,privLevel,privilege,in32BitMode,curArch,architecture,MCSR,holWordExtract]

-- Original csr2945_mode0; independently derived signed-range/permission result.
example (base : riscv_state) : observation base 2945 0 255 = (true,true,2,3,[false,false,false,false,false,false,true,true]) := by
  simp [observation,fixture,is_CSR_defined,csrRW,csrPR,checkCSROp,check_CSR_access,
    curPrivilege,privLevel,privilege,in32BitMode,curArch,architecture,MCSR,holWordExtract]

-- Original csr2946_mode0; independently derived signed-range/permission result.
example (base : riscv_state) : observation base 2946 0 7 = (true,true,2,3,[false,false,false,false,false,false,true,true]) := by
  simp [observation,fixture,is_CSR_defined,csrRW,csrPR,checkCSROp,check_CSR_access,
    curPrivilege,privLevel,privilege,in32BitMode,curArch,architecture,MCSR,holWordExtract]

-- Original csr3071_mode0; independently derived signed-range/permission result.
example (base : riscv_state) : observation base 3071 0 255 = (true,true,2,3,[false,false,false,false,false,false,true,true]) := by
  simp [observation,fixture,is_CSR_defined,csrRW,csrPR,checkCSROp,check_CSR_access,
    curPrivilege,privLevel,privilege,in32BitMode,curArch,architecture,MCSR,holWordExtract]

-- Original csr3072_mode0; independently derived signed-range/permission result.
example (base : riscv_state) : observation base 3072 0 7 = (true,true,3,0,[true,false,true,false,true,false,true,false]) := by
  simp [observation,fixture,is_CSR_defined,csrRW,csrPR,checkCSROp,check_CSR_access,
    curPrivilege,privLevel,privilege,in32BitMode,curArch,architecture,MCSR,holWordExtract]

-- Original csr3074_mode0; independently derived signed-range/permission result.
example (base : riscv_state) : observation base 3074 0 7 = (true,true,3,0,[true,false,true,false,true,false,true,false]) := by
  simp [observation,fixture,is_CSR_defined,csrRW,csrPR,checkCSROp,check_CSR_access,
    curPrivilege,privLevel,privilege,in32BitMode,curArch,architecture,MCSR,holWordExtract]

-- Original csr3075_mode0; independently derived signed-range/permission result.
example (base : riscv_state) : observation base 3075 0 255 = (true,true,3,0,[true,false,true,false,true,false,true,false]) := by
  simp [observation,fixture,is_CSR_defined,csrRW,csrPR,checkCSROp,check_CSR_access,
    curPrivilege,privLevel,privilege,in32BitMode,curArch,architecture,MCSR,holWordExtract]

-- Original csr3199_mode0; independently derived signed-range/permission result.
example (base : riscv_state) : observation base 3199 0 255 = (true,true,3,0,[true,false,true,false,true,false,true,false]) := by
  simp [observation,fixture,is_CSR_defined,csrRW,csrPR,checkCSROp,check_CSR_access,
    curPrivilege,privLevel,privilege,in32BitMode,curArch,architecture,MCSR,holWordExtract]

-- Original csr3200_mode0; independently derived signed-range/permission result.
example (base : riscv_state) : observation base 3200 0 7 = (true,true,3,0,[true,false,true,false,true,false,true,false]) := by
  simp [observation,fixture,is_CSR_defined,csrRW,csrPR,checkCSROp,check_CSR_access,
    curPrivilege,privLevel,privilege,in32BitMode,curArch,architecture,MCSR,holWordExtract]

-- Original csr3202_mode0; independently derived signed-range/permission result.
example (base : riscv_state) : observation base 3202 0 7 = (true,true,3,0,[true,false,true,false,true,false,true,false]) := by
  simp [observation,fixture,is_CSR_defined,csrRW,csrPR,checkCSROp,check_CSR_access,
    curPrivilege,privLevel,privilege,in32BitMode,curArch,architecture,MCSR,holWordExtract]

-- Original csr3203_mode0; independently derived signed-range/permission result.
example (base : riscv_state) : observation base 3203 0 255 = (true,true,3,0,[true,false,true,false,true,false,true,false]) := by
  simp [observation,fixture,is_CSR_defined,csrRW,csrPR,checkCSROp,check_CSR_access,
    curPrivilege,privLevel,privilege,in32BitMode,curArch,architecture,MCSR,holWordExtract]

-- Original csr3328_mode0; independently derived signed-range/permission result.
example (base : riscv_state) : observation base 3328 0 7 = (true,true,3,1,[false,false,true,false,true,false,true,false]) := by
  simp [observation,fixture,is_CSR_defined,csrRW,csrPR,checkCSROp,check_CSR_access,
    curPrivilege,privLevel,privilege,in32BitMode,curArch,architecture,MCSR,holWordExtract]

-- Original csr3329_mode0; independently derived signed-range/permission result.
example (base : riscv_state) : observation base 3329 0 255 = (true,true,3,1,[false,false,true,false,true,false,true,false]) := by
  simp [observation,fixture,is_CSR_defined,csrRW,csrPR,checkCSROp,check_CSR_access,
    curPrivilege,privLevel,privilege,in32BitMode,curArch,architecture,MCSR,holWordExtract]

-- Original csr3330_mode0; independently derived signed-range/permission result.
example (base : riscv_state) : observation base 3330 0 7 = (true,true,3,1,[false,false,true,false,true,false,true,false]) := by
  simp [observation,fixture,is_CSR_defined,csrRW,csrPR,checkCSROp,check_CSR_access,
    curPrivilege,privLevel,privilege,in32BitMode,curArch,architecture,MCSR,holWordExtract]

-- Original csr3393_mode0; independently derived signed-range/permission result.
example (base : riscv_state) : observation base 3393 0 255 = (true,true,3,1,[false,false,true,false,true,false,true,false]) := by
  simp [observation,fixture,is_CSR_defined,csrRW,csrPR,checkCSROp,check_CSR_access,
    curPrivilege,privLevel,privilege,in32BitMode,curArch,architecture,MCSR,holWordExtract]

-- Original csr3394_mode0; independently derived signed-range/permission result.
example (base : riscv_state) : observation base 3394 0 7 = (true,true,3,1,[false,false,true,false,true,false,true,false]) := by
  simp [observation,fixture,is_CSR_defined,csrRW,csrPR,checkCSROp,check_CSR_access,
    curPrivilege,privLevel,privilege,in32BitMode,curArch,architecture,MCSR,holWordExtract]

-- Original csr3395_mode0; independently derived signed-range/permission result.
example (base : riscv_state) : observation base 3395 0 255 = (true,true,3,1,[false,false,true,false,true,false,true,false]) := by
  simp [observation,fixture,is_CSR_defined,csrRW,csrPR,checkCSROp,check_CSR_access,
    curPrivilege,privLevel,privilege,in32BitMode,curArch,architecture,MCSR,holWordExtract]

-- Original csr3396_mode0; independently derived signed-range/permission result.
example (base : riscv_state) : observation base 3396 0 7 = (true,true,3,1,[false,false,true,false,true,false,true,false]) := by
  simp [observation,fixture,is_CSR_defined,csrRW,csrPR,checkCSROp,check_CSR_access,
    curPrivilege,privLevel,privilege,in32BitMode,curArch,architecture,MCSR,holWordExtract]

-- Original csr3456_mode0; independently derived signed-range/permission result.
example (base : riscv_state) : observation base 3456 0 7 = (true,true,3,1,[false,false,true,false,true,false,true,false]) := by
  simp [observation,fixture,is_CSR_defined,csrRW,csrPR,checkCSROp,check_CSR_access,
    curPrivilege,privLevel,privilege,in32BitMode,curArch,architecture,MCSR,holWordExtract]

-- Original csr3457_mode0; independently derived signed-range/permission result.
example (base : riscv_state) : observation base 3457 0 255 = (true,true,3,1,[false,false,true,false,true,false,true,false]) := by
  simp [observation,fixture,is_CSR_defined,csrRW,csrPR,checkCSROp,check_CSR_access,
    curPrivilege,privLevel,privilege,in32BitMode,curArch,architecture,MCSR,holWordExtract]

-- Original csr3458_mode0; independently derived signed-range/permission result.
example (base : riscv_state) : observation base 3458 0 7 = (true,true,3,1,[false,false,true,false,true,false,true,false]) := by
  simp [observation,fixture,is_CSR_defined,csrRW,csrPR,checkCSROp,check_CSR_access,
    curPrivilege,privLevel,privilege,in32BitMode,curArch,architecture,MCSR,holWordExtract]

-- Original csr3839_mode0; independently derived signed-range/permission result.
example (base : riscv_state) : observation base 3839 0 255 = (true,true,3,2,[false,false,false,false,true,false,true,false]) := by
  simp [observation,fixture,is_CSR_defined,csrRW,csrPR,checkCSROp,check_CSR_access,
    curPrivilege,privLevel,privilege,in32BitMode,curArch,architecture,MCSR,holWordExtract]

-- Original csr3840_mode0; independently derived signed-range/permission result.
example (base : riscv_state) : observation base 3840 0 7 = (true,true,3,3,[false,false,false,false,false,false,true,false]) := by
  simp [observation,fixture,is_CSR_defined,csrRW,csrPR,checkCSROp,check_CSR_access,
    curPrivilege,privLevel,privilege,in32BitMode,curArch,architecture,MCSR,holWordExtract]

-- Original csr3841_mode0; independently derived signed-range/permission result.
example (base : riscv_state) : observation base 3841 0 255 = (true,true,3,3,[false,false,false,false,false,false,true,false]) := by
  simp [observation,fixture,is_CSR_defined,csrRW,csrPR,checkCSROp,check_CSR_access,
    curPrivilege,privLevel,privilege,in32BitMode,curArch,architecture,MCSR,holWordExtract]

-- Original csr3842_mode0; independently derived signed-range/permission result.
example (base : riscv_state) : observation base 3842 0 7 = (true,true,3,3,[false,false,false,false,false,false,true,false]) := by
  simp [observation,fixture,is_CSR_defined,csrRW,csrPR,checkCSROp,check_CSR_access,
    curPrivilege,privLevel,privilege,in32BitMode,curArch,architecture,MCSR,holWordExtract]

-- Original csr3855_mode0; independently derived signed-range/permission result.
example (base : riscv_state) : observation base 3855 0 255 = (true,true,3,3,[false,false,false,false,false,false,true,false]) := by
  simp [observation,fixture,is_CSR_defined,csrRW,csrPR,checkCSROp,check_CSR_access,
    curPrivilege,privLevel,privilege,in32BitMode,curArch,architecture,MCSR,holWordExtract]

-- Original csr3856_mode0; independently derived signed-range/permission result.
example (base : riscv_state) : observation base 3856 0 7 = (true,true,3,3,[false,false,false,false,false,false,true,false]) := by
  simp [observation,fixture,is_CSR_defined,csrRW,csrPR,checkCSROp,check_CSR_access,
    curPrivilege,privLevel,privilege,in32BitMode,curArch,architecture,MCSR,holWordExtract]

-- Original csr3857_mode0; independently derived signed-range/permission result.
example (base : riscv_state) : observation base 3857 0 255 = (true,true,3,3,[false,false,false,false,false,false,true,false]) := by
  simp [observation,fixture,is_CSR_defined,csrRW,csrPR,checkCSROp,check_CSR_access,
    curPrivilege,privLevel,privilege,in32BitMode,curArch,architecture,MCSR,holWordExtract]

-- Original csr4095_mode0; independently derived signed-range/permission result.
example (base : riscv_state) : observation base 4095 0 255 = (true,true,3,3,[false,false,false,false,false,false,true,false]) := by
  simp [observation,fixture,is_CSR_defined,csrRW,csrPR,checkCSROp,check_CSR_access,
    curPrivilege,privLevel,privilege,in32BitMode,curArch,architecture,MCSR,holWordExtract]

-- Original csr0_mode2; independently derived signed-range/permission result.
example (base : riscv_state) : observation base 0 2 7 = (true,true,0,0,[true,true,true,true,true,true,true,true]) := by
  simp [observation,fixture,is_CSR_defined,csrRW,csrPR,checkCSROp,check_CSR_access,
    curPrivilege,privLevel,privilege,in32BitMode,curArch,architecture,MCSR,holWordExtract]

-- Original csr1_mode2; independently derived signed-range/permission result.
example (base : riscv_state) : observation base 1 2 255 = (true,true,0,0,[true,true,true,true,true,true,true,true]) := by
  simp [observation,fixture,is_CSR_defined,csrRW,csrPR,checkCSROp,check_CSR_access,
    curPrivilege,privLevel,privilege,in32BitMode,curArch,architecture,MCSR,holWordExtract]

-- Original csr3_mode2; independently derived signed-range/permission result.
example (base : riscv_state) : observation base 3 2 255 = (true,true,0,0,[true,true,true,true,true,true,true,true]) := by
  simp [observation,fixture,is_CSR_defined,csrRW,csrPR,checkCSROp,check_CSR_access,
    curPrivilege,privLevel,privilege,in32BitMode,curArch,architecture,MCSR,holWordExtract]

-- Original csr4_mode2; independently derived signed-range/permission result.
example (base : riscv_state) : observation base 4 2 7 = (true,true,0,0,[true,true,true,true,true,true,true,true]) := by
  simp [observation,fixture,is_CSR_defined,csrRW,csrPR,checkCSROp,check_CSR_access,
    curPrivilege,privLevel,privilege,in32BitMode,curArch,architecture,MCSR,holWordExtract]

-- Original csr255_mode2; independently derived signed-range/permission result.
example (base : riscv_state) : observation base 255 2 255 = (true,true,0,0,[true,true,true,true,true,true,true,true]) := by
  simp [observation,fixture,is_CSR_defined,csrRW,csrPR,checkCSROp,check_CSR_access,
    curPrivilege,privLevel,privilege,in32BitMode,curArch,architecture,MCSR,holWordExtract]

-- Original csr256_mode2; independently derived signed-range/permission result.
example (base : riscv_state) : observation base 256 2 7 = (true,true,0,1,[false,false,true,true,true,true,true,true]) := by
  simp [observation,fixture,is_CSR_defined,csrRW,csrPR,checkCSROp,check_CSR_access,
    curPrivilege,privLevel,privilege,in32BitMode,curArch,architecture,MCSR,holWordExtract]

-- Original csr257_mode2; independently derived signed-range/permission result.
example (base : riscv_state) : observation base 257 2 255 = (true,true,0,1,[false,false,true,true,true,true,true,true]) := by
  simp [observation,fixture,is_CSR_defined,csrRW,csrPR,checkCSROp,check_CSR_access,
    curPrivilege,privLevel,privilege,in32BitMode,curArch,architecture,MCSR,holWordExtract]

-- Original csr258_mode2; independently derived signed-range/permission result.
example (base : riscv_state) : observation base 258 2 7 = (true,true,0,1,[false,false,true,true,true,true,true,true]) := by
  simp [observation,fixture,is_CSR_defined,csrRW,csrPR,checkCSROp,check_CSR_access,
    curPrivilege,privLevel,privilege,in32BitMode,curArch,architecture,MCSR,holWordExtract]

-- Original csr259_mode2; independently derived signed-range/permission result.
example (base : riscv_state) : observation base 259 2 255 = (true,true,0,1,[false,false,true,true,true,true,true,true]) := by
  simp [observation,fixture,is_CSR_defined,csrRW,csrPR,checkCSROp,check_CSR_access,
    curPrivilege,privLevel,privilege,in32BitMode,curArch,architecture,MCSR,holWordExtract]

-- Original csr260_mode2; independently derived signed-range/permission result.
example (base : riscv_state) : observation base 260 2 7 = (true,true,0,1,[false,false,true,true,true,true,true,true]) := by
  simp [observation,fixture,is_CSR_defined,csrRW,csrPR,checkCSROp,check_CSR_access,
    curPrivilege,privLevel,privilege,in32BitMode,curArch,architecture,MCSR,holWordExtract]

-- Original csr261_mode2; independently derived signed-range/permission result.
example (base : riscv_state) : observation base 261 2 255 = (true,true,0,1,[false,false,true,true,true,true,true,true]) := by
  simp [observation,fixture,is_CSR_defined,csrRW,csrPR,checkCSROp,check_CSR_access,
    curPrivilege,privLevel,privilege,in32BitMode,curArch,architecture,MCSR,holWordExtract]

-- Original csr288_mode2; independently derived signed-range/permission result.
example (base : riscv_state) : observation base 288 2 7 = (true,true,0,1,[false,false,true,true,true,true,true,true]) := by
  simp [observation,fixture,is_CSR_defined,csrRW,csrPR,checkCSROp,check_CSR_access,
    curPrivilege,privLevel,privilege,in32BitMode,curArch,architecture,MCSR,holWordExtract]

-- Original csr289_mode2; independently derived signed-range/permission result.
example (base : riscv_state) : observation base 289 2 255 = (true,true,0,1,[false,false,true,true,true,true,true,true]) := by
  simp [observation,fixture,is_CSR_defined,csrRW,csrPR,checkCSROp,check_CSR_access,
    curPrivilege,privLevel,privilege,in32BitMode,curArch,architecture,MCSR,holWordExtract]

-- Original csr290_mode2; independently derived signed-range/permission result.
example (base : riscv_state) : observation base 290 2 7 = (true,true,0,1,[false,false,true,true,true,true,true,true]) := by
  simp [observation,fixture,is_CSR_defined,csrRW,csrPR,checkCSROp,check_CSR_access,
    curPrivilege,privLevel,privilege,in32BitMode,curArch,architecture,MCSR,holWordExtract]

-- Original csr319_mode2; independently derived signed-range/permission result.
example (base : riscv_state) : observation base 319 2 255 = (true,true,0,1,[false,false,true,true,true,true,true,true]) := by
  simp [observation,fixture,is_CSR_defined,csrRW,csrPR,checkCSROp,check_CSR_access,
    curPrivilege,privLevel,privilege,in32BitMode,curArch,architecture,MCSR,holWordExtract]

-- Original csr320_mode2; independently derived signed-range/permission result.
example (base : riscv_state) : observation base 320 2 7 = (true,true,0,1,[false,false,true,true,true,true,true,true]) := by
  simp [observation,fixture,is_CSR_defined,csrRW,csrPR,checkCSROp,check_CSR_access,
    curPrivilege,privLevel,privilege,in32BitMode,curArch,architecture,MCSR,holWordExtract]

-- Original csr321_mode2; independently derived signed-range/permission result.
example (base : riscv_state) : observation base 321 2 255 = (true,true,0,1,[false,false,true,true,true,true,true,true]) := by
  simp [observation,fixture,is_CSR_defined,csrRW,csrPR,checkCSROp,check_CSR_access,
    curPrivilege,privLevel,privilege,in32BitMode,curArch,architecture,MCSR,holWordExtract]

-- Original csr322_mode2; independently derived signed-range/permission result.
example (base : riscv_state) : observation base 322 2 7 = (true,true,0,1,[false,false,true,true,true,true,true,true]) := by
  simp [observation,fixture,is_CSR_defined,csrRW,csrPR,checkCSROp,check_CSR_access,
    curPrivilege,privLevel,privilege,in32BitMode,curArch,architecture,MCSR,holWordExtract]

-- Original csr323_mode2; independently derived signed-range/permission result.
example (base : riscv_state) : observation base 323 2 255 = (true,true,0,1,[false,false,true,true,true,true,true,true]) := by
  simp [observation,fixture,is_CSR_defined,csrRW,csrPR,checkCSROp,check_CSR_access,
    curPrivilege,privLevel,privilege,in32BitMode,curArch,architecture,MCSR,holWordExtract]

-- Original csr324_mode2; independently derived signed-range/permission result.
example (base : riscv_state) : observation base 324 2 7 = (true,true,0,1,[false,false,true,true,true,true,true,true]) := by
  simp [observation,fixture,is_CSR_defined,csrRW,csrPR,checkCSROp,check_CSR_access,
    curPrivilege,privLevel,privilege,in32BitMode,curArch,architecture,MCSR,holWordExtract]

-- Original csr325_mode2; independently derived signed-range/permission result.
example (base : riscv_state) : observation base 325 2 255 = (true,true,0,1,[false,false,true,true,true,true,true,true]) := by
  simp [observation,fixture,is_CSR_defined,csrRW,csrPR,checkCSROp,check_CSR_access,
    curPrivilege,privLevel,privilege,in32BitMode,curArch,architecture,MCSR,holWordExtract]

-- Original csr383_mode2; independently derived signed-range/permission result.
example (base : riscv_state) : observation base 383 2 255 = (true,true,0,1,[false,false,true,true,true,true,true,true]) := by
  simp [observation,fixture,is_CSR_defined,csrRW,csrPR,checkCSROp,check_CSR_access,
    curPrivilege,privLevel,privilege,in32BitMode,curArch,architecture,MCSR,holWordExtract]

-- Original csr384_mode2; independently derived signed-range/permission result.
example (base : riscv_state) : observation base 384 2 7 = (true,true,0,1,[false,false,true,true,true,true,true,true]) := by
  simp [observation,fixture,is_CSR_defined,csrRW,csrPR,checkCSROp,check_CSR_access,
    curPrivilege,privLevel,privilege,in32BitMode,curArch,architecture,MCSR,holWordExtract]

-- Original csr385_mode2; independently derived signed-range/permission result.
example (base : riscv_state) : observation base 385 2 255 = (true,true,0,1,[false,false,true,true,true,true,true,true]) := by
  simp [observation,fixture,is_CSR_defined,csrRW,csrPR,checkCSROp,check_CSR_access,
    curPrivilege,privLevel,privilege,in32BitMode,curArch,architecture,MCSR,holWordExtract]

-- Original csr386_mode2; independently derived signed-range/permission result.
example (base : riscv_state) : observation base 386 2 7 = (true,true,0,1,[false,false,true,true,true,true,true,true]) := by
  simp [observation,fixture,is_CSR_defined,csrRW,csrPR,checkCSROp,check_CSR_access,
    curPrivilege,privLevel,privilege,in32BitMode,curArch,architecture,MCSR,holWordExtract]

-- Original csr767_mode2; independently derived signed-range/permission result.
example (base : riscv_state) : observation base 767 2 255 = (true,true,0,2,[false,false,false,false,true,true,true,true]) := by
  simp [observation,fixture,is_CSR_defined,csrRW,csrPR,checkCSROp,check_CSR_access,
    curPrivilege,privLevel,privilege,in32BitMode,curArch,architecture,MCSR,holWordExtract]

-- Original csr768_mode2; independently derived signed-range/permission result.
example (base : riscv_state) : observation base 768 2 7 = (true,true,0,3,[false,false,false,false,false,false,true,true]) := by
  simp [observation,fixture,is_CSR_defined,csrRW,csrPR,checkCSROp,check_CSR_access,
    curPrivilege,privLevel,privilege,in32BitMode,curArch,architecture,MCSR,holWordExtract]

-- Original csr770_mode2; independently derived signed-range/permission result.
example (base : riscv_state) : observation base 770 2 7 = (true,true,0,3,[false,false,false,false,false,false,true,true]) := by
  simp [observation,fixture,is_CSR_defined,csrRW,csrPR,checkCSROp,check_CSR_access,
    curPrivilege,privLevel,privilege,in32BitMode,curArch,architecture,MCSR,holWordExtract]

-- Original csr771_mode2; independently derived signed-range/permission result.
example (base : riscv_state) : observation base 771 2 255 = (true,true,0,3,[false,false,false,false,false,false,true,true]) := by
  simp [observation,fixture,is_CSR_defined,csrRW,csrPR,checkCSROp,check_CSR_access,
    curPrivilege,privLevel,privilege,in32BitMode,curArch,architecture,MCSR,holWordExtract]

-- Original csr772_mode2; independently derived signed-range/permission result.
example (base : riscv_state) : observation base 772 2 7 = (true,true,0,3,[false,false,false,false,false,false,true,true]) := by
  simp [observation,fixture,is_CSR_defined,csrRW,csrPR,checkCSROp,check_CSR_access,
    curPrivilege,privLevel,privilege,in32BitMode,curArch,architecture,MCSR,holWordExtract]

-- Original csr773_mode2; independently derived signed-range/permission result.
example (base : riscv_state) : observation base 773 2 255 = (true,true,0,3,[false,false,false,false,false,false,true,true]) := by
  simp [observation,fixture,is_CSR_defined,csrRW,csrPR,checkCSROp,check_CSR_access,
    curPrivilege,privLevel,privilege,in32BitMode,curArch,architecture,MCSR,holWordExtract]

-- Original csr800_mode2; independently derived signed-range/permission result.
example (base : riscv_state) : observation base 800 2 7 = (true,true,0,3,[false,false,false,false,false,false,true,true]) := by
  simp [observation,fixture,is_CSR_defined,csrRW,csrPR,checkCSROp,check_CSR_access,
    curPrivilege,privLevel,privilege,in32BitMode,curArch,architecture,MCSR,holWordExtract]

-- Original csr801_mode2; independently derived signed-range/permission result.
example (base : riscv_state) : observation base 801 2 255 = (true,true,0,3,[false,false,false,false,false,false,true,true]) := by
  simp [observation,fixture,is_CSR_defined,csrRW,csrPR,checkCSROp,check_CSR_access,
    curPrivilege,privLevel,privilege,in32BitMode,curArch,architecture,MCSR,holWordExtract]

-- Original csr802_mode2; independently derived signed-range/permission result.
example (base : riscv_state) : observation base 802 2 7 = (true,true,0,3,[false,false,false,false,false,false,true,true]) := by
  simp [observation,fixture,is_CSR_defined,csrRW,csrPR,checkCSROp,check_CSR_access,
    curPrivilege,privLevel,privilege,in32BitMode,curArch,architecture,MCSR,holWordExtract]

-- Original csr831_mode2; independently derived signed-range/permission result.
example (base : riscv_state) : observation base 831 2 255 = (true,true,0,3,[false,false,false,false,false,false,true,true]) := by
  simp [observation,fixture,is_CSR_defined,csrRW,csrPR,checkCSROp,check_CSR_access,
    curPrivilege,privLevel,privilege,in32BitMode,curArch,architecture,MCSR,holWordExtract]

-- Original csr832_mode2; independently derived signed-range/permission result.
example (base : riscv_state) : observation base 832 2 7 = (true,true,0,3,[false,false,false,false,false,false,true,true]) := by
  simp [observation,fixture,is_CSR_defined,csrRW,csrPR,checkCSROp,check_CSR_access,
    curPrivilege,privLevel,privilege,in32BitMode,curArch,architecture,MCSR,holWordExtract]

-- Original csr836_mode2; independently derived signed-range/permission result.
example (base : riscv_state) : observation base 836 2 7 = (true,true,0,3,[false,false,false,false,false,false,true,true]) := by
  simp [observation,fixture,is_CSR_defined,csrRW,csrPR,checkCSROp,check_CSR_access,
    curPrivilege,privLevel,privilege,in32BitMode,curArch,architecture,MCSR,holWordExtract]

-- Original csr837_mode2; independently derived signed-range/permission result.
example (base : riscv_state) : observation base 837 2 255 = (true,true,0,3,[false,false,false,false,false,false,true,true]) := by
  simp [observation,fixture,is_CSR_defined,csrRW,csrPR,checkCSROp,check_CSR_access,
    curPrivilege,privLevel,privilege,in32BitMode,curArch,architecture,MCSR,holWordExtract]

-- Original csr895_mode2; independently derived signed-range/permission result.
example (base : riscv_state) : observation base 895 2 255 = (true,true,0,3,[false,false,false,false,false,false,true,true]) := by
  simp [observation,fixture,is_CSR_defined,csrRW,csrPR,checkCSROp,check_CSR_access,
    curPrivilege,privLevel,privilege,in32BitMode,curArch,architecture,MCSR,holWordExtract]

-- Original csr896_mode2; independently derived signed-range/permission result.
example (base : riscv_state) : observation base 896 2 7 = (true,true,0,3,[false,false,false,false,false,false,true,true]) := by
  simp [observation,fixture,is_CSR_defined,csrRW,csrPR,checkCSROp,check_CSR_access,
    curPrivilege,privLevel,privilege,in32BitMode,curArch,architecture,MCSR,holWordExtract]

-- Original csr901_mode2; independently derived signed-range/permission result.
example (base : riscv_state) : observation base 901 2 255 = (true,true,0,3,[false,false,false,false,false,false,true,true]) := by
  simp [observation,fixture,is_CSR_defined,csrRW,csrPR,checkCSROp,check_CSR_access,
    curPrivilege,privLevel,privilege,in32BitMode,curArch,architecture,MCSR,holWordExtract]

-- Original csr902_mode2; independently derived signed-range/permission result.
example (base : riscv_state) : observation base 902 2 7 = (true,true,0,3,[false,false,false,false,false,false,true,true]) := by
  simp [observation,fixture,is_CSR_defined,csrRW,csrPR,checkCSROp,check_CSR_access,
    curPrivilege,privLevel,privilege,in32BitMode,curArch,architecture,MCSR,holWordExtract]

-- Original csr1792_mode2; independently derived signed-range/permission result.
example (base : riscv_state) : observation base 1792 2 7 = (true,true,1,3,[false,false,false,false,false,false,true,true]) := by
  simp [observation,fixture,is_CSR_defined,csrRW,csrPR,checkCSROp,check_CSR_access,
    curPrivilege,privLevel,privilege,in32BitMode,curArch,architecture,MCSR,holWordExtract]

-- Original csr1793_mode2; independently derived signed-range/permission result.
example (base : riscv_state) : observation base 1793 2 255 = (true,true,1,3,[false,false,false,false,false,false,true,true]) := by
  simp [observation,fixture,is_CSR_defined,csrRW,csrPR,checkCSROp,check_CSR_access,
    curPrivilege,privLevel,privilege,in32BitMode,curArch,architecture,MCSR,holWordExtract]

-- Original csr1794_mode2; independently derived signed-range/permission result.
example (base : riscv_state) : observation base 1794 2 7 = (true,true,1,3,[false,false,false,false,false,false,true,true]) := by
  simp [observation,fixture,is_CSR_defined,csrRW,csrPR,checkCSROp,check_CSR_access,
    curPrivilege,privLevel,privilege,in32BitMode,curArch,architecture,MCSR,holWordExtract]

-- Original csr1856_mode2; independently derived signed-range/permission result.
example (base : riscv_state) : observation base 1856 2 7 = (true,true,1,3,[false,false,false,false,false,false,true,true]) := by
  simp [observation,fixture,is_CSR_defined,csrRW,csrPR,checkCSROp,check_CSR_access,
    curPrivilege,privLevel,privilege,in32BitMode,curArch,architecture,MCSR,holWordExtract]

-- Original csr1857_mode2; independently derived signed-range/permission result.
example (base : riscv_state) : observation base 1857 2 255 = (true,true,1,3,[false,false,false,false,false,false,true,true]) := by
  simp [observation,fixture,is_CSR_defined,csrRW,csrPR,checkCSROp,check_CSR_access,
    curPrivilege,privLevel,privilege,in32BitMode,curArch,architecture,MCSR,holWordExtract]

-- Original csr1858_mode2; independently derived signed-range/permission result.
example (base : riscv_state) : observation base 1858 2 7 = (true,true,1,3,[false,false,false,false,false,false,true,true]) := by
  simp [observation,fixture,is_CSR_defined,csrRW,csrPR,checkCSROp,check_CSR_access,
    curPrivilege,privLevel,privilege,in32BitMode,curArch,architecture,MCSR,holWordExtract]

-- Original csr1919_mode2; independently derived signed-range/permission result.
example (base : riscv_state) : observation base 1919 2 255 = (true,true,1,3,[false,false,false,false,false,false,true,true]) := by
  simp [observation,fixture,is_CSR_defined,csrRW,csrPR,checkCSROp,check_CSR_access,
    curPrivilege,privLevel,privilege,in32BitMode,curArch,architecture,MCSR,holWordExtract]

-- Original csr1920_mode2; independently derived signed-range/permission result.
example (base : riscv_state) : observation base 1920 2 7 = (true,true,1,3,[false,false,false,false,false,false,true,true]) := by
  simp [observation,fixture,is_CSR_defined,csrRW,csrPR,checkCSROp,check_CSR_access,
    curPrivilege,privLevel,privilege,in32BitMode,curArch,architecture,MCSR,holWordExtract]

-- Original csr1922_mode2; independently derived signed-range/permission result.
example (base : riscv_state) : observation base 1922 2 7 = (true,true,1,3,[false,false,false,false,false,false,true,true]) := by
  simp [observation,fixture,is_CSR_defined,csrRW,csrPR,checkCSROp,check_CSR_access,
    curPrivilege,privLevel,privilege,in32BitMode,curArch,architecture,MCSR,holWordExtract]

-- Original csr1923_mode2; independently derived signed-range/permission result.
example (base : riscv_state) : observation base 1923 2 255 = (true,true,1,3,[false,false,false,false,false,false,true,true]) := by
  simp [observation,fixture,is_CSR_defined,csrRW,csrPR,checkCSROp,check_CSR_access,
    curPrivilege,privLevel,privilege,in32BitMode,curArch,architecture,MCSR,holWordExtract]

-- Original csr1924_mode2; independently derived signed-range/permission result.
example (base : riscv_state) : observation base 1924 2 7 = (true,true,1,3,[false,false,false,false,false,false,true,true]) := by
  simp [observation,fixture,is_CSR_defined,csrRW,csrPR,checkCSROp,check_CSR_access,
    curPrivilege,privLevel,privilege,in32BitMode,curArch,architecture,MCSR,holWordExtract]

-- Original csr2047_mode2; independently derived signed-range/permission result.
example (base : riscv_state) : observation base 2047 2 255 = (true,true,1,3,[false,false,false,false,false,false,true,true]) := by
  simp [observation,fixture,is_CSR_defined,csrRW,csrPR,checkCSROp,check_CSR_access,
    curPrivilege,privLevel,privilege,in32BitMode,curArch,architecture,MCSR,holWordExtract]

-- Original csr2048_mode2; independently derived signed-range/permission result.
example (base : riscv_state) : observation base 2048 2 7 = (false,true,2,0,[false,false,false,false,false,false,false,false]) := by
  simp [observation,fixture,is_CSR_defined,csrRW,csrPR,checkCSROp,check_CSR_access,
    curPrivilege,privLevel,privilege,in32BitMode,curArch,architecture,MCSR,holWordExtract]

-- Original csr2303_mode2; independently derived signed-range/permission result.
example (base : riscv_state) : observation base 2303 2 255 = (false,true,2,0,[false,false,false,false,false,false,false,false]) := by
  simp [observation,fixture,is_CSR_defined,csrRW,csrPR,checkCSROp,check_CSR_access,
    curPrivilege,privLevel,privilege,in32BitMode,curArch,architecture,MCSR,holWordExtract]

-- Original csr2304_mode2; independently derived signed-range/permission result.
example (base : riscv_state) : observation base 2304 2 7 = (true,true,2,1,[false,false,true,true,true,true,true,true]) := by
  simp [observation,fixture,is_CSR_defined,csrRW,csrPR,checkCSROp,check_CSR_access,
    curPrivilege,privLevel,privilege,in32BitMode,curArch,architecture,MCSR,holWordExtract]

-- Original csr2306_mode2; independently derived signed-range/permission result.
example (base : riscv_state) : observation base 2306 2 7 = (true,true,2,1,[false,false,true,true,true,true,true,true]) := by
  simp [observation,fixture,is_CSR_defined,csrRW,csrPR,checkCSROp,check_CSR_access,
    curPrivilege,privLevel,privilege,in32BitMode,curArch,architecture,MCSR,holWordExtract]

-- Original csr2307_mode2; independently derived signed-range/permission result.
example (base : riscv_state) : observation base 2307 2 255 = (false,true,2,1,[false,false,false,false,false,false,false,false]) := by
  simp [observation,fixture,is_CSR_defined,csrRW,csrPR,checkCSROp,check_CSR_access,
    curPrivilege,privLevel,privilege,in32BitMode,curArch,architecture,MCSR,holWordExtract]

-- Original csr2431_mode2; independently derived signed-range/permission result.
example (base : riscv_state) : observation base 2431 2 255 = (false,true,2,1,[false,false,false,false,false,false,false,false]) := by
  simp [observation,fixture,is_CSR_defined,csrRW,csrPR,checkCSROp,check_CSR_access,
    curPrivilege,privLevel,privilege,in32BitMode,curArch,architecture,MCSR,holWordExtract]

-- Original csr2432_mode2; independently derived signed-range/permission result.
example (base : riscv_state) : observation base 2432 2 7 = (false,true,2,1,[false,false,false,false,false,false,false,false]) := by
  simp [observation,fixture,is_CSR_defined,csrRW,csrPR,checkCSROp,check_CSR_access,
    curPrivilege,privLevel,privilege,in32BitMode,curArch,architecture,MCSR,holWordExtract]

-- Original csr2434_mode2; independently derived signed-range/permission result.
example (base : riscv_state) : observation base 2434 2 7 = (false,true,2,1,[false,false,false,false,false,false,false,false]) := by
  simp [observation,fixture,is_CSR_defined,csrRW,csrPR,checkCSROp,check_CSR_access,
    curPrivilege,privLevel,privilege,in32BitMode,curArch,architecture,MCSR,holWordExtract]

-- Original csr2435_mode2; independently derived signed-range/permission result.
example (base : riscv_state) : observation base 2435 2 255 = (false,true,2,1,[false,false,false,false,false,false,false,false]) := by
  simp [observation,fixture,is_CSR_defined,csrRW,csrPR,checkCSROp,check_CSR_access,
    curPrivilege,privLevel,privilege,in32BitMode,curArch,architecture,MCSR,holWordExtract]

-- Original csr2816_mode2; independently derived signed-range/permission result.
example (base : riscv_state) : observation base 2816 2 7 = (false,true,2,3,[false,false,false,false,false,false,false,false]) := by
  simp [observation,fixture,is_CSR_defined,csrRW,csrPR,checkCSROp,check_CSR_access,
    curPrivilege,privLevel,privilege,in32BitMode,curArch,architecture,MCSR,holWordExtract]

-- Original csr2817_mode2; independently derived signed-range/permission result.
example (base : riscv_state) : observation base 2817 2 255 = (true,true,2,3,[false,false,false,false,false,false,true,true]) := by
  simp [observation,fixture,is_CSR_defined,csrRW,csrPR,checkCSROp,check_CSR_access,
    curPrivilege,privLevel,privilege,in32BitMode,curArch,architecture,MCSR,holWordExtract]

-- Original csr2818_mode2; independently derived signed-range/permission result.
example (base : riscv_state) : observation base 2818 2 7 = (true,true,2,3,[false,false,false,false,false,false,true,true]) := by
  simp [observation,fixture,is_CSR_defined,csrRW,csrPR,checkCSROp,check_CSR_access,
    curPrivilege,privLevel,privilege,in32BitMode,curArch,architecture,MCSR,holWordExtract]

-- Original csr2944_mode2; independently derived signed-range/permission result.
example (base : riscv_state) : observation base 2944 2 7 = (true,true,2,3,[false,false,false,false,false,false,true,true]) := by
  simp [observation,fixture,is_CSR_defined,csrRW,csrPR,checkCSROp,check_CSR_access,
    curPrivilege,privLevel,privilege,in32BitMode,curArch,architecture,MCSR,holWordExtract]

-- Original csr2945_mode2; independently derived signed-range/permission result.
example (base : riscv_state) : observation base 2945 2 255 = (true,true,2,3,[false,false,false,false,false,false,true,true]) := by
  simp [observation,fixture,is_CSR_defined,csrRW,csrPR,checkCSROp,check_CSR_access,
    curPrivilege,privLevel,privilege,in32BitMode,curArch,architecture,MCSR,holWordExtract]

-- Original csr2946_mode2; independently derived signed-range/permission result.
example (base : riscv_state) : observation base 2946 2 7 = (true,true,2,3,[false,false,false,false,false,false,true,true]) := by
  simp [observation,fixture,is_CSR_defined,csrRW,csrPR,checkCSROp,check_CSR_access,
    curPrivilege,privLevel,privilege,in32BitMode,curArch,architecture,MCSR,holWordExtract]

-- Original csr3071_mode2; independently derived signed-range/permission result.
example (base : riscv_state) : observation base 3071 2 255 = (true,true,2,3,[false,false,false,false,false,false,true,true]) := by
  simp [observation,fixture,is_CSR_defined,csrRW,csrPR,checkCSROp,check_CSR_access,
    curPrivilege,privLevel,privilege,in32BitMode,curArch,architecture,MCSR,holWordExtract]

-- Original csr3072_mode2; independently derived signed-range/permission result.
example (base : riscv_state) : observation base 3072 2 7 = (true,true,3,0,[true,false,true,false,true,false,true,false]) := by
  simp [observation,fixture,is_CSR_defined,csrRW,csrPR,checkCSROp,check_CSR_access,
    curPrivilege,privLevel,privilege,in32BitMode,curArch,architecture,MCSR,holWordExtract]

-- Original csr3074_mode2; independently derived signed-range/permission result.
example (base : riscv_state) : observation base 3074 2 7 = (true,true,3,0,[true,false,true,false,true,false,true,false]) := by
  simp [observation,fixture,is_CSR_defined,csrRW,csrPR,checkCSROp,check_CSR_access,
    curPrivilege,privLevel,privilege,in32BitMode,curArch,architecture,MCSR,holWordExtract]

-- Original csr3075_mode2; independently derived signed-range/permission result.
example (base : riscv_state) : observation base 3075 2 255 = (true,true,3,0,[true,false,true,false,true,false,true,false]) := by
  simp [observation,fixture,is_CSR_defined,csrRW,csrPR,checkCSROp,check_CSR_access,
    curPrivilege,privLevel,privilege,in32BitMode,curArch,architecture,MCSR,holWordExtract]

-- Original csr3199_mode2; independently derived signed-range/permission result.
example (base : riscv_state) : observation base 3199 2 255 = (true,true,3,0,[true,false,true,false,true,false,true,false]) := by
  simp [observation,fixture,is_CSR_defined,csrRW,csrPR,checkCSROp,check_CSR_access,
    curPrivilege,privLevel,privilege,in32BitMode,curArch,architecture,MCSR,holWordExtract]

-- Original csr3200_mode2; independently derived signed-range/permission result.
example (base : riscv_state) : observation base 3200 2 7 = (true,true,3,0,[true,false,true,false,true,false,true,false]) := by
  simp [observation,fixture,is_CSR_defined,csrRW,csrPR,checkCSROp,check_CSR_access,
    curPrivilege,privLevel,privilege,in32BitMode,curArch,architecture,MCSR,holWordExtract]

-- Original csr3202_mode2; independently derived signed-range/permission result.
example (base : riscv_state) : observation base 3202 2 7 = (true,true,3,0,[true,false,true,false,true,false,true,false]) := by
  simp [observation,fixture,is_CSR_defined,csrRW,csrPR,checkCSROp,check_CSR_access,
    curPrivilege,privLevel,privilege,in32BitMode,curArch,architecture,MCSR,holWordExtract]

-- Original csr3203_mode2; independently derived signed-range/permission result.
example (base : riscv_state) : observation base 3203 2 255 = (true,true,3,0,[true,false,true,false,true,false,true,false]) := by
  simp [observation,fixture,is_CSR_defined,csrRW,csrPR,checkCSROp,check_CSR_access,
    curPrivilege,privLevel,privilege,in32BitMode,curArch,architecture,MCSR,holWordExtract]

-- Original csr3328_mode2; independently derived signed-range/permission result.
example (base : riscv_state) : observation base 3328 2 7 = (true,true,3,1,[false,false,true,false,true,false,true,false]) := by
  simp [observation,fixture,is_CSR_defined,csrRW,csrPR,checkCSROp,check_CSR_access,
    curPrivilege,privLevel,privilege,in32BitMode,curArch,architecture,MCSR,holWordExtract]

-- Original csr3329_mode2; independently derived signed-range/permission result.
example (base : riscv_state) : observation base 3329 2 255 = (true,true,3,1,[false,false,true,false,true,false,true,false]) := by
  simp [observation,fixture,is_CSR_defined,csrRW,csrPR,checkCSROp,check_CSR_access,
    curPrivilege,privLevel,privilege,in32BitMode,curArch,architecture,MCSR,holWordExtract]

-- Original csr3330_mode2; independently derived signed-range/permission result.
example (base : riscv_state) : observation base 3330 2 7 = (true,true,3,1,[false,false,true,false,true,false,true,false]) := by
  simp [observation,fixture,is_CSR_defined,csrRW,csrPR,checkCSROp,check_CSR_access,
    curPrivilege,privLevel,privilege,in32BitMode,curArch,architecture,MCSR,holWordExtract]

-- Original csr3393_mode2; independently derived signed-range/permission result.
example (base : riscv_state) : observation base 3393 2 255 = (true,true,3,1,[false,false,true,false,true,false,true,false]) := by
  simp [observation,fixture,is_CSR_defined,csrRW,csrPR,checkCSROp,check_CSR_access,
    curPrivilege,privLevel,privilege,in32BitMode,curArch,architecture,MCSR,holWordExtract]

-- Original csr3394_mode2; independently derived signed-range/permission result.
example (base : riscv_state) : observation base 3394 2 7 = (true,true,3,1,[false,false,true,false,true,false,true,false]) := by
  simp [observation,fixture,is_CSR_defined,csrRW,csrPR,checkCSROp,check_CSR_access,
    curPrivilege,privLevel,privilege,in32BitMode,curArch,architecture,MCSR,holWordExtract]

-- Original csr3395_mode2; independently derived signed-range/permission result.
example (base : riscv_state) : observation base 3395 2 255 = (true,true,3,1,[false,false,true,false,true,false,true,false]) := by
  simp [observation,fixture,is_CSR_defined,csrRW,csrPR,checkCSROp,check_CSR_access,
    curPrivilege,privLevel,privilege,in32BitMode,curArch,architecture,MCSR,holWordExtract]

-- Original csr3396_mode2; independently derived signed-range/permission result.
example (base : riscv_state) : observation base 3396 2 7 = (true,true,3,1,[false,false,true,false,true,false,true,false]) := by
  simp [observation,fixture,is_CSR_defined,csrRW,csrPR,checkCSROp,check_CSR_access,
    curPrivilege,privLevel,privilege,in32BitMode,curArch,architecture,MCSR,holWordExtract]

-- Original csr3456_mode2; independently derived signed-range/permission result.
example (base : riscv_state) : observation base 3456 2 7 = (true,true,3,1,[false,false,true,false,true,false,true,false]) := by
  simp [observation,fixture,is_CSR_defined,csrRW,csrPR,checkCSROp,check_CSR_access,
    curPrivilege,privLevel,privilege,in32BitMode,curArch,architecture,MCSR,holWordExtract]

-- Original csr3457_mode2; independently derived signed-range/permission result.
example (base : riscv_state) : observation base 3457 2 255 = (true,true,3,1,[false,false,true,false,true,false,true,false]) := by
  simp [observation,fixture,is_CSR_defined,csrRW,csrPR,checkCSROp,check_CSR_access,
    curPrivilege,privLevel,privilege,in32BitMode,curArch,architecture,MCSR,holWordExtract]

-- Original csr3458_mode2; independently derived signed-range/permission result.
example (base : riscv_state) : observation base 3458 2 7 = (true,true,3,1,[false,false,true,false,true,false,true,false]) := by
  simp [observation,fixture,is_CSR_defined,csrRW,csrPR,checkCSROp,check_CSR_access,
    curPrivilege,privLevel,privilege,in32BitMode,curArch,architecture,MCSR,holWordExtract]

-- Original csr3839_mode2; independently derived signed-range/permission result.
example (base : riscv_state) : observation base 3839 2 255 = (true,true,3,2,[false,false,false,false,true,false,true,false]) := by
  simp [observation,fixture,is_CSR_defined,csrRW,csrPR,checkCSROp,check_CSR_access,
    curPrivilege,privLevel,privilege,in32BitMode,curArch,architecture,MCSR,holWordExtract]

-- Original csr3840_mode2; independently derived signed-range/permission result.
example (base : riscv_state) : observation base 3840 2 7 = (true,true,3,3,[false,false,false,false,false,false,true,false]) := by
  simp [observation,fixture,is_CSR_defined,csrRW,csrPR,checkCSROp,check_CSR_access,
    curPrivilege,privLevel,privilege,in32BitMode,curArch,architecture,MCSR,holWordExtract]

-- Original csr3841_mode2; independently derived signed-range/permission result.
example (base : riscv_state) : observation base 3841 2 255 = (true,true,3,3,[false,false,false,false,false,false,true,false]) := by
  simp [observation,fixture,is_CSR_defined,csrRW,csrPR,checkCSROp,check_CSR_access,
    curPrivilege,privLevel,privilege,in32BitMode,curArch,architecture,MCSR,holWordExtract]

-- Original csr3842_mode2; independently derived signed-range/permission result.
example (base : riscv_state) : observation base 3842 2 7 = (true,true,3,3,[false,false,false,false,false,false,true,false]) := by
  simp [observation,fixture,is_CSR_defined,csrRW,csrPR,checkCSROp,check_CSR_access,
    curPrivilege,privLevel,privilege,in32BitMode,curArch,architecture,MCSR,holWordExtract]

-- Original csr3855_mode2; independently derived signed-range/permission result.
example (base : riscv_state) : observation base 3855 2 255 = (true,true,3,3,[false,false,false,false,false,false,true,false]) := by
  simp [observation,fixture,is_CSR_defined,csrRW,csrPR,checkCSROp,check_CSR_access,
    curPrivilege,privLevel,privilege,in32BitMode,curArch,architecture,MCSR,holWordExtract]

-- Original csr3856_mode2; independently derived signed-range/permission result.
example (base : riscv_state) : observation base 3856 2 7 = (true,true,3,3,[false,false,false,false,false,false,true,false]) := by
  simp [observation,fixture,is_CSR_defined,csrRW,csrPR,checkCSROp,check_CSR_access,
    curPrivilege,privLevel,privilege,in32BitMode,curArch,architecture,MCSR,holWordExtract]

-- Original csr3857_mode2; independently derived signed-range/permission result.
example (base : riscv_state) : observation base 3857 2 255 = (true,true,3,3,[false,false,false,false,false,false,true,false]) := by
  simp [observation,fixture,is_CSR_defined,csrRW,csrPR,checkCSROp,check_CSR_access,
    curPrivilege,privLevel,privilege,in32BitMode,curArch,architecture,MCSR,holWordExtract]

-- Original csr4095_mode2; independently derived signed-range/permission result.
example (base : riscv_state) : observation base 4095 2 255 = (true,true,3,3,[false,false,false,false,false,false,true,false]) := by
  simp [observation,fixture,is_CSR_defined,csrRW,csrPR,checkCSROp,check_CSR_access,
    curPrivilege,privLevel,privilege,in32BitMode,curArch,architecture,MCSR,holWordExtract]

-- Original csr0_mode3; independently derived signed-range/permission result.
example (base : riscv_state) : observation base 0 3 7 = (true,true,0,0,[true,true,true,true,true,true,true,true]) := by
  simp [observation,fixture,is_CSR_defined,csrRW,csrPR,checkCSROp,check_CSR_access,
    curPrivilege,privLevel,privilege,in32BitMode,curArch,architecture,MCSR,holWordExtract]

-- Original csr1_mode3; independently derived signed-range/permission result.
example (base : riscv_state) : observation base 1 3 255 = (true,true,0,0,[true,true,true,true,true,true,true,true]) := by
  simp [observation,fixture,is_CSR_defined,csrRW,csrPR,checkCSROp,check_CSR_access,
    curPrivilege,privLevel,privilege,in32BitMode,curArch,architecture,MCSR,holWordExtract]

-- Original csr3_mode3; independently derived signed-range/permission result.
example (base : riscv_state) : observation base 3 3 255 = (true,true,0,0,[true,true,true,true,true,true,true,true]) := by
  simp [observation,fixture,is_CSR_defined,csrRW,csrPR,checkCSROp,check_CSR_access,
    curPrivilege,privLevel,privilege,in32BitMode,curArch,architecture,MCSR,holWordExtract]

-- Original csr4_mode3; independently derived signed-range/permission result.
example (base : riscv_state) : observation base 4 3 7 = (true,true,0,0,[true,true,true,true,true,true,true,true]) := by
  simp [observation,fixture,is_CSR_defined,csrRW,csrPR,checkCSROp,check_CSR_access,
    curPrivilege,privLevel,privilege,in32BitMode,curArch,architecture,MCSR,holWordExtract]

-- Original csr255_mode3; independently derived signed-range/permission result.
example (base : riscv_state) : observation base 255 3 255 = (true,true,0,0,[true,true,true,true,true,true,true,true]) := by
  simp [observation,fixture,is_CSR_defined,csrRW,csrPR,checkCSROp,check_CSR_access,
    curPrivilege,privLevel,privilege,in32BitMode,curArch,architecture,MCSR,holWordExtract]

-- Original csr256_mode3; independently derived signed-range/permission result.
example (base : riscv_state) : observation base 256 3 7 = (true,true,0,1,[false,false,true,true,true,true,true,true]) := by
  simp [observation,fixture,is_CSR_defined,csrRW,csrPR,checkCSROp,check_CSR_access,
    curPrivilege,privLevel,privilege,in32BitMode,curArch,architecture,MCSR,holWordExtract]

-- Original csr257_mode3; independently derived signed-range/permission result.
example (base : riscv_state) : observation base 257 3 255 = (true,true,0,1,[false,false,true,true,true,true,true,true]) := by
  simp [observation,fixture,is_CSR_defined,csrRW,csrPR,checkCSROp,check_CSR_access,
    curPrivilege,privLevel,privilege,in32BitMode,curArch,architecture,MCSR,holWordExtract]

-- Original csr258_mode3; independently derived signed-range/permission result.
example (base : riscv_state) : observation base 258 3 7 = (true,true,0,1,[false,false,true,true,true,true,true,true]) := by
  simp [observation,fixture,is_CSR_defined,csrRW,csrPR,checkCSROp,check_CSR_access,
    curPrivilege,privLevel,privilege,in32BitMode,curArch,architecture,MCSR,holWordExtract]

-- Original csr259_mode3; independently derived signed-range/permission result.
example (base : riscv_state) : observation base 259 3 255 = (true,true,0,1,[false,false,true,true,true,true,true,true]) := by
  simp [observation,fixture,is_CSR_defined,csrRW,csrPR,checkCSROp,check_CSR_access,
    curPrivilege,privLevel,privilege,in32BitMode,curArch,architecture,MCSR,holWordExtract]

-- Original csr260_mode3; independently derived signed-range/permission result.
example (base : riscv_state) : observation base 260 3 7 = (true,true,0,1,[false,false,true,true,true,true,true,true]) := by
  simp [observation,fixture,is_CSR_defined,csrRW,csrPR,checkCSROp,check_CSR_access,
    curPrivilege,privLevel,privilege,in32BitMode,curArch,architecture,MCSR,holWordExtract]

-- Original csr261_mode3; independently derived signed-range/permission result.
example (base : riscv_state) : observation base 261 3 255 = (true,true,0,1,[false,false,true,true,true,true,true,true]) := by
  simp [observation,fixture,is_CSR_defined,csrRW,csrPR,checkCSROp,check_CSR_access,
    curPrivilege,privLevel,privilege,in32BitMode,curArch,architecture,MCSR,holWordExtract]

-- Original csr288_mode3; independently derived signed-range/permission result.
example (base : riscv_state) : observation base 288 3 7 = (true,true,0,1,[false,false,true,true,true,true,true,true]) := by
  simp [observation,fixture,is_CSR_defined,csrRW,csrPR,checkCSROp,check_CSR_access,
    curPrivilege,privLevel,privilege,in32BitMode,curArch,architecture,MCSR,holWordExtract]

-- Original csr289_mode3; independently derived signed-range/permission result.
example (base : riscv_state) : observation base 289 3 255 = (true,true,0,1,[false,false,true,true,true,true,true,true]) := by
  simp [observation,fixture,is_CSR_defined,csrRW,csrPR,checkCSROp,check_CSR_access,
    curPrivilege,privLevel,privilege,in32BitMode,curArch,architecture,MCSR,holWordExtract]

-- Original csr290_mode3; independently derived signed-range/permission result.
example (base : riscv_state) : observation base 290 3 7 = (true,true,0,1,[false,false,true,true,true,true,true,true]) := by
  simp [observation,fixture,is_CSR_defined,csrRW,csrPR,checkCSROp,check_CSR_access,
    curPrivilege,privLevel,privilege,in32BitMode,curArch,architecture,MCSR,holWordExtract]

-- Original csr319_mode3; independently derived signed-range/permission result.
example (base : riscv_state) : observation base 319 3 255 = (true,true,0,1,[false,false,true,true,true,true,true,true]) := by
  simp [observation,fixture,is_CSR_defined,csrRW,csrPR,checkCSROp,check_CSR_access,
    curPrivilege,privLevel,privilege,in32BitMode,curArch,architecture,MCSR,holWordExtract]

-- Original csr320_mode3; independently derived signed-range/permission result.
example (base : riscv_state) : observation base 320 3 7 = (true,true,0,1,[false,false,true,true,true,true,true,true]) := by
  simp [observation,fixture,is_CSR_defined,csrRW,csrPR,checkCSROp,check_CSR_access,
    curPrivilege,privLevel,privilege,in32BitMode,curArch,architecture,MCSR,holWordExtract]

-- Original csr321_mode3; independently derived signed-range/permission result.
example (base : riscv_state) : observation base 321 3 255 = (true,true,0,1,[false,false,true,true,true,true,true,true]) := by
  simp [observation,fixture,is_CSR_defined,csrRW,csrPR,checkCSROp,check_CSR_access,
    curPrivilege,privLevel,privilege,in32BitMode,curArch,architecture,MCSR,holWordExtract]

-- Original csr322_mode3; independently derived signed-range/permission result.
example (base : riscv_state) : observation base 322 3 7 = (true,true,0,1,[false,false,true,true,true,true,true,true]) := by
  simp [observation,fixture,is_CSR_defined,csrRW,csrPR,checkCSROp,check_CSR_access,
    curPrivilege,privLevel,privilege,in32BitMode,curArch,architecture,MCSR,holWordExtract]

-- Original csr323_mode3; independently derived signed-range/permission result.
example (base : riscv_state) : observation base 323 3 255 = (true,true,0,1,[false,false,true,true,true,true,true,true]) := by
  simp [observation,fixture,is_CSR_defined,csrRW,csrPR,checkCSROp,check_CSR_access,
    curPrivilege,privLevel,privilege,in32BitMode,curArch,architecture,MCSR,holWordExtract]

-- Original csr324_mode3; independently derived signed-range/permission result.
example (base : riscv_state) : observation base 324 3 7 = (true,true,0,1,[false,false,true,true,true,true,true,true]) := by
  simp [observation,fixture,is_CSR_defined,csrRW,csrPR,checkCSROp,check_CSR_access,
    curPrivilege,privLevel,privilege,in32BitMode,curArch,architecture,MCSR,holWordExtract]

-- Original csr325_mode3; independently derived signed-range/permission result.
example (base : riscv_state) : observation base 325 3 255 = (true,true,0,1,[false,false,true,true,true,true,true,true]) := by
  simp [observation,fixture,is_CSR_defined,csrRW,csrPR,checkCSROp,check_CSR_access,
    curPrivilege,privLevel,privilege,in32BitMode,curArch,architecture,MCSR,holWordExtract]

-- Original csr383_mode3; independently derived signed-range/permission result.
example (base : riscv_state) : observation base 383 3 255 = (true,true,0,1,[false,false,true,true,true,true,true,true]) := by
  simp [observation,fixture,is_CSR_defined,csrRW,csrPR,checkCSROp,check_CSR_access,
    curPrivilege,privLevel,privilege,in32BitMode,curArch,architecture,MCSR,holWordExtract]

-- Original csr384_mode3; independently derived signed-range/permission result.
example (base : riscv_state) : observation base 384 3 7 = (true,true,0,1,[false,false,true,true,true,true,true,true]) := by
  simp [observation,fixture,is_CSR_defined,csrRW,csrPR,checkCSROp,check_CSR_access,
    curPrivilege,privLevel,privilege,in32BitMode,curArch,architecture,MCSR,holWordExtract]

-- Original csr385_mode3; independently derived signed-range/permission result.
example (base : riscv_state) : observation base 385 3 255 = (true,true,0,1,[false,false,true,true,true,true,true,true]) := by
  simp [observation,fixture,is_CSR_defined,csrRW,csrPR,checkCSROp,check_CSR_access,
    curPrivilege,privLevel,privilege,in32BitMode,curArch,architecture,MCSR,holWordExtract]

-- Original csr386_mode3; independently derived signed-range/permission result.
example (base : riscv_state) : observation base 386 3 7 = (true,true,0,1,[false,false,true,true,true,true,true,true]) := by
  simp [observation,fixture,is_CSR_defined,csrRW,csrPR,checkCSROp,check_CSR_access,
    curPrivilege,privLevel,privilege,in32BitMode,curArch,architecture,MCSR,holWordExtract]

-- Original csr767_mode3; independently derived signed-range/permission result.
example (base : riscv_state) : observation base 767 3 255 = (true,true,0,2,[false,false,false,false,true,true,true,true]) := by
  simp [observation,fixture,is_CSR_defined,csrRW,csrPR,checkCSROp,check_CSR_access,
    curPrivilege,privLevel,privilege,in32BitMode,curArch,architecture,MCSR,holWordExtract]

-- Original csr768_mode3; independently derived signed-range/permission result.
example (base : riscv_state) : observation base 768 3 7 = (true,true,0,3,[false,false,false,false,false,false,true,true]) := by
  simp [observation,fixture,is_CSR_defined,csrRW,csrPR,checkCSROp,check_CSR_access,
    curPrivilege,privLevel,privilege,in32BitMode,curArch,architecture,MCSR,holWordExtract]

-- Original csr770_mode3; independently derived signed-range/permission result.
example (base : riscv_state) : observation base 770 3 7 = (true,true,0,3,[false,false,false,false,false,false,true,true]) := by
  simp [observation,fixture,is_CSR_defined,csrRW,csrPR,checkCSROp,check_CSR_access,
    curPrivilege,privLevel,privilege,in32BitMode,curArch,architecture,MCSR,holWordExtract]

-- Original csr771_mode3; independently derived signed-range/permission result.
example (base : riscv_state) : observation base 771 3 255 = (true,true,0,3,[false,false,false,false,false,false,true,true]) := by
  simp [observation,fixture,is_CSR_defined,csrRW,csrPR,checkCSROp,check_CSR_access,
    curPrivilege,privLevel,privilege,in32BitMode,curArch,architecture,MCSR,holWordExtract]

-- Original csr772_mode3; independently derived signed-range/permission result.
example (base : riscv_state) : observation base 772 3 7 = (true,true,0,3,[false,false,false,false,false,false,true,true]) := by
  simp [observation,fixture,is_CSR_defined,csrRW,csrPR,checkCSROp,check_CSR_access,
    curPrivilege,privLevel,privilege,in32BitMode,curArch,architecture,MCSR,holWordExtract]

-- Original csr773_mode3; independently derived signed-range/permission result.
example (base : riscv_state) : observation base 773 3 255 = (true,true,0,3,[false,false,false,false,false,false,true,true]) := by
  simp [observation,fixture,is_CSR_defined,csrRW,csrPR,checkCSROp,check_CSR_access,
    curPrivilege,privLevel,privilege,in32BitMode,curArch,architecture,MCSR,holWordExtract]

-- Original csr800_mode3; independently derived signed-range/permission result.
example (base : riscv_state) : observation base 800 3 7 = (true,true,0,3,[false,false,false,false,false,false,true,true]) := by
  simp [observation,fixture,is_CSR_defined,csrRW,csrPR,checkCSROp,check_CSR_access,
    curPrivilege,privLevel,privilege,in32BitMode,curArch,architecture,MCSR,holWordExtract]

-- Original csr801_mode3; independently derived signed-range/permission result.
example (base : riscv_state) : observation base 801 3 255 = (true,true,0,3,[false,false,false,false,false,false,true,true]) := by
  simp [observation,fixture,is_CSR_defined,csrRW,csrPR,checkCSROp,check_CSR_access,
    curPrivilege,privLevel,privilege,in32BitMode,curArch,architecture,MCSR,holWordExtract]

-- Original csr802_mode3; independently derived signed-range/permission result.
example (base : riscv_state) : observation base 802 3 7 = (true,true,0,3,[false,false,false,false,false,false,true,true]) := by
  simp [observation,fixture,is_CSR_defined,csrRW,csrPR,checkCSROp,check_CSR_access,
    curPrivilege,privLevel,privilege,in32BitMode,curArch,architecture,MCSR,holWordExtract]

-- Original csr831_mode3; independently derived signed-range/permission result.
example (base : riscv_state) : observation base 831 3 255 = (true,true,0,3,[false,false,false,false,false,false,true,true]) := by
  simp [observation,fixture,is_CSR_defined,csrRW,csrPR,checkCSROp,check_CSR_access,
    curPrivilege,privLevel,privilege,in32BitMode,curArch,architecture,MCSR,holWordExtract]

-- Original csr832_mode3; independently derived signed-range/permission result.
example (base : riscv_state) : observation base 832 3 7 = (true,true,0,3,[false,false,false,false,false,false,true,true]) := by
  simp [observation,fixture,is_CSR_defined,csrRW,csrPR,checkCSROp,check_CSR_access,
    curPrivilege,privLevel,privilege,in32BitMode,curArch,architecture,MCSR,holWordExtract]

-- Original csr836_mode3; independently derived signed-range/permission result.
example (base : riscv_state) : observation base 836 3 7 = (true,true,0,3,[false,false,false,false,false,false,true,true]) := by
  simp [observation,fixture,is_CSR_defined,csrRW,csrPR,checkCSROp,check_CSR_access,
    curPrivilege,privLevel,privilege,in32BitMode,curArch,architecture,MCSR,holWordExtract]

-- Original csr837_mode3; independently derived signed-range/permission result.
example (base : riscv_state) : observation base 837 3 255 = (true,true,0,3,[false,false,false,false,false,false,true,true]) := by
  simp [observation,fixture,is_CSR_defined,csrRW,csrPR,checkCSROp,check_CSR_access,
    curPrivilege,privLevel,privilege,in32BitMode,curArch,architecture,MCSR,holWordExtract]

-- Original csr895_mode3; independently derived signed-range/permission result.
example (base : riscv_state) : observation base 895 3 255 = (true,true,0,3,[false,false,false,false,false,false,true,true]) := by
  simp [observation,fixture,is_CSR_defined,csrRW,csrPR,checkCSROp,check_CSR_access,
    curPrivilege,privLevel,privilege,in32BitMode,curArch,architecture,MCSR,holWordExtract]

-- Original csr896_mode3; independently derived signed-range/permission result.
example (base : riscv_state) : observation base 896 3 7 = (true,true,0,3,[false,false,false,false,false,false,true,true]) := by
  simp [observation,fixture,is_CSR_defined,csrRW,csrPR,checkCSROp,check_CSR_access,
    curPrivilege,privLevel,privilege,in32BitMode,curArch,architecture,MCSR,holWordExtract]

-- Original csr901_mode3; independently derived signed-range/permission result.
example (base : riscv_state) : observation base 901 3 255 = (true,true,0,3,[false,false,false,false,false,false,true,true]) := by
  simp [observation,fixture,is_CSR_defined,csrRW,csrPR,checkCSROp,check_CSR_access,
    curPrivilege,privLevel,privilege,in32BitMode,curArch,architecture,MCSR,holWordExtract]

-- Original csr902_mode3; independently derived signed-range/permission result.
example (base : riscv_state) : observation base 902 3 7 = (true,true,0,3,[false,false,false,false,false,false,true,true]) := by
  simp [observation,fixture,is_CSR_defined,csrRW,csrPR,checkCSROp,check_CSR_access,
    curPrivilege,privLevel,privilege,in32BitMode,curArch,architecture,MCSR,holWordExtract]

-- Original csr1792_mode3; independently derived signed-range/permission result.
example (base : riscv_state) : observation base 1792 3 7 = (true,true,1,3,[false,false,false,false,false,false,true,true]) := by
  simp [observation,fixture,is_CSR_defined,csrRW,csrPR,checkCSROp,check_CSR_access,
    curPrivilege,privLevel,privilege,in32BitMode,curArch,architecture,MCSR,holWordExtract]

-- Original csr1793_mode3; independently derived signed-range/permission result.
example (base : riscv_state) : observation base 1793 3 255 = (true,true,1,3,[false,false,false,false,false,false,true,true]) := by
  simp [observation,fixture,is_CSR_defined,csrRW,csrPR,checkCSROp,check_CSR_access,
    curPrivilege,privLevel,privilege,in32BitMode,curArch,architecture,MCSR,holWordExtract]

-- Original csr1794_mode3; independently derived signed-range/permission result.
example (base : riscv_state) : observation base 1794 3 7 = (true,true,1,3,[false,false,false,false,false,false,true,true]) := by
  simp [observation,fixture,is_CSR_defined,csrRW,csrPR,checkCSROp,check_CSR_access,
    curPrivilege,privLevel,privilege,in32BitMode,curArch,architecture,MCSR,holWordExtract]

-- Original csr1856_mode3; independently derived signed-range/permission result.
example (base : riscv_state) : observation base 1856 3 7 = (true,true,1,3,[false,false,false,false,false,false,true,true]) := by
  simp [observation,fixture,is_CSR_defined,csrRW,csrPR,checkCSROp,check_CSR_access,
    curPrivilege,privLevel,privilege,in32BitMode,curArch,architecture,MCSR,holWordExtract]

-- Original csr1857_mode3; independently derived signed-range/permission result.
example (base : riscv_state) : observation base 1857 3 255 = (true,true,1,3,[false,false,false,false,false,false,true,true]) := by
  simp [observation,fixture,is_CSR_defined,csrRW,csrPR,checkCSROp,check_CSR_access,
    curPrivilege,privLevel,privilege,in32BitMode,curArch,architecture,MCSR,holWordExtract]

-- Original csr1858_mode3; independently derived signed-range/permission result.
example (base : riscv_state) : observation base 1858 3 7 = (true,true,1,3,[false,false,false,false,false,false,true,true]) := by
  simp [observation,fixture,is_CSR_defined,csrRW,csrPR,checkCSROp,check_CSR_access,
    curPrivilege,privLevel,privilege,in32BitMode,curArch,architecture,MCSR,holWordExtract]

-- Original csr1919_mode3; independently derived signed-range/permission result.
example (base : riscv_state) : observation base 1919 3 255 = (true,true,1,3,[false,false,false,false,false,false,true,true]) := by
  simp [observation,fixture,is_CSR_defined,csrRW,csrPR,checkCSROp,check_CSR_access,
    curPrivilege,privLevel,privilege,in32BitMode,curArch,architecture,MCSR,holWordExtract]

-- Original csr1920_mode3; independently derived signed-range/permission result.
example (base : riscv_state) : observation base 1920 3 7 = (true,true,1,3,[false,false,false,false,false,false,true,true]) := by
  simp [observation,fixture,is_CSR_defined,csrRW,csrPR,checkCSROp,check_CSR_access,
    curPrivilege,privLevel,privilege,in32BitMode,curArch,architecture,MCSR,holWordExtract]

-- Original csr1922_mode3; independently derived signed-range/permission result.
example (base : riscv_state) : observation base 1922 3 7 = (true,true,1,3,[false,false,false,false,false,false,true,true]) := by
  simp [observation,fixture,is_CSR_defined,csrRW,csrPR,checkCSROp,check_CSR_access,
    curPrivilege,privLevel,privilege,in32BitMode,curArch,architecture,MCSR,holWordExtract]

-- Original csr1923_mode3; independently derived signed-range/permission result.
example (base : riscv_state) : observation base 1923 3 255 = (true,true,1,3,[false,false,false,false,false,false,true,true]) := by
  simp [observation,fixture,is_CSR_defined,csrRW,csrPR,checkCSROp,check_CSR_access,
    curPrivilege,privLevel,privilege,in32BitMode,curArch,architecture,MCSR,holWordExtract]

-- Original csr1924_mode3; independently derived signed-range/permission result.
example (base : riscv_state) : observation base 1924 3 7 = (true,true,1,3,[false,false,false,false,false,false,true,true]) := by
  simp [observation,fixture,is_CSR_defined,csrRW,csrPR,checkCSROp,check_CSR_access,
    curPrivilege,privLevel,privilege,in32BitMode,curArch,architecture,MCSR,holWordExtract]

-- Original csr2047_mode3; independently derived signed-range/permission result.
example (base : riscv_state) : observation base 2047 3 255 = (true,true,1,3,[false,false,false,false,false,false,true,true]) := by
  simp [observation,fixture,is_CSR_defined,csrRW,csrPR,checkCSROp,check_CSR_access,
    curPrivilege,privLevel,privilege,in32BitMode,curArch,architecture,MCSR,holWordExtract]

-- Original csr2048_mode3; independently derived signed-range/permission result.
example (base : riscv_state) : observation base 2048 3 7 = (false,true,2,0,[false,false,false,false,false,false,false,false]) := by
  simp [observation,fixture,is_CSR_defined,csrRW,csrPR,checkCSROp,check_CSR_access,
    curPrivilege,privLevel,privilege,in32BitMode,curArch,architecture,MCSR,holWordExtract]

-- Original csr2303_mode3; independently derived signed-range/permission result.
example (base : riscv_state) : observation base 2303 3 255 = (false,true,2,0,[false,false,false,false,false,false,false,false]) := by
  simp [observation,fixture,is_CSR_defined,csrRW,csrPR,checkCSROp,check_CSR_access,
    curPrivilege,privLevel,privilege,in32BitMode,curArch,architecture,MCSR,holWordExtract]

-- Original csr2304_mode3; independently derived signed-range/permission result.
example (base : riscv_state) : observation base 2304 3 7 = (true,true,2,1,[false,false,true,true,true,true,true,true]) := by
  simp [observation,fixture,is_CSR_defined,csrRW,csrPR,checkCSROp,check_CSR_access,
    curPrivilege,privLevel,privilege,in32BitMode,curArch,architecture,MCSR,holWordExtract]

-- Original csr2306_mode3; independently derived signed-range/permission result.
example (base : riscv_state) : observation base 2306 3 7 = (true,true,2,1,[false,false,true,true,true,true,true,true]) := by
  simp [observation,fixture,is_CSR_defined,csrRW,csrPR,checkCSROp,check_CSR_access,
    curPrivilege,privLevel,privilege,in32BitMode,curArch,architecture,MCSR,holWordExtract]

-- Original csr2307_mode3; independently derived signed-range/permission result.
example (base : riscv_state) : observation base 2307 3 255 = (false,true,2,1,[false,false,false,false,false,false,false,false]) := by
  simp [observation,fixture,is_CSR_defined,csrRW,csrPR,checkCSROp,check_CSR_access,
    curPrivilege,privLevel,privilege,in32BitMode,curArch,architecture,MCSR,holWordExtract]

-- Original csr2431_mode3; independently derived signed-range/permission result.
example (base : riscv_state) : observation base 2431 3 255 = (false,true,2,1,[false,false,false,false,false,false,false,false]) := by
  simp [observation,fixture,is_CSR_defined,csrRW,csrPR,checkCSROp,check_CSR_access,
    curPrivilege,privLevel,privilege,in32BitMode,curArch,architecture,MCSR,holWordExtract]

-- Original csr2432_mode3; independently derived signed-range/permission result.
example (base : riscv_state) : observation base 2432 3 7 = (false,true,2,1,[false,false,false,false,false,false,false,false]) := by
  simp [observation,fixture,is_CSR_defined,csrRW,csrPR,checkCSROp,check_CSR_access,
    curPrivilege,privLevel,privilege,in32BitMode,curArch,architecture,MCSR,holWordExtract]

-- Original csr2434_mode3; independently derived signed-range/permission result.
example (base : riscv_state) : observation base 2434 3 7 = (false,true,2,1,[false,false,false,false,false,false,false,false]) := by
  simp [observation,fixture,is_CSR_defined,csrRW,csrPR,checkCSROp,check_CSR_access,
    curPrivilege,privLevel,privilege,in32BitMode,curArch,architecture,MCSR,holWordExtract]

-- Original csr2435_mode3; independently derived signed-range/permission result.
example (base : riscv_state) : observation base 2435 3 255 = (false,true,2,1,[false,false,false,false,false,false,false,false]) := by
  simp [observation,fixture,is_CSR_defined,csrRW,csrPR,checkCSROp,check_CSR_access,
    curPrivilege,privLevel,privilege,in32BitMode,curArch,architecture,MCSR,holWordExtract]

-- Original csr2816_mode3; independently derived signed-range/permission result.
example (base : riscv_state) : observation base 2816 3 7 = (false,true,2,3,[false,false,false,false,false,false,false,false]) := by
  simp [observation,fixture,is_CSR_defined,csrRW,csrPR,checkCSROp,check_CSR_access,
    curPrivilege,privLevel,privilege,in32BitMode,curArch,architecture,MCSR,holWordExtract]

-- Original csr2817_mode3; independently derived signed-range/permission result.
example (base : riscv_state) : observation base 2817 3 255 = (true,true,2,3,[false,false,false,false,false,false,true,true]) := by
  simp [observation,fixture,is_CSR_defined,csrRW,csrPR,checkCSROp,check_CSR_access,
    curPrivilege,privLevel,privilege,in32BitMode,curArch,architecture,MCSR,holWordExtract]

-- Original csr2818_mode3; independently derived signed-range/permission result.
example (base : riscv_state) : observation base 2818 3 7 = (true,true,2,3,[false,false,false,false,false,false,true,true]) := by
  simp [observation,fixture,is_CSR_defined,csrRW,csrPR,checkCSROp,check_CSR_access,
    curPrivilege,privLevel,privilege,in32BitMode,curArch,architecture,MCSR,holWordExtract]

-- Original csr2944_mode3; independently derived signed-range/permission result.
example (base : riscv_state) : observation base 2944 3 7 = (true,true,2,3,[false,false,false,false,false,false,true,true]) := by
  simp [observation,fixture,is_CSR_defined,csrRW,csrPR,checkCSROp,check_CSR_access,
    curPrivilege,privLevel,privilege,in32BitMode,curArch,architecture,MCSR,holWordExtract]

-- Original csr2945_mode3; independently derived signed-range/permission result.
example (base : riscv_state) : observation base 2945 3 255 = (true,true,2,3,[false,false,false,false,false,false,true,true]) := by
  simp [observation,fixture,is_CSR_defined,csrRW,csrPR,checkCSROp,check_CSR_access,
    curPrivilege,privLevel,privilege,in32BitMode,curArch,architecture,MCSR,holWordExtract]

-- Original csr2946_mode3; independently derived signed-range/permission result.
example (base : riscv_state) : observation base 2946 3 7 = (true,true,2,3,[false,false,false,false,false,false,true,true]) := by
  simp [observation,fixture,is_CSR_defined,csrRW,csrPR,checkCSROp,check_CSR_access,
    curPrivilege,privLevel,privilege,in32BitMode,curArch,architecture,MCSR,holWordExtract]

-- Original csr3071_mode3; independently derived signed-range/permission result.
example (base : riscv_state) : observation base 3071 3 255 = (true,true,2,3,[false,false,false,false,false,false,true,true]) := by
  simp [observation,fixture,is_CSR_defined,csrRW,csrPR,checkCSROp,check_CSR_access,
    curPrivilege,privLevel,privilege,in32BitMode,curArch,architecture,MCSR,holWordExtract]

-- Original csr3072_mode3; independently derived signed-range/permission result.
example (base : riscv_state) : observation base 3072 3 7 = (true,true,3,0,[true,false,true,false,true,false,true,false]) := by
  simp [observation,fixture,is_CSR_defined,csrRW,csrPR,checkCSROp,check_CSR_access,
    curPrivilege,privLevel,privilege,in32BitMode,curArch,architecture,MCSR,holWordExtract]

-- Original csr3074_mode3; independently derived signed-range/permission result.
example (base : riscv_state) : observation base 3074 3 7 = (true,true,3,0,[true,false,true,false,true,false,true,false]) := by
  simp [observation,fixture,is_CSR_defined,csrRW,csrPR,checkCSROp,check_CSR_access,
    curPrivilege,privLevel,privilege,in32BitMode,curArch,architecture,MCSR,holWordExtract]

-- Original csr3075_mode3; independently derived signed-range/permission result.
example (base : riscv_state) : observation base 3075 3 255 = (true,true,3,0,[true,false,true,false,true,false,true,false]) := by
  simp [observation,fixture,is_CSR_defined,csrRW,csrPR,checkCSROp,check_CSR_access,
    curPrivilege,privLevel,privilege,in32BitMode,curArch,architecture,MCSR,holWordExtract]

-- Original csr3199_mode3; independently derived signed-range/permission result.
example (base : riscv_state) : observation base 3199 3 255 = (true,true,3,0,[true,false,true,false,true,false,true,false]) := by
  simp [observation,fixture,is_CSR_defined,csrRW,csrPR,checkCSROp,check_CSR_access,
    curPrivilege,privLevel,privilege,in32BitMode,curArch,architecture,MCSR,holWordExtract]

-- Original csr3200_mode3; independently derived signed-range/permission result.
example (base : riscv_state) : observation base 3200 3 7 = (true,true,3,0,[true,false,true,false,true,false,true,false]) := by
  simp [observation,fixture,is_CSR_defined,csrRW,csrPR,checkCSROp,check_CSR_access,
    curPrivilege,privLevel,privilege,in32BitMode,curArch,architecture,MCSR,holWordExtract]

-- Original csr3202_mode3; independently derived signed-range/permission result.
example (base : riscv_state) : observation base 3202 3 7 = (true,true,3,0,[true,false,true,false,true,false,true,false]) := by
  simp [observation,fixture,is_CSR_defined,csrRW,csrPR,checkCSROp,check_CSR_access,
    curPrivilege,privLevel,privilege,in32BitMode,curArch,architecture,MCSR,holWordExtract]

-- Original csr3203_mode3; independently derived signed-range/permission result.
example (base : riscv_state) : observation base 3203 3 255 = (true,true,3,0,[true,false,true,false,true,false,true,false]) := by
  simp [observation,fixture,is_CSR_defined,csrRW,csrPR,checkCSROp,check_CSR_access,
    curPrivilege,privLevel,privilege,in32BitMode,curArch,architecture,MCSR,holWordExtract]

-- Original csr3328_mode3; independently derived signed-range/permission result.
example (base : riscv_state) : observation base 3328 3 7 = (true,true,3,1,[false,false,true,false,true,false,true,false]) := by
  simp [observation,fixture,is_CSR_defined,csrRW,csrPR,checkCSROp,check_CSR_access,
    curPrivilege,privLevel,privilege,in32BitMode,curArch,architecture,MCSR,holWordExtract]

-- Original csr3329_mode3; independently derived signed-range/permission result.
example (base : riscv_state) : observation base 3329 3 255 = (true,true,3,1,[false,false,true,false,true,false,true,false]) := by
  simp [observation,fixture,is_CSR_defined,csrRW,csrPR,checkCSROp,check_CSR_access,
    curPrivilege,privLevel,privilege,in32BitMode,curArch,architecture,MCSR,holWordExtract]

-- Original csr3330_mode3; independently derived signed-range/permission result.
example (base : riscv_state) : observation base 3330 3 7 = (true,true,3,1,[false,false,true,false,true,false,true,false]) := by
  simp [observation,fixture,is_CSR_defined,csrRW,csrPR,checkCSROp,check_CSR_access,
    curPrivilege,privLevel,privilege,in32BitMode,curArch,architecture,MCSR,holWordExtract]

-- Original csr3393_mode3; independently derived signed-range/permission result.
example (base : riscv_state) : observation base 3393 3 255 = (true,true,3,1,[false,false,true,false,true,false,true,false]) := by
  simp [observation,fixture,is_CSR_defined,csrRW,csrPR,checkCSROp,check_CSR_access,
    curPrivilege,privLevel,privilege,in32BitMode,curArch,architecture,MCSR,holWordExtract]

-- Original csr3394_mode3; independently derived signed-range/permission result.
example (base : riscv_state) : observation base 3394 3 7 = (true,true,3,1,[false,false,true,false,true,false,true,false]) := by
  simp [observation,fixture,is_CSR_defined,csrRW,csrPR,checkCSROp,check_CSR_access,
    curPrivilege,privLevel,privilege,in32BitMode,curArch,architecture,MCSR,holWordExtract]

-- Original csr3395_mode3; independently derived signed-range/permission result.
example (base : riscv_state) : observation base 3395 3 255 = (true,true,3,1,[false,false,true,false,true,false,true,false]) := by
  simp [observation,fixture,is_CSR_defined,csrRW,csrPR,checkCSROp,check_CSR_access,
    curPrivilege,privLevel,privilege,in32BitMode,curArch,architecture,MCSR,holWordExtract]

-- Original csr3396_mode3; independently derived signed-range/permission result.
example (base : riscv_state) : observation base 3396 3 7 = (true,true,3,1,[false,false,true,false,true,false,true,false]) := by
  simp [observation,fixture,is_CSR_defined,csrRW,csrPR,checkCSROp,check_CSR_access,
    curPrivilege,privLevel,privilege,in32BitMode,curArch,architecture,MCSR,holWordExtract]

-- Original csr3456_mode3; independently derived signed-range/permission result.
example (base : riscv_state) : observation base 3456 3 7 = (true,true,3,1,[false,false,true,false,true,false,true,false]) := by
  simp [observation,fixture,is_CSR_defined,csrRW,csrPR,checkCSROp,check_CSR_access,
    curPrivilege,privLevel,privilege,in32BitMode,curArch,architecture,MCSR,holWordExtract]

-- Original csr3457_mode3; independently derived signed-range/permission result.
example (base : riscv_state) : observation base 3457 3 255 = (true,true,3,1,[false,false,true,false,true,false,true,false]) := by
  simp [observation,fixture,is_CSR_defined,csrRW,csrPR,checkCSROp,check_CSR_access,
    curPrivilege,privLevel,privilege,in32BitMode,curArch,architecture,MCSR,holWordExtract]

-- Original csr3458_mode3; independently derived signed-range/permission result.
example (base : riscv_state) : observation base 3458 3 7 = (true,true,3,1,[false,false,true,false,true,false,true,false]) := by
  simp [observation,fixture,is_CSR_defined,csrRW,csrPR,checkCSROp,check_CSR_access,
    curPrivilege,privLevel,privilege,in32BitMode,curArch,architecture,MCSR,holWordExtract]

-- Original csr3839_mode3; independently derived signed-range/permission result.
example (base : riscv_state) : observation base 3839 3 255 = (true,true,3,2,[false,false,false,false,true,false,true,false]) := by
  simp [observation,fixture,is_CSR_defined,csrRW,csrPR,checkCSROp,check_CSR_access,
    curPrivilege,privLevel,privilege,in32BitMode,curArch,architecture,MCSR,holWordExtract]

-- Original csr3840_mode3; independently derived signed-range/permission result.
example (base : riscv_state) : observation base 3840 3 7 = (true,true,3,3,[false,false,false,false,false,false,true,false]) := by
  simp [observation,fixture,is_CSR_defined,csrRW,csrPR,checkCSROp,check_CSR_access,
    curPrivilege,privLevel,privilege,in32BitMode,curArch,architecture,MCSR,holWordExtract]

-- Original csr3841_mode3; independently derived signed-range/permission result.
example (base : riscv_state) : observation base 3841 3 255 = (true,true,3,3,[false,false,false,false,false,false,true,false]) := by
  simp [observation,fixture,is_CSR_defined,csrRW,csrPR,checkCSROp,check_CSR_access,
    curPrivilege,privLevel,privilege,in32BitMode,curArch,architecture,MCSR,holWordExtract]

-- Original csr3842_mode3; independently derived signed-range/permission result.
example (base : riscv_state) : observation base 3842 3 7 = (true,true,3,3,[false,false,false,false,false,false,true,false]) := by
  simp [observation,fixture,is_CSR_defined,csrRW,csrPR,checkCSROp,check_CSR_access,
    curPrivilege,privLevel,privilege,in32BitMode,curArch,architecture,MCSR,holWordExtract]

-- Original csr3855_mode3; independently derived signed-range/permission result.
example (base : riscv_state) : observation base 3855 3 255 = (true,true,3,3,[false,false,false,false,false,false,true,false]) := by
  simp [observation,fixture,is_CSR_defined,csrRW,csrPR,checkCSROp,check_CSR_access,
    curPrivilege,privLevel,privilege,in32BitMode,curArch,architecture,MCSR,holWordExtract]

-- Original csr3856_mode3; independently derived signed-range/permission result.
example (base : riscv_state) : observation base 3856 3 7 = (true,true,3,3,[false,false,false,false,false,false,true,false]) := by
  simp [observation,fixture,is_CSR_defined,csrRW,csrPR,checkCSROp,check_CSR_access,
    curPrivilege,privLevel,privilege,in32BitMode,curArch,architecture,MCSR,holWordExtract]

-- Original csr3857_mode3; independently derived signed-range/permission result.
example (base : riscv_state) : observation base 3857 3 255 = (true,true,3,3,[false,false,false,false,false,false,true,false]) := by
  simp [observation,fixture,is_CSR_defined,csrRW,csrPR,checkCSROp,check_CSR_access,
    curPrivilege,privLevel,privilege,in32BitMode,curArch,architecture,MCSR,holWordExtract]

-- Original csr4095_mode3; independently derived signed-range/permission result.
example (base : riscv_state) : observation base 4095 3 255 = (true,true,3,3,[false,false,false,false,false,false,true,false]) := by
  simp [observation,fixture,is_CSR_defined,csrRW,csrPR,checkCSROp,check_CSR_access,
    curPrivilege,privLevel,privilege,in32BitMode,curArch,architecture,MCSR,holWordExtract]

private def unknownFixture (base : riscv_state) (prior : Bool) : riscv_state :=
  { fixture base 1 3 255 with exception := if prior then .INTERNAL_ERROR [120] else .NoException }
private def wantedException (prior touched : Bool) : exception :=
  if prior then .INTERNAL_ERROR [120] else if touched then
    .UNDEFINED [85,110,107,110,111,119,110,32,97,114,99,104,105,116,101,99,116,117,114,101,58,32,49]
  else .NoException
private noncomputable def unknownObservation (base : riscv_state) (csr : BitVec 12)
    (prior touched : Bool) := by
  classical
  exact let s := unknownFixture base prior
    let t := (is_CSR_defined csr s).2
    (decide (t.exception = wantedException prior touched),
      decide ({ t with exception := s.exception } = s),
      decide ((checkCSROp (csr,31,.Write) s).2 = t))
-- Original unknown_csr3200_prior0; arbitrary architecture result retained.
example (base : riscv_state) : unknownObservation base 3200 false true = (true,true,true) := by
  classical
  by_cases h : Flapjack.holArb Architecture = Architecture.RV32I <;>
   simp [h,unknownObservation,unknownFixture,wantedException,fixture,is_CSR_defined,checkCSROp,in32BitMode,curArch,architecture,MCSR,«raise'exception»,Flapjack.holNumToDecString,Flapjack.holN2s,Flapjack.holN2l,Flapjack.holHex]

-- Original unknown_csr3200_prior1; arbitrary architecture result retained.
example (base : riscv_state) : unknownObservation base 3200 true true = (true,true,true) := by
  classical
  by_cases h : Flapjack.holArb Architecture = Architecture.RV32I <;>
   simp [h,unknownObservation,unknownFixture,wantedException,fixture,is_CSR_defined,checkCSROp,in32BitMode,curArch,architecture,MCSR,«raise'exception»,Flapjack.holNumToDecString,Flapjack.holN2s,Flapjack.holN2l,Flapjack.holHex]

-- Original unknown_csr3202_prior0; arbitrary architecture result retained.
example (base : riscv_state) : unknownObservation base 3202 false true = (true,true,true) := by
  classical
  by_cases h : Flapjack.holArb Architecture = Architecture.RV32I <;>
   simp [h,unknownObservation,unknownFixture,wantedException,fixture,is_CSR_defined,checkCSROp,in32BitMode,curArch,architecture,MCSR,«raise'exception»,Flapjack.holNumToDecString,Flapjack.holN2s,Flapjack.holN2l,Flapjack.holHex]

-- Original unknown_csr3202_prior1; arbitrary architecture result retained.
example (base : riscv_state) : unknownObservation base 3202 true true = (true,true,true) := by
  classical
  by_cases h : Flapjack.holArb Architecture = Architecture.RV32I <;>
   simp [h,unknownObservation,unknownFixture,wantedException,fixture,is_CSR_defined,checkCSROp,in32BitMode,curArch,architecture,MCSR,«raise'exception»,Flapjack.holNumToDecString,Flapjack.holN2s,Flapjack.holN2l,Flapjack.holHex]

-- Original unknown_csr3457_prior0; arbitrary architecture result retained.
example (base : riscv_state) : unknownObservation base 3457 false true = (true,true,true) := by
  classical
  by_cases h : Flapjack.holArb Architecture = Architecture.RV32I <;>
   simp [h,unknownObservation,unknownFixture,wantedException,fixture,is_CSR_defined,checkCSROp,in32BitMode,curArch,architecture,MCSR,«raise'exception»,Flapjack.holNumToDecString,Flapjack.holN2s,Flapjack.holN2l,Flapjack.holHex]

-- Original unknown_csr3457_prior1; arbitrary architecture result retained.
example (base : riscv_state) : unknownObservation base 3457 true true = (true,true,true) := by
  classical
  by_cases h : Flapjack.holArb Architecture = Architecture.RV32I <;>
   simp [h,unknownObservation,unknownFixture,wantedException,fixture,is_CSR_defined,checkCSROp,in32BitMode,curArch,architecture,MCSR,«raise'exception»,Flapjack.holNumToDecString,Flapjack.holN2s,Flapjack.holN2l,Flapjack.holHex]

-- Original unknown_csr2432_prior0; arbitrary architecture result retained.
example (base : riscv_state) : unknownObservation base 2432 false true = (true,true,true) := by
  classical
  by_cases h : Flapjack.holArb Architecture = Architecture.RV32I <;>
   simp [h,unknownObservation,unknownFixture,wantedException,fixture,is_CSR_defined,checkCSROp,in32BitMode,curArch,architecture,MCSR,«raise'exception»,Flapjack.holNumToDecString,Flapjack.holN2s,Flapjack.holN2l,Flapjack.holHex]

-- Original unknown_csr2432_prior1; arbitrary architecture result retained.
example (base : riscv_state) : unknownObservation base 2432 true true = (true,true,true) := by
  classical
  by_cases h : Flapjack.holArb Architecture = Architecture.RV32I <;>
   simp [h,unknownObservation,unknownFixture,wantedException,fixture,is_CSR_defined,checkCSROp,in32BitMode,curArch,architecture,MCSR,«raise'exception»,Flapjack.holNumToDecString,Flapjack.holN2s,Flapjack.holN2l,Flapjack.holHex]

-- Original unknown_csr2434_prior0; arbitrary architecture result retained.
example (base : riscv_state) : unknownObservation base 2434 false true = (true,true,true) := by
  classical
  by_cases h : Flapjack.holArb Architecture = Architecture.RV32I <;>
   simp [h,unknownObservation,unknownFixture,wantedException,fixture,is_CSR_defined,checkCSROp,in32BitMode,curArch,architecture,MCSR,«raise'exception»,Flapjack.holNumToDecString,Flapjack.holN2s,Flapjack.holN2l,Flapjack.holHex]

-- Original unknown_csr2434_prior1; arbitrary architecture result retained.
example (base : riscv_state) : unknownObservation base 2434 true true = (true,true,true) := by
  classical
  by_cases h : Flapjack.holArb Architecture = Architecture.RV32I <;>
   simp [h,unknownObservation,unknownFixture,wantedException,fixture,is_CSR_defined,checkCSROp,in32BitMode,curArch,architecture,MCSR,«raise'exception»,Flapjack.holNumToDecString,Flapjack.holN2s,Flapjack.holN2l,Flapjack.holHex]

-- Original unknown_csr1857_prior0; arbitrary architecture result retained.
example (base : riscv_state) : unknownObservation base 1857 false true = (true,true,true) := by
  classical
  by_cases h : Flapjack.holArb Architecture = Architecture.RV32I <;>
   simp [h,unknownObservation,unknownFixture,wantedException,fixture,is_CSR_defined,checkCSROp,in32BitMode,curArch,architecture,MCSR,«raise'exception»,Flapjack.holNumToDecString,Flapjack.holN2s,Flapjack.holN2l,Flapjack.holHex]

-- Original unknown_csr1857_prior1; arbitrary architecture result retained.
example (base : riscv_state) : unknownObservation base 1857 true true = (true,true,true) := by
  classical
  by_cases h : Flapjack.holArb Architecture = Architecture.RV32I <;>
   simp [h,unknownObservation,unknownFixture,wantedException,fixture,is_CSR_defined,checkCSROp,in32BitMode,curArch,architecture,MCSR,«raise'exception»,Flapjack.holNumToDecString,Flapjack.holN2s,Flapjack.holN2l,Flapjack.holHex]

-- Original unknown_csr2945_prior0; arbitrary architecture result retained.
example (base : riscv_state) : unknownObservation base 2945 false false = (true,true,true) := by
  classical
  by_cases h : Flapjack.holArb Architecture = Architecture.RV32I <;>
   simp [h,unknownObservation,unknownFixture,wantedException,fixture,is_CSR_defined,checkCSROp,in32BitMode,curArch,architecture,MCSR,«raise'exception»,Flapjack.holNumToDecString,Flapjack.holN2s,Flapjack.holN2l,Flapjack.holHex]

-- Original unknown_csr2945_prior1; arbitrary architecture result retained.
example (base : riscv_state) : unknownObservation base 2945 true false = (true,true,true) := by
  classical
  by_cases h : Flapjack.holArb Architecture = Architecture.RV32I <;>
   simp [h,unknownObservation,unknownFixture,wantedException,fixture,is_CSR_defined,checkCSROp,in32BitMode,curArch,architecture,MCSR,«raise'exception»,Flapjack.holNumToDecString,Flapjack.holN2s,Flapjack.holN2l,Flapjack.holHex]

-- Original unknown_csr0_prior0; arbitrary architecture result retained.
example (base : riscv_state) : unknownObservation base 0 false false = (true,true,true) := by
  classical
  by_cases h : Flapjack.holArb Architecture = Architecture.RV32I <;>
   simp [h,unknownObservation,unknownFixture,wantedException,fixture,is_CSR_defined,checkCSROp,in32BitMode,curArch,architecture,MCSR,«raise'exception»,Flapjack.holNumToDecString,Flapjack.holN2s,Flapjack.holN2l,Flapjack.holHex]

-- Original unknown_csr0_prior1; arbitrary architecture result retained.
example (base : riscv_state) : unknownObservation base 0 true false = (true,true,true) := by
  classical
  by_cases h : Flapjack.holArb Architecture = Architecture.RV32I <;>
   simp [h,unknownObservation,unknownFixture,wantedException,fixture,is_CSR_defined,checkCSROp,in32BitMode,curArch,architecture,MCSR,«raise'exception»,Flapjack.holNumToDecString,Flapjack.holN2s,Flapjack.holN2l,Flapjack.holHex]

-- Original unknown_csr2048_prior0; arbitrary architecture result retained.
example (base : riscv_state) : unknownObservation base 2048 false false = (true,true,true) := by
  classical
  by_cases h : Flapjack.holArb Architecture = Architecture.RV32I <;>
   simp [h,unknownObservation,unknownFixture,wantedException,fixture,is_CSR_defined,checkCSROp,in32BitMode,curArch,architecture,MCSR,«raise'exception»,Flapjack.holNumToDecString,Flapjack.holN2s,Flapjack.holN2l,Flapjack.holHex]

-- Original unknown_csr2048_prior1; arbitrary architecture result retained.
example (base : riscv_state) : unknownObservation base 2048 true false = (true,true,true) := by
  classical
  by_cases h : Flapjack.holArb Architecture = Architecture.RV32I <;>
   simp [h,unknownObservation,unknownFixture,wantedException,fixture,is_CSR_defined,checkCSROp,in32BitMode,curArch,architecture,MCSR,«raise'exception»,Flapjack.holNumToDecString,Flapjack.holN2s,Flapjack.holN2l,Flapjack.holHex]

end Flapjack.Test.L3CSRAccessParity
