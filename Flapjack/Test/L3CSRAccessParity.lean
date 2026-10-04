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
-- Original csr256_mode0; independently derived signed-range/permission result.
example (base : riscv_state) : observation base 256 0 7 = (true,true,0,1,[false,false,true,true,true,true,true,true]) := by
  simp [observation,fixture,is_CSR_defined,csrRW,csrPR,checkCSROp,check_CSR_access,
    curPrivilege,privLevel,privilege,in32BitMode,curArch,architecture,MCSR,holWordExtract]

-- Original csr257_mode0; independently derived signed-range/permission result.
example (base : riscv_state) : observation base 257 0 255 = (true,true,0,1,[false,false,true,true,true,true,true,true]) := by
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

-- Original csr768_mode0; independently derived signed-range/permission result.
example (base : riscv_state) : observation base 768 0 7 = (true,true,0,3,[false,false,false,false,false,false,true,true]) := by
  simp [observation,fixture,is_CSR_defined,csrRW,csrPR,checkCSROp,check_CSR_access,
    curPrivilege,privLevel,privilege,in32BitMode,curArch,architecture,MCSR,holWordExtract]

-- Original csr832_mode0; independently derived signed-range/permission result.
example (base : riscv_state) : observation base 832 0 7 = (true,true,0,3,[false,false,false,false,false,false,true,true]) := by
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

-- Original csr1920_mode0; independently derived signed-range/permission result.
example (base : riscv_state) : observation base 1920 0 7 = (true,true,1,3,[false,false,false,false,false,false,true,true]) := by
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

-- Original csr3840_mode0; independently derived signed-range/permission result.
example (base : riscv_state) : observation base 3840 0 7 = (true,true,3,3,[false,false,false,false,false,false,true,false]) := by
  simp [observation,fixture,is_CSR_defined,csrRW,csrPR,checkCSROp,check_CSR_access,
    curPrivilege,privLevel,privilege,in32BitMode,curArch,architecture,MCSR,holWordExtract]

-- Original csr3841_mode0; independently derived signed-range/permission result.
example (base : riscv_state) : observation base 3841 0 255 = (true,true,3,3,[false,false,false,false,false,false,true,false]) := by
  simp [observation,fixture,is_CSR_defined,csrRW,csrPR,checkCSROp,check_CSR_access,
    curPrivilege,privLevel,privilege,in32BitMode,curArch,architecture,MCSR,holWordExtract]

-- Original csr3856_mode0; independently derived signed-range/permission result.
example (base : riscv_state) : observation base 3856 0 7 = (true,true,3,3,[false,false,false,false,false,false,true,false]) := by
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

-- Original csr320_mode2; independently derived signed-range/permission result.
example (base : riscv_state) : observation base 320 2 7 = (true,true,0,1,[false,false,true,true,true,true,true,true]) := by
  simp [observation,fixture,is_CSR_defined,csrRW,csrPR,checkCSROp,check_CSR_access,
    curPrivilege,privLevel,privilege,in32BitMode,curArch,architecture,MCSR,holWordExtract]

-- Original csr321_mode2; independently derived signed-range/permission result.
example (base : riscv_state) : observation base 321 2 255 = (true,true,0,1,[false,false,true,true,true,true,true,true]) := by
  simp [observation,fixture,is_CSR_defined,csrRW,csrPR,checkCSROp,check_CSR_access,
    curPrivilege,privLevel,privilege,in32BitMode,curArch,architecture,MCSR,holWordExtract]

-- Original csr768_mode2; independently derived signed-range/permission result.
example (base : riscv_state) : observation base 768 2 7 = (true,true,0,3,[false,false,false,false,false,false,true,true]) := by
  simp [observation,fixture,is_CSR_defined,csrRW,csrPR,checkCSROp,check_CSR_access,
    curPrivilege,privLevel,privilege,in32BitMode,curArch,architecture,MCSR,holWordExtract]

-- Original csr832_mode2; independently derived signed-range/permission result.
example (base : riscv_state) : observation base 832 2 7 = (true,true,0,3,[false,false,false,false,false,false,true,true]) := by
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

-- Original csr1920_mode2; independently derived signed-range/permission result.
example (base : riscv_state) : observation base 1920 2 7 = (true,true,1,3,[false,false,false,false,false,false,true,true]) := by
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

-- Original csr3840_mode2; independently derived signed-range/permission result.
example (base : riscv_state) : observation base 3840 2 7 = (true,true,3,3,[false,false,false,false,false,false,true,false]) := by
  simp [observation,fixture,is_CSR_defined,csrRW,csrPR,checkCSROp,check_CSR_access,
    curPrivilege,privLevel,privilege,in32BitMode,curArch,architecture,MCSR,holWordExtract]

-- Original csr3841_mode2; independently derived signed-range/permission result.
example (base : riscv_state) : observation base 3841 2 255 = (true,true,3,3,[false,false,false,false,false,false,true,false]) := by
  simp [observation,fixture,is_CSR_defined,csrRW,csrPR,checkCSROp,check_CSR_access,
    curPrivilege,privLevel,privilege,in32BitMode,curArch,architecture,MCSR,holWordExtract]

-- Original csr3856_mode2; independently derived signed-range/permission result.
example (base : riscv_state) : observation base 3856 2 7 = (true,true,3,3,[false,false,false,false,false,false,true,false]) := by
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

-- Original csr320_mode3; independently derived signed-range/permission result.
example (base : riscv_state) : observation base 320 3 7 = (true,true,0,1,[false,false,true,true,true,true,true,true]) := by
  simp [observation,fixture,is_CSR_defined,csrRW,csrPR,checkCSROp,check_CSR_access,
    curPrivilege,privLevel,privilege,in32BitMode,curArch,architecture,MCSR,holWordExtract]

-- Original csr321_mode3; independently derived signed-range/permission result.
example (base : riscv_state) : observation base 321 3 255 = (true,true,0,1,[false,false,true,true,true,true,true,true]) := by
  simp [observation,fixture,is_CSR_defined,csrRW,csrPR,checkCSROp,check_CSR_access,
    curPrivilege,privLevel,privilege,in32BitMode,curArch,architecture,MCSR,holWordExtract]

-- Original csr768_mode3; independently derived signed-range/permission result.
example (base : riscv_state) : observation base 768 3 7 = (true,true,0,3,[false,false,false,false,false,false,true,true]) := by
  simp [observation,fixture,is_CSR_defined,csrRW,csrPR,checkCSROp,check_CSR_access,
    curPrivilege,privLevel,privilege,in32BitMode,curArch,architecture,MCSR,holWordExtract]

-- Original csr832_mode3; independently derived signed-range/permission result.
example (base : riscv_state) : observation base 832 3 7 = (true,true,0,3,[false,false,false,false,false,false,true,true]) := by
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

-- Original csr1920_mode3; independently derived signed-range/permission result.
example (base : riscv_state) : observation base 1920 3 7 = (true,true,1,3,[false,false,false,false,false,false,true,true]) := by
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

-- Original csr3840_mode3; independently derived signed-range/permission result.
example (base : riscv_state) : observation base 3840 3 7 = (true,true,3,3,[false,false,false,false,false,false,true,false]) := by
  simp [observation,fixture,is_CSR_defined,csrRW,csrPR,checkCSROp,check_CSR_access,
    curPrivilege,privLevel,privilege,in32BitMode,curArch,architecture,MCSR,holWordExtract]

-- Original csr3841_mode3; independently derived signed-range/permission result.
example (base : riscv_state) : observation base 3841 3 255 = (true,true,3,3,[false,false,false,false,false,false,true,false]) := by
  simp [observation,fixture,is_CSR_defined,csrRW,csrPR,checkCSROp,check_CSR_access,
    curPrivilege,privLevel,privilege,in32BitMode,curArch,architecture,MCSR,holWordExtract]

-- Original csr3856_mode3; independently derived signed-range/permission result.
example (base : riscv_state) : observation base 3856 3 7 = (true,true,3,3,[false,false,false,false,false,false,true,false]) := by
  simp [observation,fixture,is_CSR_defined,csrRW,csrPR,checkCSROp,check_CSR_access,
    curPrivilege,privLevel,privilege,in32BitMode,curArch,architecture,MCSR,holWordExtract]


-- Former FP, counter/timer, interrupt and page-table addresses are unavailable
-- for every state, including arbitrary legacy architecture and privilege fields.
example (s : riscv_state) :
    ([1, 2, 3, 3072, 3073, 3074, 3200, 3201, 3202, 260, 289, 3329,
      3457, 324, 384, 385, 2304, 2305, 2306, 2432, 2433, 2434, 514,
      545, 3585, 3713, 2561, 2689, 770, 772, 801, 1793, 1857, 836,
      2817, 2945, 1923] : List Nat).all
      (fun n => !(is_CSR_defined (BitVec.ofNat 12 n) s).1) = true := by
  simp only [is_CSR_defined]
  decide

end Flapjack.Test.L3CSRAccessParity
