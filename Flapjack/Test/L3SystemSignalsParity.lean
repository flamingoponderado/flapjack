import Flapjack.RiscV.L3.Defs.SystemSignals
namespace Flapjack.Test.L3SystemSignalsParity
open Flapjack.RiscV.L3
/-! Flapjack-only whole-frame regressions from original HOL observations.
These guards retain arbitrary fields outside c_NextFetch and do not establish
whole Run/Next or compiler correctness. -/
private def fixture (base : riscv_state) (priv core : Nat) (prior : Bool) : riscv_state :=
{ base with procID := BitVec.ofNat 8 core, totalCore := 1, exception := if prior then .INTERNAL_ERROR [101,120,105,115,116,105,110,103] else .NoException, c_NextFetch := fun _ => some (.BranchTo 0), c_MCSR := fun id => { base.c_MCSR id with mstatus := { (base.c_MCSR id).mstatus with MPRV := BitVec.ofNat 2 priv } } }

private def view : Option TransferControl → Nat × Option Nat
  | some (.Trap t) => ((if t.trap == .Illegal_Instr then 1 else if t.trap == .Breakpoint then 2 else if t.trap == .UMode_Env_Call then 3 else if t.trap == .SMode_Env_Call then 4 else if t.trap == .HMode_Env_Call then 5 else if t.trap == .MMode_Env_Call then 6 else 9), t.badaddr.map BitVec.toNat)
  | some (.BranchTo 0) => (7,none)
  | _ => (0,none)
private noncomputable def observation (f : riscv_state → riscv_state) (s : riscv_state) := by
  classical
  exact let r := f s
    (view (r.c_NextFetch s.procID),decide (r.c_NextFetch (s.procID+1) = some (.BranchTo 0)),
      decide (r.exception = s.exception),decide ({ r with c_NextFetch := s.c_NextFetch } = s),r.totalCore,r.procID.toNat)
-- Original signal0_priv0_prior0_core7; literal independent selector/frame result.
example (base : riscv_state) :
    observation (signalEnvCall ()) (fixture base 0 7 false) =
      ((3,none),true,true,true,1,7) := by
  simp [observation,fixture,view,signalEnvCall,«dfn'ECALL»,«dfn'EBREAK»,
    «dfn'UnknownInstruction»,signalException,setTrap,«write'NextFetch»,MCSR,privilege,
    holUpdate,holWordExtract]

-- Original signal0_priv0_prior0_core255; literal independent selector/frame result.
example (base : riscv_state) :
    observation (signalEnvCall ()) (fixture base 0 255 false) =
      ((3,none),true,true,true,1,255) := by
  simp [observation,fixture,view,signalEnvCall,«dfn'ECALL»,«dfn'EBREAK»,
    «dfn'UnknownInstruction»,signalException,setTrap,«write'NextFetch»,MCSR,privilege,
    holUpdate,holWordExtract]

-- Original signal0_priv0_prior1_core7; literal independent selector/frame result.
example (base : riscv_state) :
    observation (signalEnvCall ()) (fixture base 0 7 true) =
      ((3,none),true,true,true,1,7) := by
  simp [observation,fixture,view,signalEnvCall,«dfn'ECALL»,«dfn'EBREAK»,
    «dfn'UnknownInstruction»,signalException,setTrap,«write'NextFetch»,MCSR,privilege,
    holUpdate,holWordExtract]

-- Original signal0_priv0_prior1_core255; literal independent selector/frame result.
example (base : riscv_state) :
    observation (signalEnvCall ()) (fixture base 0 255 true) =
      ((3,none),true,true,true,1,255) := by
  simp [observation,fixture,view,signalEnvCall,«dfn'ECALL»,«dfn'EBREAK»,
    «dfn'UnknownInstruction»,signalException,setTrap,«write'NextFetch»,MCSR,privilege,
    holUpdate,holWordExtract]

-- Original signal0_priv1_prior0_core7; literal independent selector/frame result.
example (base : riscv_state) :
    observation (signalEnvCall ()) (fixture base 1 7 false) =
      ((4,none),true,true,true,1,7) := by
  simp [observation,fixture,view,signalEnvCall,«dfn'ECALL»,«dfn'EBREAK»,
    «dfn'UnknownInstruction»,signalException,setTrap,«write'NextFetch»,MCSR,privilege,
    holUpdate,holWordExtract]

-- Original signal0_priv1_prior0_core255; literal independent selector/frame result.
example (base : riscv_state) :
    observation (signalEnvCall ()) (fixture base 1 255 false) =
      ((4,none),true,true,true,1,255) := by
  simp [observation,fixture,view,signalEnvCall,«dfn'ECALL»,«dfn'EBREAK»,
    «dfn'UnknownInstruction»,signalException,setTrap,«write'NextFetch»,MCSR,privilege,
    holUpdate,holWordExtract]

-- Original signal0_priv1_prior1_core7; literal independent selector/frame result.
example (base : riscv_state) :
    observation (signalEnvCall ()) (fixture base 1 7 true) =
      ((4,none),true,true,true,1,7) := by
  simp [observation,fixture,view,signalEnvCall,«dfn'ECALL»,«dfn'EBREAK»,
    «dfn'UnknownInstruction»,signalException,setTrap,«write'NextFetch»,MCSR,privilege,
    holUpdate,holWordExtract]

-- Original signal0_priv1_prior1_core255; literal independent selector/frame result.
example (base : riscv_state) :
    observation (signalEnvCall ()) (fixture base 1 255 true) =
      ((4,none),true,true,true,1,255) := by
  simp [observation,fixture,view,signalEnvCall,«dfn'ECALL»,«dfn'EBREAK»,
    «dfn'UnknownInstruction»,signalException,setTrap,«write'NextFetch»,MCSR,privilege,
    holUpdate,holWordExtract]

-- Original signal0_priv2_prior0_core7; literal independent selector/frame result.
example (base : riscv_state) :
    observation (signalEnvCall ()) (fixture base 2 7 false) =
      ((5,none),true,true,true,1,7) := by
  simp [observation,fixture,view,signalEnvCall,«dfn'ECALL»,«dfn'EBREAK»,
    «dfn'UnknownInstruction»,signalException,setTrap,«write'NextFetch»,MCSR,privilege,
    holUpdate,holWordExtract]

-- Original signal0_priv2_prior0_core255; literal independent selector/frame result.
example (base : riscv_state) :
    observation (signalEnvCall ()) (fixture base 2 255 false) =
      ((5,none),true,true,true,1,255) := by
  simp [observation,fixture,view,signalEnvCall,«dfn'ECALL»,«dfn'EBREAK»,
    «dfn'UnknownInstruction»,signalException,setTrap,«write'NextFetch»,MCSR,privilege,
    holUpdate,holWordExtract]

-- Original signal0_priv2_prior1_core7; literal independent selector/frame result.
example (base : riscv_state) :
    observation (signalEnvCall ()) (fixture base 2 7 true) =
      ((5,none),true,true,true,1,7) := by
  simp [observation,fixture,view,signalEnvCall,«dfn'ECALL»,«dfn'EBREAK»,
    «dfn'UnknownInstruction»,signalException,setTrap,«write'NextFetch»,MCSR,privilege,
    holUpdate,holWordExtract]

-- Original signal0_priv2_prior1_core255; literal independent selector/frame result.
example (base : riscv_state) :
    observation (signalEnvCall ()) (fixture base 2 255 true) =
      ((5,none),true,true,true,1,255) := by
  simp [observation,fixture,view,signalEnvCall,«dfn'ECALL»,«dfn'EBREAK»,
    «dfn'UnknownInstruction»,signalException,setTrap,«write'NextFetch»,MCSR,privilege,
    holUpdate,holWordExtract]

-- Original signal0_priv3_prior0_core7; literal independent selector/frame result.
example (base : riscv_state) :
    observation (signalEnvCall ()) (fixture base 3 7 false) =
      ((6,none),true,true,true,1,7) := by
  simp [observation,fixture,view,signalEnvCall,«dfn'ECALL»,«dfn'EBREAK»,
    «dfn'UnknownInstruction»,signalException,setTrap,«write'NextFetch»,MCSR,privilege,
    holUpdate,holWordExtract]

-- Original signal0_priv3_prior0_core255; literal independent selector/frame result.
example (base : riscv_state) :
    observation (signalEnvCall ()) (fixture base 3 255 false) =
      ((6,none),true,true,true,1,255) := by
  simp [observation,fixture,view,signalEnvCall,«dfn'ECALL»,«dfn'EBREAK»,
    «dfn'UnknownInstruction»,signalException,setTrap,«write'NextFetch»,MCSR,privilege,
    holUpdate,holWordExtract]

-- Original signal0_priv3_prior1_core7; literal independent selector/frame result.
example (base : riscv_state) :
    observation (signalEnvCall ()) (fixture base 3 7 true) =
      ((6,none),true,true,true,1,7) := by
  simp [observation,fixture,view,signalEnvCall,«dfn'ECALL»,«dfn'EBREAK»,
    «dfn'UnknownInstruction»,signalException,setTrap,«write'NextFetch»,MCSR,privilege,
    holUpdate,holWordExtract]

-- Original signal0_priv3_prior1_core255; literal independent selector/frame result.
example (base : riscv_state) :
    observation (signalEnvCall ()) (fixture base 3 255 true) =
      ((6,none),true,true,true,1,255) := by
  simp [observation,fixture,view,signalEnvCall,«dfn'ECALL»,«dfn'EBREAK»,
    «dfn'UnknownInstruction»,signalException,setTrap,«write'NextFetch»,MCSR,privilege,
    holUpdate,holWordExtract]

-- Original signal1_priv0_prior0_core7; literal independent selector/frame result.
example (base : riscv_state) :
    observation «dfn'ECALL» (fixture base 0 7 false) =
      ((3,none),true,true,true,1,7) := by
  simp [observation,fixture,view,signalEnvCall,«dfn'ECALL»,«dfn'EBREAK»,
    «dfn'UnknownInstruction»,signalException,setTrap,«write'NextFetch»,MCSR,privilege,
    holUpdate,holWordExtract]

-- Original signal1_priv0_prior0_core255; literal independent selector/frame result.
example (base : riscv_state) :
    observation «dfn'ECALL» (fixture base 0 255 false) =
      ((3,none),true,true,true,1,255) := by
  simp [observation,fixture,view,signalEnvCall,«dfn'ECALL»,«dfn'EBREAK»,
    «dfn'UnknownInstruction»,signalException,setTrap,«write'NextFetch»,MCSR,privilege,
    holUpdate,holWordExtract]

-- Original signal1_priv0_prior1_core7; literal independent selector/frame result.
example (base : riscv_state) :
    observation «dfn'ECALL» (fixture base 0 7 true) =
      ((3,none),true,true,true,1,7) := by
  simp [observation,fixture,view,signalEnvCall,«dfn'ECALL»,«dfn'EBREAK»,
    «dfn'UnknownInstruction»,signalException,setTrap,«write'NextFetch»,MCSR,privilege,
    holUpdate,holWordExtract]

-- Original signal1_priv0_prior1_core255; literal independent selector/frame result.
example (base : riscv_state) :
    observation «dfn'ECALL» (fixture base 0 255 true) =
      ((3,none),true,true,true,1,255) := by
  simp [observation,fixture,view,signalEnvCall,«dfn'ECALL»,«dfn'EBREAK»,
    «dfn'UnknownInstruction»,signalException,setTrap,«write'NextFetch»,MCSR,privilege,
    holUpdate,holWordExtract]

-- Original signal1_priv1_prior0_core7; literal independent selector/frame result.
example (base : riscv_state) :
    observation «dfn'ECALL» (fixture base 1 7 false) =
      ((4,none),true,true,true,1,7) := by
  simp [observation,fixture,view,signalEnvCall,«dfn'ECALL»,«dfn'EBREAK»,
    «dfn'UnknownInstruction»,signalException,setTrap,«write'NextFetch»,MCSR,privilege,
    holUpdate,holWordExtract]

-- Original signal1_priv1_prior0_core255; literal independent selector/frame result.
example (base : riscv_state) :
    observation «dfn'ECALL» (fixture base 1 255 false) =
      ((4,none),true,true,true,1,255) := by
  simp [observation,fixture,view,signalEnvCall,«dfn'ECALL»,«dfn'EBREAK»,
    «dfn'UnknownInstruction»,signalException,setTrap,«write'NextFetch»,MCSR,privilege,
    holUpdate,holWordExtract]

-- Original signal1_priv1_prior1_core7; literal independent selector/frame result.
example (base : riscv_state) :
    observation «dfn'ECALL» (fixture base 1 7 true) =
      ((4,none),true,true,true,1,7) := by
  simp [observation,fixture,view,signalEnvCall,«dfn'ECALL»,«dfn'EBREAK»,
    «dfn'UnknownInstruction»,signalException,setTrap,«write'NextFetch»,MCSR,privilege,
    holUpdate,holWordExtract]

-- Original signal1_priv1_prior1_core255; literal independent selector/frame result.
example (base : riscv_state) :
    observation «dfn'ECALL» (fixture base 1 255 true) =
      ((4,none),true,true,true,1,255) := by
  simp [observation,fixture,view,signalEnvCall,«dfn'ECALL»,«dfn'EBREAK»,
    «dfn'UnknownInstruction»,signalException,setTrap,«write'NextFetch»,MCSR,privilege,
    holUpdate,holWordExtract]

-- Original signal1_priv2_prior0_core7; literal independent selector/frame result.
example (base : riscv_state) :
    observation «dfn'ECALL» (fixture base 2 7 false) =
      ((5,none),true,true,true,1,7) := by
  simp [observation,fixture,view,signalEnvCall,«dfn'ECALL»,«dfn'EBREAK»,
    «dfn'UnknownInstruction»,signalException,setTrap,«write'NextFetch»,MCSR,privilege,
    holUpdate,holWordExtract]

-- Original signal1_priv2_prior0_core255; literal independent selector/frame result.
example (base : riscv_state) :
    observation «dfn'ECALL» (fixture base 2 255 false) =
      ((5,none),true,true,true,1,255) := by
  simp [observation,fixture,view,signalEnvCall,«dfn'ECALL»,«dfn'EBREAK»,
    «dfn'UnknownInstruction»,signalException,setTrap,«write'NextFetch»,MCSR,privilege,
    holUpdate,holWordExtract]

-- Original signal1_priv2_prior1_core7; literal independent selector/frame result.
example (base : riscv_state) :
    observation «dfn'ECALL» (fixture base 2 7 true) =
      ((5,none),true,true,true,1,7) := by
  simp [observation,fixture,view,signalEnvCall,«dfn'ECALL»,«dfn'EBREAK»,
    «dfn'UnknownInstruction»,signalException,setTrap,«write'NextFetch»,MCSR,privilege,
    holUpdate,holWordExtract]

-- Original signal1_priv2_prior1_core255; literal independent selector/frame result.
example (base : riscv_state) :
    observation «dfn'ECALL» (fixture base 2 255 true) =
      ((5,none),true,true,true,1,255) := by
  simp [observation,fixture,view,signalEnvCall,«dfn'ECALL»,«dfn'EBREAK»,
    «dfn'UnknownInstruction»,signalException,setTrap,«write'NextFetch»,MCSR,privilege,
    holUpdate,holWordExtract]

-- Original signal1_priv3_prior0_core7; literal independent selector/frame result.
example (base : riscv_state) :
    observation «dfn'ECALL» (fixture base 3 7 false) =
      ((6,none),true,true,true,1,7) := by
  simp [observation,fixture,view,signalEnvCall,«dfn'ECALL»,«dfn'EBREAK»,
    «dfn'UnknownInstruction»,signalException,setTrap,«write'NextFetch»,MCSR,privilege,
    holUpdate,holWordExtract]

-- Original signal1_priv3_prior0_core255; literal independent selector/frame result.
example (base : riscv_state) :
    observation «dfn'ECALL» (fixture base 3 255 false) =
      ((6,none),true,true,true,1,255) := by
  simp [observation,fixture,view,signalEnvCall,«dfn'ECALL»,«dfn'EBREAK»,
    «dfn'UnknownInstruction»,signalException,setTrap,«write'NextFetch»,MCSR,privilege,
    holUpdate,holWordExtract]

-- Original signal1_priv3_prior1_core7; literal independent selector/frame result.
example (base : riscv_state) :
    observation «dfn'ECALL» (fixture base 3 7 true) =
      ((6,none),true,true,true,1,7) := by
  simp [observation,fixture,view,signalEnvCall,«dfn'ECALL»,«dfn'EBREAK»,
    «dfn'UnknownInstruction»,signalException,setTrap,«write'NextFetch»,MCSR,privilege,
    holUpdate,holWordExtract]

-- Original signal1_priv3_prior1_core255; literal independent selector/frame result.
example (base : riscv_state) :
    observation «dfn'ECALL» (fixture base 3 255 true) =
      ((6,none),true,true,true,1,255) := by
  simp [observation,fixture,view,signalEnvCall,«dfn'ECALL»,«dfn'EBREAK»,
    «dfn'UnknownInstruction»,signalException,setTrap,«write'NextFetch»,MCSR,privilege,
    holUpdate,holWordExtract]

-- Original signal2_priv0_prior0_core7; literal independent selector/frame result.
example (base : riscv_state) :
    observation «dfn'EBREAK» (fixture base 0 7 false) =
      ((2,none),true,true,true,1,7) := by
  simp [observation,fixture,view,signalEnvCall,«dfn'ECALL»,«dfn'EBREAK»,
    «dfn'UnknownInstruction»,signalException,setTrap,«write'NextFetch»,MCSR,privilege,
    holUpdate,holWordExtract]

-- Original signal2_priv0_prior0_core255; literal independent selector/frame result.
example (base : riscv_state) :
    observation «dfn'EBREAK» (fixture base 0 255 false) =
      ((2,none),true,true,true,1,255) := by
  simp [observation,fixture,view,signalEnvCall,«dfn'ECALL»,«dfn'EBREAK»,
    «dfn'UnknownInstruction»,signalException,setTrap,«write'NextFetch»,MCSR,privilege,
    holUpdate,holWordExtract]

-- Original signal2_priv0_prior1_core7; literal independent selector/frame result.
example (base : riscv_state) :
    observation «dfn'EBREAK» (fixture base 0 7 true) =
      ((2,none),true,true,true,1,7) := by
  simp [observation,fixture,view,signalEnvCall,«dfn'ECALL»,«dfn'EBREAK»,
    «dfn'UnknownInstruction»,signalException,setTrap,«write'NextFetch»,MCSR,privilege,
    holUpdate,holWordExtract]

-- Original signal2_priv0_prior1_core255; literal independent selector/frame result.
example (base : riscv_state) :
    observation «dfn'EBREAK» (fixture base 0 255 true) =
      ((2,none),true,true,true,1,255) := by
  simp [observation,fixture,view,signalEnvCall,«dfn'ECALL»,«dfn'EBREAK»,
    «dfn'UnknownInstruction»,signalException,setTrap,«write'NextFetch»,MCSR,privilege,
    holUpdate,holWordExtract]

-- Original signal2_priv1_prior0_core7; literal independent selector/frame result.
example (base : riscv_state) :
    observation «dfn'EBREAK» (fixture base 1 7 false) =
      ((2,none),true,true,true,1,7) := by
  simp [observation,fixture,view,signalEnvCall,«dfn'ECALL»,«dfn'EBREAK»,
    «dfn'UnknownInstruction»,signalException,setTrap,«write'NextFetch»,MCSR,privilege,
    holUpdate,holWordExtract]

-- Original signal2_priv1_prior0_core255; literal independent selector/frame result.
example (base : riscv_state) :
    observation «dfn'EBREAK» (fixture base 1 255 false) =
      ((2,none),true,true,true,1,255) := by
  simp [observation,fixture,view,signalEnvCall,«dfn'ECALL»,«dfn'EBREAK»,
    «dfn'UnknownInstruction»,signalException,setTrap,«write'NextFetch»,MCSR,privilege,
    holUpdate,holWordExtract]

-- Original signal2_priv1_prior1_core7; literal independent selector/frame result.
example (base : riscv_state) :
    observation «dfn'EBREAK» (fixture base 1 7 true) =
      ((2,none),true,true,true,1,7) := by
  simp [observation,fixture,view,signalEnvCall,«dfn'ECALL»,«dfn'EBREAK»,
    «dfn'UnknownInstruction»,signalException,setTrap,«write'NextFetch»,MCSR,privilege,
    holUpdate,holWordExtract]

-- Original signal2_priv1_prior1_core255; literal independent selector/frame result.
example (base : riscv_state) :
    observation «dfn'EBREAK» (fixture base 1 255 true) =
      ((2,none),true,true,true,1,255) := by
  simp [observation,fixture,view,signalEnvCall,«dfn'ECALL»,«dfn'EBREAK»,
    «dfn'UnknownInstruction»,signalException,setTrap,«write'NextFetch»,MCSR,privilege,
    holUpdate,holWordExtract]

-- Original signal2_priv2_prior0_core7; literal independent selector/frame result.
example (base : riscv_state) :
    observation «dfn'EBREAK» (fixture base 2 7 false) =
      ((2,none),true,true,true,1,7) := by
  simp [observation,fixture,view,signalEnvCall,«dfn'ECALL»,«dfn'EBREAK»,
    «dfn'UnknownInstruction»,signalException,setTrap,«write'NextFetch»,MCSR,privilege,
    holUpdate,holWordExtract]

-- Original signal2_priv2_prior0_core255; literal independent selector/frame result.
example (base : riscv_state) :
    observation «dfn'EBREAK» (fixture base 2 255 false) =
      ((2,none),true,true,true,1,255) := by
  simp [observation,fixture,view,signalEnvCall,«dfn'ECALL»,«dfn'EBREAK»,
    «dfn'UnknownInstruction»,signalException,setTrap,«write'NextFetch»,MCSR,privilege,
    holUpdate,holWordExtract]

-- Original signal2_priv2_prior1_core7; literal independent selector/frame result.
example (base : riscv_state) :
    observation «dfn'EBREAK» (fixture base 2 7 true) =
      ((2,none),true,true,true,1,7) := by
  simp [observation,fixture,view,signalEnvCall,«dfn'ECALL»,«dfn'EBREAK»,
    «dfn'UnknownInstruction»,signalException,setTrap,«write'NextFetch»,MCSR,privilege,
    holUpdate,holWordExtract]

-- Original signal2_priv2_prior1_core255; literal independent selector/frame result.
example (base : riscv_state) :
    observation «dfn'EBREAK» (fixture base 2 255 true) =
      ((2,none),true,true,true,1,255) := by
  simp [observation,fixture,view,signalEnvCall,«dfn'ECALL»,«dfn'EBREAK»,
    «dfn'UnknownInstruction»,signalException,setTrap,«write'NextFetch»,MCSR,privilege,
    holUpdate,holWordExtract]

-- Original signal2_priv3_prior0_core7; literal independent selector/frame result.
example (base : riscv_state) :
    observation «dfn'EBREAK» (fixture base 3 7 false) =
      ((2,none),true,true,true,1,7) := by
  simp [observation,fixture,view,signalEnvCall,«dfn'ECALL»,«dfn'EBREAK»,
    «dfn'UnknownInstruction»,signalException,setTrap,«write'NextFetch»,MCSR,privilege,
    holUpdate,holWordExtract]

-- Original signal2_priv3_prior0_core255; literal independent selector/frame result.
example (base : riscv_state) :
    observation «dfn'EBREAK» (fixture base 3 255 false) =
      ((2,none),true,true,true,1,255) := by
  simp [observation,fixture,view,signalEnvCall,«dfn'ECALL»,«dfn'EBREAK»,
    «dfn'UnknownInstruction»,signalException,setTrap,«write'NextFetch»,MCSR,privilege,
    holUpdate,holWordExtract]

-- Original signal2_priv3_prior1_core7; literal independent selector/frame result.
example (base : riscv_state) :
    observation «dfn'EBREAK» (fixture base 3 7 true) =
      ((2,none),true,true,true,1,7) := by
  simp [observation,fixture,view,signalEnvCall,«dfn'ECALL»,«dfn'EBREAK»,
    «dfn'UnknownInstruction»,signalException,setTrap,«write'NextFetch»,MCSR,privilege,
    holUpdate,holWordExtract]

-- Original signal2_priv3_prior1_core255; literal independent selector/frame result.
example (base : riscv_state) :
    observation «dfn'EBREAK» (fixture base 3 255 true) =
      ((2,none),true,true,true,1,255) := by
  simp [observation,fixture,view,signalEnvCall,«dfn'ECALL»,«dfn'EBREAK»,
    «dfn'UnknownInstruction»,signalException,setTrap,«write'NextFetch»,MCSR,privilege,
    holUpdate,holWordExtract]

-- Original signal4_priv0_prior0_core7; literal independent selector/frame result.
example (base : riscv_state) :
    observation «dfn'UnknownInstruction» (fixture base 0 7 false) =
      ((1,none),true,true,true,1,7) := by
  simp [observation,fixture,view,signalEnvCall,«dfn'ECALL»,«dfn'EBREAK»,
    «dfn'UnknownInstruction»,signalException,setTrap,«write'NextFetch»,MCSR,privilege,
    holUpdate,holWordExtract]

-- Original signal4_priv0_prior0_core255; literal independent selector/frame result.
example (base : riscv_state) :
    observation «dfn'UnknownInstruction» (fixture base 0 255 false) =
      ((1,none),true,true,true,1,255) := by
  simp [observation,fixture,view,signalEnvCall,«dfn'ECALL»,«dfn'EBREAK»,
    «dfn'UnknownInstruction»,signalException,setTrap,«write'NextFetch»,MCSR,privilege,
    holUpdate,holWordExtract]

-- Original signal4_priv0_prior1_core7; literal independent selector/frame result.
example (base : riscv_state) :
    observation «dfn'UnknownInstruction» (fixture base 0 7 true) =
      ((1,none),true,true,true,1,7) := by
  simp [observation,fixture,view,signalEnvCall,«dfn'ECALL»,«dfn'EBREAK»,
    «dfn'UnknownInstruction»,signalException,setTrap,«write'NextFetch»,MCSR,privilege,
    holUpdate,holWordExtract]

-- Original signal4_priv0_prior1_core255; literal independent selector/frame result.
example (base : riscv_state) :
    observation «dfn'UnknownInstruction» (fixture base 0 255 true) =
      ((1,none),true,true,true,1,255) := by
  simp [observation,fixture,view,signalEnvCall,«dfn'ECALL»,«dfn'EBREAK»,
    «dfn'UnknownInstruction»,signalException,setTrap,«write'NextFetch»,MCSR,privilege,
    holUpdate,holWordExtract]

-- Original signal4_priv1_prior0_core7; literal independent selector/frame result.
example (base : riscv_state) :
    observation «dfn'UnknownInstruction» (fixture base 1 7 false) =
      ((1,none),true,true,true,1,7) := by
  simp [observation,fixture,view,signalEnvCall,«dfn'ECALL»,«dfn'EBREAK»,
    «dfn'UnknownInstruction»,signalException,setTrap,«write'NextFetch»,MCSR,privilege,
    holUpdate,holWordExtract]

-- Original signal4_priv1_prior0_core255; literal independent selector/frame result.
example (base : riscv_state) :
    observation «dfn'UnknownInstruction» (fixture base 1 255 false) =
      ((1,none),true,true,true,1,255) := by
  simp [observation,fixture,view,signalEnvCall,«dfn'ECALL»,«dfn'EBREAK»,
    «dfn'UnknownInstruction»,signalException,setTrap,«write'NextFetch»,MCSR,privilege,
    holUpdate,holWordExtract]

-- Original signal4_priv1_prior1_core7; literal independent selector/frame result.
example (base : riscv_state) :
    observation «dfn'UnknownInstruction» (fixture base 1 7 true) =
      ((1,none),true,true,true,1,7) := by
  simp [observation,fixture,view,signalEnvCall,«dfn'ECALL»,«dfn'EBREAK»,
    «dfn'UnknownInstruction»,signalException,setTrap,«write'NextFetch»,MCSR,privilege,
    holUpdate,holWordExtract]

-- Original signal4_priv1_prior1_core255; literal independent selector/frame result.
example (base : riscv_state) :
    observation «dfn'UnknownInstruction» (fixture base 1 255 true) =
      ((1,none),true,true,true,1,255) := by
  simp [observation,fixture,view,signalEnvCall,«dfn'ECALL»,«dfn'EBREAK»,
    «dfn'UnknownInstruction»,signalException,setTrap,«write'NextFetch»,MCSR,privilege,
    holUpdate,holWordExtract]

-- Original signal4_priv2_prior0_core7; literal independent selector/frame result.
example (base : riscv_state) :
    observation «dfn'UnknownInstruction» (fixture base 2 7 false) =
      ((1,none),true,true,true,1,7) := by
  simp [observation,fixture,view,signalEnvCall,«dfn'ECALL»,«dfn'EBREAK»,
    «dfn'UnknownInstruction»,signalException,setTrap,«write'NextFetch»,MCSR,privilege,
    holUpdate,holWordExtract]

-- Original signal4_priv2_prior0_core255; literal independent selector/frame result.
example (base : riscv_state) :
    observation «dfn'UnknownInstruction» (fixture base 2 255 false) =
      ((1,none),true,true,true,1,255) := by
  simp [observation,fixture,view,signalEnvCall,«dfn'ECALL»,«dfn'EBREAK»,
    «dfn'UnknownInstruction»,signalException,setTrap,«write'NextFetch»,MCSR,privilege,
    holUpdate,holWordExtract]

-- Original signal4_priv2_prior1_core7; literal independent selector/frame result.
example (base : riscv_state) :
    observation «dfn'UnknownInstruction» (fixture base 2 7 true) =
      ((1,none),true,true,true,1,7) := by
  simp [observation,fixture,view,signalEnvCall,«dfn'ECALL»,«dfn'EBREAK»,
    «dfn'UnknownInstruction»,signalException,setTrap,«write'NextFetch»,MCSR,privilege,
    holUpdate,holWordExtract]

-- Original signal4_priv2_prior1_core255; literal independent selector/frame result.
example (base : riscv_state) :
    observation «dfn'UnknownInstruction» (fixture base 2 255 true) =
      ((1,none),true,true,true,1,255) := by
  simp [observation,fixture,view,signalEnvCall,«dfn'ECALL»,«dfn'EBREAK»,
    «dfn'UnknownInstruction»,signalException,setTrap,«write'NextFetch»,MCSR,privilege,
    holUpdate,holWordExtract]

-- Original signal4_priv3_prior0_core7; literal independent selector/frame result.
example (base : riscv_state) :
    observation «dfn'UnknownInstruction» (fixture base 3 7 false) =
      ((1,none),true,true,true,1,7) := by
  simp [observation,fixture,view,signalEnvCall,«dfn'ECALL»,«dfn'EBREAK»,
    «dfn'UnknownInstruction»,signalException,setTrap,«write'NextFetch»,MCSR,privilege,
    holUpdate,holWordExtract]

-- Original signal4_priv3_prior0_core255; literal independent selector/frame result.
example (base : riscv_state) :
    observation «dfn'UnknownInstruction» (fixture base 3 255 false) =
      ((1,none),true,true,true,1,255) := by
  simp [observation,fixture,view,signalEnvCall,«dfn'ECALL»,«dfn'EBREAK»,
    «dfn'UnknownInstruction»,signalException,setTrap,«write'NextFetch»,MCSR,privilege,
    holUpdate,holWordExtract]

-- Original signal4_priv3_prior1_core7; literal independent selector/frame result.
example (base : riscv_state) :
    observation «dfn'UnknownInstruction» (fixture base 3 7 true) =
      ((1,none),true,true,true,1,7) := by
  simp [observation,fixture,view,signalEnvCall,«dfn'ECALL»,«dfn'EBREAK»,
    «dfn'UnknownInstruction»,signalException,setTrap,«write'NextFetch»,MCSR,privilege,
    holUpdate,holWordExtract]

-- Original signal4_priv3_prior1_core255; literal independent selector/frame result.
example (base : riscv_state) :
    observation «dfn'UnknownInstruction» (fixture base 3 255 true) =
      ((1,none),true,true,true,1,255) := by
  simp [observation,fixture,view,signalEnvCall,«dfn'ECALL»,«dfn'EBREAK»,
    «dfn'UnknownInstruction»,signalException,setTrap,«write'NextFetch»,MCSR,privilege,
    holUpdate,holWordExtract]

end Flapjack.Test.L3SystemSignalsParity
