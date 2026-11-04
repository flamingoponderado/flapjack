import Flapjack.HolRef
import Flapjack.Basis.Pure.MlString
import Flapjack.Compiler.Encoders.Arm8.Encode

/-!
# L3 ARMv8 model: datatypes and the machine-state carrier

Counterpart of the `Record`/`Construct` declarations of the L3-generated
`HOL/examples/l3-machine-code/arm8/model/arm8Script.sml`, in source order:
`ProcState` (8-10), `TCR_EL1` (12-13), `TCR_EL2_EL3` (15), `SCTLRType` (17-20),
`BranchType` (22-27), `AccType` (29-35), `ExtendType` (42-46), `LogicalOp`
(48-50), `MemOp` (52-53), `MemBarrierOp` (55-58), `RevOp` (64-67),
`SystemHintOp` (69-73), `PSTATEField` (75-78), `System` (80-88), `Debug`
(90-93), `LoadStore` (95-224), `Branch` (226-234), `CRCExt` (236-241), `Data`
(243-349), `instruction` (351-358), `MachineCode` (360), `exception` (362-365)
and `arm8_state` (367-375).  `ShiftType` (37-40) and `MoveWideOp` (60-62) are
already ported, with Lean constructor names, in
`Flapjack/Compiler/Encoders/Arm8/Encode.lean`.

The renderings follow the RISC-V L3 port (`Flapjack/RiscV/L3/Types.lean`): L3
`F n`/`FTy n` is `BitVec n`, `bTy` is `Bool`, `nTy` is `Nat`, `sTy` (HOL
`string`, a `char list`) is `List HolChar`, `PTy` is `×`, `OTy` is `Option`,
`LTy` is `List`, and `ATy (a, b)` (an L3 map, the HOL function type) is `a → b`.
Names are HOL's, with `«»` quoting where Lean requires it.

`scripts/tests/test_hol_l3_types_to_lean.py` checks that this block is exactly
the `scripts/l3_types_to_lean.py` rendering of those declarations.  The
generator is a mechanical transcription aid; it does not establish HOL-to-Lean
equivalence, and the reviewed manifest rows record the source comparison.
-/

namespace Flapjack.Compiler.Encoders.Arm8.L3

open Flapjack.Basis.Pure.MlString

/-- HOL L3 record `ProcState` (`arm8Script.sml:8`). -/
@[hol "HOL/examples/l3-machine-code/arm8/model/arm8Script.sml" "ProcState"]
structure ProcState where
  C : Bool
  EL : (BitVec 2)
  N : Bool
  SPS : Bool
  V : Bool
  Z : Bool
  deriving DecidableEq, Repr, Inhabited

/-- HOL L3 record `TCR_EL1` (`arm8Script.sml:12`). -/
@[hol "HOL/examples/l3-machine-code/arm8/model/arm8Script.sml" "TCR_EL1"]
structure TCR_EL1 where
  TBI0 : Bool
  TBI1 : Bool
  «tcr_el1'rst» : (BitVec 62)
  deriving DecidableEq, Repr, Inhabited

/-- HOL L3 record `TCR_EL2_EL3` (`arm8Script.sml:15`). -/
@[hol "HOL/examples/l3-machine-code/arm8/model/arm8Script.sml" "TCR_EL2_EL3"]
structure TCR_EL2_EL3 where
  TBI : Bool
  «tcr_el2_el3'rst» : (BitVec 31)
  deriving DecidableEq, Repr, Inhabited

/-- HOL L3 record `SCTLRType` (`arm8Script.sml:17`). -/
@[hol "HOL/examples/l3-machine-code/arm8/model/arm8Script.sml" "SCTLRType"]
structure SCTLRType where
  A : Bool
  E0E : Bool
  EE : Bool
  SA : Bool
  SA0 : Bool
  «sctlrtype'rst» : (BitVec 27)
  deriving DecidableEq, Repr, Inhabited

/-- HOL L3 datatype `BranchType` (`arm8Script.sml:22`). -/
@[hol "HOL/examples/l3-machine-code/arm8/model/arm8Script.sml" "BranchType"]
inductive BranchType where
  | BranchType_CALL
  | BranchType_ERET
  | BranchType_DBGEXIT
  | BranchType_RET
  | BranchType_JMP
  | BranchType_EXCEPTION
  | BranchType_UNKNOWN
  deriving DecidableEq, Repr, Inhabited

/-- HOL L3 datatype `AccType` (`arm8Script.sml:29`). -/
@[hol "HOL/examples/l3-machine-code/arm8/model/arm8Script.sml" "AccType"]
inductive AccType where
  | AccType_NORMAL
  | AccType_VEC
  | AccType_STREAM
  | AccType_VECSTREAM
  | AccType_ATOMIC
  | AccType_ORDERED
  | AccType_UNPRIV
  | AccType_IFETCH
  | AccType_PTW
  | AccType_DC
  | AccType_IC
  | AccType_AT
  deriving DecidableEq, Repr, Inhabited

/-- HOL L3 datatype `ExtendType` (`arm8Script.sml:42`). -/
@[hol "HOL/examples/l3-machine-code/arm8/model/arm8Script.sml" "ExtendType"]
inductive ExtendType where
  | ExtendType_UXTB
  | ExtendType_UXTH
  | ExtendType_UXTW
  | ExtendType_UXTX
  | ExtendType_SXTB
  | ExtendType_SXTH
  | ExtendType_SXTW
  | ExtendType_SXTX
  deriving DecidableEq, Repr, Inhabited

/-- HOL L3 datatype `LogicalOp` (`arm8Script.sml:48`). -/
@[hol "HOL/examples/l3-machine-code/arm8/model/arm8Script.sml" "LogicalOp"]
inductive LogicalOp where
  | LogicalOp_AND
  | LogicalOp_ORR
  | LogicalOp_EOR
  deriving DecidableEq, Repr, Inhabited

/-- HOL L3 datatype `MemOp` (`arm8Script.sml:52`). -/
@[hol "HOL/examples/l3-machine-code/arm8/model/arm8Script.sml" "MemOp"]
inductive MemOp where
  | MemOp_LOAD
  | MemOp_STORE
  | MemOp_PREFETCH
  deriving DecidableEq, Repr, Inhabited

/-- HOL L3 datatype `MemBarrierOp` (`arm8Script.sml:55`). -/
@[hol "HOL/examples/l3-machine-code/arm8/model/arm8Script.sml" "MemBarrierOp"]
inductive MemBarrierOp where
  | MemBarrierOp_DSB
  | MemBarrierOp_DMB
  | MemBarrierOp_ISB
  deriving DecidableEq, Repr, Inhabited

/-- HOL L3 datatype `RevOp` (`arm8Script.sml:64`). -/
@[hol "HOL/examples/l3-machine-code/arm8/model/arm8Script.sml" "RevOp"]
inductive RevOp where
  | RevOp_RBIT
  | RevOp_REV16
  | RevOp_REV32
  | RevOp_REV64
  deriving DecidableEq, Repr, Inhabited

/-- HOL L3 datatype `SystemHintOp` (`arm8Script.sml:69`). -/
@[hol "HOL/examples/l3-machine-code/arm8/model/arm8Script.sml" "SystemHintOp"]
inductive SystemHintOp where
  | SystemHintOp_NOP
  | SystemHintOp_YIELD
  | SystemHintOp_WFE
  | SystemHintOp_WFI
  | SystemHintOp_SEV
  | SystemHintOp_SEVL
  deriving DecidableEq, Repr, Inhabited

/-- HOL L3 datatype `PSTATEField` (`arm8Script.sml:75`). -/
@[hol "HOL/examples/l3-machine-code/arm8/model/arm8Script.sml" "PSTATEField"]
inductive PSTATEField where
  | PSTATEField_DAIFSet
  | PSTATEField_DAIFClr
  | PSTATEField_SP
  deriving DecidableEq, Repr, Inhabited

/-- HOL L3 datatype `System` (`arm8Script.sml:80`). -/
@[hol "HOL/examples/l3-machine-code/arm8/model/arm8Script.sml" "System"]
inductive System where
  | ExceptionReturn
  | HypervisorCall (a0 : (BitVec 16))
  | MoveImmediateProcState (a0 : (PSTATEField × (BitVec 4)))
  | MoveSystemRegister (a0 : (Bool × ((BitVec 3) × ((BitVec 3) × ((BitVec 3) × ((BitVec 4) × ((BitVec 4) × (BitVec 5))))))))
  | SecureMonitorCall (a0 : (BitVec 16))
  | SupervisorCall (a0 : (BitVec 16))
  | SystemInstruction (a0 : ((BitVec 3) × ((BitVec 3) × ((BitVec 4) × ((BitVec 4) × (Bool × (BitVec 5)))))))
  deriving DecidableEq, Repr, Inhabited

/-- HOL L3 datatype `Debug` (`arm8Script.sml:90`). -/
@[hol "HOL/examples/l3-machine-code/arm8/model/arm8Script.sml" "Debug"]
inductive Debug where
  | Breakpoint (a0 : (BitVec 16))
  | DebugRestore
  | DebugSwitch (a0 : (BitVec 2))
  | Halt (a0 : (BitVec 16))
  deriving DecidableEq, Repr, Inhabited

/-- HOL L3 datatype `LoadStore` (`arm8Script.sml:95`). -/
@[hol "HOL/examples/l3-machine-code/arm8/model/arm8Script.sml" "LoadStore"]
inductive LoadStore where
  | «LoadLiteral@32» (a0 : ((BitVec 32) × (MemOp × (Bool × ((BitVec 64) × (BitVec 5))))))
  | «LoadLiteral@64» (a0 : ((BitVec 64) × (MemOp × (Bool × ((BitVec 64) × (BitVec 5))))))
  | «LoadStoreAcquire@16» (a0 : ((BitVec 16) × (MemOp × (AccType × (Bool × (Bool × (Bool × ((BitVec 5) × ((BitVec 5) × (BitVec 5))))))))))
  | «LoadStoreAcquire@32» (a0 : ((BitVec 32) × (MemOp × (AccType × (Bool × (Bool × (Bool × ((BitVec 5) × ((BitVec 5) × (BitVec 5))))))))))
  | «LoadStoreAcquire@64» (a0 : ((BitVec 64) × (MemOp × (AccType × (Bool × (Bool × (Bool × ((BitVec 5) × ((BitVec 5) × (BitVec 5))))))))))
  | «LoadStoreAcquire@8» (a0 : ((BitVec 8) × (MemOp × (AccType × (Bool × (Bool × (Bool × ((BitVec 5) × ((BitVec 5) × (BitVec 5))))))))))
  | «LoadStoreAcquirePair@128» (a0 : ((BitVec 128) × (MemOp × (AccType × (Bool × (Bool × ((BitVec 5) × ((BitVec 5) × ((BitVec 5) × (BitVec 5))))))))))
  | «LoadStoreAcquirePair@64» (a0 : ((BitVec 64) × (MemOp × (AccType × (Bool × (Bool × ((BitVec 5) × ((BitVec 5) × ((BitVec 5) × (BitVec 5))))))))))
  | «LoadStoreImmediate@16» (a0 : ((BitVec 16) × (Bool × (MemOp × (AccType × (Bool × (Bool × (Bool × (Bool × (Bool × (Bool × ((BitVec 64) × ((BitVec 5) × (BitVec 5))))))))))))))
  | «LoadStoreImmediate@32» (a0 : ((BitVec 32) × (Bool × (MemOp × (AccType × (Bool × (Bool × (Bool × (Bool × (Bool × (Bool × ((BitVec 64) × ((BitVec 5) × (BitVec 5))))))))))))))
  | «LoadStoreImmediate@64» (a0 : ((BitVec 64) × (Bool × (MemOp × (AccType × (Bool × (Bool × (Bool × (Bool × (Bool × (Bool × ((BitVec 64) × ((BitVec 5) × (BitVec 5))))))))))))))
  | «LoadStoreImmediate@8» (a0 : ((BitVec 8) × (Bool × (MemOp × (AccType × (Bool × (Bool × (Bool × (Bool × (Bool × (Bool × ((BitVec 64) × ((BitVec 5) × (BitVec 5))))))))))))))
  | «LoadStorePair@32» (a0 : ((BitVec 32) × (MemOp × (AccType × (Bool × (Bool × (Bool × (Bool × (Bool × ((BitVec 64) × ((BitVec 5) × ((BitVec 5) × (BitVec 5)))))))))))))
  | «LoadStorePair@64» (a0 : ((BitVec 64) × (MemOp × (AccType × (Bool × (Bool × (Bool × (Bool × (Bool × ((BitVec 64) × ((BitVec 5) × ((BitVec 5) × (BitVec 5)))))))))))))
  | «LoadStoreRegister@16» (a0 : ((BitVec 16) × (Bool × (MemOp × (Bool × ((BitVec 5) × (ExtendType × (Nat × ((BitVec 5) × (BitVec 5))))))))))
  | «LoadStoreRegister@32» (a0 : ((BitVec 32) × (Bool × (MemOp × (Bool × ((BitVec 5) × (ExtendType × (Nat × ((BitVec 5) × (BitVec 5))))))))))
  | «LoadStoreRegister@64» (a0 : ((BitVec 64) × (Bool × (MemOp × (Bool × ((BitVec 5) × (ExtendType × (Nat × ((BitVec 5) × (BitVec 5))))))))))
  | «LoadStoreRegister@8» (a0 : ((BitVec 8) × (Bool × (MemOp × (Bool × ((BitVec 5) × (ExtendType × (Nat × ((BitVec 5) × (BitVec 5))))))))))
  deriving BEq, Repr, Inhabited

/-- HOL L3 datatype `Branch` (`arm8Script.sml:226`). -/
@[hol "HOL/examples/l3-machine-code/arm8/model/arm8Script.sml" "Branch"]
inductive Branch where
  | BranchConditional (a0 : ((BitVec 64) × (BitVec 4)))
  | BranchImmediate (a0 : ((BitVec 64) × BranchType))
  | BranchRegister (a0 : ((BitVec 5) × BranchType))
  | «CompareAndBranch@32» (a0 : ((BitVec 32) × (Bool × ((BitVec 64) × (BitVec 5)))))
  | «CompareAndBranch@64» (a0 : ((BitVec 64) × (Bool × ((BitVec 64) × (BitVec 5)))))
  | «TestBitAndBranch@32» (a0 : ((BitVec 32) × ((BitVec 6) × (Bool × ((BitVec 64) × (BitVec 5))))))
  | «TestBitAndBranch@64» (a0 : ((BitVec 64) × ((BitVec 6) × (Bool × ((BitVec 64) × (BitVec 5))))))
  deriving DecidableEq, Repr, Inhabited

/-- HOL L3 datatype `CRCExt` (`arm8Script.sml:236`). -/
@[hol "HOL/examples/l3-machine-code/arm8/model/arm8Script.sml" "CRCExt"]
inductive CRCExt where
  | «CRC@16» (a0 : ((BitVec 16) × (Bool × ((BitVec 5) × ((BitVec 5) × (BitVec 5))))))
  | «CRC@32» (a0 : ((BitVec 32) × (Bool × ((BitVec 5) × ((BitVec 5) × (BitVec 5))))))
  | «CRC@64» (a0 : ((BitVec 64) × (Bool × ((BitVec 5) × ((BitVec 5) × (BitVec 5))))))
  | «CRC@8» (a0 : ((BitVec 8) × (Bool × ((BitVec 5) × ((BitVec 5) × (BitVec 5))))))
  deriving DecidableEq, Repr, Inhabited

/-- HOL L3 datatype `Data` (`arm8Script.sml:243`). -/
@[hol "HOL/examples/l3-machine-code/arm8/model/arm8Script.sml" "Data"]
inductive Data where
  | «AddSubCarry@32» (a0 : ((BitVec 32) × (Bool × (Bool × ((BitVec 5) × ((BitVec 5) × (BitVec 5)))))))
  | «AddSubCarry@64» (a0 : ((BitVec 64) × (Bool × (Bool × ((BitVec 5) × ((BitVec 5) × (BitVec 5)))))))
  | «AddSubExtendRegister@32» (a0 : ((BitVec 32) × (Bool × (Bool × ((BitVec 5) × (ExtendType × ((BitVec 3) × ((BitVec 5) × (BitVec 5)))))))))
  | «AddSubExtendRegister@64» (a0 : ((BitVec 64) × (Bool × (Bool × ((BitVec 5) × (ExtendType × ((BitVec 3) × ((BitVec 5) × (BitVec 5)))))))))
  | «AddSubImmediate@32» (a0 : ((BitVec 32) × (Bool × (Bool × ((BitVec 32) × ((BitVec 5) × (BitVec 5)))))))
  | «AddSubImmediate@64» (a0 : ((BitVec 64) × (Bool × (Bool × ((BitVec 64) × ((BitVec 5) × (BitVec 5)))))))
  | «AddSubShiftedRegister@32» (a0 : ((BitVec 32) × (Bool × (Bool × (ShiftType × ((BitVec 5) × ((BitVec 6) × ((BitVec 5) × (BitVec 5)))))))))
  | «AddSubShiftedRegister@64» (a0 : ((BitVec 64) × (Bool × (Bool × (ShiftType × ((BitVec 5) × ((BitVec 6) × ((BitVec 5) × (BitVec 5)))))))))
  | «BitfieldMove@32» (a0 : ((BitVec 32) × (Bool × (Bool × ((BitVec 32) × ((BitVec 32) × (Nat × (Nat × ((BitVec 5) × (BitVec 5))))))))))
  | «BitfieldMove@64» (a0 : ((BitVec 64) × (Bool × (Bool × ((BitVec 64) × ((BitVec 64) × (Nat × (Nat × ((BitVec 5) × (BitVec 5))))))))))
  | «ConditionalCompareImmediate@32» (a0 : ((BitVec 32) × (Bool × ((BitVec 32) × ((BitVec 4) × ((Bool × (Bool × (Bool × Bool))) × (BitVec 5)))))))
  | «ConditionalCompareImmediate@64» (a0 : ((BitVec 64) × (Bool × ((BitVec 64) × ((BitVec 4) × ((Bool × (Bool × (Bool × Bool))) × (BitVec 5)))))))
  | «ConditionalCompareRegister@32» (a0 : ((BitVec 32) × (Bool × ((BitVec 4) × ((Bool × (Bool × (Bool × Bool))) × ((BitVec 5) × (BitVec 5)))))))
  | «ConditionalCompareRegister@64» (a0 : ((BitVec 64) × (Bool × ((BitVec 4) × ((Bool × (Bool × (Bool × Bool))) × ((BitVec 5) × (BitVec 5)))))))
  | «ConditionalSelect@32» (a0 : ((BitVec 32) × (Bool × (Bool × ((BitVec 4) × ((BitVec 5) × ((BitVec 5) × (BitVec 5))))))))
  | «ConditionalSelect@64» (a0 : ((BitVec 64) × (Bool × (Bool × ((BitVec 4) × ((BitVec 5) × ((BitVec 5) × (BitVec 5))))))))
  | «CountLeading@32» (a0 : ((BitVec 32) × (Bool × ((BitVec 5) × (BitVec 5)))))
  | «CountLeading@64» (a0 : ((BitVec 64) × (Bool × ((BitVec 5) × (BitVec 5)))))
  | «Division@32» (a0 : ((BitVec 32) × (Bool × ((BitVec 5) × ((BitVec 5) × (BitVec 5))))))
  | «Division@64» (a0 : ((BitVec 64) × (Bool × ((BitVec 5) × ((BitVec 5) × (BitVec 5))))))
  | «ExtractRegister@32» (a0 : ((BitVec 32) × ((BitVec 6) × ((BitVec 5) × ((BitVec 5) × (BitVec 5))))))
  | «ExtractRegister@64» (a0 : ((BitVec 64) × ((BitVec 6) × ((BitVec 5) × ((BitVec 5) × (BitVec 5))))))
  | «LogicalImmediate@32» (a0 : ((BitVec 32) × (LogicalOp × (Bool × ((BitVec 32) × ((BitVec 5) × (BitVec 5)))))))
  | «LogicalImmediate@64» (a0 : ((BitVec 64) × (LogicalOp × (Bool × ((BitVec 64) × ((BitVec 5) × (BitVec 5)))))))
  | «LogicalShiftedRegister@32» (a0 : ((BitVec 32) × (LogicalOp × (Bool × (Bool × (ShiftType × (Nat × ((BitVec 5) × ((BitVec 5) × (BitVec 5))))))))))
  | «LogicalShiftedRegister@64» (a0 : ((BitVec 64) × (LogicalOp × (Bool × (Bool × (ShiftType × (Nat × ((BitVec 5) × ((BitVec 5) × (BitVec 5))))))))))
  | «MoveWide@32» (a0 : ((BitVec 32) × (MoveWideOp × ((BitVec 2) × ((BitVec 16) × (BitVec 5))))))
  | «MoveWide@64» (a0 : ((BitVec 64) × (MoveWideOp × ((BitVec 2) × ((BitVec 16) × (BitVec 5))))))
  | «MultiplyAddSub@32» (a0 : ((BitVec 32) × (Bool × ((BitVec 5) × ((BitVec 5) × ((BitVec 5) × (BitVec 5)))))))
  | «MultiplyAddSub@64» (a0 : ((BitVec 64) × (Bool × ((BitVec 5) × ((BitVec 5) × ((BitVec 5) × (BitVec 5)))))))
  | MultiplyAddSubLong (a0 : (Bool × (Bool × ((BitVec 5) × ((BitVec 5) × ((BitVec 5) × (BitVec 5)))))))
  | MultiplyHigh (a0 : (Bool × ((BitVec 5) × ((BitVec 5) × (BitVec 5)))))
  | «Reverse@32» (a0 : ((BitVec 32) × (RevOp × ((BitVec 5) × (BitVec 5)))))
  | «Reverse@64» (a0 : ((BitVec 64) × (RevOp × ((BitVec 5) × (BitVec 5)))))
  | «Shift@32» (a0 : ((BitVec 32) × (ShiftType × ((BitVec 5) × ((BitVec 5) × (BitVec 5))))))
  | «Shift@64» (a0 : ((BitVec 64) × (ShiftType × ((BitVec 5) × ((BitVec 5) × (BitVec 5))))))
  deriving BEq, Repr, Inhabited

/-- HOL L3 datatype `instruction` (`arm8Script.sml:351`). -/
@[hol "HOL/examples/l3-machine-code/arm8/model/arm8Script.sml" "instruction"]
inductive instruction where
  | Address (a0 : (Bool × ((BitVec 64) × (BitVec 5))))
  | Branch (a0 : Branch)
  | CRCExt (a0 : CRCExt)
  | ClearExclusive (a0 : (BitVec 4))
  | Data (a0 : Data)
  | Debug (a0 : Debug)
  | Hint (a0 : SystemHintOp)
  | LoadStore (a0 : LoadStore)
  | MemoryBarrier (a0 : (MemBarrierOp × (BitVec 4)))
  | Reserved
  | System (a0 : System)
  | Unallocated
  deriving BEq, Repr, Inhabited

/-- HOL L3 datatype `MachineCode` (`arm8Script.sml:360`). -/
@[hol "HOL/examples/l3-machine-code/arm8/model/arm8Script.sml" "MachineCode"]
inductive MachineCode where
  | ARM8 (a0 : (BitVec 32))
  | BadCode (a0 : List HolChar)
  deriving DecidableEq, Repr, Inhabited

/-- HOL L3 datatype `exception` (`arm8Script.sml:362`). -/
@[hol "HOL/examples/l3-machine-code/arm8/model/arm8Script.sml" "exception"]
inductive exception where
  | ALIGNMENT_FAULT
  | ASSERT (a0 : List HolChar)
  | NoException
  | UNDEFINED_FAULT (a0 : List HolChar)
  deriving DecidableEq, Repr, Inhabited

/-- HOL L3 record `arm8_state` (`arm8Script.sml:367`). -/
@[hol "HOL/examples/l3-machine-code/arm8/model/arm8Script.sml" "arm8_state"]
structure arm8_state where
  MEM : ((BitVec 64) → (BitVec 8))
  PC : (BitVec 64)
  PSTATE : ProcState
  REG : ((BitVec 5) → (BitVec 64))
  SCTLR_EL1 : SCTLRType
  SCTLR_EL2 : SCTLRType
  SCTLR_EL3 : SCTLRType
  SP_EL0 : (BitVec 64)
  SP_EL1 : (BitVec 64)
  SP_EL2 : (BitVec 64)
  SP_EL3 : (BitVec 64)
  TCR_EL1 : TCR_EL1
  TCR_EL2 : TCR_EL2_EL3
  TCR_EL3 : TCR_EL2_EL3
  branch_hint : (Option BranchType)
  exception : exception
  deriving Inhabited
end Flapjack.Compiler.Encoders.Arm8.L3
