import Flapjack.HolRef
import Flapjack.Basis.Pure.MlString

/-!
# L3 ARMv8 model: the machine-state carriers

Counterpart of the `Record`/`Construct` declarations of the L3-generated
`HOL/examples/l3-machine-code/arm8/model/arm8Script.sml` that make up the
`arm8_state` carrier and its nested control-register records: `ProcState`
(lines 8-10), `TCR_EL1` (12-13), `TCR_EL2_EL3` (15), `SCTLRType` (17-20),
`BranchType` (22-27), `exception` (362-365) and `arm8_state` (367-375), in
source order.  The renderings follow the RISC-V L3 port
(`Flapjack/RiscV/L3/Types.lean`): L3 `F n`/`FTy n` is `BitVec n`, `bTy` is
`Bool`, `sTy` (HOL `string`, a `char list`) is `List HolChar`, `PTy` is `×`,
`OTy` is `Option`, `LTy` is `List`, and `ATy (a, b)` (an L3 map, the HOL
function type) is `a → b`.  Names are HOL's, with `«»` quoting where Lean
requires it.

The rest of the model's types (`AccType`, `ShiftType`, `ExtendType`,
`LogicalOp`, `MemOp`, `MemBarrierOp`, `MoveWideOp`, `RevOp`, `SystemHintOp`,
`PSTATEField`, `System`, `Debug`, `LoadStore`, `Branch`, `CRCExt`, `Data`,
`instruction`, `MachineCode`) are not declared here: the emitted-instruction
carrier and its instruction-level companions are tracked in issue #1229, and
`ShiftType`/`MoveWideOp` are already ported in
`Flapjack/Compiler/Encoders/Arm8/Encode.lean`.

`scripts/tests/test_hol_l3_types_to_lean.py` checks that this block is exactly
the `scripts/l3_types_to_lean.py` rendering of those seven declarations.  The
generator is a mechanical transcription aid; it does not establish
HOL-to-Lean equivalence, and the reviewed manifest rows record the source
comparison.
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
