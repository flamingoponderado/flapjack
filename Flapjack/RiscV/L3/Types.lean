import Flapjack.HolRef
import Flapjack.Basis.Pure.MlString

/-!
# L3 RISC-V model: datatypes and the machine state

Counterpart of the type declarations of the L3-generated
`HOL/examples/l3-machine-code/riscv/model/riscvScript.sml` (lines 6-362): every
`Construct`/`Record` declaration, in source order, constructor for constructor and field for
field. L3 type constructors are rendered as `F n`/`FTy n` = `BitVec n`, `bTy` = `Bool`,
`nTy` = `Nat`, `sTy` (HOL `string`, a `char list`) = `List HolChar`, `PTy` = `×`, `OTy` =
`Option`, `LTy` = `List`, and `ATy (a, b)` (an L3 map, the HOL function type) = `a → b`.
Names are HOL's, with `«»` quoting where Lean requires it.
-/

namespace Flapjack.RiscV.L3

open Flapjack.Basis.Pure.MlString

/-- HOL L3 datatype `rawInstType` (`riscvScript.sml:6`). -/
@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "rawInstType"]
inductive rawInstType where
  | Half (a0 : (BitVec 16))
  | Word (a0 : (BitVec 32))
  deriving DecidableEq, Repr, Inhabited

/-- HOL L3 datatype `accessType` (`riscvScript.sml:8`). -/
@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "accessType"]
inductive accessType where
  | Read
  | Write
  deriving DecidableEq, Repr, Inhabited

/-- HOL L3 datatype `fetchType` (`riscvScript.sml:10`). -/
@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "fetchType"]
inductive fetchType where
  | Instruction
  | Data
  deriving DecidableEq, Repr, Inhabited

/-- HOL L3 datatype `Architecture` (`riscvScript.sml:12`). -/
@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "Architecture"]
inductive Architecture where
  | RV32I
  | RV64I
  | RV128I
  deriving DecidableEq, Repr, Inhabited

/-- HOL L3 datatype `Privilege` (`riscvScript.sml:15`). -/
@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "Privilege"]
inductive Privilege where
  | User
  | Supervisor
  | Hypervisor
  | Machine
  deriving DecidableEq, Repr, Inhabited

/-- HOL L3 datatype `VM_Mode` (`riscvScript.sml:19`). -/
@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "VM_Mode"]
inductive VM_Mode where
  | Mbare
  | Mbb
  | Mbbid
  | Sv32
  | Sv39
  | Sv48
  | Sv57
  | Sv64
  deriving DecidableEq, Repr, Inhabited

/-- HOL L3 datatype `ExtStatus` (`riscvScript.sml:24`). -/
@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "ExtStatus"]
inductive ExtStatus where
  | Off
  | Initial
  | Clean
  | Dirty
  deriving DecidableEq, Repr, Inhabited

/-- HOL L3 datatype `ExceptionType` (`riscvScript.sml:29`). -/
@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "ExceptionType"]
inductive ExceptionType where
  | Fetch_Misaligned
  | Fetch_Fault
  | Illegal_Instr
  | Breakpoint
  | Load_Fault
  | AMO_Misaligned
  | Store_AMO_Fault
  | UMode_Env_Call
  | SMode_Env_Call
  | HMode_Env_Call
  | MMode_Env_Call
  deriving DecidableEq, Repr, Inhabited

/-- HOL L3 record `mcpuid` (`riscvScript.sml:36`). -/
@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "mcpuid"]
structure mcpuid where
  ArchBase : (BitVec 2)
  I : Bool
  M : Bool
  S : Bool
  U : Bool
  «mcpuid'rst» : (BitVec 58)
  deriving DecidableEq, Repr, Inhabited

/-- HOL L3 record `mimpid` (`riscvScript.sml:41`). -/
@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "mimpid"]
structure mimpid where
  RVImpl : (BitVec 48)
  RVSource : (BitVec 16)
  deriving DecidableEq, Repr, Inhabited

/-- HOL L3 record `mstatus` (`riscvScript.sml:43`). -/
@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "mstatus"]
structure mstatus where
  MFS : (BitVec 2)
  MIE : Bool
  MIE1 : Bool
  MIE2 : Bool
  MIE3 : Bool
  MMPRV : Bool
  MPRV : (BitVec 2)
  MPRV1 : (BitVec 2)
  MPRV2 : (BitVec 2)
  MPRV3 : (BitVec 2)
  MSD : Bool
  MXS : (BitVec 2)
  VM : (BitVec 5)
  «mstatus'rst» : (BitVec 41)
  deriving DecidableEq, Repr, Inhabited

/-- HOL L3 record `mtdeleg` (`riscvScript.sml:50`). -/
@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "mtdeleg"]
structure mtdeleg where
  Exc_deleg : (BitVec 16)
  Intr_deleg : (BitVec 48)
  deriving DecidableEq, Repr, Inhabited

/-- HOL L3 record `mip` (`riscvScript.sml:52`). -/
@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "mip"]
structure mip where
  HSIP : Bool
  HTIP : Bool
  MSIP : Bool
  MTIP : Bool
  SSIP : Bool
  STIP : Bool
  «mip'rst» : (BitVec 58)
  deriving DecidableEq, Repr, Inhabited

/-- HOL L3 record `mie` (`riscvScript.sml:57`). -/
@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "mie"]
structure mie where
  HSIE : Bool
  HTIE : Bool
  MSIE : Bool
  MTIE : Bool
  SSIE : Bool
  STIE : Bool
  «mie'rst» : (BitVec 58)
  deriving DecidableEq, Repr, Inhabited

/-- HOL L3 record `mcause` (`riscvScript.sml:62`). -/
@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "mcause"]
structure mcause where
  EC : (BitVec 4)
  Int : Bool
  «mcause'rst» : (BitVec 59)
  deriving DecidableEq, Repr, Inhabited

/-- HOL L3 record `MachineCSR` (`riscvScript.sml:64`). -/
structure MachineCSR where
  mbadaddr : (BitVec 64)
  mbase : (BitVec 64)
  mbound : (BitVec 64)
  mcause : mcause
  mcpuid : mcpuid
  mdbase : (BitVec 64)
  mdbound : (BitVec 64)
  mepc : (BitVec 64)
  mfromhost : (BitVec 64)
  mhartid : (BitVec 64)
  mibase : (BitVec 64)
  mibound : (BitVec 64)
  mie : mie
  mimpid : mimpid
  mip : mip
  mscratch : (BitVec 64)
  mstatus : mstatus
  mtdeleg : mtdeleg
  mtohost : (BitVec 64)
  mtvec : (BitVec 64)
  deriving DecidableEq, Repr, Inhabited

/-- HOL L3 record `HypervisorCSR` (`riscvScript.sml:73`). -/
structure HypervisorCSR where
  hbadaddr : (BitVec 64)
  hcause : mcause
  hepc : (BitVec 64)
  hscratch : (BitVec 64)
  hstatus : mstatus
  htdeleg : mtdeleg
  htvec : (BitVec 64)
  deriving DecidableEq, Repr, Inhabited

/-- HOL L3 record `sstatus` (`riscvScript.sml:79`). -/
@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "sstatus"]
structure sstatus where
  SFS : (BitVec 2)
  SIE : Bool
  SMPRV : Bool
  SPIE : Bool
  SPS : Bool
  SSD : Bool
  SXS : (BitVec 2)
  «sstatus'rst» : (BitVec 55)
  deriving DecidableEq, Repr, Inhabited

/-- HOL L3 record `sip` (`riscvScript.sml:84`). -/
@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "sip"]
structure sip where
  SSIP : Bool
  STIP : Bool
  «sip'rst» : (BitVec 62)
  deriving DecidableEq, Repr, Inhabited

/-- HOL L3 record `sie` (`riscvScript.sml:86`). -/
@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "sie"]
structure sie where
  SSIE : Bool
  STIE : Bool
  «sie'rst» : (BitVec 62)
  deriving DecidableEq, Repr, Inhabited

/-- HOL L3 record `SupervisorCSR` (`riscvScript.sml:88`). -/
structure SupervisorCSR where
  sasid : (BitVec 64)
  sbadaddr : (BitVec 64)
  scause : mcause
  sepc : (BitVec 64)
  sptbr : (BitVec 64)
  sscratch : (BitVec 64)
  stvec : (BitVec 64)
  deriving DecidableEq, Repr, Inhabited

/-- HOL L3 record `SynchronousTrap` (`riscvScript.sml:104`). -/
structure SynchronousTrap where
  badaddr : (Option (BitVec 64))
  trap : ExceptionType
  deriving DecidableEq, Repr, Inhabited

/-- HOL L3 datatype `TransferControl` (`riscvScript.sml:107`). -/
inductive TransferControl where
  | BranchTo (a0 : (BitVec 64))
  | Trap (a0 : SynchronousTrap)
  deriving DecidableEq, Repr, Inhabited

/-- HOL L3 record `StateDelta` (`riscvScript.sml:116`). -/
structure StateDelta where
  addr : (Option (BitVec 64))
  data1 : (Option (BitVec 64))
  data2 : (Option (BitVec 64))
  exc_taken : Bool
  fetch_exc : Bool
  pc : (BitVec 64)
  rinstr : rawInstType
  st_width : (Option (BitVec 32))
  deriving DecidableEq, Repr, Inhabited

/-- HOL L3 datatype `Internal` (`riscvScript.sml:137`). -/
inductive Internal where
  | FETCH_FAULT (a0 : (BitVec 64))
  | FETCH_MISALIGNED (a0 : (BitVec 64))
  deriving DecidableEq, Repr, Inhabited

/-- HOL L3 datatype `System` (`riscvScript.sml:140`). -/
inductive System where
  | EBREAK
  | ECALL
  deriving DecidableEq, Repr, Inhabited

/-- HOL L3 datatype `Store` (`riscvScript.sml:246`). -/
@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "Store"]
inductive Store where
  | SB (a0 : ((BitVec 5) × ((BitVec 5) × (BitVec 12))))
  | SD (a0 : ((BitVec 5) × ((BitVec 5) × (BitVec 12))))
  | SH (a0 : ((BitVec 5) × ((BitVec 5) × (BitVec 12))))
  | SW (a0 : ((BitVec 5) × ((BitVec 5) × (BitVec 12))))
  deriving DecidableEq, Repr, Inhabited

/-- HOL L3 datatype `Load` (`riscvScript.sml:253`). -/
@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "Load"]
inductive Load where
  | LB (a0 : ((BitVec 5) × ((BitVec 5) × (BitVec 12))))
  | LBU (a0 : ((BitVec 5) × ((BitVec 5) × (BitVec 12))))
  | LD (a0 : ((BitVec 5) × ((BitVec 5) × (BitVec 12))))
  | LH (a0 : ((BitVec 5) × ((BitVec 5) × (BitVec 12))))
  | LHU (a0 : ((BitVec 5) × ((BitVec 5) × (BitVec 12))))
  | LW (a0 : ((BitVec 5) × ((BitVec 5) × (BitVec 12))))
  | LWU (a0 : ((BitVec 5) × ((BitVec 5) × (BitVec 12))))
  deriving DecidableEq, Repr, Inhabited

/-- HOL L3 datatype `Branch` (`riscvScript.sml:263`). -/
@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "Branch"]
inductive Branch where
  | BEQ (a0 : ((BitVec 5) × ((BitVec 5) × (BitVec 12))))
  | BGE (a0 : ((BitVec 5) × ((BitVec 5) × (BitVec 12))))
  | BGEU (a0 : ((BitVec 5) × ((BitVec 5) × (BitVec 12))))
  | BLT (a0 : ((BitVec 5) × ((BitVec 5) × (BitVec 12))))
  | BLTU (a0 : ((BitVec 5) × ((BitVec 5) × (BitVec 12))))
  | BNE (a0 : ((BitVec 5) × ((BitVec 5) × (BitVec 12))))
  | JAL (a0 : ((BitVec 5) × (BitVec 20)))
  | JALR (a0 : ((BitVec 5) × ((BitVec 5) × (BitVec 12))))
  deriving DecidableEq, Repr, Inhabited

/-- HOL L3 datatype `MulDiv` (`riscvScript.sml:273`). -/
inductive MulDiv where
  | DIV (a0 : ((BitVec 5) × ((BitVec 5) × (BitVec 5))))
  | DIVU (a0 : ((BitVec 5) × ((BitVec 5) × (BitVec 5))))
  | MUL (a0 : ((BitVec 5) × ((BitVec 5) × (BitVec 5))))
  | MULH (a0 : ((BitVec 5) × ((BitVec 5) × (BitVec 5))))
  | MULHSU (a0 : ((BitVec 5) × ((BitVec 5) × (BitVec 5))))
  | MULHU (a0 : ((BitVec 5) × ((BitVec 5) × (BitVec 5))))
  | REM (a0 : ((BitVec 5) × ((BitVec 5) × (BitVec 5))))
  | REMU (a0 : ((BitVec 5) × ((BitVec 5) × (BitVec 5))))
  deriving DecidableEq, Repr, Inhabited

/-- HOL L3 datatype `Shift` (`riscvScript.sml:289`). -/
inductive Shift where
  | SLL (a0 : ((BitVec 5) × ((BitVec 5) × (BitVec 5))))
  | SLLI (a0 : ((BitVec 5) × ((BitVec 5) × (BitVec 6))))
  | SRA (a0 : ((BitVec 5) × ((BitVec 5) × (BitVec 5))))
  | SRAI (a0 : ((BitVec 5) × ((BitVec 5) × (BitVec 6))))
  | SRL (a0 : ((BitVec 5) × ((BitVec 5) × (BitVec 5))))
  | SRLI (a0 : ((BitVec 5) × ((BitVec 5) × (BitVec 6))))
  deriving DecidableEq, Repr, Inhabited

/-- HOL L3 datatype `ArithR` (`riscvScript.sml:304`). -/
inductive ArithR where
  | ADD (a0 : ((BitVec 5) × ((BitVec 5) × (BitVec 5))))
  | AND (a0 : ((BitVec 5) × ((BitVec 5) × (BitVec 5))))
  | OR (a0 : ((BitVec 5) × ((BitVec 5) × (BitVec 5))))
  | SLT (a0 : ((BitVec 5) × ((BitVec 5) × (BitVec 5))))
  | SLTU (a0 : ((BitVec 5) × ((BitVec 5) × (BitVec 5))))
  | SUB (a0 : ((BitVec 5) × ((BitVec 5) × (BitVec 5))))
  | XOR (a0 : ((BitVec 5) × ((BitVec 5) × (BitVec 5))))
  deriving DecidableEq, Repr, Inhabited

/-- HOL L3 datatype `ArithI` (`riscvScript.sml:316`). -/
inductive ArithI where
  | ADDI (a0 : ((BitVec 5) × ((BitVec 5) × (BitVec 12))))
  | ADDIW (a0 : ((BitVec 5) × ((BitVec 5) × (BitVec 12))))
  | ANDI (a0 : ((BitVec 5) × ((BitVec 5) × (BitVec 12))))
  | AUIPC (a0 : ((BitVec 5) × (BitVec 20)))
  | LUI (a0 : ((BitVec 5) × (BitVec 20)))
  | ORI (a0 : ((BitVec 5) × ((BitVec 5) × (BitVec 12))))
  | SLTI (a0 : ((BitVec 5) × ((BitVec 5) × (BitVec 12))))
  | SLTIU (a0 : ((BitVec 5) × ((BitVec 5) × (BitVec 12))))
  | XORI (a0 : ((BitVec 5) × ((BitVec 5) × (BitVec 12))))
  deriving DecidableEq, Repr, Inhabited

/-- HOL L3 datatype `instruction` (`riscvScript.sml:327`). -/
inductive instruction where
  | ArithI (a0 : ArithI)
  | ArithR (a0 : ArithR)
  | Branch (a0 : Branch)
  | FENCE (a0 : ((BitVec 5) × ((BitVec 5) × ((BitVec 4) × (BitVec 4)))))
  | Internal (a0 : Internal)
  | Load (a0 : Load)
  | MulDiv (a0 : MulDiv)
  | Shift (a0 : Shift)
  | Store (a0 : Store)
  | System (a0 : System)
  | UnknownInstruction
  deriving DecidableEq, Repr, Inhabited

/-- HOL L3 datatype `FetchResult` (`riscvScript.sml:338`). -/
inductive FetchResult where
  | F_Error (a0 : instruction)
  | F_Result (a0 : rawInstType)
  deriving DecidableEq, Repr, Inhabited

/-- HOL L3 datatype `rvc` (`riscvScript.sml:342`). -/
@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "rvc"]
inductive rvc where
  | Comp (a0 : (BitVec 16))
  | Full (a0 : (BitVec 32))
  deriving DecidableEq, Repr, Inhabited

/-- HOL L3 datatype `exception` (`riscvScript.sml:344`). -/
inductive exception where
  | INTERNAL_ERROR (a0 : List HolChar)
  | NoException
  | UNDEFINED (a0 : List HolChar)
  deriving DecidableEq, Repr, Inhabited

/-- HOL L3 record `riscv_state` (`riscvScript.sml:348`). -/
structure riscv_state where
  MEM8 : ((BitVec 64) → (BitVec 8))
  c_ExitCode : ((BitVec 8) → (BitVec 64))
  c_HCSR : ((BitVec 8) → HypervisorCSR)
  c_MCSR : ((BitVec 8) → MachineCSR)
  c_NextFetch : ((BitVec 8) → (Option TransferControl))
  c_PC : ((BitVec 8) → (BitVec 64))
  c_SCSR : ((BitVec 8) → SupervisorCSR)
  c_Skip : ((BitVec 8) → (BitVec 64))
  c_gpr : ((BitVec 8) → ((BitVec 5) → (BitVec 64)))
  c_update : ((BitVec 8) → StateDelta)
  «done» : Bool
  exception : exception
  log : (List (Nat × List HolChar))
  procID : (BitVec 8)
  totalCore : Nat
  deriving Inhabited


end Flapjack.RiscV.L3
