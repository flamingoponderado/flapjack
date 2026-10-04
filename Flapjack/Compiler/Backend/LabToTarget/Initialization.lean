import Flapjack.Compiler.Backend.LabSem.State
import Flapjack.Compiler.Encoders.AsmSem.State
import Flapjack.Compiler.Backend.Semantics.TargetProps.RegisterOracles

namespace Flapjack.Compiler.Backend.LabToTarget
open Flapjack Flapjack.Compiler.Backend.LabSem
open Flapjack.Compiler.Backend.Semantics.TargetProps

/-- Full original proof-layer initializer. Compiler configuration remains
independent of target state, projection and FFI host. All 23 state fields and
the four actual target register oracles are retained. This builds the source
state for the still-open initialization simulation, not an executed compiler
replacement; that consumer is tracked by the linked initializer theorem. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
noncomputable def makeInit {width : Nat} [NeZero width] {C S Q : Type} {F : Type}
    (mc : MachineConfig width S Q) (ffi : HolFfiState F) (t : AsmState width)
    (m : BitVec width → WordLocW width) (dm sdm : BitVec width → Bool)
    (ms : S) (code : LabProgHOL width)
    (comp : C → LabProgHOL width → Option (List (BitVec 8) × C))
    (cbpos : BitVec width) (cbspace : Nat) (coracle : Nat → C × LabProgHOL width) :
    State width C F :=
  { regs := fun k => .word (t.regs k)
    fpRegs := t.fpRegs
    memory := m
    memDomain := dm
    sharedMemDomain := sdm
    pc := 0
    be := mc.target.config.bigEndian
    ffi := ffi
    ioRegs := targetIoRegs mc ffi ms
    ioFpRegs := targetIoFpRegs mc ffi ms
    ccRegs := targetCcRegs mc ffi ms
    ccFpRegs := targetCcFpRegs mc ffi ms
    code := code
    clock := 0
    failed := false
    ptrReg := mc.ptrReg
    lenReg := mc.lenReg
    ptr2Reg := mc.ptr2Reg
    len2Reg := mc.len2Reg
    linkReg := match mc.target.config.linkReg with | some n => n | none => 0
    compile := comp
    codeBuffer := { position := cbpos, buffer := [], spaceLeft := cbspace }
    compileOracle := coracle }

end Flapjack.Compiler.Backend.LabToTarget
