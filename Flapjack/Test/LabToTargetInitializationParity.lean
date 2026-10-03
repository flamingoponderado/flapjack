import Flapjack.Compiler.Backend.LabToTarget.Initialization
namespace Flapjack.Test.LabToTargetInitializationParity
open Flapjack Flapjack.Compiler.Backend.LabSem
open Flapjack.Compiler.Backend.LabToTarget Flapjack.Compiler.Backend.Semantics.TargetProps
example {width : Nat} [NeZero width] {C S Q F : Type}
    (mc : MachineConfig width S Q) (ffi : HolFfiState F) (t : AsmState width)
    (m : BitVec width → WordLocW width) (dm sdm : BitVec width → Bool)
    (ms : S) (code : LabProgHOL width)
    (comp : C → LabProgHOL width → Option (List (BitVec 8) × C))
    (cbpos : BitVec width) (cbspace : Nat) (coracle : Nat → C × LabProgHOL width) :
    makeInit mc ffi t m dm sdm ms code comp cbpos cbspace coracle =
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
    compileOracle := coracle } := rfl

section
variable {width : Nat} [NeZero width] {C S Q F : Type}
variable (mc : MachineConfig width S Q) (ffi : HolFfiState F) (t : AsmState width)
variable (m : BitVec width → WordLocW width) (dm sdm : BitVec width → Bool) (ms : S)
variable (code : LabProgHOL width)
variable (comp : C → LabProgHOL width → Option (List (BitVec 8) × C))
variable (cbpos : BitVec width) (cbspace : Nat) (coracle : Nat → C × LabProgHOL width)
example : (makeInit mc ffi t m dm sdm ms code comp cbpos cbspace coracle).regs = (fun k => WordLocW.word (t.regs k)) := rfl
example : (makeInit mc ffi t m dm sdm ms code comp cbpos cbspace coracle).fpRegs = (t.fpRegs) := rfl
example : (makeInit mc ffi t m dm sdm ms code comp cbpos cbspace coracle).memory = (m) := rfl
example : (makeInit mc ffi t m dm sdm ms code comp cbpos cbspace coracle).memDomain = (dm) := rfl
example : (makeInit mc ffi t m dm sdm ms code comp cbpos cbspace coracle).sharedMemDomain = (sdm) := rfl
example : (makeInit mc ffi t m dm sdm ms code comp cbpos cbspace coracle).pc = (0) := rfl
example : (makeInit mc ffi t m dm sdm ms code comp cbpos cbspace coracle).be = (mc.target.config.bigEndian) := rfl
example : (makeInit mc ffi t m dm sdm ms code comp cbpos cbspace coracle).ffi = (ffi) := rfl
example : (makeInit mc ffi t m dm sdm ms code comp cbpos cbspace coracle).ioRegs = (targetIoRegs mc ffi ms) := rfl
example : (makeInit mc ffi t m dm sdm ms code comp cbpos cbspace coracle).ioFpRegs = (targetIoFpRegs mc ffi ms) := rfl
example : (makeInit mc ffi t m dm sdm ms code comp cbpos cbspace coracle).ccRegs = (targetCcRegs mc ffi ms) := rfl
example : (makeInit mc ffi t m dm sdm ms code comp cbpos cbspace coracle).ccFpRegs = (targetCcFpRegs mc ffi ms) := rfl
example : (makeInit mc ffi t m dm sdm ms code comp cbpos cbspace coracle).code = (code) := rfl
example : (makeInit mc ffi t m dm sdm ms code comp cbpos cbspace coracle).clock = (0) := rfl
example : (makeInit mc ffi t m dm sdm ms code comp cbpos cbspace coracle).failed = (false) := rfl
example : (makeInit mc ffi t m dm sdm ms code comp cbpos cbspace coracle).ptrReg = (mc.ptrReg) := rfl
example : (makeInit mc ffi t m dm sdm ms code comp cbpos cbspace coracle).lenReg = (mc.lenReg) := rfl
example : (makeInit mc ffi t m dm sdm ms code comp cbpos cbspace coracle).ptr2Reg = (mc.ptr2Reg) := rfl
example : (makeInit mc ffi t m dm sdm ms code comp cbpos cbspace coracle).len2Reg = (mc.len2Reg) := rfl
example : (makeInit mc ffi t m dm sdm ms code comp cbpos cbspace coracle).linkReg = (match mc.target.config.linkReg with | some n => n | none => 0) := rfl
example : (makeInit mc ffi t m dm sdm ms code comp cbpos cbspace coracle).compile = (comp) := rfl
example : (makeInit mc ffi t m dm sdm ms code comp cbpos cbspace coracle).codeBuffer = ({position := cbpos, buffer := [], spaceLeft := cbspace}) := rfl
example : (makeInit mc ffi t m dm sdm ms code comp cbpos cbspace coracle).compileOracle = (coracle) := rfl
end
end Flapjack.Test.LabToTargetInitializationParity
