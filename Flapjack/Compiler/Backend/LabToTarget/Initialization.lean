module

public import Flapjack.Compiler.Backend.LabSem.State
public import Flapjack.Compiler.Encoders.AsmSem.State
public import Flapjack.Compiler.Backend.Semantics.TargetProps.RegisterOracles
public import Flapjack.Byte.SetByte

@[expose] public section

namespace Flapjack.Compiler.Backend.LabToTarget
open Flapjack Flapjack.Compiler.Backend.LabSem
open Flapjack.Compiler.Backend.Semantics.TargetProps

/-- Write a list of bytes, from the given address upwards, into the zero
word using the reviewed `set_byte` port. -/
@[hol "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "set_bytes_def"
  (words_as_type_indexed_bitvec)]
def setBytes {width : Nat} [NeZero width] (a : BitVec width) (be : Bool) :
    List (BitVec 8) → BitVec width
  | [] => 0#width
  | b :: bs => HolByte.setByte a b (setBytes (a + 1#width) be bs) be

/-- Assemble the word at an address from its four (32-bit) or eight
(otherwise) bytes in the byte memory. -/
@[hol "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "make_word_def"
  (words_as_type_indexed_bitvec)]
def makeWord {width : Nat} [NeZero width] (be : Bool) (m : BitVec width → BitVec 8)
    (a : BitVec width) : WordLocW width :=
  if width = 32 then
    .word (setBytes a be [m a, m (a + 1#width), m (a + 2#width), m (a + 3#width)])
  else
    .word (setBytes a be [m a, m (a + 1#width), m (a + 2#width), m (a + 3#width),
      m (a + 4#width), m (a + 5#width), m (a + 6#width), m (a + 7#width)])

/-- Full original proof-layer initializer. Compiler configuration remains
independent of target state, projection and FFI host. All 23 state fields and
the four actual target register oracles are retained. This builds the source
state for the still-open initialization simulation, not an executed compiler
replacement; that consumer is tracked by the linked initializer theorem. -/
@[hol "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "make_init_def"
  (words_as_type_indexed_bitvec)]
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
