import Flapjack.Compiler.Encoders.Mips32.Target
import Flapjack.Basis.Pure.MlString
import Flapjack.Compiler.Backend.Backend

/-! # Running MIPS32 images on Ziren's ISA model

A test harness that installs a compiled MIPS32 image in `ZirenDet.Isa` memory and runs it
with the backend's `mips32Next`, following the layout and entry convention of CakeML's MIPS
export (`export_mipsScript.sml`): the 16-byte FFI stubs, `cake_clear` and `cake_exit`
precede `cake_main`; `$a0` holds the entry address, `$a1` the first heap address, `$a2` the
first stack address and `$a3` the first address past the stack. Reaching `cake_exit` halts.
Reaching an FFI stub records the call, lets an oracle rewrite the array argument (`$a2`,
`$a3`) and returns to `$ra`, as `ffi_interfer` does.

Flapjack test infrastructure; it is not part of the compiler or of any correctness claim.
-/

namespace Flapjack.Mips32.Run
open ZirenDet.Isa Flapjack.Compiler.Encoders.Mips32

/-- Memory holding `bytes` from `base` (addresses are distinct, so list order is irrelevant). -/
def memOfBytes (base : W) (bytes : List (BitVec 8)) : Mem :=
  ⟨(bytes.zipIdx.map fun (b, i) => (base + BitVec.ofNat 32 i, b)).reverse⟩

def readBytes (m : Mem) (a : W) (n : Nat) : List (BitVec 8) :=
  (List.range n).map fun i => m.readByte (a + BitVec.ofNat 32 i)

def writeBytes (m : Mem) (a : W) : List (BitVec 8) → Mem
  | [] => m
  | b :: bs => writeBytes (m.writeByte a b) (a + 1) bs

/-- One recorded FFI call: its name, the bytes of its first (read-only) argument and the
bytes of its array argument before the call. -/
structure FfiCall where
  name : String
  conf : List (BitVec 8)
  array : List (BitVec 8)
  deriving Repr, BEq

structure Layout where
  base : W := 0x10000
  heap : W := 0x100000
  stack : W := 0x400000
  stackEnd : W := 0x800000

inductive Stop where
  | halted
  | trapped
  | outOfFuel
  deriving Repr, BEq

structure Outcome where
  stop : Stop
  calls : List FfiCall
  steps : Nat
  state : State

def ffiEntry (base : W) (index : Nat) : W := base - BitVec.ofNat 32 (16 * (index + 3))

def initialState (layout : Layout) (bytes : List (BitVec 8)) : State :=
  let regs : Fin 32 → W := fun r =>
    if r = 4 then layout.base else if r = 5 then layout.heap
    else if r = 6 then layout.stack else if r = 7 then layout.stackEnd else 0
  { pc := layout.base, nextPc := layout.base + 4, gpr := regs, hi := 0, lo := 0,
    mem := memOfBytes layout.base bytes, trapped := false }

/-- Run until `cake_exit`, a stop, or fuel exhaustion. `oracle name conf array` gives the
new array contents of an FFI call. -/
def run (layout : Layout) (ffiNames : List String)
    (oracle : String → List (BitVec 8) → List (BitVec 8) → List (BitVec 8)) :
    Nat → Nat → List FfiCall → State → Outcome
  | 0, steps, calls, s => ⟨.outOfFuel, calls.reverse, steps, s⟩
  | fuel + 1, steps, calls, s =>
    if s.trapped then ⟨.trapped, calls.reverse, steps, s⟩
    else if s.pc = layout.base - 16 then ⟨.halted, calls.reverse, steps, s⟩
    else
      match (List.range ffiNames.length).find? (fun i => s.pc = ffiEntry layout.base i) with
      | some i =>
        let name := ffiNames[i]!
        let conf := readBytes s.mem (s.reg 4) (s.reg 5).toNat
        let array := readBytes s.mem (s.reg 6) (s.reg 7).toNat
        let array' := oracle name conf array
        let ra := s.reg 31
        let s' := { s with mem := writeBytes s.mem (s.reg 6) array', pc := ra, nextPc := ra + 4 }
        run layout ffiNames oracle fuel (steps + 1) (⟨name, conf, array⟩ :: calls) s'
      | none => run layout ffiNames oracle fuel (steps + 1) calls (mips32Next s)

/-- The FFI names of a compiled configuration, in index order. -/
def ffiNamesOf (config : Flapjack.Compiler.Backend.Backend.Config) : List String :=
  (Flapjack.Compiler.Backend.Backend.ffinamesToStringList (config.labConf.ffiNames.getD [])).map
    Flapjack.Basis.Pure.MlString.toStringOfBytes

end Flapjack.Mips32.Run
