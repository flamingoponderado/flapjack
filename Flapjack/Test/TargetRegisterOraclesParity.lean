import Flapjack.Compiler.Backend.Semantics.TargetProps.RegisterOracles

namespace Flapjack.Test.TargetRegisterOraclesParity
open Flapjack Flapjack.Compiler.Backend.Semantics.TargetProps
variable {w : Nat} [NeZero w] {S Q σ : Type}
variable (mc : MachineConfig w S Q) (ffi : HolFfiState σ) (ms : S) (k n r : Nat)
example (name : HolFfiName) (h : interferencePos (fun app => isFfiApp app = true) mc ffi ms k = none) :
    targetIoRegs mc ffi ms k name r = none := by
  simp [targetIoRegs, h]
example (i : Nat) (h : interferencePos (fun app => isFfiApp app = true) mc ffi ms k = none) :
    targetIoFpRegs mc ffi ms k i = 0 := by
  simp [targetIoFpRegs, h]
example (i : Nat) (index : Nat) (bytes : List (BitVec 8)) (pre post : S)
    (mc' : MachineConfig w S Q) (ffi' : HolFfiState σ)
    (hp : interferencePos (fun app => isFfiApp app = true) mc ffi ms k = some n)
    (hs : interferenceAppSeq mc ffi ms n = some (.ffiApp index bytes pre post, mc', ffi')) :
    targetIoFpRegs mc ffi ms k i = mc.target.getFpReg post i := by
  simp [targetIoFpRegs, hp, hs]
example (name : HolFfiName) (index : Nat) (bytes : List (BitVec 8)) (pre post : S)
    (mc' : MachineConfig w S Q) (ffi' : HolFfiState σ)
    (hp : interferencePos (fun app => isFfiApp app = true) mc ffi ms k = some n)
    (hs : interferenceAppSeq mc ffi ms n = some (.ffiApp index bytes pre post, mc', ffi'))
    (hc : r ∈ mc.calleeSavedRegs) :
    targetIoRegs mc ffi ms k name r = none := by
  simp [targetIoRegs, hp, hs, hc]
example (name : HolFfiName) (index : Nat) (bytes : List (BitVec 8)) (pre post : S)
    (mc' : MachineConfig w S Q) (ffi' : HolFfiState σ)
    (hp : interferencePos (fun app => isFfiApp app = true) mc ffi ms k = some n)
    (hs : interferenceAppSeq mc ffi ms n = some (.ffiApp index bytes pre post, mc', ffi'))
    (hc : r ∉ mc.calleeSavedRegs) 
    (hr : r < mc.target.config.regCount) (ha : r ∉ mc.target.config.avoidRegs) :
    targetIoRegs mc ffi ms k name r = some (mc.target.getReg post r) := by
  simp [targetIoRegs, hp, hs, hc, hr, ha]
example  (h : interferencePos (fun app => ¬ isFfiApp app = true) mc ffi ms k = none) :
    targetCcRegs mc ffi ms k r = none := by
  simp at h
  simp [targetCcRegs, h]
example (i : Nat) (h : interferencePos (fun app => ¬ isFfiApp app = true) mc ffi ms k = none) :
    targetCcFpRegs mc ffi ms k i = 0 := by
  simp at h
  simp [targetCcFpRegs, h]
example (i : Nat) (a b : BitVec w) (pre post : S)
    (mc' : MachineConfig w S Q) (ffi' : HolFfiState σ)
    (hp : interferencePos (fun app => ¬ isFfiApp app = true) mc ffi ms k = some n)
    (hs : interferenceAppSeq mc ffi ms n = some (.ccApp a b pre post, mc', ffi')) :
    targetCcFpRegs mc ffi ms k i = mc.target.getFpReg post i := by
  simp at hp
  simp [targetCcFpRegs, hp, hs]
example  (a b : BitVec w) (pre post : S)
    (mc' : MachineConfig w S Q) (ffi' : HolFfiState σ)
    (hp : interferencePos (fun app => ¬ isFfiApp app = true) mc ffi ms k = some n)
    (hs : interferenceAppSeq mc ffi ms n = some (.ccApp a b pre post, mc', ffi'))
    (hc : r ∈ mc.calleeSavedRegs) :
    targetCcRegs mc ffi ms k r = none := by
  simp at hp
  simp [targetCcRegs, hp, hs, hc]
example  (a b : BitVec w) (pre post : S)
    (mc' : MachineConfig w S Q) (ffi' : HolFfiState σ)
    (hp : interferencePos (fun app => ¬ isFfiApp app = true) mc ffi ms k = some n)
    (hs : interferenceAppSeq mc ffi ms n = some (.ccApp a b pre post, mc', ffi'))
    (hc : r ∉ mc.calleeSavedRegs) (hptr : r ≠ mc.ptrReg)
    (hr : r < mc.target.config.regCount) (ha : r ∉ mc.target.config.avoidRegs) :
    targetCcRegs mc ffi ms k r = some (mc.target.getReg post r) := by
  simp at hp
  simp [targetCcRegs, hp, hs, hc, hr, ha, hptr]

example (name : HolFfiName)
    (hp : interferencePos (fun app => isFfiApp app = true) mc ffi ms k = some n)
    (hs : interferenceAppSeq mc ffi ms n = none) :
    targetIoRegs mc ffi ms k name r = none := by
  skip
  simp [targetIoRegs, hp, hs]
example (name : HolFfiName) (index : Nat) (bytes : List (BitVec 8)) (pre post : S) (mc' : MachineConfig w S Q) (ffi' : HolFfiState σ)
    (hp : interferencePos (fun app => isFfiApp app = true) mc ffi ms k = some n)
    (hs : interferenceAppSeq mc ffi ms n = some (.ffiApp index bytes pre post, mc', ffi')) (hr : ¬ r < mc.target.config.regCount) :
    targetIoRegs mc ffi ms k name r = none := by
  skip
  simp [targetIoRegs, hp, hs, hr]
example (name : HolFfiName) (index : Nat) (bytes : List (BitVec 8)) (pre post : S) (mc' : MachineConfig w S Q) (ffi' : HolFfiState σ)
    (hp : interferencePos (fun app => isFfiApp app = true) mc ffi ms k = some n)
    (hs : interferenceAppSeq mc ffi ms n = some (.ffiApp index bytes pre post, mc', ffi')) (ha : r ∈ mc.target.config.avoidRegs) :
    targetIoRegs mc ffi ms k name r = none := by
  skip
  simp [targetIoRegs, hp, hs, ha]
example 
    (hp : interferencePos (fun app => ¬ isFfiApp app = true) mc ffi ms k = some n)
    (hs : interferenceAppSeq mc ffi ms n = none) :
    targetCcRegs mc ffi ms k r = none := by
  simp at hp
  simp [targetCcRegs, hp, hs]
example  (a b : BitVec w) (pre post : S) (mc' : MachineConfig w S Q) (ffi' : HolFfiState σ)
    (hp : interferencePos (fun app => ¬ isFfiApp app = true) mc ffi ms k = some n)
    (hs : interferenceAppSeq mc ffi ms n = some (.ccApp a b pre post, mc', ffi')) (hr : ¬ r < mc.target.config.regCount) :
    targetCcRegs mc ffi ms k r = none := by
  simp at hp
  simp [targetCcRegs, hp, hs, hr]
example  (a b : BitVec w) (pre post : S) (mc' : MachineConfig w S Q) (ffi' : HolFfiState σ)
    (hp : interferencePos (fun app => ¬ isFfiApp app = true) mc ffi ms k = some n)
    (hs : interferenceAppSeq mc ffi ms n = some (.ccApp a b pre post, mc', ffi')) (ha : r ∈ mc.target.config.avoidRegs) :
    targetCcRegs mc ffi ms k r = none := by
  simp at hp
  simp [targetCcRegs, hp, hs, ha]
example (a b : BitVec w) (pre post : S) (mc' : MachineConfig w S Q) (ffi' : HolFfiState σ)
    (hp : interferencePos (fun app => ¬ isFfiApp app = true) mc ffi ms k = some n)
    (hs : interferenceAppSeq mc ffi ms n = some (.ccApp a b pre post, mc', ffi')) (hr : r = mc.ptrReg) :
    targetCcRegs mc ffi ms k r = none := by
  simp at hp
  simp [targetCcRegs, hp, hs, hr]
end Flapjack.Test.TargetRegisterOraclesParity
