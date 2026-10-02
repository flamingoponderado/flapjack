import Flapjack.Compiler.Backend.LabToTarget.MemoryTransport
namespace Flapjack.Test.LabToTargetMemoryTransportParity
open Flapjack Flapjack.Compiler.Backend.LabToTarget
example {width : Nat} [NeZero width] {machine projection : Type}
    (pc : BitVec width) (bytes : List (BitVec 8))
    (mcConf : MachineConfig width machine projection) (ms1 : machine) (t1 : AsmState width) :
    (∀ a, t1.memDomain a → mcConf.target.getByte ms1 a = t1.mem a) ∧
      bytesInMemoryHOL pc bytes t1.mem t1.memDomain →
    bytesInMemoryHOL pc bytes (mcConf.target.getByte ms1) t1.memDomain :=
  bytesInMemory_eqMem pc bytes mcConf ms1 t1
private def source {width : Nat} (base : BitVec width) (a : BitVec width) : BitVec 8 :=
  if a=base then 11 else if a=base+1 then 22 else 99
private def target {width : Nat} (base : BitVec width) (a : BitVec width) : BitVec 8 :=
  if a=base then 11 else if a=base+1 then 22 else 44
private def domain {width : Nat} (base : BitVec width) (a : BitVec width) : Prop :=
  a=base ∨ a=base+1
private def state {width : Nat} [NeZero width] (base : BitVec width) : AsmState width :=
  {regs:=fun _=>0,fpRegs:=fun _=>0,mem:=source base,memDomain:=domain base,
   pc:=base,lr:=0,align:=0,be:=false,failed:=false}
example : bytesInMemoryHOL (255 : BitVec 8) [11,22] (source 255) (domain 255) ∧
    bytesInMemoryHOL (255 : BitVec 8) [11,22] (target 255) (domain 255) := by cbv
example : bytesInMemoryHOL (1 : BitVec 1) [11,22] (source 1) (domain 1) ∧
    bytesInMemoryHOL (1 : BitVec 1) [11,22] (target 1) (domain 1) := by cbv
example : bytesInMemoryHOL (-1 : BitVec 64) [11,22] (source (-1)) (domain (-1)) ∧
    bytesInMemoryHOL (-1 : BitVec 64) [11,22] (target (-1)) (domain (-1)) := by cbv <;> simp
example : bytesInMemoryHOL (-1 : BitVec 80) [11,22] (source (-1)) (domain (-1)) ∧
    bytesInMemoryHOL (-1 : BitVec 80) [11,22] (target (-1)) (domain (-1)) := by cbv <;> simp
example : source (255 : BitVec 8) 7 ≠ target (width := 8) 255 7 := by cbv
example : bytesInMemoryHOL (7 : BitVec 8) [] (source 255) (fun _=>False) ∧
    bytesInMemoryHOL (7 : BitVec 8) [] (target 255) (fun _=>False) := by cbv
example : ¬bytesInMemoryHOL (255 : BitVec 8) [11,22] (target 255) (fun a=>a=255) := by cbv
/-- Actual consumer retains arbitrary unrelated machine/projection carriers and
all configuration fields. It discharges source-domain agreement even though
the two memories differ at every address outside the two-byte region. -/
example {machine projection : Type} (mc : MachineConfig 8 machine projection) (ms : machine) :
    bytesInMemoryHOL 255 [11,22]
      ({mc with target:={mc.target with getByte:=fun _=>target 255}}.target.getByte ms)
      (state 255).memDomain := by
  apply bytesInMemory_eqMem 255 [11,22]
    {mc with target:={mc.target with getByte:=fun _=>target 255}} ms (state 255)
  constructor
  · intro a h
    change a=(255 : BitVec 8) ∨ a=255+1 at h
    rcases h with rfl | rfl <;> cbv
  · cbv
end Flapjack.Test.LabToTargetMemoryTransportParity
