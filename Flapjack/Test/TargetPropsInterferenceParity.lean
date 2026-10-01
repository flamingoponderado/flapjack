import Flapjack.Compiler.Backend.LabToTarget.Interference

namespace Flapjack.Test.TargetPropsInterferenceParity
open Flapjack Flapjack.Compiler.Backend.Semantics.TargetProps

-- Original-source HOL observations; unspecified machine fields are never read.
example (c : MachineConfig 8 Nat Unit) :
    (shiftInterfer 0 { c with nextInterfer := fun i s => i + s }).nextInterfer 2 7 = 9 := rfl
example (c : MachineConfig 8 Nat Unit) :
    (shiftInterfer 3 { c with nextInterfer := fun i s => i + s }).nextInterfer 2 7 = 12 := rfl
example (c : MachineConfig 8 Nat Unit) :
    (shiftInterfer 4 (shiftInterfer 3 { c with nextInterfer := fun i s => i + s })).nextInterfer 2 7 = 16 := rfl
example (c : MachineConfig 8 Nat Unit) :
    (shiftInterfer 3 { c with ffiInterfer := fun i (n, _, s) => i + n + s }).ffiInterfer 2 (4, [], 7) = 13 := rfl
example (c : MachineConfig 8 Nat Unit) : (shiftInterfer 3 c).target = c.target := rfl
example (c : MachineConfig 8 Nat Unit) (s : AsmState 8) :
    ffiEntryPcsDisjoint { c with ffiEntryPcs := [0, 0] } { s with pc := 254 } 0 := by
  simp [ffiEntryPcsDisjoint]
example (c : MachineConfig 8 Nat Unit) (s : AsmState 8) :
    ffiEntryPcsDisjoint { c with ffiEntryPcs := [0, 0] } { s with pc := 254 } 2 := by
  rintro address ⟨haddr, n, hn, heq⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, or_self] at haddr
  have heq0 : (0 : BitVec 8) = 254 + BitVec.ofNat 8 n := by
    simpa [haddr] using heq
  have hn : n = 0 ∨ n = 1 := by omega
  rcases hn with rfl | rfl
  · exact (by decide : (0 : BitVec 8) ≠ 254 + BitVec.ofNat 8 0) heq0
  · exact (by decide : (0 : BitVec 8) ≠ 254 + BitVec.ofNat 8 1) heq0
example (c : MachineConfig 8 Nat Unit) (s : AsmState 8) :
    ¬ ffiEntryPcsDisjoint { c with ffiEntryPcs := [0, 0] } { s with pc := 254 } 3 := by
  intro h
  exact h 0 ⟨by simp, 2, by decide, by change (0 : BitVec 8) = 254 + 2; decide⟩

def runChecks : IO Bool := do
  IO.println "PASS original-source machine oracle shifts and wrapped FFI regions (8 kernel replays)"
  return true
end Flapjack.Test.TargetPropsInterferenceParity
