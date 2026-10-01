import Flapjack.Compiler.Backend.LabToTarget.Memory

/-! Eleven kernel replays of fresh original miscTheory EVAL observations in
scripts/hol-probes/bytes_in_mem_probe.out. Nat and Bool payloads retain the
original polymorphic β. Width two exercises 3→0 wraparound; both domain and
excluded-set failure positions are covered. These finite rows do not prove
cross-language equivalence or full compiler correctness. -/
namespace Flapjack.Test.BytesInMemParity
open Flapjack Flapjack.Compiler.Backend.LabToTarget
private def memory (a : BitVec 2) : Nat := if a = 3 then 7 else if a = 0 then 9 else 0

-- empty_ignores_guards=T
example : bytesInMemHOL 0 ([] : List Nat) memory (fun _ => False) (fun _ => True) := by
  simp [bytesInMemHOL]
-- nat_wrap=T
example : bytesInMemHOL 3 [7, 9] memory (fun _ => True) (fun _ => False) := by
  simp [bytesInMemHOL, memory]
-- excluded_head=F
example : ¬bytesInMemHOL 3 [7, 9] memory (fun _ => True) (fun a => a = 3) := by
  simp [bytesInMemHOL, memory]
-- excluded_tail=F
example : ¬bytesInMemHOL 3 [7, 9] memory (fun _ => True) (fun a => a = 0) := by
  simp [bytesInMemHOL, memory]
-- domain_head=F
example : ¬bytesInMemHOL 3 [7, 9] memory (fun a => a ≠ 3) (fun _ => False) := by
  simp [bytesInMemHOL, memory]
-- domain_tail=F
example : ¬bytesInMemHOL 3 [7, 9] memory (fun a => a ≠ 0) (fun _ => False) := by
  simp [bytesInMemHOL, memory]
-- wrong_value=F
example : ¬bytesInMemHOL 3 [7, 8] memory (fun _ => True) (fun _ => False) := by
  simp [bytesInMemHOL, memory]
-- bool_payload=T
example : bytesInMemHOL (3 : BitVec 2) [true, false] (fun a => a == 3)
    (fun _ => True) (fun _ => False) := by
  simp [bytesInMemHOL]
-- update_off_region=T
example : bytesInMemHOL 3 [7, 9] (fun a => if a = 1 then 88 else memory a)
    (fun _ => True) (fun _ => False) := by
  simp [bytesInMemHOL, memory]
-- update_hit_region=F
example : ¬bytesInMemHOL 3 [7, 9] (fun a => if a = 0 then 88 else memory a)
    (fun _ => True) (fun _ => False) := by
  simp [bytesInMemHOL, memory]
-- append_wrapped=T
example : bytesInMemHOL 3 [7] memory (fun _ => True) (fun _ => False) ∧
    bytesInMemHOL ((3 : BitVec 2) + BitVec.ofNat 2 1) [9] memory
      (fun _ => True) (fun _ => False) := by
  simp [bytesInMemHOL, memory]

def runChecks : IO Bool := do
  IO.println "PASS original bytes_in_mem generic payload/domain/exclusion/wrap/update rows (11 kernel replays)"
  pure true
end Flapjack.Test.BytesInMemParity
