import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSARenameLookup
namespace Flapjack.Test.SSARenameLookupParity
open Flapjack Flapjack.Compiler.Backend.WordAlloc
private def observe (names : List Nat) (ssa : Spt Nat) (next : Nat) (keys : List Nat) :=
  let r := listNextVarRename names ssa next
  (r.1, names.map (fun key => (sptLookup key r.2.1).getD 0),
    keys.map (fun key => sptLookup key r.2.1), r.2.2)
-- Full observations of the same inputs as the freshly run original probe.
example : observe [] (sptFromAList [(9,99)]) 5 [0,1,2,9] =
  ([],[],[none,none,none,some 99],5) := by decide +kernel
example : observe [1,2] (sptFromAList [(9,99),(1,88)]) 5 [0,1,2,9] =
  ([5,9],[5,9],[none,some 5,some 9,some 99],13) := by decide +kernel
example : observe [0,4] (.bn .ln .ln) 0 [0,1,4] =
  ([0,4],[0,4],[some 0,none,some 4],8) := by decide +kernel
example : observe [4,0,2] (sptFromAList [(9,99)]) 101 [0,2,4,9] =
  ([101,105,109],[101,105,109],[some 105,some 109,some 101,some 99],113) := by decide +kernel
example : observe [18446744073709551616,3] .ln 18446744073709551616
    [0,3,18446744073709551616] =
  ([18446744073709551616,18446744073709551620],
   [18446744073709551616,18446744073709551620],
   [none,some 18446744073709551620,some 18446744073709551616],18446744073709551624) := by decide +kernel
-- Actual theorem application retains every conjunct and arbitrary initial tree/start.
example (ssa : Spt Nat) (next : Nat) :
    let r := listNextVarRename [4,0,2] ssa next
    r.1 = [4,0,2].map (fun key => (sptLookup key r.2.1).getD 0) ∧
    sptDomain r.2.1 = (fun key => sptDomain ssa key ∨ key ∈ ([4,0,2] : List Nat)) ∧
    (∀ key, key ∉ ([4,0,2] : List Nat) → sptLookup key r.2.1 = sptLookup key ssa) ∧
    (∀ key, key ∈ ([4,0,2] : List Nat) → ∃ value, sptLookup key r.2.1 = some value) :=
  listNextVarRenameLemma2 [4,0,2] ssa next (by decide)
-- Changing the NONE default to 999 cannot affect the mapped names.
example (names : List Nat) (ssa : Spt Nat) (next : Nat) (distinct : names.Nodup) :
    (listNextVarRename names ssa next).1 =
      names.map (fun key => (sptLookup key (listNextVarRename names ssa next).2.1).getD 999) :=
  listNextVarRenameSelectorIndependent names ssa next distinct (fun value => value.getD 999)
    (fun _ => rfl)
-- Result-equality specialization retains arbitrary outputs and all four conclusions.
example (names outputNames : List Nat) (ssa outputMap : Spt Nat)
    (next outputNext : Nat)
    (result : listNextVarRename names ssa next = (outputNames, outputMap, outputNext))
    (distinct : names.Nodup) :
    outputNames = names.map (fun key => (sptLookup key outputMap).getD 0) ∧
    sptDomain outputMap = (fun key => sptDomain ssa key ∨ key ∈ names) ∧
    (∀ key, key ∉ names → sptLookup key outputMap = sptLookup key ssa) ∧
    (∀ key, key ∈ names → ∃ value, sptLookup key outputMap = some value) :=
  listNextVarRenameLemma2Prime names ssa next outputNames outputMap outputNext result distinct

end Flapjack.Test.SSARenameLookupParity
