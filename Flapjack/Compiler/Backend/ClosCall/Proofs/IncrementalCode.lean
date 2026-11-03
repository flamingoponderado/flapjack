import Flapjack.Compiler.Backend.ClosCall.Proofs.IncrementalOracle
import Flapjack.Compiler.Backend.ClosCall.Proofs.KnownOrigins
import Flapjack.Compiler.Backend.ClosCall.Proofs.StateExtension

/-! Generated-code properties of incremental direct-call compilation. -/
namespace Flapjack.Compiler.Backend.ClosCall
open Flapjack ClosLang ClosProps

/-- A successful production incremental step exposes its underlying list
traversal and final compiler state. Incoming auxiliary code is discarded. -/
theorem compileIncFuel_traversal (fuel : Nat) (known : NumSet) (program : ClosSem.Program)
    (nextKnown : NumSet) (converted : ClosSem.Program)
    (run : compileIncFuel? fuel known program = some (nextKnown, converted)) :
    callsListBounded fuel program.1 (known, []) = some (converted.1, (nextKnown, converted.2)) := by
  simp only [compileIncFuel?, Bind.bind, Option.bind_eq_some_iff, Pure.pure,
    Option.some.injEq, Prod.mk.injEq] at run
  obtain ⟨⟨expressions, ⟨finalKnown, auxiliary⟩⟩, traversal, rfl, rfl⟩ := run
  exact traversal

/-- Generated labels originate at source closure locations, are distinct
when those locations are distinct, and the known-location set only grows.
These are properties of the executed bounded pass, not a HOL equivalence proof. -/
theorem compileIncFuel_generated (fuel : Nat) (known : NumSet) (program : ClosSem.Program)
    (nextKnown : NumSet) (converted : ClosSem.Program)
    (run : compileIncFuel? fuel known program = some (nextKnown, converted))
    (distinct : (codeLocations program.1).Nodup) :
    (converted.2.map Prod.fst).Nodup ∧
      (∀ label ∈ converted.2.map Prod.fst, ∃ loc ∈ codeLocations program.1, label = loc + 1) ∧
      (∀ loc, sptDomain known loc → sptDomain nextKnown loc) := by
  have traversal := compileIncFuel_traversal fuel known program nextKnown converted run
  have fresh : LabelsFresh (codeLocations program.1) (known, []) := by simp [LabelsFresh]
  have nodup := callsListBounded_labelsDistinct fuel program.1 (known, []) (nextKnown, converted.2)
    converted.1 traversal distinct fresh (by simp)
  have bound := callsListBounded_labelsBound fuel program.1 (known, []) (nextKnown, converted.2)
    converted.1 traversal
  have knownExt := callsListBounded_knownExt fuel program.1 (known, []) (nextKnown, converted.2)
    converted.1 traversal
  refine ⟨nodup, ?_, knownExt⟩
  intro label member
  rcases bound label member with old | new
  · simp at old
  · exact new

/-- If old target code is absent at successors of the source locations, the
new auxiliary labels are disjoint from that code. -/
theorem compileIncFuel_generated_fresh (fuel : Nat) (known : NumSet) (program : ClosSem.Program)
    (nextKnown : NumSet) (converted : ClosSem.Program)
    (oldCode : HolFiniteMapExact Nat (Nat × ClosLang.Exp))
    (run : compileIncFuel? fuel known program = some (nextKnown, converted))
    (fresh : ∀ loc ∈ codeLocations program.1, oldCode.lookup (loc + 1) = none) :
    ∀ label ∈ converted.2.map Prod.fst, oldCode.lookup label = none := by
  have traversal := compileIncFuel_traversal fuel known program nextKnown converted run
  have bound := callsListBounded_labelsBound fuel program.1 (known, []) (nextKnown, converted.2)
    converted.1 traversal
  intro label member
  rcases bound label member with old | ⟨loc, sourceMember, rfl⟩
  · simp at old
  · exact fresh loc sourceMember

/-- Installing fresh generated auxiliary code preserves every existing
target-code lookup. -/
theorem compileIncFuel_install_preserves (fuel : Nat) (known : NumSet) (program : ClosSem.Program)
    (nextKnown : NumSet) (converted : ClosSem.Program)
    (oldCode : HolFiniteMapExact Nat (Nat × ClosLang.Exp))
    (run : compileIncFuel? fuel known program = some (nextKnown, converted))
    (fresh : ∀ loc ∈ codeLocations program.1, oldCode.lookup (loc + 1) = none) :
    ∀ label entry, oldCode.lookup label = some entry →
      (oldCode.updateListEq converted.2).lookup label = some entry := by
  intro label entry found
  have absent : label ∉ converted.2.map Prod.fst := by
    intro member
    have missing := compileIncFuel_generated_fresh fuel known program nextKnown converted oldCode run fresh label member
    rw [found] at missing
    contradiction
  rw [HolFiniteMapExact.lookup_updateListEq]
  have same := FLOOKUP_FUPDATE_LIST_HOL_not_mem oldCode.lookup converted.2 label absent
  simpa [FLOOKUP] using same.trans found

/-- Installing one incremental result preserves freshness for a later program
whose closure locations are disjoint from the current program's locations. -/
theorem compileIncFuel_install_preserves_future_fresh (fuel : Nat) (known : NumSet)
    (program future : ClosSem.Program) (nextKnown : NumSet) (converted : ClosSem.Program)
    (oldCode : HolFiniteMapExact Nat (Nat × ClosLang.Exp))
    (run : compileIncFuel? fuel known program = some (nextKnown, converted))
    (futureFresh : ∀ loc ∈ codeLocations future.1, oldCode.lookup (loc + 1) = none)
    (disjoint : ∀ loc ∈ codeLocations future.1, loc ∉ codeLocations program.1) :
    ∀ loc ∈ codeLocations future.1, (oldCode.updateListEq converted.2).lookup (loc + 1) = none := by
  have traversal := compileIncFuel_traversal fuel known program nextKnown converted run
  have bound := callsListBounded_labelsBound fuel program.1 (known, []) (nextKnown, converted.2)
    converted.1 traversal
  intro loc member
  have absent : loc + 1 ∉ converted.2.map Prod.fst := by
    intro labelMember
    rcases bound (loc + 1) labelMember with old | ⟨original, originalMember, eq⟩
    · simp at old
    · have same : loc = original := by omega
      subst original
      exact disjoint loc member originalMember
  rw [HolFiniteMapExact.lookup_updateListEq]
  have same := FLOOKUP_FUPDATE_LIST_HOL_not_mem oldCode.lookup converted.2 (loc + 1) absent
  simpa [FLOOKUP] using same.trans (futureFresh loc member)

/-- Every transformed oracle entry has distinct auxiliary labels and
preserves the current target code when its source locations are distinct and
fresh. The changing-code invariant across multiple entries remains a separate
induction obligation. -/
theorem compileIncFuelOracle_generated {C : Type} (fuel : Nat)
    (oracle : ClosSem.CompileOracle (NumSet × C)) (index : Nat)
    (oldCode : HolFiniteMapExact Nat (Nat × ClosLang.Exp))
    (distinct : (codeLocations (oracle index).2.1).Nodup)
    (fresh : ∀ loc ∈ codeLocations (oracle index).2.1, oldCode.lookup (loc + 1) = none) :
    ∃ nextKnown,
      compileIncFuel? fuel (oracle index).1.1 (oracle index).2 =
        some (nextKnown, (compileIncFuelOracle fuel oracle index).2) ∧
      (((compileIncFuelOracle fuel oracle index).2.2).map Prod.fst).Nodup ∧
      (∀ loc, sptDomain (oracle index).1.1 loc → sptDomain nextKnown loc) ∧
      (∀ label entry, oldCode.lookup label = some entry →
        (oldCode.updateListEq (compileIncFuelOracle fuel oracle index).2.2).lookup label = some entry) := by
  obtain ⟨nextKnown, run, _⟩ := compileIncFuelOracle_entry fuel oracle index
  have generated := compileIncFuel_generated fuel (oracle index).1.1 (oracle index).2 nextKnown
    (compileIncFuelOracle fuel oracle index).2 run distinct
  exact ⟨nextKnown, run, generated.1, generated.2.2,
    compileIncFuel_install_preserves fuel (oracle index).1.1 (oracle index).2 nextKnown
      (compileIncFuelOracle fuel oracle index).2 oldCode run fresh⟩

/-- Installing the current oracle entry preserves freshness for every later
entry when their source closure locations are pairwise disjoint. -/
theorem compileIncFuelOracle_preserves_later_fresh {C : Type} (fuel : Nat)
    (oracle : ClosSem.CompileOracle (NumSet × C)) (index : Nat)
    (oldCode : HolFiniteMapExact Nat (Nat × ClosLang.Exp))
    (fresh : ∀ later, index < later → ∀ loc ∈ codeLocations (oracle later).2.1,
      oldCode.lookup (loc + 1) = none)
    (disjoint : ∀ later, index < later → ∀ loc ∈ codeLocations (oracle later).2.1,
      loc ∉ codeLocations (oracle index).2.1) :
    ∀ later, index < later → ∀ loc ∈ codeLocations (oracle later).2.1,
      (oldCode.updateListEq (compileIncFuelOracle fuel oracle index).2.2).lookup (loc + 1) = none := by
  obtain ⟨nextKnown, run, _⟩ := compileIncFuelOracle_entry fuel oracle index
  intro later order
  exact compileIncFuel_install_preserves_future_fresh fuel (oracle index).1.1 (oracle index).2
    (oracle later).2 nextKnown (compileIncFuelOracle fuel oracle index).2 oldCode run
      (fresh later order) (disjoint later order)

end Flapjack.Compiler.Backend.ClosCall
