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

/-- Retrying the list traversal preserves the origin property for every
newly known location. -/
theorem callsListBounded_knownBound (fuel : Nat) (es : List ClosLang.Exp) (initial final : State)
    (out : List ClosLang.Exp) (run : callsListBounded fuel es initial = some (out, final)) :
    KnownBound initial final := by
  unfold callsListBounded at run
  cases first : callsListFuel fuel es initial with
  | some result =>
    simp only [first, Option.some.injEq] at run
    subst result
    exact callsListFuel_knownBound fuel es initial final out first
  | none =>
    simp only [first] at run
    exact callsListFuel_knownBound _ es initial final out run

/-- Reattach previously generated code to an incremental result. Distinct
and fresh source locations ensure the combined compiler state remains well
formed and extends the previous one. -/
theorem compileIncFuel_merge_state (fuel : Nat) (known : NumSet)
    (oldCode : List (Nat × Nat × ClosLang.Exp)) (program : ClosSem.Program)
    (nextKnown : NumSet) (converted : ClosSem.Program)
    (run : compileIncFuel? fuel known program = some (nextKnown, converted))
    (oldWell : wellFormed (known, oldCode))
    (distinct : (codeLocations program.1).Nodup)
    (fresh : LabelsFresh (codeLocations program.1) (known, oldCode)) :
    wellFormed (nextKnown, converted.2 ++ oldCode) ∧
      stateExtends (known, oldCode) (nextKnown, converted.2 ++ oldCode) := by
  have traversal := compileIncFuel_traversal fuel known program nextKnown converted run
  have generated := compileIncFuel_generated fuel known program nextKnown converted run distinct
  have origins := callsListBounded_knownBound fuel program.1 (known, []) (nextKnown, converted.2)
    converted.1 traversal
  have weak := callsListBounded_weaklyWellFormed fuel program.1 (known, []) (nextKnown, converted.2)
    converted.1 traversal (by simp [weaklyWellFormed])
  have extension := callsListBounded_stateExtends fuel program.1 (known, []) (nextKnown, converted.2)
    converted.1 traversal distinct (by simp [LabelsFresh]) (by simp)
  have separate : ∀ label ∈ converted.2.map Prod.fst, label ∉ oldCode.map Prod.fst := by
    intro label member
    obtain ⟨loc, locMember, rfl⟩ := generated.2.1 label member
    exact fresh loc locMember
  have combinedDistinct : ((converted.2 ++ oldCode).map Prod.fst).Nodup := by
    simp only [List.map_append]
    apply List.nodup_append.mpr
    refine ⟨generated.1, oldWell.2, ?_⟩
    intro a inNew b inOld equal
    subst b
    exact separate a inNew inOld
  have combinedWell : wellFormed (nextKnown, converted.2 ++ oldCode) := by
    constructor
    · apply Set.Subset.antisymm
      · intro label member
        simp only [Set.mem_ofPred_eq, List.map_append, List.mem_append] at member
        cases member with
        | inl new => exact weak new
        | inr old =>
          have oldImage : label ∈ Set.image Nat.succ (sptDomain known) := by
            rw [← oldWell.1]
            exact old
          obtain ⟨loc, knownLoc, rfl⟩ := oldImage
          exact ⟨loc, generated.2.2 loc knownLoc, rfl⟩
      · intro label member
        obtain ⟨loc, knownLoc, rfl⟩ := member
        simp only [Set.mem_ofPred_eq, List.map_append, List.mem_append]
        rcases origins loc knownLoc with old | new
        · right
          have oldImage : loc + 1 ∈ Set.image Nat.succ (sptDomain known) := ⟨loc, old, by omega⟩
          rw [← oldWell.1] at oldImage
          simpa using oldImage
        · left
          simpa using new
    · exact combinedDistinct
  refine ⟨combinedWell, extension.1, ?_, combinedDistinct⟩
  intro key value lookup
  rw [logicalAssocLookup_nat] at lookup ⊢
  have member := sptAListLookup_mem key oldCode value lookup
  have inCombined : (key, value) ∈ converted.2 ++ oldCode := List.mem_append_right _ member
  apply sptAListLookup_eq_of_mem_unique key value (converted.2 ++ oldCode) inCombined
  intro other otherMember
  have injective := (List.nodup_map_iff_inj_on (List.Nodup.of_map Prod.fst combinedDistinct)).mp combinedDistinct
  have eq : (key, other) = (key, value) := injective _ otherMember _ inCombined rfl
  exact congrArg Prod.snd eq

/-- Installing a list with distinct keys makes every listed binding
available in the resulting finite map. -/
theorem lookup_updateListEq_of_mem_unique {V : Type} (code : HolFiniteMapExact Nat V)
    (entries : List (Nat × V)) (distinct : (entries.map Prod.fst).Nodup)
    (key : Nat) (value : V) (member : (key, value) ∈ entries) :
    (code.updateListEq entries).lookup key = some value := by
  induction entries generalizing code with
  | nil => simp at member
  | cons entry entries ih =>
    obtain ⟨label, item⟩ := entry
    simp only [List.map_cons, List.nodup_cons] at distinct
    simp only [List.mem_cons] at member
    cases member with
    | inl eq =>
      cases eq
      rw [HolFiniteMapExact.lookup_updateListEq, FUPDATE_LIST_HOL_cons]
      have same := FLOOKUP_FUPDATE_LIST_HOL_not_mem (FUPDATE_HOL code.lookup (key, value)) entries key distinct.1
      change FUPDATE_LIST_HOL (FUPDATE_HOL code.lookup (key, value)) entries key =
        FUPDATE_HOL code.lookup (key, value) key at same
      rw [same]
      simp [FUPDATE_HOL]
    | inr later =>
      have next := ih (code.updateEq (label, item)) distinct.2 later
      have updated : (code.updateEq (label, item)).lookup =
          FUPDATE_HOL code.lookup (label, item) := by
        funext k
        exact HolFiniteMapExact.lookup_updateEq code (label, item) k
      simpa only [HolFiniteMapExact.lookup_updateListEq, FUPDATE_LIST_HOL_cons,
        updated] using next

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
