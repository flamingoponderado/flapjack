import Flapjack.Compiler.Backend.ClosCall.Proofs.RecClosure
import Flapjack.Compiler.Backend.ClosCall.Proofs.CodeIncludes
import Flapjack.Compiler.Backend.ClosCall.Proofs.GroupClosed
import Flapjack.Compiler.Backend.ClosCall.Proofs.FuelStability
import Flapjack.Compiler.Backend.ClosCall.Stubs

/-! Fuel-aware recursive-closure relation for direct-call conversion. -/
namespace Flapjack.Compiler.Backend.ClosCall
open Flapjack ClosLang ClosProps

/-- A transformed group is closed at each original function's arity. -/
def groupClosed (fns : List (Nat × ClosLang.Exp)) (bodies : List ClosLang.Exp) : Prop :=
  List.Forall₂ (fun fn body => ∀ n, freeVarExp n body → n < fn.1) fns bodies

/-- Locations appearing in the original group, but not known by the
intermediate state, must belong to the permitted set. -/
def groupLocationsCovered (fns : List (Nat × ClosLang.Exp)) (state : State) (allowed : Set Nat) : Prop :=
  ∀ loc ∈ codeLocations (fns.map Prod.snd), ¬ sptDomain state.1 loc → loc ∈ allowed

/-- Fuel-aware form of the recursive-closure relation. Both alternatives
follow the source relation: closed groups use stubs and extracted code; open
groups rerun the bodies from the original state. This is not tagged as the
HOL relation because it uses the bounded executable traversal, whose full
correspondence with HOL's total `calls` remains open. -/
def recClosureRelFuel (fuel : Nat) (g : State) (allowed : Set Nat)
    (code : HolFiniteMapExact Nat (Nat × ClosLang.Exp)) (loc : Nat)
    (fns1 fns2 : List (Nat × ClosLang.Exp)) : Prop :=
  ∃ g0 : State,
    recClosureWellFormed loc fns1 ∧ wellFormed g0 ∧
    (∀ k ∈ codeLocations (fns1.map Prod.snd), k + 1 ∉ g0.2.map Prod.fst) ∧
    (∀ i, i < fns1.length → 2 * i + loc + 1 ∉ g0.2.map Prod.fst) ∧
    ∃ bodies afterProbe,
      callsListBounded fuel (fns1.map Prod.snd) (insertEach loc fns1.length g0) =
        some (bodies, afterProbe) ∧
      ((groupClosed fns1 bodies ∧
        (∃ trace index, fns2 = callsListSource trace index loc fns1) ∧
        stateExtends (codeList loc ((fns1.map Prod.fst).zip bodies) afterProbe) g ∧
        groupLocationsCovered fns1 afterProbe allowed ∧
        codeIncludes (codeList loc ((fns1.map Prod.fst).zip bodies) afterProbe).2 code) ∨
       (¬ groupClosed fns1 bodies ∧
        ∃ openBodies afterOpen,
          callsListBounded fuel (fns1.map Prod.snd) g0 = some (openBodies, afterOpen) ∧
          fns2 = (fns1.map Prod.fst).zip openBodies ∧ stateExtends afterOpen g ∧
          groupLocationsCovered fns1 afterOpen allowed ∧
          (∀ i, i < fns1.length → 2 * i + loc ∈ allowed) ∧
          codeIncludes afterOpen.2 code))

/-- The recursive-closure relation is independent of its traversal fuel:
both bounded traversals return the same result at every initial fuel. This is
Flapjack-specific infrastructure; correspondence with HOL remains open. -/
theorem recClosureRelFuel_independent (left right : Nat) (g : State) (allowed : Set Nat)
    (code : HolFiniteMapExact Nat (Nat × ClosLang.Exp)) (loc : Nat) (fns1 fns2 : List (Nat × ClosLang.Exp)) :
    recClosureRelFuel left g allowed code loc fns1 fns2 ↔
      recClosureRelFuel right g allowed code loc fns1 fns2 := by
  simp only [recClosureRelFuel, callsListBounded_independent left right]

/-- A related recursive closure has one target function for every source
function, in both the extracted and non-extracted cases. -/
theorem recClosureRelFuel_length (fuel : Nat) (g : State) (allowed : Set Nat)
    (code : HolFiniteMapExact Nat (Nat × ClosLang.Exp)) (loc : Nat) (fns1 fns2 : List (Nat × ClosLang.Exp))
    (related : recClosureRelFuel fuel g allowed code loc fns1 fns2) : fns2.length = fns1.length := by
  obtain ⟨g0, _, _, _, _, bodies, afterProbe, probe, alternatives⟩ := related
  rcases alternatives with ⟨_, ⟨trace, index, rfl⟩, _⟩ |
      ⟨_, openBodies, afterOpen, openRun, rfl, _⟩
  · rw [callsListSource_eq_range]
    simp [List.length_zip]
  · have length := callsListBounded_length fuel (fns1.map Prod.snd) g0 afterOpen openBodies openRun
    simp only [List.length_map] at length
    simp [List.length_zip, length]

/-- A related singleton group remains a singleton with the original arity.
This is a bounded-traversal counterpart of the shape fact used to construct
a related ordinary closure. -/
theorem recClosureRelFuel_singleton (fuel : Nat) (g : State) (allowed : Set Nat)
    (code : HolFiniteMapExact Nat (Nat × ClosLang.Exp)) (loc arity : Nat)
    (body : ClosLang.Exp) (targets : List (Nat × ClosLang.Exp))
    (related : recClosureRelFuel fuel g allowed code loc [(arity, body)] targets) :
    ∃ targetBody, targets = [(arity, targetBody)] := by
  obtain ⟨g0, _, _, _, _, bodies, afterProbe, _, alternatives⟩ := related
  rcases alternatives with ⟨_, ⟨trace, index, targetEq⟩, _⟩ |
      ⟨_, openBodies, afterOpen, openRun, targetEq, _⟩
  · exact ⟨_, by simpa [callsListSource] using targetEq⟩
  · have length := callsListBounded_length fuel ([(arity, body)].map Prod.snd) g0 afterOpen openBodies openRun
    have size : openBodies.length = 1 := by simpa using length
    cases openBodies with
    | nil => simp at size
    | cons first rest =>
      cases rest with
      | nil => exact ⟨first, by simpa using targetEq⟩
      | cons second rest => simp at size

/-- The relation's two alternatives agree with the actual executable
recursive-group closedness decision. -/
theorem recClosureRelFuel_executableCases (fuel : Nat) (g : State) (allowed : Set Nat)
    (code : HolFiniteMapExact Nat (Nat × ClosLang.Exp)) (loc : Nat)
    (fns1 fns2 : List (Nat × ClosLang.Exp))
    (related : recClosureRelFuel fuel g allowed code loc fns1 fns2) :
    ∃ g0 bodies afterProbe,
      callsListBounded fuel (fns1.map Prod.snd) (insertEach loc fns1.length g0) =
        some (bodies, afterProbe) ∧
      ((groupClosedFuel fuel fns1 bodies = some true ∧
        ∃ trace index, fns2 = callsListSource trace index loc fns1) ∨
       (groupClosedFuel fuel fns1 bodies = some false ∧
        ∃ openBodies afterOpen,
          callsListBounded fuel (fns1.map Prod.snd) g0 = some (openBodies, afterOpen) ∧
          fns2 = (fns1.map Prod.fst).zip openBodies)) := by
  obtain ⟨g0, _, _, _, _, bodies, afterProbe, probe, alternatives⟩ := related
  have length : fns1.length = bodies.length := by
    have h := callsListBounded_length fuel (fns1.map Prod.snd)
      (insertEach loc fns1.length g0) afterProbe bodies probe
    simpa using h.symm
  refine ⟨g0, bodies, afterProbe, probe, ?_⟩
  rcases alternatives with ⟨closed, target, _⟩ | ⟨notClosed, openBodies, afterOpen, run, target, _⟩
  · exact Or.inl ⟨(groupClosedFuel_iff fuel fns1 bodies length).mpr closed, target⟩
  · exact Or.inr ⟨(groupClosedFuel_false_iff fuel fns1 bodies length).mpr notClosed,
      openBodies, afterOpen, run, target⟩

/-- Extending compiler state, permitted locations and installed code
preserves the fuel-aware recursive-closure relation. -/
theorem recClosureRelFuel_mono (fuel : Nat) (g g' : State) (allowed allowed' : Set Nat)
    (code code' : HolFiniteMapExact Nat (Nat × ClosLang.Exp)) (loc : Nat)
    (fns1 fns2 : List (Nat × ClosLang.Exp))
    (related : recClosureRelFuel fuel g allowed code loc fns1 fns2)
    (stateGrowth : stateExtends g g') (allowedGrowth : allowed ⊆ allowed')
    (codeGrowth : ∀ key value, code.lookup key = some value → code'.lookup key = some value) :
    recClosureRelFuel fuel g' allowed' code' loc fns1 fns2 := by
  obtain ⟨g0, wf, well, nestedFresh, ownFresh, bodies, afterProbe, probe, alternatives⟩ := related
  refine ⟨g0, wf, well, nestedFresh, ownFresh, bodies, afterProbe, probe, ?_⟩
  rcases alternatives with ⟨closed, target, stateRel, covered, included⟩ |
      ⟨notClosed, openBodies, afterOpen, run, target, stateRel, covered, ownAllowed, included⟩
  · left
    refine ⟨closed, target, stateExtends_trans _ _ _ stateRel stateGrowth, ?_, ?_⟩
    · intro k member notKnown
      exact allowedGrowth (covered k member notKnown)
    · exact codeIncludes_mono _ code code' codeGrowth included
  · right
    refine ⟨notClosed, openBodies, afterOpen, run, target,
      stateExtends_trans _ _ _ stateRel stateGrowth, ?_, ?_, ?_⟩
    · intro k member notKnown
      exact allowedGrowth (covered k member notKnown)
    · intro i bound
      exact allowedGrowth (ownAllowed i bound)
    · exact codeIncludes_mono _ code code' codeGrowth included

end Flapjack.Compiler.Backend.ClosCall
