module

public import Flapjack.Compiler.Backend.ClosCall.Proofs.RecClosure
public import Flapjack.Compiler.Backend.ClosCall.Proofs.CodeIncludes
public import Flapjack.Compiler.Backend.ClosCall.Proofs.GroupClosed
public import Flapjack.Compiler.Backend.ClosCall.Proofs.FuelStability
public import Flapjack.Compiler.Backend.ClosCall.Proofs.TraversalLookup
public import Flapjack.Compiler.Backend.ClosCall.Stubs

@[expose] public section

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

/-- A related group remains related when the compiler state grows and its
entire code list is installed in a new code map. This Flapjack-specific
retargeting does not require unrelated old map entries to be preserved. -/
theorem recClosureRelFuel_retarget (fuel : Nat) (g g' : State) (allowed : Set Nat)
    (code code' : HolFiniteMapExact Nat (Nat × ClosLang.Exp)) (loc : Nat)
    (fns1 fns2 : List (Nat × ClosLang.Exp))
    (related : recClosureRelFuel fuel g allowed code loc fns1 fns2)
    (growth : stateExtends g g') (included : codeIncludes g'.2 code') :
    recClosureRelFuel fuel g' allowed code' loc fns1 fns2 := by
  obtain ⟨g0, well, initialWf, nestedFresh, ownFresh, bodies, afterProbe, probe, alternatives⟩ := related
  refine ⟨g0, well, initialWf, nestedFresh, ownFresh, bodies, afterProbe, probe, ?_⟩
  rcases alternatives with ⟨closed, target, ext, covered, _⟩ |
      ⟨notClosed, openBodies, afterOpen, run, target, ext, covered, ownAllowed, _⟩
  · left
    have combined := stateExtends_trans _ _ _ ext growth
    exact ⟨closed, target, combined, covered, codeIncludes_of_stateExtends _ _ code' combined included⟩
  · right
    have combined := stateExtends_trans _ _ _ ext growth
    exact ⟨notClosed, openBodies, afterOpen, run, target, combined, covered, ownAllowed,
      codeIncludes_of_stateExtends _ _ code' combined included⟩

/-- The recursive-closure relation is independent of its traversal fuel:
both bounded traversals return the same result at every initial fuel. This is
Flapjack-specific infrastructure; correspondence with HOL remains open. -/
theorem recClosureRelFuel_independent (left right : Nat) (g : State) (allowed : Set Nat)
    (code : HolFiniteMapExact Nat (Nat × ClosLang.Exp)) (loc : Nat) (fns1 fns2 : List (Nat × ClosLang.Exp)) :
    recClosureRelFuel left g allowed code loc fns1 fns2 ↔
      recClosureRelFuel right g allowed code loc fns1 fns2 := by
  simp only [recClosureRelFuel, callsListBounded_independent left right]

/-- A selected recursive function has an actual transformed probe body and
single-expression traversal. The probe's initially reserved locations need
not form a fully well-formed state. This is Flapjack-specific infrastructure
for relating closure bodies to the bounded traversal. -/
theorem recClosureRelFuel_probe_body (fuel : Nat) (g : State) (allowed : Set Nat)
    (code : HolFiniteMapExact Nat (Nat × ClosLang.Exp)) (loc : Nat)
    (fns1 fns2 : List (Nat × ClosLang.Exp)) (index arity : Nat) (body : ClosLang.Exp)
    (related : recClosureRelFuel fuel g allowed code loc fns1 fns2)
    (sourceLookup : fns1[index]? = some (arity, body)) :
    ∃ g0 bodies afterProbe transformed depth before after,
      wellFormed g0 ∧ LabelsFresh (codeLocations (fns1.map Prod.snd)) g0 ∧
      callsListBounded fuel (fns1.map Prod.snd) (insertEach loc fns1.length g0) = some (bodies, afterProbe) ∧
      bodies[index]? = some transformed ∧
      depth < max fuel (listBudget (fns1.map Prod.snd) + 1) ∧
      callsFuel depth body before = some (transformed, after) ∧
      (codeLocationsExp body).Nodup ∧ LabelsFresh (codeLocationsExp body) before ∧
      (before.2.map Prod.fst).Nodup ∧ weaklyWellFormed before ∧
      (∀ k ∈ codeLocationsExp body, sptDomain before.1 k → k + 1 ∈ before.2.map Prod.fst) ∧
      stateExtends before afterProbe ∧ stateExtends after afterProbe ∧
      ((groupClosed fns1 bodies ∧
        (∃ trace stubIndex, fns2 = callsListSource trace stubIndex loc fns1) ∧
        stateExtends afterProbe g ∧
        stateExtends (codeList loc ((fns1.map Prod.fst).zip bodies) afterProbe) g ∧
        groupLocationsCovered fns1 afterProbe allowed ∧
        codeIncludes (codeList loc ((fns1.map Prod.fst).zip bodies) afterProbe).2 code) ∨
       (¬ groupClosed fns1 bodies ∧
        ∃ openBodies afterOpen,
          callsListBounded fuel (fns1.map Prod.snd) g0 = some (openBodies, afterOpen) ∧
          fns2 = (fns1.map Prod.fst).zip openBodies ∧ stateExtends afterOpen g ∧
          groupLocationsCovered fns1 afterOpen allowed ∧
          (∀ i, i < fns1.length → 2 * i + loc ∈ allowed) ∧
          codeIncludes afterOpen.2 code)) := by
  obtain ⟨g0, well, initialWf, nestedFresh, ownFresh, bodies, afterProbe, probe, alternatives⟩ := related
  have sourceIndex : (fns1.map Prod.snd)[index]? = some body := by
    simp [List.getElem?_map, sourceLookup]
  have sourceBound : index < fns1.length := (List.getElem?_eq_some_iff.mp sourceLookup).choose
  have length := callsListBounded_length fuel (fns1.map Prod.snd) (insertEach loc fns1.length g0)
    afterProbe bodies probe
  have targetBound : index < bodies.length := by simp only [List.length_map] at length; omega
  have targetIndex : bodies[index]? = some bodies[index] := by simp [targetBound]
  have fresh : LabelsFresh (codeLocations (fns1.map Prod.snd)) (insertEach loc fns1.length g0) := by
    simpa [LabelsFresh, insertEach] using nestedFresh
  have initialDistinct : ((insertEach loc fns1.length g0).2.map Prod.fst).Nodup := by
    simpa [insertEach] using initialWf.2
  have initialWeak := weaklyWellFormed_insertEach loc fns1.length g0 (wellFormed_weak g0 initialWf)
  obtain ⟨depth, before, after, depthLt, selected, bodyDistinct, bodyFresh, beforeDistinct, beforeWeak,
    knownBound, initialSuffix, extended⟩ :=
    callsListBounded_lookup_run_weak fuel (fns1.map Prod.snd) bodies (insertEach loc fns1.length g0) afterProbe
      probe well.2.2.2 fresh initialDistinct initialWeak index body bodies[index] sourceIndex targetIndex
  have initialFresh : LabelsFresh (codeLocations (fns1.map Prod.snd)) g0 := by
    simpa [LabelsFresh] using nestedFresh
  have knownCovered : ∀ k ∈ codeLocationsExp body, sptDomain before.1 k → k + 1 ∈ before.2.map Prod.fst := by
    intro k bodyMember known
    rcases knownBound k known with initialKnown | emitted
    · rcases (insertEach_domain loc fns1.length g0 k).mp initialKnown with old | ⟨i, bound, eq⟩
      · have initialLabel : k + 1 ∈ g0.2.map Prod.fst := by
          have labelIn : k + 1 ∈ {label | label ∈ g0.2.map Prod.fst} := by
            rw [initialWf.1]
            exact ⟨k, old, rfl⟩
          exact labelIn
        have probeLabel : k + 1 ∈ (insertEach loc fns1.length g0).2.map Prod.fst := by
          simpa [insertEach] using initialLabel
        obtain ⟨front, suffixEq⟩ := initialSuffix
        rw [← suffixEq, List.map_append]
        exact List.mem_append_right _ probeLabel
      · have bodyIn : body ∈ fns1.map Prod.snd := by
          exact List.mem_of_getElem? sourceIndex
        have nested : k ∈ codeLocations (fns1.map Prod.snd) :=
          (mem_codeLocations k (fns1.map Prod.snd)).mpr ⟨body, bodyIn, bodyMember⟩
        subst k
        have nested' : 2 * i + loc ∈ codeLocations (fns1.map Prod.snd) := by
          simpa [Nat.add_comm] using nested
        exact (recClosureWellFormed_disjoint loc fns1 well i bound nested').elim
    · exact emitted
  have singleton : callsListBounded (depth + 1) [body] before = some ([bodies[index]], after) := by
    simp [callsListBounded, callsListFuel, selected]
  have beforeAfter := callsListBounded_stateExtends (depth + 1) [body] before after [bodies[index]] singleton
    (by simpa [codeLocations] using bodyDistinct) (by simpa [codeLocations] using bodyFresh) beforeDistinct
  have beforeProbe := stateExtends_trans before after afterProbe beforeAfter extended
  have alternatives' :
      (groupClosed fns1 bodies ∧ (∃ trace stubIndex, fns2 = callsListSource trace stubIndex loc fns1) ∧
        stateExtends afterProbe g ∧ stateExtends (codeList loc ((fns1.map Prod.fst).zip bodies) afterProbe) g ∧
        groupLocationsCovered fns1 afterProbe allowed ∧
        codeIncludes (codeList loc ((fns1.map Prod.fst).zip bodies) afterProbe).2 code) ∨
      (¬ groupClosed fns1 bodies ∧ ∃ openBodies afterOpen,
        callsListBounded fuel (fns1.map Prod.snd) g0 = some (openBodies, afterOpen) ∧
        fns2 = (fns1.map Prod.fst).zip openBodies ∧ stateExtends afterOpen g ∧
        groupLocationsCovered fns1 afterOpen allowed ∧
        (∀ i, i < fns1.length → 2 * i + loc ∈ allowed) ∧ codeIncludes afterOpen.2 code) := by
    rcases alternatives with ⟨closed, stubs, codeExt, coverage, included⟩ | openCase
    · left
      have afterDistinct := callsListBounded_labelsDistinct fuel (fns1.map Prod.snd)
        (insertEach loc fns1.length g0) afterProbe bodies probe well.2.2.2 fresh initialDistinct
      have bodyLength : bodies.length = fns1.length := by simpa using length
      have generatedFresh : ∀ i, i < ((fns1.map Prod.fst).zip bodies).length →
          loc + i * 2 + 1 ∉ afterProbe.2.map Prod.fst := by
        intro i bound present
        have indexBound : i < fns1.length := by simp [List.length_zip, bodyLength] at bound; omega
        have origins := callsListBounded_labelsBound fuel (fns1.map Prod.snd)
          (insertEach loc fns1.length g0) afterProbe bodies probe
        rcases origins _ present with old | ⟨origin, member, equal⟩
        · have old' : 2 * i + loc + 1 ∈ g0.2.map Prod.fst := by
            simpa [insertEach, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc, Nat.mul_comm] using old
          exact ownFresh i indexBound old'
        · have eq : origin = 2 * i + loc := by omega
          subst origin
          exact recClosureWellFormed_disjoint loc fns1 well i indexBound member
      have codeDistinct := codeList_labels_nodup loc ((fns1.map Prod.fst).zip bodies) afterProbe
        afterDistinct generatedFresh
      have probeExt := codeList_stateExtends loc ((fns1.map Prod.fst).zip bodies) afterProbe codeDistinct
      exact ⟨closed, stubs, stateExtends_trans _ _ _ probeExt codeExt, codeExt, coverage, included⟩
    · exact Or.inr openCase
  exact ⟨g0, bodies, afterProbe, bodies[index], depth, before, after, initialWf, initialFresh, probe, targetIndex, depthLt,
    selected, bodyDistinct, bodyFresh, beforeDistinct, beforeWeak, knownCovered, beforeProbe, extended, alternatives'⟩

/-- A related target body is either a generated stub or the result of an
actual open-group body traversal whose state extends into the current state.
This is Flapjack-specific infrastructure for the closure-body induction. -/
theorem recClosureRelFuel_target_body (fuel : Nat) (g : State) (allowed : Set Nat)
    (code : HolFiniteMapExact Nat (Nat × ClosLang.Exp)) (loc : Nat)
    (fns1 fns2 : List (Nat × ClosLang.Exp)) (index arity : Nat) (body targetBody : ClosLang.Exp)
    (related : recClosureRelFuel fuel g allowed code loc fns1 fns2)
    (sourceLookup : fns1[index]? = some (arity, body))
    (targetLookup : fns2[index]? = some (arity, targetBody)) :
    (∃ trace stubIndex, fns2 = callsListSource trace stubIndex loc fns1) ∨
      ∃ depth before after, depth < max fuel (listBudget (fns1.map Prod.snd) + 1) ∧
        callsFuel depth body before = some (targetBody, after) ∧
        (codeLocationsExp body).Nodup ∧ LabelsFresh (codeLocationsExp body) before ∧
        wellFormed before ∧ stateExtends after g := by
  obtain ⟨g0, well, initialWf, nestedFresh, _, bodies, afterProbe, _, alternatives⟩ := related
  rcases alternatives with ⟨_, stubs, _⟩ | ⟨_, openBodies, afterOpen, openRun, targetEq, openExt, _⟩
  · exact Or.inl stubs
  · right
    have openFresh : LabelsFresh (codeLocations (fns1.map Prod.snd)) g0 := by
      simpa [LabelsFresh] using nestedFresh
    have zippedLookup : ((fns1.map Prod.fst).zip openBodies)[index]? = some (arity, targetBody) := by
      simpa [targetEq] using targetLookup
    obtain ⟨depth, before, after, depthLt, selected, bodyDistinct, bodyFresh, beforeWf, extended⟩ :=
      callsListBounded_open_body fuel fns1 openBodies g0 afterOpen openRun well.2.2.2 openFresh initialWf
        index arity body targetBody sourceLookup zippedLookup
    exact ⟨depth, before, after, depthLt, selected, bodyDistinct, bodyFresh, beforeWf,
      stateExtends_trans after afterOpen g extended openExt⟩

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
