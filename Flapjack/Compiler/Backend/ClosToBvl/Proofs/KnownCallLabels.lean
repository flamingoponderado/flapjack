import Flapjack.Compiler.Backend.ClosToBvl.Proofs.KnownLabelOracle
import Flapjack.Compiler.Backend.ClosToBvl.Proofs.CallPreparedSemantics

/-! Label invariants for known-function optimization followed by direct calls. -/
namespace Flapjack.Compiler.Backend.ClosToBvl
open Flapjack Flapjack.Compiler.Backend.ClosSem Flapjack.Compiler.Backend.ClosProps
open Flapjack.Compiler.Backend.BackendProps

/-- If the incoming locations are distinct and even, direct-call conversion
and annotation produce mutually distinct entry and nested locations. -/
theorem callOracle_entries_and_locations_nodup {C : Type} (fuel : Nat)
    (oracle : CompileOracle (NumSet × C)) (index : Nat)
    (distinct : (codeLocations (oracle index).2.1).Nodup)
    (sourceEven : ∀ loc ∈ codeLocations (oracle index).2.1, loc % 2 = 0) :
    let called := ClosCall.compileIncFuelOracle fuel oracle index
    ((ClosAnnotate.compile called.2.2).map Prod.fst ++
      (codeLocations (ClosAnnotate.annotateList 0 called.2.1) ++
       codeLocations ((ClosAnnotate.compile called.2.2).map (fun (_, _, body) => body)))).Nodup := by
  let called := ClosCall.compileIncFuelOracle fuel oracle index
  obtain ⟨nextKnown, pass, _⟩ := ClosCall.compileIncFuelOracle_entry fuel oracle index
  have generated := ClosCall.compileIncFuel_generated fuel (oracle index).1.1 (oracle index).2 nextKnown called.2 pass distinct
  have within := ClosCall.compileIncFuelOracle_locationsWithin fuel oracle index
  have beforeDistinct := ClosCall.compileIncFuelOracle_all_locations_nodup fuel oracle index distinct
  have nestedDistinct : (codeLocations (ClosAnnotate.annotateList 0 called.2.1) ++
      codeLocations ((ClosAnnotate.compile called.2.2).map (fun (_, _, body) => body))).Nodup :=
    ((ClosAnnotate.annotateList_codeLocations_sublist 0 called.2.1).append
      (ClosAnnotate.compile_codeLocations_sublist called.2.2)).nodup beforeDistinct
  have entryDistinct : ((ClosAnnotate.compile called.2.2).map Prod.fst).Nodup := by
    simpa only [annotated_labels] using generated.1
  apply List.Nodup.append entryDistinct nestedDistinct
  intro label inEntry inNested
  have beforeEntry : label ∈ called.2.2.map Prod.fst := by simpa only [annotated_labels] using inEntry
  obtain ⟨origin, inSource, equal⟩ := callOracle_label_origin fuel oracle index label beforeEntry
  have originEven := sourceEven origin inSource
  have inSource : label ∈ codeLocations (oracle index).2.1 := by
    rcases List.mem_append.mp inNested with main | auxiliary
    · exact within.1 label ((ClosAnnotate.annotateList_codeLocations_sublist 0 called.2.1).subset main)
    · have before := (ClosAnnotate.compile_codeLocations_sublist called.2.2).subset auxiliary
      obtain ⟨body, bodyMember, locMember⟩ := (mem_codeLocations label _).1 before
      obtain ⟨entry, entryMember, bodyEq⟩ := List.mem_map.mp bodyMember
      obtain ⟨name, arity, sourceBody⟩ := entry
      simp only at bodyEq
      subst body
      exact within.2 name arity sourceBody entryMember label locMember
  have labelEven := sourceEven label inSource
  omega

/-- Known-function optimization retains the even locations assigned by
numbering. -/
theorem knownClosureFuture_locations_even {C : Type} (c : ClosKnown.Config)
    (oracle : CompileOracle (Nat × (Spt ClosKnown.ValApprox × C))) (index loc : Nat)
    (member : loc ∈ codeLocations (knownClosureFuture c oracle index).2.1) :
    loc % 2 = 0 := by
  have before := knownClosureFuture_codeLocations_subset c oracle index member
  apply ClosNumber.compileInc_location_even (oracle index).1.1 loc (oracle index).2.1
  simpa [stateCo, ClosNumber.ignoreTable] using before

/-- Numbering, known-function optimization, direct-call conversion and
annotation yield mutually distinct entries and nested closure locations. -/
theorem knownCallOracle_entries_and_locations_nodup {C : Type} (fuel : Nat) (c : ClosKnown.Config)
    (oracle : CompileOracle (Nat × (Spt ClosKnown.ValApprox × (NumSet × C)))) (index : Nat) :
    let called := ClosCall.compileIncFuelOracle fuel (knownClosureFuture c oracle) index
    ((ClosAnnotate.compile called.2.2).map Prod.fst ++
      (codeLocations (ClosAnnotate.annotateList 0 called.2.1) ++
       codeLocations ((ClosAnnotate.compile called.2.2).map (fun (_, _, body) => body)))).Nodup :=
  callOracle_entries_and_locations_nodup fuel (knownClosureFuture c oracle) index
    (knownClosureFuture_codeLocations_nodup c oracle index)
    (fun loc member => knownClosureFuture_locations_even c oracle index loc member)

/-- Optimized source locations retain the successor-reserved numbering
interval of their corresponding oracle entry. -/
theorem knownClosureFuture_location_bounds {C : Type} (c : ClosKnown.Config)
    (oracle : CompileOracle (Nat × (Spt ClosKnown.ValApprox × C)))
    (state : isStateOracle (ClosNumber.ignoreTable ClosNumber.compileInc) oracle)
    (index loc : Nat) (member : loc ∈ codeLocations (knownClosureFuture c oracle index).2.1) :
    (oracle index).1.1 ≤ loc ∧ loc + 1 < (oracle (index + 1)).1.1 := by
  apply numberingOracle_location_successor_bounds oracle state index loc
  exact knownClosureFuture_codeLocations_subset c oracle index member

/-- The generated auxiliary entry labels retain the source numbering
interval after known-function and direct-call conversion. -/
theorem knownCallOracle_aux_distinct_and_range {C : Type} (fuel : Nat) (c : ClosKnown.Config)
    (oracle : CompileOracle (Nat × (Spt ClosKnown.ValApprox × (NumSet × C))))
    (state : isStateOracle (ClosNumber.ignoreTable ClosNumber.compileInc) oracle) :
    ∀ index,
      ((ClosAnnotate.compile (ClosCall.compileIncFuelOracle fuel (knownClosureFuture c oracle) index).2.2).map Prod.fst).Nodup ∧
      ∀ label ∈ (ClosAnnotate.compile (ClosCall.compileIncFuelOracle fuel (knownClosureFuture c oracle) index).2.2).map Prod.fst,
        (oracle index).1.1 ≤ label ∧ label < (oracle (index + 1)).1.1 := by
  apply annotatedCallOracle_aux_distinct_and_range fuel (knownClosureFuture c oracle)
    (fun index => (oracle index).1.1) (fun index => (oracle (index + 1)).1.1)
  · exact knownClosureFuture_codeLocations_nodup c oracle
  · exact knownClosureFuture_location_bounds c oracle state

/-- The numbered entry marker and expression count survive both known-function
optimization and direct-call conversion. -/
theorem knownCallOracle_marker {C : Type} (fuel : Nat) (c : ClosKnown.Config)
    (oracle : CompileOracle (Nat × (Spt ClosKnown.ValApprox × (NumSet × C)))) (index : Nat) :
    ∃ output : List ClosLang.Exp,
      (ClosCall.compileIncFuelOracle fuel (knownClosureFuture c oracle) index).2.1 =
        .op .none (.intOp (.const (Int.ofNat (oracle index).1.1))) [] :: output ∧
      output.length = (oracle index).2.1.length := by
  let future := knownClosureFuture c oracle
  let called := ClosCall.compileIncFuelOracle fuel future index
  obtain ⟨numbered, marker, length⟩ := knownClosureFuture_marker c oracle index
  change (future index).2.1 = .op .none (.intOp (.const (Int.ofNat (oracle index).1.1))) [] :: numbered at marker
  obtain ⟨nextKnown, run, _⟩ := ClosCall.compileIncFuelOracle_entry fuel future index
  have run' : ClosCall.compileIncFuel? fuel (future index).1.1
      (.op .none (.intOp (.const (Int.ofNat (oracle index).1.1))) [] :: numbered, (future index).2.2) =
      some (nextKnown, called.2) := by
    cases pair : (future index).2 with
    | mk es aux =>
      simp only [pair] at marker run ⊢
      subst es
      exact run
  obtain ⟨output, outputMarker, outputLength⟩ := ClosCall.compileIncFuel_entryMarker
    fuel (future index).1.1 nextKnown .none (oracle index).1.1 numbered (future index).2.2 called.2 run'
  exact ⟨output, outputMarker, outputLength.trans length⟩

/-- The incremental BVL code generated after known-function and direct-call
conversion has distinct labels. -/
theorem knownCallOracle_bvl_labels_nodup {C : Type} (maxApp fuel : Nat) (c : ClosKnown.Config)
    (oracle : CompileOracle (Nat × (Spt ClosKnown.ValApprox × (NumSet × C)))) :
    ∀ index, ((compileInc maxApp (ClosAnnotate.compileInc
      (ClosCall.compileIncFuelOracle fuel (knownClosureFuture c oracle) index).2)).map Prod.fst).Nodup := by
  intro index
  let start := (oracle index).1.1
  let expressions := (oracle index).2.1
  let future := knownClosureFuture c oracle
  let called := ClosCall.compileIncFuelOracle fuel future index
  let program := ClosAnnotate.compileInc called.2
  obtain ⟨output, marker, outputLength⟩ := knownCallOracle_marker fuel c oracle index
  have marker' : called.2.1 = .op .none (.intOp (.const (Int.ofNat start))) [] :: output := marker
  have annotatedMarker : program.1 = .op .none (.intOp (.const (Int.ofNat start))) [] ::
      ClosAnnotate.annotateList 0 output := by
    simpa [program, ClosAnnotate.compileInc, marker'] using ClosAnnotate.annotateList_name_marker start output
  let real := (extractName program.1).2
  have shape := extractName_numbered_marker start (ClosAnnotate.annotateList 0 output)
  have startEq : (extractName program.1).1 = start := by simpa [annotatedMarker] using shape.1
  have lengthEq : real.length = max 1 expressions.length := by
    have l : real.length = max 1 output.length := by
      simpa [real, annotatedMarker, ClosAnnotate.annotateList_length] using shape.2.1
    simpa [expressions, outputLength] using l
  have extract : extractName program.1 = (start, real) := by
    cases h : extractName program.1 with
    | mk first second => simp [real, h] at startEq ⊢; exact startEq
  have mainEq : codeLocations real = codeLocations program.1 := by
    rw [show codeLocations real = codeLocations (ClosAnnotate.annotateList 0 output) by
      simpa [real, annotatedMarker] using shape.2.2]
    simp [annotatedMarker, codeLocations, codeLocationsExp]
  have allDistinct : ((program.2.map Prod.fst) ++ (codeLocations real ++
      codeLocations (program.2.map (fun (_, _, body) => body)))).Nodup := by
    rw [mainEq]
    exact knownCallOracle_entries_and_locations_nodup fuel c oracle index
  have entriesDistinct := allDistinct.of_append_left
  have bodyMainDistinct := allDistinct.of_append_right
  have auxDistinct : ((program.2.map Prod.fst) ++
      codeLocations (program.2.map (fun (_, _, body) => body))).Nodup := by
    apply List.Nodup.append entriesDistinct bodyMainDistinct.of_append_right
    intro label inEntry inBody
    exact allDistinct.disjoint inEntry (List.mem_append_right _ inBody)
  have mainAuxDisjoint : ∀ label ∈ codeLocations real,
      label ∉ (program.2.map Prod.fst) ++ codeLocations (program.2.map (fun (_, _, body) => body)) := by
    intro label inMain inAux
    rcases List.mem_append.mp inAux with entry | body
    · exact allDistinct.disjoint entry (List.mem_append_left _ inMain)
    · exact bodyMainDistinct.disjoint inMain body
  have sourceAbove : ∀ label ∈ codeLocations (future index).2.1,
      start + max 1 real.length ≤ label := by
    intro label member
    have source := knownClosureFuture_codeLocations_subset c oracle index member
    have bound := ClosNumber.compileInc_location_after_entries start label expressions (by
      simpa [stateCo, ClosNumber.ignoreTable, start, expressions] using source)
    simpa [lengthEq] using bound
  have within := ClosCall.compileIncFuelOracle_locationsWithin fuel future index
  have mainAbove : ∀ label ∈ codeLocations real, start + max 1 real.length ≤ label := by
    intro label member
    rw [mainEq] at member
    exact sourceAbove label (within.1 label ((ClosAnnotate.annotateList_codeLocations_sublist 0 called.2.1).subset member))
  have auxAbove : ∀ label ∈ (program.2.map Prod.fst) ++
      codeLocations (program.2.map (fun (_, _, body) => body)), start + max 1 real.length ≤ label := by
    intro label member
    rcases List.mem_append.mp member with entry | body
    · have before : label ∈ called.2.2.map Prod.fst := by simpa [program, ClosAnnotate.compileInc, annotated_labels] using entry
      obtain ⟨origin, inSource, equal⟩ := callOracle_label_origin fuel future index label before
      have bound := sourceAbove origin inSource
      omega
    · have before : label ∈ codeLocations (called.2.2.map (fun (_, _, body) => body)) :=
        (ClosAnnotate.compile_codeLocations_sublist called.2.2).subset body
      obtain ⟨sourceBody, bodyMember, locMember⟩ := (mem_codeLocations label _).1 before
      obtain ⟨entry, entryMember, bodyEq⟩ := List.mem_map.mp bodyMember
      obtain ⟨name, arity, sourceBody'⟩ := entry
      simp only at bodyEq
      subst sourceBody
      exact sourceAbove label (within.2 name arity sourceBody' entryMember label locMember)
  exact compileInc_labels_nodup maxApp start program real extract bodyMainDistinct.of_append_left
    auxDistinct mainAbove auxAbove mainAuxDisjoint

/-- Nested locations in optimized, direct-called, and annotated oracle
programs remain inside their source numbering interval. -/
theorem knownCallOracle_nested_location_bounds {C : Type} (fuel : Nat) (c : ClosKnown.Config)
    (oracle : CompileOracle (Nat × (Spt ClosKnown.ValApprox × (NumSet × C))))
    (state : isStateOracle (ClosNumber.ignoreTable ClosNumber.compileInc) oracle) :
    ∀ index,
      (∀ loc ∈ codeLocations (ClosAnnotate.annotateList 0
        (ClosCall.compileIncFuelOracle fuel (knownClosureFuture c oracle) index).2.1),
        (oracle index).1.1 ≤ loc ∧ loc + 1 < (oracle (index + 1)).1.1) ∧
      (∀ loc ∈ codeLocations ((ClosAnnotate.compile
        (ClosCall.compileIncFuelOracle fuel (knownClosureFuture c oracle) index).2.2).map
          (fun (_, _, body) => body)),
        (oracle index).1.1 ≤ loc ∧ loc + 1 < (oracle (index + 1)).1.1) := by
  intro index
  let future := knownClosureFuture c oracle
  let called := ClosCall.compileIncFuelOracle fuel future index
  have within := ClosCall.compileIncFuelOracle_locationsWithin fuel future index
  constructor
  · intro loc member
    exact knownClosureFuture_location_bounds c oracle state index loc
      (within.1 loc ((ClosAnnotate.annotateList_codeLocations_sublist 0 called.2.1).subset member))
  · intro loc member
    have before : loc ∈ codeLocations (called.2.2.map (fun (_, _, body) => body)) :=
      (ClosAnnotate.compile_codeLocations_sublist called.2.2).subset member
    obtain ⟨body, bodyMember, locMember⟩ := (mem_codeLocations loc _).1 before
    obtain ⟨entry, entryMember, bodyEq⟩ := List.mem_map.mp bodyMember
    obtain ⟨name, arity, sourceBody⟩ := entry
    simp only at bodyEq
    subst body
    exact knownClosureFuture_location_bounds c oracle state index loc
      (within.2 name arity sourceBody entryMember loc locMember)

/-- Optimized direct-call BVL labels stay inside the shifted numbering interval. -/
theorem knownCallOracle_bvl_labels_range {C : Type} (maxApp fuel : Nat) (c : ClosKnown.Config)
    (oracle : CompileOracle (Nat × (Spt ClosKnown.ValApprox × (NumSet × C))))
    (state : isStateOracle (ClosNumber.ignoreTable ClosNumber.compileInc) oracle) :
    ∀ index label, label ∈ (compileInc maxApp (ClosAnnotate.compileInc
      (ClosCall.compileIncFuelOracle fuel
        (knownClosureFuture c oracle) index).2)).map Prod.fst →
      (oracle index).1.1 + numStubs maxApp ≤ label ∧
        label < (oracle (index + 1)).1.1 + numStubs maxApp := by
  intro index label member
  let start := (oracle index).1.1
  let limit := (oracle (index + 1)).1.1
  let expressions := (oracle index).2.1
  let future := knownClosureFuture c oracle
  let called := ClosCall.compileIncFuelOracle fuel future index
  let program := ClosAnnotate.compileInc called.2
  obtain ⟨output, marker, outputLength⟩ := knownCallOracle_marker fuel c oracle index
  have marker' : called.2.1 = .op .none (.intOp (.const (Int.ofNat start))) [] :: output := marker
  have annotatedMarker : program.1 = .op .none (.intOp (.const (Int.ofNat start))) [] ::
      ClosAnnotate.annotateList 0 output := by
    simpa [program, ClosAnnotate.compileInc, marker'] using ClosAnnotate.annotateList_name_marker start output
  let real := (extractName program.1).2
  have shape := extractName_numbered_marker start (ClosAnnotate.annotateList 0 output)
  have startEq : (extractName program.1).1 = start := by simpa [annotatedMarker] using shape.1
  have lengthEq : real.length = max 1 expressions.length := by
    have l : real.length = max 1 output.length := by
      simpa [real, annotatedMarker, ClosAnnotate.annotateList_length] using shape.2.1
    simpa [expressions, outputLength] using l
  have extract : extractName program.1 = (start, real) := by
    cases h : extractName program.1 with
    | mk first second => simp [real, h] at startEq ⊢; exact startEq
  have mainEq : codeLocations real = codeLocations program.1 := by
    rw [show codeLocations real = codeLocations (ClosAnnotate.annotateList 0 output) by
      simpa [real, annotatedMarker] using shape.2.2]
    simp [annotatedMarker, codeLocations, codeLocationsExp]
  have entriesBound : start + max 1 real.length ≤ limit := by
    have reserve := ClosNumber.compileInc_reservation start expressions
    have next := state index
    simp only [ClosNumber.ignoreTable] at next
    simpa [lengthEq, start, expressions, limit, next] using reserve
  have nested := knownCallOracle_nested_location_bounds fuel c oracle state index
  have mainBounds : ∀ loc ∈ codeLocations real, start ≤ loc ∧ loc < limit := by
    intro loc inside
    rw [mainEq] at inside
    have bound := nested.1 loc inside
    omega
  have auxBounds : ∀ entry ∈ program.2, start ≤ entry.1 ∧ entry.1 < limit ∧
      ∀ loc ∈ codeLocationsExp entry.2.2, start ≤ loc ∧ loc < limit := by
    intro entry inside
    have labelIn : entry.1 ∈ program.2.map Prod.fst := List.mem_map.mpr ⟨entry, inside, rfl⟩
    have bound := (knownCallOracle_aux_distinct_and_range fuel c oracle state index).2 entry.1 labelIn
    refine ⟨bound.1, bound.2, ?_⟩
    intro loc locIn
    have bodyIn : entry.2.2 ∈ program.2.map (fun (_, _, body) => body) :=
      List.mem_map.mpr ⟨entry, inside, rfl⟩
    have locs : loc ∈ codeLocations (program.2.map (fun (_, _, body) => body)) :=
      (mem_codeLocations loc _).2 ⟨entry.2.2, bodyIn, locIn⟩
    have locBound := nested.2 loc locs
    omega
  exact compileInc_labels_range maxApp start limit program real extract entriesBound mainBounds auxBounds label member


end Flapjack.Compiler.Backend.ClosToBvl
