import Flapjack.Compiler.Backend.BvlToBvi.Proofs.CompileInstallArgs
import Mathlib.Data.List.Nodup

/-! Fresh auxiliary-name accounting for BVL-to-BVI compilation. -/
namespace Flapjack.Compiler.Backend.BvlToBvi.Proofs

/-- The sequence of auxiliary labels allocated from a given counter. -/
def auxNameSequence (start count : Nat) : List Nat :=
  (List.range' start count).map (fun n => bvlNumStubs + bvlToBviNamespaces * n + 1)

/-- An auxiliary tree contains exactly the labels allocated between its
initial and final counters, in allocation order. -/
def auxNameRange (start : Nat) (aux : AppList (Nat × Nat × Bvi.Exp)) (finish : Nat) : Prop :=
  ∃ count, finish = start + count ∧ (appListAppend aux).map Prod.fst = auxNameSequence start count

theorem auxNameRange_empty (start : Nat) : auxNameRange start .nil start := by
  exact ⟨0, by simp [auxNameSequence, appListAppend, appendAux]⟩

theorem auxNameRange_append {start middle finish : Nat} {first second : AppList (Nat × Nat × Bvi.Exp)}
    (left : auxNameRange start first middle) (right : auxNameRange middle second finish) :
    auxNameRange start (smartAppend first second) finish := by
  obtain ⟨leftCount, rfl, leftNames⟩ := left
  obtain ⟨rightCount, rfl, rightNames⟩ := right
  refine ⟨leftCount + rightCount, by omega, ?_⟩
  rw [appListAppend_smartAppend, List.map_append, leftNames, rightNames]
  simp [auxNameSequence, ← List.map_append, List.range'_append_1]

theorem auxNameRange_fresh (start arity : Nat) (body : Bvi.Exp) :
    auxNameRange start (compileAuxSource (start, arity, body)) (start + 1) := by
  refine ⟨1, rfl, ?_⟩
  simp [compileAuxSource, auxNameSequence, appListAppend, appendAux]

private theorem destLetBudget' (exp : Bvl.Exp) :
    listBudget (destLet exp).1 ≤ expBudget exp ∧ expBudget (destLet exp).2 ≤ expBudget exp := by
  cases exp <;> simp [destLet, expBudget, listBudget] <;> omega

mutual
/-- Every generated auxiliary label is allocated exactly once and in order. -/
theorem compileSingSource_auxNameRange (start : Nat) (exp : Bvl.Exp) :
    auxNameRange start (compileSingSource start exp).2.1 (compileSingSource start exp).2.2 := by
  cases exp with
  | var v => simpa [compileSingSource] using auxNameRange_empty start
  | force loc v => simpa [compileSingSource] using auxNameRange_empty start
  | raise x =>
    rcases h : compileSingSource start x with ⟨converted, aux, next⟩
    have ih := compileSingSource_auxNameRange start x
    simpa [compileSingSource, h] using ih
  | tick x =>
    rcases h : compileSingSource start x with ⟨converted, aux, next⟩
    have ih := compileSingSource_auxNameRange start x
    simpa [compileSingSource, h] using ih
  | op op xs =>
    rcases h : compileListSource start xs with ⟨converted, aux, next⟩
    have ih := compileListSource_auxNameRange start xs
    simpa [compileSingSource, h] using ih
  | call ticks dest xs =>
    rcases h : compileListSource start xs with ⟨converted, aux, next⟩
    have ih := compileListSource_auxNameRange start xs
    simpa [compileSingSource, h] using ih
  | ifThenElse x y z =>
    rcases hx : compileSingSource start x with ⟨x', a, n1⟩
    rcases hy : compileSingSource n1 y with ⟨y', b, n2⟩
    rcases hz : compileSingSource n2 z with ⟨z', c, n3⟩
    have ix := compileSingSource_auxNameRange start x
    have iy := compileSingSource_auxNameRange n1 y
    have iz := compileSingSource_auxNameRange n2 z
    simp only [hx] at ix
    simp only [hy] at iy
    simp only [hz] at iz
    simpa [compileSingSource, hx, hy, hz] using auxNameRange_append (auxNameRange_append ix iy) iz
  | «let» xs body =>
    by_cases empty : xs.isEmpty
    · rcases ha : compileListSource start (destLet body).1 with ⟨args, a, n1⟩
      rcases hb : compileSingSource n1 (destLet body).2 with ⟨inner, b, n2⟩
      have ia := compileListSource_auxNameRange start (destLet body).1
      have ib := compileSingSource_auxNameRange n1 (destLet body).2
      simp only [ha] at ia
      simp only [hb] at ib
      simpa [compileSingSource, empty, ha, hb] using
        auxNameRange_append (auxNameRange_append ia ib) (auxNameRange_fresh n2 (destLet body).1.length inner)
    · rcases ha : compileListSource start xs with ⟨args, a, n1⟩
      rcases hb : compileSingSource n1 body with ⟨body', b, n2⟩
      have ia := compileListSource_auxNameRange start xs
      have ib := compileSingSource_auxNameRange n1 body
      simp only [ha] at ia
      simp only [hb] at ib
      simpa [compileSingSource, empty, ha, hb] using auxNameRange_append ia ib
  | handle body handler =>
    rcases ha : compileListSource start (destLet body).1 with ⟨args, a, n1⟩
    rcases hb : compileSingSource n1 (destLet body).2 with ⟨inner, b, n2⟩
    rcases hc : compileSingSource n2 handler with ⟨handler', c, n3⟩
    have ia := compileListSource_auxNameRange start (destLet body).1
    have ib := compileSingSource_auxNameRange n1 (destLet body).2
    have ic := compileSingSource_auxNameRange n2 handler
    simp only [ha] at ia
    simp only [hb] at ib
    simp only [hc] at ic
    simpa [compileSingSource, ha, hb, hc] using
      auxNameRange_append (auxNameRange_append (auxNameRange_append ia ib) ic)
        (auxNameRange_fresh n3 (destLet body).1.length inner)
termination_by expBudget exp
decreasing_by
  all_goals try simp only [expBudget]
  all_goals try (have := destLetBudget' body)
  all_goals omega

/-- The corresponding expression-list traversal allocates one contiguous
sequence of auxiliary labels. -/
theorem compileListSource_auxNameRange (start : Nat) (xs : List Bvl.Exp) :
    auxNameRange start (compileListSource start xs).2.1 (compileListSource start xs).2.2 := by
  cases xs with
  | nil => simpa [compileListSource] using auxNameRange_empty start
  | cons x xs =>
    rcases hx : compileSingSource start x with ⟨converted, a, n1⟩
    rcases ht : compileListSource n1 xs with ⟨rest, b, n2⟩
    have ix := compileSingSource_auxNameRange start x
    have it := compileListSource_auxNameRange n1 xs
    simp only [hx] at ix
    simp only [ht] at it
    simpa [compileListSource, hx, ht] using auxNameRange_append ix it
termination_by listBudget xs
decreasing_by all_goals simp only [listBudget]; omega
end

/-- A conversion never decreases its fresh-name counter. -/
theorem auxNameRange_mono {start finish : Nat} {aux : AppList (Nat × Nat × Bvi.Exp)}
    (range : auxNameRange start aux finish) : start ≤ finish := by
  obtain ⟨count, rfl, _⟩ := range
  omega

/-- Every auxiliary name encodes a counter in the conversion's allocation
interval. -/
theorem auxNameRange_member {start finish : Nat} {aux : AppList (Nat × Nat × Bvi.Exp)}
    (range : auxNameRange start aux finish) (name : Nat)
    (member : name ∈ (appListAppend aux).map Prod.fst) :
    ∃ index, start ≤ index ∧ index < finish ∧ name = bvlNumStubs + bvlToBviNamespaces * index + 1 := by
  obtain ⟨count, rfl, names⟩ := range
  rw [names] at member
  obtain ⟨index, indexMem, equal⟩ := List.mem_map.mp member
  obtain ⟨offset, offsetBound, indexEq⟩ := List.mem_range'.mp indexMem
  refine ⟨index, ?_, ?_, equal.symm⟩ <;> simp at indexEq <;> omega

/-- A generated auxiliary-label sequence contains no duplicates. -/
theorem auxNameRange_nodup {start finish : Nat} {aux : AppList (Nat × Nat × Bvi.Exp)}
    (range : auxNameRange start aux finish) : ((appListAppend aux).map Prod.fst).Nodup := by
  obtain ⟨count, _, names⟩ := range
  rw [names]
  apply List.Nodup.map _ (List.nodup_range')
  intro x y equal
  simp only [bvlToBviNamespaces] at equal
  omega

/-- The incrementally compiled program's counter is monotone, and every
emitted name is either the translation of an input function label or a
fresh auxiliary label in the allocated interval. -/
theorem compileProgramsSource_nameRange (start : Nat) (programs : List (Nat × Nat × Bvl.Exp)) :
    start ≤ (compileProgramsSource start programs).2 ∧
    ∀ name ∈ (appListAppend (compileProgramsSource start programs).1).map Prod.fst,
      (∃ input ∈ programs.map Prod.fst, name = bvlNumStubs + bvlToBviNamespaces * input) ∨
      (∃ index, start ≤ index ∧ index < (compileProgramsSource start programs).2 ∧
        name = bvlNumStubs + bvlToBviNamespaces * index + 1) := by
  induction programs generalizing start with
  | nil => simp [compileProgramsSource, appListAppend, appendAux]
  | cons entry rest ih =>
    rcases entry with ⟨key, arity, body⟩
    rcases first : compileSingSource start body with ⟨converted, aux, next⟩
    rcases remaining : compileProgramsSource next rest with ⟨other, finish⟩
    have range := compileSingSource_auxNameRange start body
    simp only [first] at range
    have startNext := auxNameRange_mono range
    have tail := ih next
    simp only [remaining] at tail
    have nextFinish := tail.1
    simp only [compileProgramsSource, compileSingleSource, first, remaining,
      appListAppend_smartAppend, List.map_append]
    constructor
    · omega
    intro name member
    simp only [appListAppend, appendAux, List.mem_append] at member
    rcases member with (equal | auxMember) | tailMember
    · left
      refine ⟨key, by simp, ?_⟩
      simpa using equal
    · right
      have auxMember' : name ∈ (appListAppend aux).map Prod.fst := by simpa [appListAppend] using auxMember
      obtain ⟨index, lower, upper, equal⟩ := auxNameRange_member range name auxMember'
      exact ⟨index, lower, by omega, equal⟩
    · have tailMember' : name ∈ (appListAppend other).map Prod.fst := by simpa [appListAppend] using tailMember
      rcases tail.2 name tailMember' with ⟨input, inputMem, equal⟩ | ⟨index, lower, upper, equal⟩
      · left
        exact ⟨input, by simp [inputMem], equal⟩
      · right
        exact ⟨index, by omega, upper, equal⟩

/-- Incremental compilation does not decrease its fresh-name counter. -/
theorem compileIncSource_counter_mono (start : Nat) (programs : List (Nat × Nat × Bvl.Exp)) :
    start ≤ (compileIncSource start programs).1 := by
  have range := compileProgramsSource_nameRange start programs
  rcases run : compileProgramsSource start programs with ⟨tree, finish⟩
  simpa [compileIncSource, run] using range.1

/-- Every incrementally compiled label is either a translated input label or
a fresh auxiliary label within the allocated counter interval. -/
theorem compileIncSource_nameRange (start : Nat) (programs : List (Nat × Nat × Bvl.Exp))
    (name : Nat) (member : name ∈ (compileIncSource start programs).2.map Prod.fst) :
    (∃ input ∈ programs.map Prod.fst, name = bvlNumStubs + bvlToBviNamespaces * input) ∨
    (∃ index, start ≤ index ∧ index < (compileIncSource start programs).1 ∧
      name = bvlNumStubs + bvlToBviNamespaces * index + 1) := by
  have range := compileProgramsSource_nameRange start programs
  rcases run : compileProgramsSource start programs with ⟨tree, finish⟩
  simp only [run] at range
  simp only [compileIncSource, run] at member ⊢
  exact range.2 name member

/-- Freshly compiled labels do not collide with code already in a related
target when the source program's labels are absent from source code. -/
theorem compileIncSource_available {C α β : Type}
    (source : Spt α) (target : Spt β)
    (oracle : Nat → (Nat × C) × List (Nat × Nat × Bvl.Exp))
    (names : namesOk source target oracle)
    (sourceAvailable : ∀ entry ∈ (oracle 0).2, sptLookup entry.1 source = none) :
    ∀ entry ∈ (compileIncSource (oracle 0).1.1 (oracle 0).2).2,
      sptLookup entry.1 target = none := by
  intro entry member
  cases targetLookup : sptLookup entry.1 target with
  | none => rfl
  | some old =>
    have targetPresent : sptMem entry.1 target := (sptMem_iff_lookup _ _).mpr ⟨old, targetLookup⟩
    have nameMember : entry.1 ∈ (compileIncSource (oracle 0).1.1 (oracle 0).2).2.map Prod.fst :=
      List.mem_map.mpr ⟨entry, member, rfl⟩
    rcases compileIncSource_nameRange (oracle 0).1.1 (oracle 0).2 entry.1 nameMember with
      ⟨sourceName, sourceMember, nameEq⟩ | ⟨index, lower, _, nameEq⟩
    · obtain ⟨sourceEntry, entryMember, keyEq⟩ := List.mem_map.mp sourceMember
      have stubMod := bvlNumStubMod
      simp only [bvlToBviNamespaces] at stubMod
      have lowerBound : bvlNumStubs ≤ entry.1 := by rw [nameEq]; omega
      have modulo : entry.1 % bvlToBviNamespaces = 0 := by
        rw [nameEq]
        simp only [bvlToBviNamespaces]
        omega
      have quotient : (entry.1 - bvlNumStubs) / bvlToBviNamespaces = sourceName := by
        rw [nameEq]
        simp [bvlToBviNamespaces]
      have fromNames := names.2 entry.1 ⟨targetPresent, lowerBound⟩
      change (if entry.1 % bvlToBviNamespaces = 1 then
        entry.1 < bvlNumStubs + bvlToBviNamespaces * (oracle 0).1.1 else
        entry.1 % bvlToBviNamespaces = 0 ∧ sptMem ((entry.1 - bvlNumStubs) / bvlToBviNamespaces) source) at fromNames
      simp only [modulo, Nat.zero_ne_one, if_false, quotient] at fromNames
      obtain ⟨cell, found⟩ := (sptMem_iff_lookup _ _).mp fromNames.2
      have notFound := sourceAvailable sourceEntry entryMember
      rw [keyEq] at notFound
      rw [notFound] at found
      contradiction
    · have stubMod := bvlNumStubMod
      simp only [bvlToBviNamespaces] at stubMod
      have lowerBound : bvlNumStubs ≤ entry.1 := by rw [nameEq]; omega
      have modulo : entry.1 % bvlToBviNamespaces = 1 := by
        rw [nameEq]
        simp only [bvlToBviNamespaces]
        omega
      have fromNames := names.2 entry.1 ⟨targetPresent, lowerBound⟩
      simp [modulo] at fromNames
      rw [nameEq] at fromNames
      simp only [bvlToBviNamespaces] at fromNames
      omega

/-- Distinct source function labels and disjoint fresh auxiliary intervals
produce distinct compiled labels. -/
theorem compileProgramsSource_names_nodup (start : Nat) (programs : List (Nat × Nat × Bvl.Exp))
    (distinct : (programs.map Prod.fst).Nodup) :
    ((appListAppend (compileProgramsSource start programs).1).map Prod.fst).Nodup := by
  induction programs generalizing start with
  | nil => simp [compileProgramsSource, appListAppend, appendAux]
  | cons entry rest ih =>
    rcases entry with ⟨key, arity, body⟩
    simp only [List.map_cons, List.nodup_cons] at distinct
    rcases first : compileSingSource start body with ⟨converted, aux, next⟩
    rcases remaining : compileProgramsSource next rest with ⟨other, finish⟩
    have range := compileSingSource_auxNameRange start body
    simp only [first] at range
    have tail := ih next distinct.2
    simp only [remaining] at tail
    have tailRange := compileProgramsSource_nameRange next rest
    simp only [remaining] at tailRange
    let label := bvlNumStubs + bvlToBviNamespaces * key
    let auxKeys := (appListAppend aux).map Prod.fst
    let tailKeys := (appListAppend other).map Prod.fst
    have headNotAux : label ∉ auxKeys := by
      intro member
      obtain ⟨index, _, _, equal⟩ := auxNameRange_member range label member
      simp only [label, bvlToBviNamespaces] at equal
      omega
    have leftNodup : ([label] ++ auxKeys).Nodup := by
      simp [headNotAux, auxKeys, auxNameRange_nodup range]
    have disjoint : ∀ name ∈ [label] ++ auxKeys, ∀ otherName ∈ tailKeys, name ≠ otherName := by
      intro name inLeft otherName inTail equal
      simp only [List.mem_append, List.mem_singleton] at inLeft
      rcases tailRange.2 otherName inTail with ⟨input, inputMem, targetEq⟩ | ⟨index, lower, _, targetEq⟩
      · rcases inLeft with head | auxMem
        · have inputNe : key ≠ input := by intro eq; subst input; exact distinct.1 inputMem
          simp only [label, bvlToBviNamespaces] at head targetEq
          omega
        · obtain ⟨auxIndex, _, _, auxEq⟩ := auxNameRange_member range name auxMem
          simp only [bvlToBviNamespaces] at auxEq targetEq
          omega
      · rcases inLeft with head | auxMem
        · simp only [label, bvlToBviNamespaces] at head targetEq
          omega
        · obtain ⟨auxIndex, _, upper, auxEq⟩ := auxNameRange_member range name auxMem
          simp only [bvlToBviNamespaces] at auxEq targetEq
          omega
    have combined : (([label] ++ auxKeys) ++ tailKeys).Nodup := List.nodup_append.mpr ⟨leftNodup, tail, disjoint⟩
    simp only [compileProgramsSource, compileSingleSource, first, remaining, appListAppend_smartAppend, List.map_append]
    simpa [appListAppend, appendAux, label, auxKeys, tailKeys] using combined

/-- Incremental compilation preserves distinctness of input function labels. -/
theorem compileIncSource_names_nodup (start : Nat) (programs : List (Nat × Nat × Bvl.Exp))
    (distinct : (programs.map Prod.fst).Nodup) :
    ((compileIncSource start programs).2.map Prod.fst).Nodup := by
  have result := compileProgramsSource_names_nodup start programs distinct
  rcases run : compileProgramsSource start programs with ⟨tree, finish⟩
  simpa [compileIncSource, run] using result

/-- A successful source installation transfers to the target primitive:
freshness and distinctness of the compiled code are consequences of the
source guards and the state relation. Untagged pending evaluator and
dispatcher correspondence review. -/
theorem install_target_transfer_of_related {C F : Type} (relocate : Nat → Nat)
    (source next : BvlSem.State (Nat × C) F) (target : BviSem.BviState C F)
    (byteValue wordValue result : BvlSem.Value) (related : stateRel relocate source target)
    (run : BvlSem.doInstall (R := BvlSem.Value) [byteValue, wordValue] source = .val (result, next)) :
    ∃ bytes words targetNext,
      BvlSem.valueToBytes byteValue = some bytes ∧ BvlSem.valueToWords wordValue = some words ∧
      BviSem.doApp .install [adjustBv relocate byteValue, adjustBv relocate wordValue,
        .number bytes.length, .number words.length] target = .val (adjustBv relocate result, targetNext) ∧
      targetNext.code = sptUnion target.code (sptFromAList (compileIncSource (source.compileOracle 0).1.1 (source.compileOracle 0).2).2) ∧
      targetNext.compileOracle = (fun n => target.compileOracle (n + 1)) ∧
      targetNext = { target with
        code := sptUnion target.code (sptFromAList (compileIncSource (source.compileOracle 0).1.1 (source.compileOracle 0).2).2)
        compileOracle := fun n => target.compileOracle (n + 1) } := by
  obtain ⟨_, _, config, _, key, arity, body, rest, _, _, oracle, available, distinct, _, _, _, _⟩ :=
    install_success_shape byteValue wordValue source next result run
  have names : namesOk source.code target.code source.compileOracle := related.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have sourceAvailable : ∀ entry ∈ (source.compileOracle 0).2, sptLookup entry.1 source.code = none := by
    simpa [oracle] using available
  have sourceDistinct : ((source.compileOracle 0).2.map Prod.fst).Nodup := by simpa [oracle] using distinct
  exact install_target_transfer relocate source next target byteValue wordValue result related run
    (compileIncSource_available source.code target.code source.compileOracle names sourceAvailable)
    (compileIncSource_names_nodup (source.compileOracle 0).1.1 (source.compileOracle 0).2 sourceDistinct)

end Flapjack.Compiler.Backend.BvlToBvi.Proofs
