import Flapjack.Compiler.Backend.BvlToBvi.Proofs.InitGlobalsStub

/-! Initial code-name invariants for BVL-to-BVI compilation. -/
namespace Flapjack.Compiler.Backend.BvlToBvi.Proofs

/-- Association-list concatenation has the same lookup behavior as a
left-biased union of the two generated sparse trees. -/
theorem sptLookup_fromAList_append {α : Type} (first second : List (Nat × α)) (key : Nat) :
    sptLookup key (sptFromAList (first ++ second)) =
      sptLookup key (sptUnion (sptFromAList first) (sptFromAList second)) := by
  simp only [sptLookup_sptFromAList, sptLookup_sptUnion]
  induction first with
  | nil => simp [sptAListLookup]
  | cons entry rest ih =>
    rcases entry with ⟨name, value⟩
    by_cases equal : key = name <;> simp [sptAListLookup, equal, ih]

/-- Each runtime stub lies below the namespace used for compiled functions
and auxiliary code. -/
theorem stubs_below_namespace (start n : Nat) (entry : Nat × Nat × Bvi.Exp)
    (member : entry ∈ stubs start n) : entry.1 < bvlNumStubs := by
  simp [stubs, allocGlobalLocation, copyGlobalsLocation, initGlobalsLocation, listLengthLocation,
    fromListByteLocation, toListByteLocation, sumListLengthLocation, concatByteLocation] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [bvlNumStubs, dataNumStubs, wordNumStubs, stackNumStubs]

/-- No emitted function or auxiliary label overlaps the runtime stubs. -/
theorem compiled_disjoint_stubs (start n counter : Nat) (programs : List (Nat × Nat × Bvl.Exp)) :
    ∀ entry ∈ (compileIncSource counter programs).2,
      sptLookup entry.1 (sptFromAList (stubs start n)) = none := by
  intro entry member
  have nameMember : entry.1 ∈ (compileIncSource counter programs).2.map Prod.fst :=
    List.mem_map.mpr ⟨entry, member, rfl⟩
  have lower : bvlNumStubs ≤ entry.1 := by
    rcases compileIncSource_nameRange counter programs entry.1 nameMember with
      ⟨_, _, equal⟩ | ⟨_, _, _, equal⟩ <;> rw [equal] <;> omega
  cases found : sptLookup entry.1 (sptFromAList (stubs start n)) with
  | none => rfl
  | some value =>
    rw [sptLookup_sptFromAList] at found
    have stubMember := sptAListLookup_mem entry.1 (stubs start n) value found
    have upper := stubs_below_namespace start n (entry.1, value) stubMember
    simp only at upper
    omega

/-- Initial compiled code and source code satisfy the code-name invariant
when the oracle's first counter starts after the initial compilation. -/
theorem namesOk_initial {C : Type} (start n counter : Nat)
    (programs : List (Nat × Nat × Bvl.Exp))
    (oracle : Nat → (Nat × C) × List (Nat × Nat × Bvl.Exp))
    (oracleHandlers : ∀ index name arity body,
      (name, arity, body) ∈ (oracle index).2 → BvlHandle.Proofs.handleOk [body])
    (counterBound : (compileIncSource counter programs).1 ≤ (oracle 0).1.1) :
    namesOk (sptFromAList programs)
      (sptFromAList (stubs start n ++ (compileIncSource counter programs).2)) oracle := by
  dsimp only [namesOk]
  constructor
  · intro index config prog eq name arity body member
    have actual : (oracle index).2 = prog := congrArg Prod.snd eq
    apply oracleHandlers index name arity body
    simpa [actual] using member
  intro name ⟨present, lower⟩
  obtain ⟨payload, found⟩ := (sptMem_iff_lookup _ _).mp present
  rw [sptLookup_sptFromAList] at found
  have member := sptAListLookup_mem name _ payload found
  rcases List.mem_append.mp member with stub | compiled
  · have upper := stubs_below_namespace start n (name, payload) stub
    simp only at upper
    omega
  · have keyMember : name ∈ (compileIncSource counter programs).2.map Prod.fst :=
      List.mem_map.mpr ⟨(name, payload), compiled, rfl⟩
    rcases compileIncSource_nameRange counter programs name keyMember with
      ⟨sourceName, sourceMember, nameEq⟩ | ⟨index, _, upper, nameEq⟩
    · have stubMod := bvlNumStubMod
      simp only [bvlToBviNamespaces] at stubMod
      have modulo : name % bvlToBviNamespaces = 0 := by rw [nameEq]; simp only [bvlToBviNamespaces]; omega
      have quotient : (name - bvlNumStubs) / bvlToBviNamespaces = sourceName := by rw [nameEq]; simp [bvlToBviNamespaces]
      simp only [modulo, Nat.zero_ne_one, if_false, quotient]
      exact ⟨trivial, sptMem_fromAList_of_key programs sourceName sourceMember⟩
    · have stubMod := bvlNumStubMod
      simp only [bvlToBviNamespaces] at stubMod
      have modulo : name % bvlToBviNamespaces = 1 := by rw [nameEq]; simp only [bvlToBviNamespaces]; omega
      simp only [modulo, ite_true]
      rw [nameEq]
      simp only [bvlToBviNamespaces]
      omega

/-- Installation of auxiliary entries depends only on sparse-tree lookup. -/
theorem auxCodeInstalled_lookup_congr {α β : Type} (aux : List (Nat × α × β))
    (first second : Spt (α × β)) (same : ∀ key, sptLookup key first = sptLookup key second)
    (installed : auxCodeInstalled aux first) : auxCodeInstalled aux second := by
  induction aux with
  | nil => trivial
  | cons entry rest ih =>
    rcases entry with ⟨name, arity, body⟩
    exact ⟨(same name).symm.trans installed.1, ih installed.2⟩

/-- Every initial source function is represented by its translated target
function and its auxiliary code in the initial compiled program. -/
theorem initial_code_correspondence (start n counter : Nat) (programs : List (Nat × Nat × Bvl.Exp))
    (distinct : (programs.map Prod.fst).Nodup)
    (handlers : ∀ name arity body, (name, arity, body) ∈ programs → BvlHandle.Proofs.handleOk [body]) :
    ∀ name arity body, sptLookup name (sptFromAList programs) = some (arity, body) →
      ∃ initialName, let (converted, aux, _) := compileSingSource initialName body
        sptLookup (bvlNumStubs + bvlToBviNamespaces * name)
          (sptFromAList (stubs start n ++ (compileIncSource counter programs).2)) =
            some (arity, BviLet.compileSing [] 0 converted) ∧
        auxCodeInstalled (appListAppend aux) (sptFromAList (stubs start n ++ (compileIncSource counter programs).2)) ∧
        BvlHandle.Proofs.handleOk [body] := by
  let compiled := (compileIncSource counter programs).2
  let stubTree := sptFromAList (stubs start n)
  have compiledDistinct : (compiled.map Prod.fst).Nodup := compileIncSource_names_nodup counter programs distinct
  have available : ∀ entry ∈ compiled, sptLookup entry.1 stubTree = none := compiled_disjoint_stubs start n counter programs
  intro name arity body lookup
  rw [sptLookup_sptFromAList] at lookup
  have member : (name, arity, body) ∈ programs := sptAListLookup_mem name programs (arity, body) lookup
  obtain ⟨initialName, converted, aux, next, conversion, translated, auxSubset⟩ :=
    compileProgramsSource_entry counter programs name arity body member
  rcases compilation : compileProgramsSource counter programs with ⟨tree, finish⟩
  have translated' : (bvlNumStubs + bvlToBviNamespaces * name, arity, BviLet.compileSing [] 0 converted) ∈ compiled := by
    simpa [compiled, compileIncSource, compilation] using translated
  have auxSubset' : ∀ entry ∈ appListAppend aux, entry ∈ compiled := by
    intro entry inAux
    simpa [compiled, compileIncSource, compilation] using auxSubset entry inAux
  have stubNone := available _ translated'
  have compiledLookup := sptLookup_fromAList_of_distinct compiled _ _ compiledDistinct translated'
  have auxInstalled := auxCodeInstalled_union_right (appListAppend aux) compiled stubTree compiledDistinct available auxSubset'
  refine ⟨initialName, ?_⟩
  rw [conversion]
  refine ⟨?_, ?_, handlers name arity body member⟩
  · rw [sptLookup_fromAList_append, sptLookup_sptUnion, stubNone, compiledLookup]
  · apply auxCodeInstalled_lookup_congr _ (sptUnion stubTree (sptFromAList compiled))
    · intro key
      exact (sptLookup_fromAList_append (stubs start n) compiled key).symm
    · exact auxInstalled

end Flapjack.Compiler.Backend.BvlToBvi.Proofs
