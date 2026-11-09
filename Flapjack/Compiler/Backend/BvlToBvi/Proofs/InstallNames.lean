import Flapjack.Compiler.Backend.BvlToBvi.Proofs.AuxNameRange

/-! Code-name invariant after BVL-to-BVI installation. -/
namespace Flapjack.Compiler.Backend.BvlToBvi.Proofs

/-- Every key present in an association list belongs to its sparse tree. -/
theorem sptMem_fromAList_of_key {α : Type} (entries : List (Nat × α)) (key : Nat)
    (member : key ∈ entries.map Prod.fst) : sptMem key (sptFromAList entries) := by
  induction entries with
  | nil => simp at member
  | cons entry rest ih =>
    rcases entry with ⟨first, value⟩
    simp only [List.map_cons, List.mem_cons] at member
    rcases member with equal | tail
    · subst key
      apply (sptMem_iff_lookup _ _).mpr
      exact ⟨value, by simp [sptFromAList, sptLookup_sptInsert_same]⟩
    · by_cases same : key = first
      · subst key
        apply (sptMem_iff_lookup _ _).mpr
        exact ⟨value, by simp [sptFromAList, sptLookup_sptInsert_same]⟩
      · obtain ⟨found, lookup⟩ := (sptMem_iff_lookup _ _).mp (ih tail)
        apply (sptMem_iff_lookup _ _).mpr
        exact ⟨found, by simpa [sptFromAList, sptLookup_sptInsert_ne, same] using lookup⟩

/-- Installing a compiled oracle program and advancing the oracle preserves
the code-name invariant when the new counter matches the shifted oracle. -/
theorem namesOk_install {C : Type} (source : Spt (Nat × Bvl.Exp)) (target : Spt (Nat × Bvi.Exp))
    (oracle : Nat → (Nat × C) × List (Nat × Nat × Bvl.Exp))
    (names : namesOk source target oracle)
    (advance : (oracle 1).1.1 = (compileIncSource (oracle 0).1.1 (oracle 0).2).1) :
    namesOk (sptUnion source (sptFromAList (oracle 0).2))
      (sptUnion target (sptFromAList (compileIncSource (oracle 0).1.1 (oracle 0).2).2))
      (fun n => oracle (n + 1)) := by
  dsimp only [namesOk]
  constructor
  · intro n config prog oracleEq name arity exp member
    exact names.1 (n + 1) config prog oracleEq name arity exp member
  intro name ⟨present, lower⟩
  have oldOrNew := (sptMem_sptUnion target _ name).mp present
  have counterMono := compileIncSource_counter_mono (oracle 0).1.1 (oracle 0).2
  have shiftedCounter : (oracle 0).1.1 ≤ (oracle 1).1.1 := by rw [advance]; exact counterMono
  rcases oldOrNew with old | new
  · have oldNames := names.2 name ⟨old, lower⟩
    change (if name % bvlToBviNamespaces = 1 then
      name < bvlNumStubs + bvlToBviNamespaces * (oracle 1).1.1 else
      name % bvlToBviNamespaces = 0 ∧
        sptMem ((name - bvlNumStubs) / bvlToBviNamespaces) (sptUnion source (sptFromAList (oracle 0).2)))
    split
    · rename_i inAux
      simp [inAux] at oldNames
      simp only [bvlToBviNamespaces] at oldNames ⊢
      omega
    · rename_i notAux
      simp [notAux] at oldNames
      exact ⟨oldNames.1, (sptMem_sptUnion _ _ _).mpr (Or.inl oldNames.2)⟩
  · obtain ⟨payload, found⟩ := (sptMem_iff_lookup _ _).mp new
    rw [sptLookup_sptFromAList] at found
    have member := sptAListLookup_mem name _ payload found
    have keyMember : name ∈ (compileIncSource (oracle 0).1.1 (oracle 0).2).2.map Prod.fst :=
      List.mem_map.mpr ⟨(name, payload), member, rfl⟩
    rcases compileIncSource_nameRange (oracle 0).1.1 (oracle 0).2 name keyMember with
      ⟨sourceName, sourceMember, nameEq⟩ | ⟨index, _, upper, nameEq⟩
    · have stubMod := bvlNumStubMod
      simp only [bvlToBviNamespaces] at stubMod
      have modulo : name % bvlToBviNamespaces = 0 := by rw [nameEq]; simp only [bvlToBviNamespaces]; omega
      have quotient : (name - bvlNumStubs) / bvlToBviNamespaces = sourceName := by
        rw [nameEq]
        simp [bvlToBviNamespaces]
      change (if name % bvlToBviNamespaces = 1 then
        name < bvlNumStubs + bvlToBviNamespaces * (oracle 1).1.1 else
        name % bvlToBviNamespaces = 0 ∧
          sptMem ((name - bvlNumStubs) / bvlToBviNamespaces) (sptUnion source (sptFromAList (oracle 0).2)))
      simp only [modulo, Nat.zero_ne_one, if_false, quotient]
      exact ⟨trivial, (sptMem_sptUnion _ _ _).mpr (Or.inr (sptMem_fromAList_of_key _ _ sourceMember))⟩
    · have stubMod := bvlNumStubMod
      simp only [bvlToBviNamespaces] at stubMod
      have modulo : name % bvlToBviNamespaces = 1 := by rw [nameEq]; simp only [bvlToBviNamespaces]; omega
      change (if name % bvlToBviNamespaces = 1 then
        name < bvlNumStubs + bvlToBviNamespaces * (oracle 1).1.1 else
        name % bvlToBviNamespaces = 0 ∧
          sptMem ((name - bvlNumStubs) / bvlToBviNamespaces) (sptUnion source (sptFromAList (oracle 0).2)))
      simp only [modulo, ite_true]
      rw [advance, nameEq]
      simp only [bvlToBviNamespaces]
      omega

end Flapjack.Compiler.Backend.BvlToBvi.Proofs
