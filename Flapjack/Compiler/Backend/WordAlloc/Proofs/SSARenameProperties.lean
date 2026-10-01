import Flapjack.Compiler.Backend.WordAlloc.SSASetup
import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSAMap
import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSARegisterClass

namespace Flapjack.Compiler.Backend.WordAlloc

/-- Full native renaming properties. The source permits repeated names and
arbitrary source trees; no distinctness or tree validity premise is needed. -/
@[hol "cakeml/compiler/backend/proofs/word_allocProofScript.sml"
  "list_next_var_rename_props"]
theorem listNextVarRenameProps (names : List Nat) (ssa : Spt Nat) (next : Nat)
    (names' : List Nat) (ssa' : Spt Nat) (next' : Nat)
    (heq : listNextVarRename names ssa next = (names', ssa', next'))
    (h : (isAllocVar next ∨ isStackVar next) ∧ ssaMapOK next ssa) :
    next ≤ next' ∧
    (isAllocVar next → isAllocVar next') ∧
    (isStackVar next → isStackVar next') ∧ ssaMapOK next' ssa' := by
  induction names generalizing ssa next names' ssa' next' with
  | nil =>
      simp only [listNextVarRename, Prod.mk.injEq] at heq
      rcases heq with ⟨rfl, rfl, rfl⟩
      exact ⟨Nat.le_refl _, id, id, h.2⟩
  | cons name names ih =>
      generalize htail : listNextVarRename names (sptInsert name next ssa)
        (next + 4) = tail
      rcases tail with ⟨tailNames, tailSSA, tailNext⟩
      have hmap : ssaMapOK (next + 4) (sptInsert name next ssa) := by
        intro x y hlookup
        by_cases hx : x = name
        · subst x
          rw [sptLookup_sptInsert_same] at hlookup
          cases hlookup
          have hn : ¬ isPhyVar next := by
            rcases h.1 with ha | hs
            · exact ((conventionPartitions next).2.2.mp ha).1
            · exact ((conventionPartitions next).1.mp hs).1
          exact ⟨hn, by omega⟩
        · rw [sptLookup_sptInsert_ne name x next ssa hx] at hlookup
          obtain ⟨hn, hb⟩ := h.2 x y hlookup
          exact ⟨hn, by omega⟩
      have hc : isAllocVar (next + 4) ∨ isStackVar (next + 4) :=
        h.1.elim (fun ha => Or.inl (isAllocVarAdd next ha))
          (fun hs => Or.inr (isStackVarAdd next hs))
      have ht := ih (sptInsert name next ssa) (next + 4)
        tailNames tailSSA tailNext htail ⟨hc, hmap⟩
      simp only [listNextVarRename, nextVarRename, htail] at heq
      simp only [Prod.mk.injEq] at heq
      rcases heq with ⟨rfl, rfl, rfl⟩
      exact ⟨by omega, fun ha => ht.2.1 (isAllocVarAdd next ha),
        fun hs => ht.2.2.1 (isStackVarAdd next hs), ht.2.2.2⟩

end Flapjack.Compiler.Backend.WordAlloc
