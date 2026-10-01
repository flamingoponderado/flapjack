import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSALocalsInsert
import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSAMapExtend
import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSASetup.ListNextVarRenameArithmetic
import Flapjack.Pancake.Semantics.LoopProps.NestedSeqExact

namespace Flapjack.Compiler.Backend.WordAlloc

/-- Full original list-renaming/locals-update relation. Fresh original inferred
types confirm arbitrary payload alpha and native natural-key trees: no word
or state-carrier translation is needed. All seven original premises, including
the producer equality and nonphysical counter, are retained; the conclusion
uses the actual output map/counter and both native list inserts. -/
@[hol "cakeml/compiler/backend/proofs/word_allocProofScript.sml"
  "ssa_locals_rel_list_next_var_rename"]
theorem ssaLocalsRelListNextVarRename {α : Type}
    (names : List Nat) (ssa : Spt Nat) (next : Nat) (source target : Spt α)
    (outputs : List Nat) (ssaOut : Spt Nat) (nextOut : Nat) (values : List α)
    (h : listNextVarRename names ssa next = (outputs, ssaOut, nextOut) ∧
      ssaLocalsRel next ssa source target ∧ ssaMapOK next ssa ∧
      names.length = values.length ∧ (∀ name ∈ names, name < next) ∧
      names.Nodup ∧ ¬ isPhyVar next) :
    ssaLocalsRel nextOut ssaOut
      (LoopSemStateFiniteExact.sptAlistInsert names values source)
      (LoopSemStateFiniteExact.sptAlistInsert outputs values target) := by
  induction names generalizing ssa next source target outputs ssaOut nextOut values with
  | nil =>
      rcases h with ⟨produced, related, _, lengths, _, _, _⟩
      cases values with
      | cons value values => simp at lengths
      | nil =>
          simp only [listNextVarRename, Prod.mk.injEq] at produced
          rcases produced with ⟨rfl, rfl, rfl⟩
          exact related
  | cons name names ih =>
      rcases h with ⟨produced, related, valid, lengths, below, distinct, nonphysical⟩
      cases values with
      | nil => simp at lengths
      | cons value values =>
          generalize tailRename : listNextVarRename names (sptInsert name next ssa)
            (next + 4) = renamed
          rcases renamed with ⟨tailOutputs, tailMap, tailNext⟩
          simp only [listNextVarRename, nextVarRename, tailRename, Prod.mk.injEq] at produced
          rcases produced with ⟨rfl, rfl, rfl⟩
          have hd := List.nodup_cons.mp distinct
          have hl : names.length = values.length := by simpa using lengths
          have newRelated := ssaLocalsRelInsert next ssa source target name value
            ⟨related, valid, below name (by simp)⟩
          have newValid := ssaMapOKExtend next ssa name ⟨valid, nonphysical⟩
          have newBelow : ∀ key ∈ names, key < next + 4 := by
            intro key member
            have := below key (List.mem_cons_of_mem name member)
            omega
          have newNonphysical : ¬ isPhyVar (next + 4) := by
            simpa only [isPhyVar, Nat.add_mod, Nat.reduceMod, Nat.add_zero, Nat.mod_mod] using nonphysical
          have result := ih (sptInsert name next ssa) (next + 4)
            (sptInsert name value source) (sptInsert next value target)
            tailOutputs tailMap tailNext values
            ⟨tailRename, newRelated, newValid, hl, newBelow, hd.2, newNonphysical⟩
          have arithmetic := listNextVarRenameLemma1 names (sptInsert name next ssa)
            (next + 4) tailOutputs tailMap tailNext tailRename
          have fresh : next ∉ tailOutputs := by
            intro member
            rw [arithmetic.2.1] at member
            rcases List.mem_map.mp member with ⟨index, _, equal⟩
            omega
          rw [LoopSemStateFiniteExact.sptAlistInsert_sptInsert_comm name value
              names values source hd.1,
            LoopSemStateFiniteExact.sptAlistInsert_sptInsert_comm next value
              tailOutputs values target fresh] at result
          exact result

end Flapjack.Compiler.Backend.WordAlloc
