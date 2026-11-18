module

public import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.FrameRoots
public import Flapjack.Compiler.Backend.BviToData.Proofs.DomainNames

@[expose] public section

/-! Root multiplicities for an allocation's argument names. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
open Flapjack Flapjack.Compiler.Backend.BviToData

/-- Successful reads and the final live set have the source's root permutation. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_gcProofScript.sml" "get_vars_PERM_toList_inter"]
theorem getVarsPermToListInter {α : Type} (locals : Spt α)
    (args : List Nat) (names : NumSet) (vals : List α)
    (run : DataSem.getVars args locals = some vals) :
    ∃ dups, (vals ++ sptToList (sptInter locals names)).Perm
        (dups ++ sptToList (sptInter locals (sptListInsert args names))) ∧
      (∀ v ∈ dups, v ∈ vals) ∧
      (∀ v ∈ vals, v ∈ sptToList (sptInter locals (sptListInsert args names))) := by
  induction args generalizing names vals with
  | nil =>
    simp [DataSem.getVars] at run
    subst vals
    exact ⟨[], by simp [sptListInsert], by simp, by simp⟩
  | cons key args ih =>
    cases head : sptLookup key locals with
    | none => simp [DataSem.getVars, DataSem.getVar, head] at run
    | some value =>
      cases tail : DataSem.getVars args locals with
      | none => simp [DataSem.getVars, DataSem.getVar, head, tail] at run
      | some rest =>
        have valsEq : vals = value :: rest := by
          simpa [DataSem.getVars, DataSem.getVar, head, tail] using run.symm
        subst vals
        obtain ⟨dups, perm, dupsIn, restIn⟩ := ih (sptInsert key () names) rest tail
        simp only [sptListInsert] at *
        have insertedKey : sptLookup key (sptInter locals (sptInsert key () names)) = some value := by
          rw [sptLookup_sptInterCases, head, sptLookup_sptInsert_same]
        have finalKey : sptLookup key (sptListInsert args (sptInsert key () names)) = some () := by
          have member : sptMem key (sptListInsert args (sptInsert key () names)) := by
            change sptDomain (sptListInsert args (sptInsert key () names)) key
            rw [domain_listInsert]
            exact Or.inr ((sptMem_sptInsert key key () names).mpr (Or.inl rfl))
          obtain ⟨entry, found⟩ := (sptMem_iff_lookup _ _).mp member
          cases entry
          exact found
        have valueIn : value ∈ sptToList (sptInter locals (sptListInsert args (sptInsert key () names))) := by
          apply (sptMemToList _ _).mpr
          refine ⟨key, ?_⟩
          rw [sptLookup_sptInterCases, head, finalKey]
        cases known : sptLookup key names with
        | none =>
          have lookupEq : ∀ k,
              sptLookup k (sptDelete key (sptInter locals (sptInsert key () names))) =
                sptLookup k (sptInter locals names) := by
            intro k
            rw [sptLookup_sptDelete, sptLookup_sptInterCases]
            by_cases eq : k = key
            · subst k
              simp [sptLookup_sptInterCases, known]
            · simp [eq, sptLookup_sptInterCases, sptLookup_sptInsert_ne key k () names eq]
          have insertedPerm := (permToListDelete key _ value insertedKey).trans
            ((permToListLookupEq _ _ lookupEq).cons value)
          refine ⟨dups, ?_, ?_, ?_⟩
          · exact List.Perm.trans List.perm_middle.symm
              (List.Perm.trans (insertedPerm.symm.append_left rest) perm)
          · intro v member
            exact List.mem_cons_of_mem _ (dupsIn v member)
          · intro v member
            rcases List.mem_cons.mp member with rfl | member
            · exact valueIn
            · exact restIn v member
        | some entry =>
          have lookupEq : ∀ k,
              sptLookup k (sptInter locals (sptInsert key () names)) =
                sptLookup k (sptInter locals names) := by
            intro k
            rw [sptLookup_sptInterCases, sptLookup_sptInterCases]
            by_cases eq : k = key
            · subst k
              simp [sptLookup_sptInsert_same, head, known]
            · simp [sptLookup_sptInsert_ne key k () names eq]
          have insertedPerm := permToListLookupEq _ _ lookupEq
          refine ⟨value :: dups, ?_, ?_, ?_⟩
          · exact ((insertedPerm.symm.append_left rest).trans perm).cons value
          · intro v member
            rcases List.mem_cons.mp member with rfl | member
            · exact List.mem_cons_self
            · exact List.mem_cons_of_mem _ (dupsIn v member)
          · intro v member
            rcases List.mem_cons.mp member with rfl | member
            · exact valueIn
            · exact restIn v member

end Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
