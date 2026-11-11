module

public import Flapjack.Compiler.Backend.ClosCall.Proofs.CodeList
public import Flapjack.FiniteMap.AlistExact.Lookup
public import Flapjack.Misc.Option
public import Flapjack.Misc.ListEl

@[expose] public section

/-! Lookup in direct-call auxiliary code lists. -/
namespace Flapjack.Compiler.Backend.ClosCall
open Flapjack

/-- Lookup in generated auxiliary code uses the unique matching source index,
falling back to the previous code list when there is none. -/
@[hol "cakeml/compiler/backend/proofs/clos_callProofScript.sml" "ALOOKUP_code_list"]
theorem codeListSource_alookup {A B C : Type} [Nonempty (A × B)] (loc : Nat) (fns : List (A × B))
    (state : C × List (Nat × A × B)) (key : Nat) :
    holALookup (codeListSource loc fns state).2 key =
      match holOptionSome (fun i => i < fns.length ∧ key = loc + 2 * i + 1) with
      | some i => some (holEl i fns)
      | none => holALookup state.2 key := by
  classical
  rw [codeListSource_snd_zip, holALookup_append]
  set labels := (List.range fns.length).map (fun i => loc + 1 + 2 * i)
  set entries := (labels.zip fns).reverse
  have lens : labels.length = fns.length := by simp [labels]
  have keys : entries.map Prod.fst = labels.reverse := by
    simp [entries, List.map_reverse, List.map_fst_zip, lens]
  have distinct : (entries.map Prod.fst).Nodup := by
    rw [keys, List.nodup_reverse]
    apply List.Nodup.map (fun _ _ eq => by omega) List.nodup_range
  cases choice : holOptionSome (fun i => i < fns.length ∧ key = loc + 2 * i + 1) with
  | none =>
    have absent : key ∉ entries.map Prod.fst := by
      rw [keys]
      simp only [List.mem_reverse, labels, List.mem_map, List.mem_range, not_exists, not_and]
      intro i bound equal
      exact (holOptionSome_none choice i) ⟨bound, by omega⟩
    have noLookup : holALookup entries key = none := by
      cases found : holALookup entries key with
      | none => rfl
      | some value =>
        exact False.elim (absent (List.mem_map.mpr ⟨(key, value), holALookup_member entries key value found, rfl⟩))
    simp [noLookup]
  | some i =>
    obtain ⟨bound, equal⟩ := holOptionSome_some choice
    have inZip : (key, fns[i]) ∈ labels.zip fns := by
      have b : i < (labels.zip fns).length := by simp [List.length_zip, lens, bound]
      have hm := List.getElem_mem (l := labels.zip fns) b
      simp only [List.getElem_zip] at hm
      dsimp [labels] at hm
      simp only [List.getElem_map, List.getElem_range] at hm
      convert hm using 1
      congr 1
      omega
    have member : (key, holEl i fns) ∈ entries := by
      rw [holEl_eq_getElem i fns bound]
      exact List.mem_reverse.mpr inZip
    have found := holALookup_of_distinct_member entries key (holEl i fns) ⟨distinct, member⟩
    simp [found]

end Flapjack.Compiler.Backend.ClosCall
