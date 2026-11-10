module

public import Flapjack.Compiler.Backend.ClosCall
public import Mathlib.Tactic

@[expose] public section

/-! Label accounting for direct-call auxiliary functions. -/
namespace Flapjack.Compiler.Backend.ClosCall
open Flapjack

/-- Generating auxiliary functions does not change the state’s first component. -/
@[hol "cakeml/compiler/backend/proofs/clos_callProofScript.sml" "FST_code_list"]
theorem codeListSource_fst {A B C : Type} (loc : Nat) (fns : List (A × B))
    (state : C × List (Nat × A × B)) : (codeListSource loc fns state).1 = state.1 := by
  induction fns generalizing loc state with
  | nil => rfl
  | cons fn rest ih =>
    cases fn
    cases state
    exact ih _ _

/-- The source-shaped generator depends on the incoming state only through
its existing code list when observing the resulting code list. -/
@[hol "cakeml/compiler/backend/proofs/clos_callProofScript.sml" "SND_code_list_change"]
theorem codeListSource_snd_change {A B C D : Type} (loc : Nat) (fns : List (A × B))
    (state : C × List (Nat × A × B)) (state' : D × List (Nat × A × B))
    (same : state.2 = state'.2) :
    (codeListSource loc fns state).2 = (codeListSource loc fns state').2 := by
  induction fns generalizing loc state state' with
  | nil => exact same
  | cons fn rest ih =>
    obtain ⟨arity, body⟩ := fn
    obtain ⟨known, code⟩ := state
    obtain ⟨known', code'⟩ := state'
    simp only at same
    subst code'
    exact ih _ _ _ rfl

/-- Auxiliary labels are the reversed odd-offset range followed by the
previous code labels, as in the original pass. -/
@[hol "cakeml/compiler/backend/proofs/clos_callProofScript.sml" "MAP_FST_code_list"]
theorem codeListSource_labels {A B C : Type} (loc : Nat) (fns : List (A × B))
    (state : C × List (Nat × A × B)) :
    ((codeListSource loc fns state).2.map Prod.fst) =
      ((List.range fns.length).map (fun i => loc + i * 2 + 1)).reverse ++ state.2.map Prod.fst := by
  induction fns generalizing loc state with
  | nil => simp [codeListSource]
  | cons fn rest ih =>
    obtain ⟨arity, body⟩ := fn
    obtain ⟨known, code⟩ := state
    simp only [codeListSource, ih, List.length_cons, List.range_succ_eq_map,
      List.map_cons, List.map_map, List.reverse_cons, List.append_assoc, List.map_cons]
    congr 1
    apply congrArg List.reverse
    apply List.map_congr_left
    intro i member
    simp only [Function.comp_apply]
    omega

/-- Auxiliary entries are the reversed zip of generated labels and functions,
followed by the incoming code list. -/
@[hol "cakeml/compiler/backend/proofs/clos_callProofScript.sml" "SND_code_list_ZIP"]
theorem codeListSource_snd_zip {A B C : Type} (loc : Nat) (fns : List (A × B))
    (state : C × List (Nat × A × B)) :
    (codeListSource loc fns state).2 =
      (((List.range fns.length).map (fun i => loc + 1 + 2 * i)).zip fns).reverse ++ state.2 := by
  induction fns generalizing loc state with
  | nil => simp [codeListSource]
  | cons fn rest ih =>
    obtain ⟨a, b⟩ := fn
    obtain ⟨known, code⟩ := state
    simp only [codeListSource, ih, List.length_cons, List.range_succ_eq_map,
      List.map_cons, List.map_map, List.zip_cons_cons, List.reverse_cons,
      List.append_assoc, List.singleton_append]
    congr 1
    congr 3
    funext i
    simp only [Function.comp_apply]
    omega

/-- Replacing the input code suffix preserves the generated prefix. -/
@[hol "cakeml/compiler/backend/proofs/clos_callProofScript.sml" "code_list_replace_SND"]
theorem codeListSource_replace_snd {A B C : Type} (loc : Nat) (fns : List (A × B))
    (g0 g g0' : C × List (Nat × A × B)) (ls : List (Nat × A × B))
    (h : codeListSource loc fns g0 = g ∧ g0.1 = g0'.1 ∧ g.2 = ls ++ g0.2) :
    codeListSource loc fns g0' = (g.1, ls ++ g0'.2) := by
  obtain ⟨run, same, suffix⟩ := h
  have first : g.1 = g0.1 := by
    rw [← run, codeListSource_fst]
  have generated : (((List.range fns.length).map (fun i => loc + 1 + 2 * i)).zip fns).reverse = ls := by
    have eq : (((List.range fns.length).map (fun i => loc + 1 + 2 * i)).zip fns).reverse ++ g0.2 = ls ++ g0.2 := by
      rw [← codeListSource_snd_zip, run]
      exact suffix
    exact List.append_cancel_right eq
  apply Prod.ext
  · simpa [codeListSource_fst] using same.symm.trans first.symm
  · simp [codeListSource_snd_zip, generated]

/-- The indexed fold used by the executable pass is the source recursion. -/
theorem codeList_eq_source (loc : Nat) (fns : List (Nat × ClosLang.Exp))
    (state : State) : codeList loc fns state = codeListSource loc fns state := by
  have fold_eq (loc : Nat) (fns : List (Nat × ClosLang.Exp))
      (code : List (Nat × Nat × ClosLang.Exp)) :
      (fns.zip (List.range fns.length)).foldl
          (fun code ((arity, body), i) => (loc + 2 * i + 1, arity, body) :: code) code =
        (codeListSource loc fns ((), code)).2 := by
    induction fns generalizing loc code with
    | nil => rfl
    | cons fn rest ih =>
      obtain ⟨arity, body⟩ := fn
      simp only [List.length_cons, List.range_succ_eq_map, List.zip_cons_cons,
        List.foldl_cons, List.zip_map_right, List.foldl_map, Prod.map, id_eq,
        codeListSource]
      convert ih (loc + 2) ((loc + 1, arity, body) :: code) using 1
      simp only [Nat.mul_zero, Nat.add_zero, Nat.mul_succ]
      congr 1
      funext acc pair
      rcases pair with ⟨⟨a, b⟩, i⟩
      simp only
      congr 2
      omega
  cases state with
  | mk known code =>
    simp only [codeList]
    rw [fold_eq]
    induction fns generalizing loc code with
    | nil => rfl
    | cons fn rest ih =>
      cases fn
      exact ih _ _

/-- The label formula applies to the executable direct-call pass. -/
theorem codeList_labels (loc : Nat) (fns : List (Nat × ClosLang.Exp)) (state : State) :
    (codeList loc fns state).2.map Prod.fst =
      ((List.range fns.length).map (fun i => loc + i * 2 + 1)).reverse ++
        state.2.map Prod.fst := by
  rw [codeList_eq_source]
  exact codeListSource_labels loc fns state

/-- New auxiliary labels are distinct. This supports the direct-call pass's
code-location invariant. -/
private theorem codeList_newLabels_nodup (loc count : Nat) :
    (((List.range count).map (fun i => loc + i * 2 + 1)).reverse).Nodup := by
  apply List.nodup_reverse.mpr
  apply List.Nodup.map (fun _ _ equal => by omega) List.nodup_range

/-- Appending generated code preserves distinct labels whenever the new range
is disjoint from the labels already in the state. -/
theorem codeList_labels_nodup (loc : Nat) (fns : List (Nat × ClosLang.Exp))
    (state : State) (oldDistinct : (state.2.map Prod.fst).Nodup)
    (fresh : ∀ i, i < fns.length → loc + i * 2 + 1 ∉ state.2.map Prod.fst) :
    ((codeList loc fns state).2.map Prod.fst).Nodup := by
  rw [codeList_labels]
  apply List.Nodup.append (codeList_newLabels_nodup loc fns.length) oldDistinct
  intro label generated old
  simp only [List.mem_reverse, List.mem_map, List.mem_range] at generated
  obtain ⟨i, bound, rfl⟩ := generated
  exact fresh i bound old

end Flapjack.Compiler.Backend.ClosCall
