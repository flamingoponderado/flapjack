import Flapjack.Compiler.Backend.ClosCall

/-! Appending pre-existing auxiliary code to the closure-call pass state.
These lemmas concern Flapjack's fuel-bounded traversal and retry wrapper;
they have no direct HOL originals. -/
namespace Flapjack.Compiler.Backend.ClosCall

open Flapjack ClosLang

def appendAux (state : State) (old : List (Nat × Nat × Exp)) : State :=
  (state.1, state.2 ++ old)

theorem insertEach_appendAux (loc count : Nat) (state : State) (old : List (Nat × Nat × Exp)) :
    insertEach loc count (appendAux state old) = appendAux (insertEach loc count state) old := by
  rfl

theorem codeList_appendAux (loc : Nat) (fns : List (Nat × Exp)) (state : State)
    (old : List (Nat × Nat × Exp)) :
    codeList loc fns (appendAux state old) = appendAux (codeList loc fns state) old := by
  simp only [codeList, appendAux]
  generalize fns.zip (List.range fns.length) = entries
  induction entries generalizing state with
  | nil => rfl
  | cons entry entries ih =>
    rcases entry with ⟨⟨arity, body⟩, index⟩
    simpa only [List.foldl_cons, List.cons_append] using
      ih (state := (state.1, (loc + 2 * index + 1, arity, body) :: state.2))

private theorem bind_map_option {A B C : Type} (value : Option A) (f : A → B) (g : B → Option C) :
    (value.map f).bind g = value.bind (fun x => g (f x)) := by
  cases value <;> rfl

/-- Both mutually recursive traversals preserve an arbitrary suffix of old
auxiliary code, including on exhaustion and speculative retries. -/
theorem callsFuel_appendAux_pair (fuel : Nat) :
    (∀ e state old, callsFuel fuel e (appendAux state old) =
      (callsFuel fuel e state).map (fun (out, result) => (out, appendAux result old))) ∧
    (∀ es state old, callsListFuel fuel es (appendAux state old) =
      (callsListFuel fuel es state).map (fun (out, result) => (out, appendAux result old))) := by
  induction fuel with
  | zero =>
    constructor
    · intro e state old
      simp [callsFuel]
    · intro es state old
      cases es <;> simp [callsListFuel]
  | succ fuel ih =>
    obtain ⟨ihE, ihL⟩ := ih
    constructor
    · intro e state old
      cases e <;> simp [callsFuel, ihE, ihL, insertEach_appendAux, codeList_appendAux, bind_map_option,
        Function.comp_def, apply_ite]
      case app t loc expression args =>
        cases loc <;> simp [appendAux, apply_ite] <;> rfl
      all_goals simp [appendAux]
    · intro es state old
      cases es <;> simp [callsListFuel, ihE, ihL, bind_map_option, Function.comp_def]

/-- The bounded retry wrapper preserves the same auxiliary-code suffix. -/
theorem callsListBounded_appendAux (fuel : Nat) (es : List Exp) (state : State)
    (old : List (Nat × Nat × Exp)) :
    callsListBounded fuel es (appendAux state old) =
      (callsListBounded fuel es state).map (fun (out, result) => (out, appendAux result old)) := by
  unfold callsListBounded
  rw [(callsFuel_appendAux_pair fuel).2]
  cases run : callsListFuel fuel es state with
  | none =>
    simpa [run] using (callsFuel_appendAux_pair (max fuel (listBudget es + 1))).2 es state old
  | some result => simp

end Flapjack.Compiler.Backend.ClosCall
