module

public import Flapjack.Compiler.Backend.ClosCall.Free
public import Flapjack.Compiler.Backend.ClosKnown.Inline.Free.Correct
public import Flapjack.Misc.ListEl

@[expose] public section

/-! Source lemmas about the direct-call free-variable traversal. -/
namespace Flapjack.Compiler.Backend.ClosCall
open ClosLang DbVars ClosKnown

/-- The list traversal agrees with the single-expression traversal on a
singleton list, and HOL's `free` and `free_list` are the same list recursion
here: `free` and `freeList` both abbreviate `ClosKnown.freeHOL`, whose clauses
are exactly HOL's `free_list` clauses, so the second conjunct is definitional. -/
@[hol "cakeml/compiler/backend/clos_callScript.sml" "free_sing_eq"]
theorem free_sing_eq :
    (∀ expression, free [expression] = (fun (e, vs) => ([e], vs)) (freeSing expression)) ∧
    (∀ es, free es = freeList es) := by
  constructor
  · intro expression
    simp [free, freeHOL, mkUnion_empty_right]
  · intro es
    rfl

/-- Free-variable analysis preserves the number of top-level expressions. -/
@[hol "cakeml/compiler/backend/clos_callScript.sml" "free_LENGTH"]
theorem free_LENGTH (xs : List Exp) (ys : List Exp) (vars : DbVarSet)
    (run : free xs = (ys, vars)) : ys.length = xs.length := by
  obtain ⟨result, fuel⟩ :=
    freeListFuel_succeeds (listBudget xs + 1) xs (Nat.lt_succ_self _)
  have length := freeListFuel_length (listBudget xs + 1) xs result.1 result.2 fuel
  have agreement := (freeFuel_correct (listBudget xs + 1)).2 xs result.1 result.2 fuel
  have run' : freeHOL xs = (ys, vars) := run
  have eq := agreement.trans run'
  have first := congrArg Prod.fst eq
  simp at first
  rw [← first]
  exact length

/-- Free-variable analysis of a singleton produces a singleton list. -/
@[hol "cakeml/compiler/backend/clos_callScript.sml" "free_SING"]
theorem free_SING (x : Exp) (ys : List Exp) (l : DbVarSet) (run : free [x] = (ys, l)) :
    ∃ y, ys = [y] := by
  have length := free_LENGTH [x] ys l run
  cases ys with
  | nil => simp at length
  | cons y rest =>
    cases rest with
    | nil => exact ⟨y, rfl⟩
    | cons z rest => simp at length

/-- The first projection of the traversal keeps the input length. -/
@[hol "cakeml/compiler/backend/clos_callScript.sml" "LENGTH_FST_free"]
theorem LENGTH_FST_free (fns : List Exp) : (free fns).1.length = fns.length := by
  cases h : free fns with
  | mk ys l => exact free_LENGTH fns ys l h

/-- A singleton traversal is exactly the singleton of its head. -/
@[hol "cakeml/compiler/backend/clos_callScript.sml" "HD_FST_free"]
theorem HD_FST_free (x1 : Exp) :
    [@holHd Exp ⟨.var .none 0⟩ (free [x1]).1] = (free [x1]).1 := by
  obtain ⟨y, hy⟩ := free_SING x1 (free [x1]).1 (free [x1]).2 rfl
  rw [hy]
  simp [holHd]

/-- The traversal of a cons is the head of the singleton traversal consed onto
the traversal of the tail. -/
@[hol "cakeml/compiler/backend/clos_callScript.sml" "free_CONS"]
theorem free_CONS (x : Exp) (xs : List Exp) :
    (free (x :: xs)).1 = @holHd Exp ⟨.var .none 0⟩ (free [x]).1 :: (free xs).1 := by
  have head : (free [x]).1 = [(freeExpHOL x).1] := by
    simp [free, freeHOL]
  have body : (free (x :: xs)).1 = (freeExpHOL x).1 :: (freeHOL xs).1 := by
    simp [free, freeHOL]
  rw [body, head]
  simp [holHd]

/-- A list element at an in-bounds index is a member.  HOL's two conjuncts
    `i < LENGTH xs /\ x = EL i xs` are one premise. -/
@[hol "cakeml/compiler/backend/clos_callScript.sml" "EL_MEM_LEMMA"
  (total_function_inhabitants := [α])]
theorem EL_MEM_LEMMA {α : Type} [Nonempty α] (xs : List α) (i : Nat) (x : α)
    (h : i < xs.length ∧ x = holEl i xs) : x ∈ xs := by
  obtain ⟨bound, eq⟩ := h
  rw [eq, holEl_eq_getElem i xs bound]
  exact List.get_mem xs ⟨i, bound⟩

end Flapjack.Compiler.Backend.ClosCall
