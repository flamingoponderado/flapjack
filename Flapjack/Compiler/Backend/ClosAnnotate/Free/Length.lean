module

public import Flapjack.Compiler.Backend.ClosAnnotate.Free.OriginalEquivalence
public import Flapjack.Misc.ListEl

@[expose] public section

/-! Length and singleton lemmas for source-shaped free-variable discovery. -/
namespace Flapjack.Compiler.Backend.ClosAnnotate
open ClosLang DbVars

/-- Free-variable discovery preserves the number of top-level expressions. -/
@[hol "cakeml/compiler/backend/clos_annotateScript.sml" "alt_free_LENGTH_LEMMA"]
theorem alt_free_LENGTH_LEMMA (xs : List Exp) :
    xs.length = (altFreeSource xs).1.length := by
  rw [altFreeSource_eq_altFree]
  simp [altFree, altFreeList_length]

/-- Free-variable discovery of a list keeps its length. -/
@[hol "cakeml/compiler/backend/clos_annotateScript.sml" "alt_free_LENGTH"]
theorem alt_free_LENGTH (xs : List Exp) (ys : List Exp) (l : DbVarSet)
    (run : altFreeSource xs = (ys, l)) : ys.length = xs.length := by
  have step := alt_free_LENGTH_LEMMA xs
  rw [run] at step
  exact step.symm

/-- Free-variable discovery of a singleton produces a singleton list. -/
@[hol "cakeml/compiler/backend/clos_annotateScript.sml" "alt_free_SING"]
theorem alt_free_SING (x : Exp) (ys : List Exp) (l : DbVarSet)
    (run : altFreeSource [x] = (ys, l)) : ∃ y, ys = [y] := by
  have length := alt_free_LENGTH [x] ys l run
  cases ys with
  | nil => simp at length
  | cons y rest =>
    cases rest with
    | nil => exact ⟨y, rfl⟩
    | cons z rest => simp at length

/-- The first projection of free-variable discovery keeps the input length. -/
@[hol "cakeml/compiler/backend/clos_annotateScript.sml" "LENGTH_FST_alt_free"]
theorem LENGTH_FST_alt_free (fns : List Exp) : (altFreeSource fns).1.length = fns.length := by
  exact alt_free_LENGTH fns (altFreeSource fns).1 (altFreeSource fns).2 rfl

/-- A singleton free-variable discovery is exactly the singleton of its head. -/
@[hol "cakeml/compiler/backend/clos_annotateScript.sml" "HD_FST_alt_free"]
theorem HD_FST_alt_free (x1 : Exp) :
    [@holHd Exp ⟨.var .none 0⟩ (altFreeSource [x1]).1] = (altFreeSource [x1]).1 := by
  obtain ⟨y, hy⟩ := alt_free_SING x1 (altFreeSource [x1]).1 (altFreeSource [x1]).2 rfl
  rw [hy]
  simp [holHd]

/-- Discovery of a cons is the head of the singleton discovery consed onto the
discovery of the tail. -/
@[hol "cakeml/compiler/backend/clos_annotateScript.sml" "alt_free_CONS"]
theorem alt_free_CONS (x : Exp) (xs : List Exp) :
    (altFreeSource (x :: xs)).1 =
      @holHd Exp ⟨.var .none 0⟩ (altFreeSource [x]).1 :: (altFreeSource xs).1 := by
  have head : (altFreeSource [x]).1 = [(altFreeSing x).1] := by
    rw [altFreeSource_eq_altFree]
    simp [altFree, altFreeList]
  have body : (altFreeSource (x :: xs)).1 = (altFreeSing x).1 :: (altFreeList xs).1 := by
    rw [altFreeSource_eq_altFree]
    simp [altFree, altFreeList]
  have tail : (altFreeSource xs).1 = (altFreeList xs).1 := by
    rw [altFreeSource_eq_altFree]
    simp [altFree]
  rw [body, head, tail]
  simp [holHd]

end Flapjack.Compiler.Backend.ClosAnnotate
