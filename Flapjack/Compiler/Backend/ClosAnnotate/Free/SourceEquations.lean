import Flapjack.Compiler.Backend.ClosAnnotate.Proofs.CodeLocations
import Flapjack.Misc.ListEl

/-! Source-shaped equations for closure free-variable discovery. -/
namespace Flapjack.Compiler.Backend.ClosAnnotate
open ClosLang DbVars

/-- Auxiliary alias for source-shaped equations of the optimized traversal.
The separate original recursion and its equivalence are in `Free.Original`
and `Free.OriginalEquivalence`. -/
def altFree (expressions : List Exp) : List Exp × DbVarSet := altFreeList expressions

private theorem mkUnion_empty_right (set : DbVarSet) : mkUnion set .empty = set := by
  cases set <;> rfl

/-- A singleton is transformed into exactly one expression. -/
theorem altFree_singleton (expression : Exp) :
    altFree [expression] = ([(altFreeSing expression).1], (altFreeSing expression).2) := by
  simp [altFree, altFreeList, mkUnion_empty_right]

/-- The source's non-singleton list equation. -/
theorem altFree_cons_cons (first second : Exp) (rest : List Exp) :
    altFree (first :: second :: rest) =
      ((altFree [first]).1 ++ (altFree (second :: rest)).1,
        mkUnion (altFree [first]).2 (altFree (second :: rest)).2) := by
  simp [altFree, altFreeList, mkUnion_empty_right]

/-- The original empty-list equation. -/
theorem altFree_nil : altFree [] = ([], .empty) := rfl

/-- The original variable equation. -/
theorem altFree_var (trace : BackendCommon.Tra) (index : Nat) :
    altFree [.var trace index] = ([.var trace index], .var index) := by
  simp [altFree_singleton, altFreeSing]

/-- The original conditional equation, including its singleton head reads. -/
theorem altFree_if (trace : BackendCommon.Tra) (condition yes no : Exp) :
    altFree [.ifThenElse trace condition yes no] =
      ([.ifThenElse trace
        (@Flapjack.holHd Exp ⟨.var .none 0⟩ (altFree [condition]).1)
        (@Flapjack.holHd Exp ⟨.var .none 0⟩ (altFree [yes]).1)
        (@Flapjack.holHd Exp ⟨.var .none 0⟩ (altFree [no]).1)],
       mkUnion (altFree [condition]).2 (mkUnion (altFree [yes]).2 (altFree [no]).2)) := by
  simp [altFree_singleton, altFreeSing, Flapjack.holHd]

/-- The original `let` equation preserves the optimization test on the
unmodified bindings and the original binding count. -/
theorem altFree_let (trace : BackendCommon.Tra) (bindings : List Exp) (body : Exp) :
    altFree [.let trace bindings body] =
      if noOverlap bindings.length (altFree [body]).2 && pureList bindings then
        ([.let trace (List.replicate bindings.length (const0 trace))
          (@Flapjack.holHd Exp ⟨.var .none 0⟩ (altFree [body]).1)],
          .shift bindings.length (altFree [body]).2)
      else
        ([.let trace (altFree bindings).1
          (@Flapjack.holHd Exp ⟨.var .none 0⟩ (altFree [body]).1)],
          mkUnion (altFree bindings).2 (.shift bindings.length (altFree [body]).2)) := by
  simp only [altFree_singleton, altFreeSing, Flapjack.holHd]
  unfold altFree
  split <;> simp [altFreeList_length]

theorem altFree_raise (trace : BackendCommon.Tra) (body : Exp) :
    altFree [.raise trace body] =
      ([.raise trace (@Flapjack.holHd Exp ⟨.var .none 0⟩ (altFree [body]).1)], (altFree [body]).2) := by
  simp [altFree_singleton, altFreeSing, Flapjack.holHd]

theorem altFree_tick (trace : BackendCommon.Tra) (body : Exp) :
    altFree [.tick trace body] =
      ([.tick trace (@Flapjack.holHd Exp ⟨.var .none 0⟩ (altFree [body]).1)], (altFree [body]).2) := by
  simp [altFree_singleton, altFreeSing, Flapjack.holHd]

theorem altFree_op (trace : BackendCommon.Tra) (op : Op) (args : List Exp) :
    altFree [.op trace op args] = ([.op trace op (altFree args).1], (altFree args).2) := by
  simp only [altFree_singleton, altFreeSing]
  rfl

theorem altFree_call (trace : BackendCommon.Tra) (ticks location : Nat) (args : List Exp) :
    altFree [.call trace ticks location args] =
      ([.call trace ticks location (altFree args).1], (altFree args).2) := by
  simp only [altFree_singleton, altFreeSing]
  rfl

theorem altFree_app (trace : BackendCommon.Tra) (location : Option Nat) (function : Exp) (args : List Exp) :
    altFree [.app trace location function args] =
      ([.app trace location (@Flapjack.holHd Exp ⟨.var .none 0⟩ (altFree [function]).1) (altFree args).1],
        mkUnion (altFree [function]).2 (altFree args).2) := by
  simp only [altFree_singleton, altFreeSing, Flapjack.holHd]
  rfl

theorem altFree_fn (name : Flapjack.Basis.Pure.MlString.MlString) (location : Option Nat)
    (vars : Option (List Nat)) (arity : Nat) (body : Exp) :
    altFree [.fn name location vars arity body] =
      ([.fn name location (some (varsToList (.shift arity (altFree [body]).2))) arity
        (@Flapjack.holHd Exp ⟨.var .none 0⟩ (altFree [body]).1)], .shift arity (altFree [body]).2) := by
  simp [altFree_singleton, altFreeSing, Flapjack.holHd]

theorem altFree_handle (trace : BackendCommon.Tra) (body handler : Exp) :
    altFree [.handle trace body handler] =
      ([.handle trace (@Flapjack.holHd Exp ⟨.var .none 0⟩ (altFree [body]).1)
        (@Flapjack.holHd Exp ⟨.var .none 0⟩ (altFree [handler]).1)],
        mkUnion (altFree [body]).2 (.shift 1 (altFree [handler]).2)) := by
  simp [altFree_singleton, altFreeSing, Flapjack.holHd]

theorem altFreeFuns_as_map (count : Nat) (functions : List (Nat × Exp)) :
    altFreeFuns count functions = functions.map (fun (arity, body) =>
      ((arity, @Flapjack.holHd Exp ⟨.var .none 0⟩ (altFree [body]).1),
        DbVarSet.shift (arity + count) (altFree [body]).2)) := by
  induction functions with
  | nil => rfl
  | cons entry rest ih =>
    obtain ⟨arity, body⟩ := entry
    simp [altFreeFuns, altFree_singleton, Flapjack.holHd, ih]

/-- Recursive declarations use the original function count to shift each
body, preserving the list order and each function arity. -/
theorem altFree_letrec (names : List Flapjack.Basis.Pure.MlString.MlString)
    (location : Option Nat) (vars : Option (List Nat)) (functions : List (Nat × Exp)) (body : Exp) :
    let results := functions.map (fun (arity, body) =>
      ((arity, @Flapjack.holHd Exp ⟨.var .none 0⟩ (altFree [body]).1),
        DbVarSet.shift (arity + functions.length) (altFree [body]).2))
    let live := listMkUnion (results.map Prod.snd)
    altFree [.letrec names location vars functions body] =
      ([.letrec names location (some (varsToList live)) (results.map Prod.fst)
        (@Flapjack.holHd Exp ⟨.var .none 0⟩ (altFree [body]).1)],
       mkUnion live (.shift functions.length (altFree [body]).2)) := by
  simp [altFree_singleton, altFreeSing, Flapjack.holHd, altFreeFuns_as_map]

end Flapjack.Compiler.Backend.ClosAnnotate
