import Flapjack.Compiler.Backend.ClosAnnotate.Free
import Flapjack.Misc.ListEl
import Mathlib.Tactic

/-! Source-shaped closure free-variable discovery. -/
namespace Flapjack.Compiler.Backend.ClosAnnotate
open ClosLang DbVars

/-- The original list-shaped free-variable recursion. The executed optimized
traversal agrees with it by the `alt_free_sing_eq` port. The attached map in
the recursive-group clause supplies only termination evidence. -/
@[hol "cakeml/compiler/backend/clos_annotateScript.sml" "alt_free_def"]
noncomputable def altFreeSource : List Exp → List Exp × DbVarSet
  | [] => ([], .empty)
  | x :: y :: xs =>
      let (first, firstVars) := altFreeSource [x]
      let (rest, restVars) := altFreeSource (y :: xs)
      (first ++ rest, mkUnion firstVars restVars)
  | [.var t v] => ([.var t v], .var v)
  | [.ifThenElse t x y z] =>
      let (a, av) := altFreeSource [x]
      let (b, bv) := altFreeSource [y]
      let (c, cv) := altFreeSource [z]
      ([.ifThenElse t (@Flapjack.holHd Exp ⟨.var .none 0⟩ a)
        (@Flapjack.holHd Exp ⟨.var .none 0⟩ b) (@Flapjack.holHd Exp ⟨.var .none 0⟩ c)],
        mkUnion av (mkUnion bv cv))
  | [.let t xs body] =>
      let m := xs.length
      let (nextBody, live) := altFreeSource [body]
      if noOverlap m live && xs.all pure then
        ([.let t (List.replicate m (const0 t)) (@Flapjack.holHd Exp ⟨.var .none 0⟩ nextBody)],
          .shift m live)
      else
        let (nextXs, argsLive) := altFreeSource xs
        ([.let t nextXs (@Flapjack.holHd Exp ⟨.var .none 0⟩ nextBody)],
          mkUnion argsLive (.shift xs.length live))
  | [.raise t x] =>
      let (body, live) := altFreeSource [x]
      ([.raise t (@Flapjack.holHd Exp ⟨.var .none 0⟩ body)], live)
  | [.tick t x] =>
      let (body, live) := altFreeSource [x]
      ([.tick t (@Flapjack.holHd Exp ⟨.var .none 0⟩ body)], live)
  | [.op t op xs] =>
      let (args, live) := altFreeSource xs
      ([.op t op args], live)
  | [.app t loc x xs] =>
      let (body, live) := altFreeSource [x]
      let (args, argsLive) := altFreeSource xs
      ([.app t loc (@Flapjack.holHd Exp ⟨.var .none 0⟩ body) args], mkUnion live argsLive)
  | [.fn name loc _ arity body] =>
      let (nextBody, live) := altFreeSource [body]
      let shifted := DbVarSet.shift arity live
      ([.fn name loc (some (varsToList shifted)) arity
        (@Flapjack.holHd Exp ⟨.var .none 0⟩ nextBody)], shifted)
  | [.letrec names loc _ functions body] =>
      let m := functions.length
      let (nextBody, bodyLive) := altFreeSource [body]
      let result := functions.attach.map fun ⟨entry, _member⟩ =>
        let (next, live) := altFreeSource [entry.2]
        ((entry.1, @Flapjack.holHd Exp ⟨.var .none 0⟩ next), DbVarSet.shift (entry.1 + m) live)
      let live := listMkUnion (result.map Prod.snd)
      ([.letrec names loc (some (varsToList live)) (result.map Prod.fst)
        (@Flapjack.holHd Exp ⟨.var .none 0⟩ nextBody)],
        mkUnion live (.shift functions.length bodyLive))
  | [.handle t x y] =>
      let (a, av) := altFreeSource [x]
      let (b, bv) := altFreeSource [y]
      ([.handle t (@Flapjack.holHd Exp ⟨.var .none 0⟩ a) (@Flapjack.holHd Exp ⟨.var .none 0⟩ b)],
        mkUnion av (.shift 1 bv))
  | [.call t ticks dest xs] =>
      let (args, live) := altFreeSource xs
      ([.call t ticks dest args], live)
termination_by expressions => sizeOf expressions
decreasing_by
  all_goals try (have h := List.sizeOf_lt_of_mem ‹_›)
  all_goals simp_wf
  all_goals try omega
  all_goals try (cases y <;> simp_wf <;> omega)
  all_goals (cases entry; simp only [Prod.mk.sizeOf_spec] at *; omega)

/-- The source recursive-group clause with an ordinary map; this supporting
equation has no separate HOL declaration. -/
theorem altFreeSource_letrec (names : List Flapjack.Basis.Pure.MlString.MlString)
    (loc : Option Nat) (vars : Option (List Nat)) (functions : List (Nat × Exp)) (body : Exp) :
    altFreeSource [.letrec names loc vars functions body] =
      let m := functions.length
      let (nextBody, bodyLive) := altFreeSource [body]
      let result := functions.map fun (n, expression) =>
        let (next, live) := altFreeSource [expression]
        ((n, @Flapjack.holHd Exp ⟨.var .none 0⟩ next), DbVarSet.shift (n + m) live)
      let live := listMkUnion (result.map Prod.snd)
      ([.letrec names loc (some (varsToList live)) (result.map Prod.fst)
        (@Flapjack.holHd Exp ⟨.var .none 0⟩ nextBody)],
        mkUnion live (.shift functions.length bodyLive)) := by
  simp only [altFreeSource, List.map_attach_eq_pmap]
  simp only [List.pmap_eq_map]

end Flapjack.Compiler.Backend.ClosAnnotate
