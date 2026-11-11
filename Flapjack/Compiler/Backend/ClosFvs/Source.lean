module

public import Flapjack.Compiler.Backend.ClosLang.Syntax
public import Flapjack.Misc.ListEl

@[expose] public section

/-! Source-shaped total traversal for closure free-variable removal. -/
namespace Flapjack.Compiler.Backend.ClosFvs
open ClosLang

mutual
/-- Replace out-of-scope variables with the source type-error expression. -/
@[hol "cakeml/compiler/backend/clos_fvsScript.sml" "remove_fvs_sing_def"]
def removeSing (bound : Nat) : Exp → Exp
  | .var t v => if v < bound then .var t v else .op t (.memOp .el) []
  | .ifThenElse t x y z => .ifThenElse t (removeSing bound x) (removeSing bound y) (removeSing bound z)
  | .let t xs body =>
      let ys := removeList bound xs
      .let t ys (removeSing (bound + ys.length) body)
  | .raise t x => .raise t (removeSing bound x)
  | .handle t x y => .handle t (removeSing bound x) (removeSing (bound + 1) y)
  | .op t op xs => .op t op (removeList bound xs)
  | .tick t x => .tick t (removeSing bound x)
  | .call t ticks dest xs => .call t ticks dest (removeList bound xs)
  | .app t loc x xs => .app t loc (removeSing bound x) (removeList bound xs)
  | .fn name loc vs arity body =>
      let captured := (vs.map List.length).getD bound
      .fn name loc vs arity (removeSing (arity + captured) body)
  | .letrec names loc vs fns body =>
      let captured := (vs.map List.length).getD bound
      .letrec names loc vs (removeFuns fns.length captured fns)
        (removeSing (fns.length + bound) body)

/-- Remove free variables from a list in source order. -/
@[hol "cakeml/compiler/backend/clos_fvsScript.sml" "remove_fvs_sing_def"]
def removeList (bound : Nat) : List Exp → List Exp
  | [] => []
  | x :: xs => removeSing bound x :: removeList bound xs

/-- Process recursive functions with their shared captured-environment size. -/
@[hol "cakeml/compiler/backend/clos_fvsScript.sml" "remove_fvs_sing_def"]
def removeFuns (count captured : Nat) : List (Nat × Exp) → List (Nat × Exp)
  | [] => []
  | (arity, body) :: rest =>
      (arity, removeSing (arity + count + captured) body) :: removeFuns count captured rest
end

/-- Removing free variables leaves a recursive function list's length intact. This Lean helper supports the recursive cleanup proofs. -/
theorem removeFuns_length (count captured : Nat) (functions : List (Nat × ClosLang.Exp)) :
    (removeFuns count captured functions).length = functions.length := by
  induction functions with
  | nil => rfl
  | cons function rest ih => cases function; simp [removeFuns, ih]

/-- Original list-shaped free-variable removal. -/
@[hol "cakeml/compiler/backend/clos_fvsScript.sml" "remove_fvs_def"]
noncomputable def removeSource : Nat → List Exp → List Exp
  | _, [] => []
  | bound, x :: y :: xs => (@Flapjack.holHd Exp ⟨.var .none 0⟩ (removeSource (bound) [x])) :: removeSource bound (y :: xs)
  | bound, [.var t v] =>
      if v < bound then [.var t v] else [.op t (.memOp .el) []]
  | bound, [.ifThenElse t x y z] =>
      [.ifThenElse t (@Flapjack.holHd Exp ⟨.var .none 0⟩ (removeSource (bound) [x])) (@Flapjack.holHd Exp ⟨.var .none 0⟩ (removeSource (bound) [y])) (@Flapjack.holHd Exp ⟨.var .none 0⟩ (removeSource (bound) [z]))]
  | bound, [.let t xs x] =>
      let ys := removeSource bound xs
      [.let t ys (@Flapjack.holHd Exp ⟨.var .none 0⟩ (removeSource (bound + ys.length) [x]))]
  | bound, [.raise t x] => [.raise t (@Flapjack.holHd Exp ⟨.var .none 0⟩ (removeSource (bound) [x]))]
  | bound, [.handle t x y] => [.handle t (@Flapjack.holHd Exp ⟨.var .none 0⟩ (removeSource (bound) [x])) (@Flapjack.holHd Exp ⟨.var .none 0⟩ (removeSource (bound + 1) [y]))]
  | bound, [.op t op xs] => [.op t op (removeSource bound xs)]
  | bound, [.tick t x] => [.tick t (@Flapjack.holHd Exp ⟨.var .none 0⟩ (removeSource (bound) [x]))]
  | bound, [.call t ticks dest xs] => [.call t ticks dest (removeSource bound xs)]
  | bound, [.app t loc x xs] => [.app t loc (@Flapjack.holHd Exp ⟨.var .none 0⟩ (removeSource (bound) [x])) (removeSource bound xs)]
  | bound, [.fn name loc vs arity x] =>
      let captured := (vs.map List.length).getD bound
      [.fn name loc vs arity (@Flapjack.holHd Exp ⟨.var .none 0⟩ (removeSource (arity + captured) [x]))]
  | bound, [.letrec names loc vs fns x] =>
      let captured := (vs.map List.length).getD bound
      let bodies := fns.attach.map fun ⟨entry, _member⟩ =>
        (entry.1, (@Flapjack.holHd Exp ⟨.var .none 0⟩ (removeSource (entry.1 + fns.length + captured) [entry.2])))
      [.letrec names loc vs bodies (@Flapjack.holHd Exp ⟨.var .none 0⟩ (removeSource (fns.length + bound) [x]))]
termination_by _ expressions => sizeOf expressions
decreasing_by
  all_goals try (have h := List.sizeOf_lt_of_mem ‹_›)
  all_goals simp_wf
  all_goals try omega
  all_goals try (cases y <;> simp_wf <;> omega)
  all_goals (cases entry; simp only [Prod.mk.sizeOf_spec] at *; omega)

/-- The recursive bundle traversal preserves arities and source order. -/
theorem removeFuns_eq_map (count captured : Nat) (functions : List (Nat × Exp)) :
    removeFuns count captured functions =
      functions.map (fun (arity, body) => (arity, removeSing (arity + count + captured) body)) := by
  induction functions with
  | nil => rfl
  | cons entry rest ih => cases entry; simp [removeFuns, ih]

/-- The original list recursion agrees with the executable traversal. -/
@[simp] theorem removeSource_eq_list (bound : Nat) (expressions : List Exp) :
    removeSource bound expressions = removeList bound expressions := by
  induction bound, expressions using removeSource.induct <;>
    simp_all [removeSource, removeList, removeSing, Flapjack.holHd, removeFuns_eq_map]
  case case4 => split <;> rfl
  case case6 =>
    rename_i bound trace xs body ys ihList ihBody
    dsimp [ys] at ihBody
    simpa [ihList, Flapjack.holHd] using congrArg (@Flapjack.holHd Exp ⟨.var .none 0⟩) ihBody
  case case13 =>
    rename_i bound name loc vs arity body captured ih
    dsimp [captured] at ih
    simpa [Flapjack.holHd] using congrArg (@Flapjack.holHd Exp ⟨.var .none 0⟩) ih
  case case14 =>
    rename_i bound names loc vs fns body captured ihF ihBody
    dsimp [captured] at ihF
    simp only [List.map_attach_eq_pmap, List.pmap_eq_map]
    apply List.map_congr_left
    intro entry member
    cases entry with
    | mk arity body => simp [ihF arity body member]

/-- The original source and singleton traversals agree in all three forms. -/
@[hol "cakeml/compiler/backend/clos_fvsScript.sml" "remove_fvs_sing_eq"]
theorem removeSource_sing_eq :
    (∀ bound e, removeSource bound [e] = [removeSing bound e]) ∧
    (∀ bound es, removeSource bound es = removeList bound es) ∧
    (∀ count captured fns, removeFuns count captured fns =
      fns.map (fun (arity, body) =>
        (arity, @Flapjack.holHd Exp ⟨.var .none 0⟩ (removeSource (arity + count + captured) [body])))) := by
  refine ⟨?_, removeSource_eq_list, ?_⟩
  · intro bound e
    simp [removeList]
  · intro count captured fns
    simp [removeFuns_eq_map, removeList, Flapjack.holHd]

/-- The executable list traversal preserves length. -/
theorem removeList_length (bound : Nat) (xs : List Exp) : (removeList bound xs).length = xs.length := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [removeList, ih]

/-- The original free-variable traversal preserves list length. -/
@[hol "cakeml/compiler/backend/clos_fvsScript.sml" "LENGTH_remove_fvs"]
theorem removeSource_length (bound : Nat) (xs : List Exp) : (removeSource bound xs).length = xs.length := by
  rw [removeSource_eq_list]
  exact removeList_length bound xs

/-- Original free-variable removal for a closed program. -/
@[hol "cakeml/compiler/backend/clos_fvsScript.sml" "compile_def"]
noncomputable def compileSource (expressions : List Exp) : List Exp := removeSource 0 expressions

/-- Original compilation equals the singleton-derived list traversal. -/
@[hol "cakeml/compiler/backend/clos_fvsScript.sml" "compile_eq"]
theorem compileSource_eq_list (expressions : List Exp) : compileSource expressions = removeList 0 expressions := by
  simp [compileSource]

/-- Executed free-variable removal uses the equivalent total traversal. -/
def compile (expressions : List Exp) : List Exp := removeList 0 expressions

/-- Source and executable free-variable removal agree. -/
@[simp] theorem compileSource_eq_compile (expressions : List Exp) : compileSource expressions = compile expressions := by
  simp [compileSource, compile]

/-- Original incremental removal discards the auxiliary component. The input type and
output auxiliary element type are independent as in HOL. -/
@[hol "cakeml/compiler/backend/clos_fvsScript.sml" "compile_inc_def"]
noncomputable def compileIncSource {α β : Type} (program : List Exp × α) : List Exp × List β :=
  (compileSource program.1, [])

/-- The executable incremental pass uses the equivalent total traversal. -/
def compileInc {α β : Type} (program : List Exp × α) : List Exp × List β :=
  (compile program.1, [])

/-- Original and executable incremental passes agree. -/
theorem compileIncSource_eq_compileInc {α β : Type} (program : List Exp × α) :
    (compileIncSource program : List Exp × List β) = compileInc program := by
  simp [compileIncSource, compileInc]

/-- The source and executable incremental passes are equal as functions. -/
@[simp] theorem compileIncSource_eq {α β : Type} :
    (compileIncSource : List Exp × α → List Exp × List β) = compileInc := by
  funext program
  exact compileIncSource_eq_compileInc program

end Flapjack.Compiler.Backend.ClosFvs
