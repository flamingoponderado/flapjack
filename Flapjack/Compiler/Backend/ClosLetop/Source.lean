module

public import Flapjack.Compiler.Backend.ClosLang.Syntax
public import Flapjack.Misc.ListEl

@[expose] public section

/-! Source-shaped total traversal for closure let-operation cleanup. -/
namespace Flapjack.Compiler.Backend.ClosLetop
open ClosLang

/-- Check that variables enumerate the bindings from the given index. -/
@[hol "cakeml/compiler/backend/clos_letopScript.sml" "var_list_def"]
def varList {α : Type} : Nat → List Exp → List α → Bool
  | _, [], [] => true
  | n, .var _ m :: xs, _ :: ys => (m == n) && varList (n + 1) xs ys
  | _, _, _ => false

/-- Recognize an operation applied to all its bound variables. -/
@[hol "cakeml/compiler/backend/clos_letopScript.sml" "dest_op_def"]
def destOp {α : Type} : Exp → List α → Option Op
  | .op _ op xs, args => if varList 0 xs args then some op else none
  | _, _ => none

mutual
/-- Clean up a closure expression in the original traversal order. -/
@[hol "cakeml/compiler/backend/clos_letopScript.sml" "let_op_sing_def"]
def compileSing : Exp → Exp
  | .var t v => .var t v
  | .ifThenElse t x y z => .ifThenElse t (compileSing x) (compileSing y) (compileSing z)
  | .let t xs body =>
      let ys := compileList xs
      let nextBody := compileSing body
      match destOp nextBody ys with
      | some op => .op t op ys
      | none => .let t ys nextBody
  | .raise t x => .raise t (compileSing x)
  | .handle t x y => .handle t (compileSing x) (compileSing y)
  | .op t op xs => .op t op (compileList xs)
  | .tick t x => .tick t (compileSing x)
  | .call t ticks dest xs => .call t ticks dest (compileList xs)
  | .app t loc x xs => .app t loc (compileSing x) (compileList xs)
  | .fn name loc vs arity body => .fn name loc vs arity (compileSing body)
  | .letrec names loc vs fns body => .letrec names loc vs (compileFuns fns) (compileSing body)

/-- Process expression lists in their original order. -/
@[hol "cakeml/compiler/backend/clos_letopScript.sml" "let_op_sing_def"]
def compileList : List Exp → List Exp
  | [] => []
  | x :: xs => compileSing x :: compileList xs

/-- Process recursive bodies without changing their arities. -/
@[hol "cakeml/compiler/backend/clos_letopScript.sml" "let_op_sing_def"]
def compileFuns : List (Nat × Exp) → List (Nat × Exp)
  | [] => []
  | (arity, body) :: rest => (arity, compileSing body) :: compileFuns rest
end

/-- Original list-shaped traversal, including its singleton recursion. -/
@[hol "cakeml/compiler/backend/clos_letopScript.sml" "let_op_def"]
noncomputable def compileSource : List Exp → List Exp
  | [] => []
  | x :: y :: xs => (@Flapjack.holHd Exp ⟨.var .none 0⟩ (compileSource [x])) :: compileSource (y :: xs)
  | [.var t v] => [.var t v]
  | [.ifThenElse t x y z] => [.ifThenElse t (@Flapjack.holHd Exp ⟨.var .none 0⟩ (compileSource [x])) (@Flapjack.holHd Exp ⟨.var .none 0⟩ (compileSource [y])) (@Flapjack.holHd Exp ⟨.var .none 0⟩ (compileSource [z]))]
  | [.let t xs x] =>
      let ys := compileSource xs
      let body := (@Flapjack.holHd Exp ⟨.var .none 0⟩ (compileSource [x]))
      match destOp body ys with
      | some op => [.op t op ys]
      | none => [.let t ys body]
  | [.raise t x] => [.raise t (@Flapjack.holHd Exp ⟨.var .none 0⟩ (compileSource [x]))]
  | [.handle t x y] => [.handle t (@Flapjack.holHd Exp ⟨.var .none 0⟩ (compileSource [x])) (@Flapjack.holHd Exp ⟨.var .none 0⟩ (compileSource [y]))]
  | [.op t op xs] => [.op t op (compileSource xs)]
  | [.tick t x] => [.tick t (@Flapjack.holHd Exp ⟨.var .none 0⟩ (compileSource [x]))]
  | [.call t ticks dest xs] => [.call t ticks dest (compileSource xs)]
  | [.app t loc x xs] => [.app t loc (@Flapjack.holHd Exp ⟨.var .none 0⟩ (compileSource [x])) (compileSource xs)]
  | [.fn name loc vs arity x] => [.fn name loc vs arity (@Flapjack.holHd Exp ⟨.var .none 0⟩ (compileSource [x]))]
  | [.letrec names loc vs fns x] =>
      let bodies := fns.attach.map fun ⟨entry, _member⟩ =>
        (entry.1, (@Flapjack.holHd Exp ⟨.var .none 0⟩ (compileSource [entry.2])))
      [.letrec names loc vs bodies (@Flapjack.holHd Exp ⟨.var .none 0⟩ (compileSource [x]))]
termination_by expressions => sizeOf expressions
decreasing_by
  all_goals try (have h := List.sizeOf_lt_of_mem ‹_›)
  all_goals simp_wf
  all_goals try omega
  all_goals try (cases y <;> simp_wf <;> omega)
  all_goals (cases entry; simp only [Prod.mk.sizeOf_spec] at *; omega)

private theorem compileFuns_as_map (functions : List (Nat × Exp)) :
    compileFuns functions = functions.map (fun (n, x) => (n, compileSing x)) := by
  induction functions with
  | nil => rfl
  | cons entry rest ih => cases entry; simp [compileFuns, ih]

/-- The original list recursion agrees with the singleton traversal. -/
@[simp] theorem compileSource_eq_list (expressions : List Exp) :
    compileSource expressions = compileList expressions := by
  induction expressions using compileSource.induct <;>
    simp_all [compileSource, compileList, compileSing, Flapjack.holHd, compileFuns_as_map]
  all_goals try (split <;> rfl)
  case case14 =>
    rename_i names loc vs fns x ihF ihBody
    simp only [List.map_attach_eq_pmap, List.pmap_eq_map]
    apply List.map_congr_left
    intro entry member
    cases entry with
    | mk arity body => simp [ihF arity body member]

/-- HOL's original and singleton/list traversals agree. -/
@[hol "cakeml/compiler/backend/clos_letopScript.sml" "let_op_sing_eq"]
theorem compileSource_sing_eq :
    (∀ e, compileSource [e] = [compileSing e]) ∧
    (∀ es, compileSource es = compileList es) ∧
    (∀ fns, compileFuns fns = fns.map (fun (n, x) =>
      (n, @Flapjack.holHd Exp ⟨.var .none 0⟩ (compileSource [x])))) := by
  refine ⟨?_, compileSource_eq_list, ?_⟩
  · intro e
    simp [compileList]
  · intro fns
    simp [compileFuns_as_map, compileSource_eq_list, compileList, Flapjack.holHd]

/-- The optimized list traversal preserves length; the original HOL theorem
is stated separately about the source-shaped traversal. -/
theorem compileList_length (xs : List Exp) : (compileList xs).length = xs.length := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [compileList, ih]

/-- The original HOL traversal preserves the length of its input. -/
@[hol "cakeml/compiler/backend/clos_letopScript.sml" "LENGTH_let_op"]
theorem compileSource_length (xs : List Exp) : (compileSource xs).length = xs.length := by
  rw [compileSource_eq_list]
  exact compileList_length xs

/-- The original incremental pass uses the source-shaped list traversal. -/
@[hol "cakeml/compiler/backend/clos_letopScript.sml" "compile_inc_def"]
noncomputable def compileIncSource {α β : Type} (program : List Exp × α) : List Exp × List β :=
  (compileSource program.1, [])

/-- The executed incremental traversal discards the auxiliary component.
It agrees with the original source definition by `compileSource_eq_list`. -/
def compileInc {α β : Type} (program : List Exp × α) : List Exp × List β :=
  (compileList program.1, [])

/-- The executable incremental pass agrees with the original. -/
theorem compileIncSource_eq_compileInc {α β : Type} (program : List Exp × α) :
    (compileIncSource program : List Exp × List β) = compileInc program := by
  simp [compileIncSource, compileInc]

/-- The two incremental passes are equal as functions. -/
theorem compileIncSource_eq {α β : Type} :
    (compileIncSource : List Exp × α → List Exp × List β) = compileInc := by
  funext program
  exact compileIncSource_eq_compileInc program

end Flapjack.Compiler.Backend.ClosLetop
