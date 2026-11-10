module

public import Flapjack.Compiler.Backend.ClosLang.Syntax
public import Flapjack.Misc.ListEl

@[expose] public section

/-! Source-shaped total traversal for closure tick removal. -/
namespace Flapjack.Compiler.Backend.ClosTicks
open ClosLang

mutual
/-- Remove ticks and reset call tick counts, retaining the other annotations. -/
@[hol "cakeml/compiler/backend/clos_ticksScript.sml" "remove_ticks_sing_def"]
def removeSing : Exp → Exp
  | .var t v => .var t v
  | .ifThenElse t x y z => .ifThenElse t (removeSing x) (removeSing y) (removeSing z)
  | .let t xs body => .let t (removeList xs) (removeSing body)
  | .raise t x => .raise t (removeSing x)
  | .handle t x y => .handle t (removeSing x) (removeSing y)
  | .op t op xs => .op t op (removeList xs)
  | .tick _ x => removeSing x
  | .call t _ dest xs => .call t 0 dest (removeList xs)
  | .app t loc x xs => .app t loc (removeSing x) (removeList xs)
  | .fn name loc vs arity body => .fn name loc vs arity (removeSing body)
  | .letrec names loc vs fns body => .letrec names loc vs (removeFuns fns) (removeSing body)

/-- Process expressions in their original order. -/
@[hol "cakeml/compiler/backend/clos_ticksScript.sml" "remove_ticks_sing_def"]
def removeList : List Exp → List Exp
  | [] => []
  | x :: xs => removeSing x :: removeList xs

/-- Process recursive function bodies without changing their arities. -/
@[hol "cakeml/compiler/backend/clos_ticksScript.sml" "remove_ticks_sing_def"]
def removeFuns : List (Nat × Exp) → List (Nat × Exp)
  | [] => []
  | (arity, body) :: rest => (arity, removeSing body) :: removeFuns rest
end

/-- Original list-shaped traversal, including its singleton recursion. -/
@[hol "cakeml/compiler/backend/clos_ticksScript.sml" "remove_ticks_def"]
noncomputable def removeSource : List Exp → List Exp
  | [] => []
  | x :: y :: xs => (@Flapjack.holHd Exp ⟨.var .none 0⟩ (removeSource [x])) :: removeSource (y :: xs)
  | [.var t v] => [.var t v]
  | [.ifThenElse t x y z] => [.ifThenElse t (@Flapjack.holHd Exp ⟨.var .none 0⟩ (removeSource [x])) (@Flapjack.holHd Exp ⟨.var .none 0⟩ (removeSource [y])) (@Flapjack.holHd Exp ⟨.var .none 0⟩ (removeSource [z]))]
  | [.let t xs x] =>
      [.let t (removeSource xs) (@Flapjack.holHd Exp ⟨.var .none 0⟩ (removeSource [x]))]
  | [.raise t x] => [.raise t (@Flapjack.holHd Exp ⟨.var .none 0⟩ (removeSource [x]))]
  | [.handle t x y] => [.handle t (@Flapjack.holHd Exp ⟨.var .none 0⟩ (removeSource [x])) (@Flapjack.holHd Exp ⟨.var .none 0⟩ (removeSource [y]))]
  | [.op t op xs] => [.op t op (removeSource xs)]
  | [.tick _ x] => removeSource [x]
  | [.call t _ dest xs] => [.call t 0 dest (removeSource xs)]
  | [.app t loc x xs] => [.app t loc (@Flapjack.holHd Exp ⟨.var .none 0⟩ (removeSource [x])) (removeSource xs)]
  | [.fn name loc vs arity x] => [.fn name loc vs arity (@Flapjack.holHd Exp ⟨.var .none 0⟩ (removeSource [x]))]
  | [.letrec names loc vs fns x] =>
      let bodies := fns.attach.map fun ⟨entry, _member⟩ =>
        (entry.1, (@Flapjack.holHd Exp ⟨.var .none 0⟩ (removeSource [entry.2])))
      [.letrec names loc vs bodies (@Flapjack.holHd Exp ⟨.var .none 0⟩ (removeSource [x]))]
termination_by expressions => sizeOf expressions
decreasing_by
  all_goals try (have h := List.sizeOf_lt_of_mem ‹_›)
  all_goals simp_wf
  all_goals try omega
  all_goals try (cases y <;> simp_wf <;> omega)
  all_goals (cases entry; simp only [Prod.mk.sizeOf_spec] at *; omega)

private theorem removeFuns_as_map (functions : List (Nat × Exp)) :
    removeFuns functions = functions.map (fun (n, x) => (n, removeSing x)) := by
  induction functions with
  | nil => rfl
  | cons entry rest ih => cases entry; simp [removeFuns, ih]

/-- The original list recursion agrees with the singleton traversal. -/
@[simp] theorem removeSource_eq_list (expressions : List Exp) :
    removeSource expressions = removeList expressions := by
  induction expressions using removeSource.induct <;>
    simp_all [removeSource, removeList, removeSing, Flapjack.holHd, removeFuns_as_map]
  case case13 =>
    rename_i names loc vs fns x ihF ihBody
    simp only [List.map_attach_eq_pmap, List.pmap_eq_map]
    apply List.map_congr_left
    intro entry member
    cases entry with
    | mk arity body => simp [ihF arity body member]

/-- HOL's original and singleton/list traversals agree. -/
@[hol "cakeml/compiler/backend/clos_ticksScript.sml" "remove_ticks_sing_eq"]
theorem removeSource_sing_eq :
    (∀ e, removeSource [e] = [removeSing e]) ∧
    (∀ es, removeSource es = removeList es) ∧
    (∀ fns, removeFuns fns = fns.map (fun (n, x) =>
      (n, @Flapjack.holHd Exp ⟨.var .none 0⟩ (removeSource [x])))) := by
  refine ⟨?_, removeSource_eq_list, ?_⟩
  · intro e
    simp [removeList]
  · intro fns
    simp [removeFuns_as_map, removeSource_eq_list, removeList, Flapjack.holHd]

/-- The optimized list traversal preserves length; the original HOL theorem
is stated separately about the source-shaped traversal. -/
theorem removeList_length (xs : List Exp) : (removeList xs).length = xs.length := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [removeList, ih]

/-- The original HOL traversal preserves the length of its input. -/
@[hol "cakeml/compiler/backend/clos_ticksScript.sml" "LENGTH_remove_ticks"]
theorem removeSource_length (xs : List Exp) : (removeSource xs).length = xs.length := by
  rw [removeSource_eq_list]
  exact removeList_length xs

/-- The original incremental pass uses the source-shaped list traversal. -/
@[hol "cakeml/compiler/backend/clos_ticksScript.sml" "compile_inc_def"]
noncomputable def compileIncSource {α β : Type} (program : List Exp × α) : List Exp × List β :=
  (removeSource program.1, [])

/-- The executed incremental traversal discards the auxiliary component.
It agrees with the original source definition by `removeSource_eq_list`. -/
def compileInc {α β : Type} (program : List Exp × α) : List Exp × List β :=
  (removeList program.1, [])

/-- The executable incremental pass agrees with the original. -/
theorem compileIncSource_eq_compileInc {α β : Type} (program : List Exp × α) :
    (compileIncSource program : List Exp × List β) = compileInc program := by
  simp [compileIncSource, compileInc]

/-- The two incremental passes are equal as functions. -/
@[simp] theorem compileIncSource_eq {α β : Type} :
    (compileIncSource : List Exp × α → List Exp × List β) = compileInc := by
  funext program
  exact compileIncSource_eq_compileInc program

end Flapjack.Compiler.Backend.ClosTicks
