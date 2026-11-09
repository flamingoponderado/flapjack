module

public import Flapjack.Compiler.Backend.ClosCall.Calls
public import Flapjack.Misc.ListEl

@[expose] public section

/-! Total direct-call compiler entry points. -/
namespace Flapjack.Compiler.Backend.ClosCall
open ClosLang
instance compileInst1 : Nonempty Exp := ⟨.var .none 0⟩

/-- The list traversal is the single-list form proved equivalent to HOL's
`calls` by `calls_sing_eq`. -/
@[hol "cakeml/compiler/backend/clos_callScript.sml" "calls_def"]
abbrev calls : List Exp → State → List Exp × State := callsSingList

/-- The list traversal agrees with the single-expression traversal. -/
@[hol "cakeml/compiler/backend/clos_callScript.sml" "calls_sing_eq"]
theorem callsSing_eq :
    (∀ e state, calls [e] state = (let (out, next) := callsSing e state; ([out], next))) ∧
    (∀ es state, calls es state = callsSingList es state) := by
  constructor
  · intro e state
    simp [calls, callsSingList]
  · intro es state
    rfl

/-- The list clauses of HOL's `calls_def` hold for the shared traversal.
The singleton constructor clauses follow from `callsSing_eq` and `callsSing`. -/
theorem calls_list_equations (x y : Exp) (xs : List Exp) (state : State) :
    calls [] state = ([], state) ∧
      calls (x :: y :: xs) state =
        (let (first, middle) := calls [x] state
         let (rest, final) := calls (y :: xs) middle
         (first ++ rest, final)) := by
  constructor
  · simp [calls, callsSingList]
  · cases first : callsSing x state with
    | mk out middle =>
      cases rest : callsSingList (y :: xs) middle with
      | mk tail final =>
        simp [calls, callsSingList, first, rest]

/-- Constructor equations of HOL's original list recursion, stated using
HOL's head operation. They are comparison evidence for `calls_def`, not a
separately named HOL theorem. -/
theorem calls_singleton_simple_equations :
    (∀ t v s, calls [.var t v] s = ([.var t v], s)) ∧
    (∀ t x y z s, calls [.ifThenElse t x y z] s =
      (let (xs, s) := calls [x] s
       let (ys, s) := calls [y] s
       let (zs, s) := calls [z] s
       ([.ifThenElse t (Flapjack.holHd xs) (Flapjack.holHd ys) (Flapjack.holHd zs)], s))) ∧
    (∀ t xs body s, calls [.let t xs body] s =
      (let (xs, s) := calls xs s
       let (body, s) := calls [body] s
       ([.let t xs (Flapjack.holHd body)], s))) ∧
    (∀ t x s, calls [.raise t x] s =
      (let (x, s) := calls [x] s; ([.raise t (Flapjack.holHd x)], s))) ∧
    (∀ t x s, calls [.tick t x] s =
      (let (x, s) := calls [x] s; ([.tick t (Flapjack.holHd x)], s))) ∧
    (∀ t x y s, calls [.handle t x y] s =
      (let (x, s) := calls [x] s
       let (y, s) := calls [y] s
       ([.handle t (Flapjack.holHd x) (Flapjack.holHd y)], s))) ∧
    (∀ t ticks dest xs s, calls [.call t ticks dest xs] s =
      (let (xs, s) := calls xs s; ([.call t ticks dest xs], s))) ∧
    (∀ t op xs s, calls [.op t op xs] s =
      (let (xs, s) := calls xs s; ([.op t op xs], s))) := by
  repeat' constructor
  all_goals intros
  all_goals simp only [calls, callsSingList, callsSing, Flapjack.holHd]

/-- Length-checked zip traversal represents HOL's `EVERY2`. This generic
comparison lemma has no separate HOL declaration. -/
theorem every2_length_zip {α β : Type} (p : α → β → Bool) (xs : List α) (ys : List β) :
    (xs.length == ys.length && (xs.zip ys).all (fun (x, y) => p x y)) = true ↔
      List.Forall₂ (fun x y => p x y = true) xs ys := by
  induction xs generalizing ys with
  | nil => cases ys <;> simp
  | cons x xs ih => cases ys <;> simp_all [List.forall₂_cons, and_left_comm]

/-- The application, function and recursive-function clauses of HOL's list
recursion. The length-and-zip condition represents HOL's `EVERY2`. -/
theorem calls_singleton_closure_equations :
    (∀ t loc x xs s, calls [.app t loc x xs] s =
      (let (xs, s) := calls xs s
       let (body, s) := calls [x] s
       let body := Flapjack.holHd body
       let n := loc.getD 0
       if loc.isSome && (sptLookup n s.1).isSome then
         if ClosLang.pure x then ([.call t xs.length (n + 1) xs], s)
         else ([.let (BackendCommon.mkCons t 0) (xs ++ [body])
           (.call (BackendCommon.mkCons t 1) xs.length (n + 1)
             (variablesSource .none 2 xs.length))], s)
       else ([.app t loc body xs], s))) ∧
    (∀ name loc ws arity body s, calls [.fn name loc ws arity body] s =
      (let n := loc.getD 0
       let fresh := insertEachSource n 1 s
       let (out, fresh) := calls [body] fresh
       let fresh := (fresh.1, (n + 1, arity, Flapjack.holHd out) :: fresh.2)
       if closed (.fn name loc ws arity (Flapjack.holHd out)) then
         ([.fn name loc ws arity (.call .none 0 (n + 1) (variablesSource .none 1 arity))], fresh)
       else
         let (out, s) := calls [body] s
         ([.fn name loc ws arity (Flapjack.holHd out)], s))) ∧
    (∀ names loc ws fns body s, calls [.letrec names loc ws fns body] s =
      (let n := loc.getD 0
       let fresh := insertEachSource n fns.length s
       let (bodies, fresh) := calls (fns.map Prod.snd) fresh
       if fns.length == bodies.length && (fns.zip bodies).all (fun (fn, code) =>
          closed (.fn (Flapjack.Basis.Pure.MlString.ofString "") none none fn.1 code)) then
         let fresh := codeListSource n ((fns.map Prod.fst).zip bodies) fresh
         let (out, s) := calls [body] fresh
         ([.letrec names loc ws (callsListSource .none 1 n fns) (Flapjack.holHd out)], s)
       else
         let (bodies, s) := calls (fns.map Prod.snd) s
         let (out, s) := calls [body] s
         ([.letrec names loc ws ((fns.map Prod.fst).zip bodies) (Flapjack.holHd out)], s))) := by
  constructor
  · intro t loc x xs s
    cases loc <;> simp only [calls, callsSingList, callsSing, Flapjack.holHd,
      Option.isSome_none, Option.isSome_some, Option.getD_none, Option.getD_some,
      Bool.false_and, Bool.true_and, Bool.false_eq_true, ↓reduceIte]
    all_goals split_ifs <;> rfl
  · constructor
    · intros
      simp only [calls, callsSingList, callsSing, Flapjack.holHd]
      split <;> rfl
    · intros
      simp only [calls, callsSingList, callsSing, Flapjack.holHd]
      split <;> rfl

/-- Conditionally apply direct-call conversion from the empty state. -/
@[hol "cakeml/compiler/backend/clos_callScript.sml" "compile_def"]
def compile (enabled : Bool) (es : List Exp) : List Exp × State :=
  if enabled then calls es (.ln, []) else (es, (.ln, []))

/-- Convert one incremental program, discarding its incoming auxiliary payload. -/
@[hol "cakeml/compiler/backend/clos_callScript.sml" "compile_inc_def"]
def compileInc {A : Type} (known : NumSet) (program : List Exp × A) :
    NumSet × (List Exp × List (Nat × Nat × Exp)) :=
  let (es, next) := calls program.1 (known, [])
  (next.1, (es, next.2))

/-- Incremental conversion can be disabled, in which case both inputs pass through. -/
@[hol "cakeml/compiler/backend/clos_callScript.sml" "cond_call_compile_inc_def"]
def condCallCompileInc (enabled : Bool) (known : NumSet)
    (program : List Exp × List (Nat × Nat × Exp)) :
    NumSet × (List Exp × List (Nat × Nat × Exp)) :=
  if enabled then compileInc known program else (known, program)

/-- The original compiler equations expressed with the single-list traversal. -/
@[hol "cakeml/compiler/backend/clos_callScript.sml" "compile_eq"]
theorem compile_eq (es : List Exp) :
    compile false es = (es, (.ln, [])) ∧
    compile true es = (let (xs, state) := callsSingList es (.ln, []); (xs, state)) := by
  simp [compile, calls]

/-- The incremental compiler expressed with the single-list traversal. -/
@[hol "cakeml/compiler/backend/clos_callScript.sml" "compile_inc_eq"]
theorem compileInc_eq {A : Type} (known : NumSet) (es : List Exp) (old : A) :
    compileInc known (es, old) =
      (let (out, next) := callsSingList es (known, []); (next.1, (out, next.2))) := by
  rfl

end Flapjack.Compiler.Backend.ClosCall
