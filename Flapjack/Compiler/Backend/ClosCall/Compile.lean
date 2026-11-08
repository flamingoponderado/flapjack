import Flapjack.Compiler.Backend.ClosCall.Calls

/-! Total direct-call compiler entry points. -/
namespace Flapjack.Compiler.Backend.ClosCall
open ClosLang

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
