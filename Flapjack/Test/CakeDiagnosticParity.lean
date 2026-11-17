module

public import Flapjack.Compiler.Inference.Infer.Diagnostics
public import Flapjack.CakeParser.Frontend

-- Checks below run compiled code from these modules.
public meta import Flapjack.Basis.Pure.MlString
public meta import Flapjack.Compiler.Inference.Infer.Core
public meta import Flapjack.Compiler.Inference.Infer.Diagnostics
public meta import Flapjack.CakeParser.Frontend
@[expose] public section

/-! Original inferencer message and source-location formatting for undefined
variables and selected built-in type mismatches. -/
namespace Flapjack.Test.CakeDiagnosticParity
open Flapjack Flapjack.AstHOL Flapjack.Misc.Location
open Flapjack.Compiler.Inference.Infer Flapjack.Compiler.Inference.Infer.Core
open Flapjack.Compiler.Inference.Infer.Diagnostics Flapjack.Basis.Pure.MlString

private def loc : Locs := .locs (.posn 0 11) (.posn 0 15)
private def qname : NamespaceHOL.Ident MlString MlString := .long (ofString "A") (.short (ofString "foo"))

-- HOL's operator table also covers unsafe and thunk operators, even though
-- inference reports their dedicated errors before consulting their arities.
#guard opToString .aallocFixed == (ofString "AallocFixed", 1)
#guard opToString (.thunkOp (.updateThunk .notEvaluated)) == (ofString "UpdateThunk", 2)
#guard opToString (.arith .fma .float64T) == (ofString "Arith", 3)
#guard opToString (.arith .fma .intT) == (ofString "Arith", 0)

#guard renderUnsupportedPrimitive [] (.primitiveArity .opref 12) ==
  some (ofString "### ERROR: type error\nPrimitive Opref given 12 arguments, but expects 1 at unknown location\nProgram exited with nonzero exit code.\n").explode

-- HOL add_constraints rejects unequal lists with this internal-error message.
#guard match constrainMany 20 [] [.uvar 0] ⟨3, .ln, 7⟩ with
  | (.error .badConstraintLists, _) => true
  | _ => false

#guard match withLoc loc emptyEnv (constrainMany 20 [] [.uvar 0]) ⟨3, .ln, 7⟩ with
  | (.error (.located actual .badConstraintLists), _) => actual == loc
  | _ => false

-- The source retains fresh-variable allocation when a later pattern fails.
#guard match inferPatternState 100 100 emptyEnv
    (.pcon none [.pvar (ofString "a"), .plit (.float64 0)]) ⟨3, .ln, 7⟩ with
  | (.error .floatPattern, state) =>
      state.nextUvar == 4 && state.nextId == 7 && sptIsEmpty state.subst
  | _ => false

-- A datatype check fails after allocating its type identifier in HOL.
#guard match inferDeclsState 100 100 emptyEnv
    [.dtype (.locs (.posn 0 0) (.posn 0 1))
      [([], ofString "t", [(ofString "C", []), (ofString "C", [])])]] ⟨3, .ln, 7⟩ with
  | (.error (.located _ (.sourceTypeMessage message)), state) =>
      message == ofString "Duplicate constructor C in the definition of type t" &&
        state.nextUvar == 3 && state.nextId == 8 && sptIsEmpty state.subst
  | _ => false

#guard renderUnsupportedPrimitive [] .badConstraintLists ==
  some (ofString "### ERROR: type error\nInternal error: Bad call to add_constraints at unknown location\nProgram exited with nonzero exit code.\n").explode

#guard renderUnsupportedPrimitive [] (.located loc .badConstraintLists) ==
  some (ofString "### ERROR: type error\nInternal error: Bad call to add_constraints at line 1\n\n\n           ^^^^^\n\nProgram exited with nonzero exit code.\n").explode

#guard match inferExprFuel 100 100 emptyEnv (.lannot (.var qname) loc) ⟨0, .ln, 15⟩ with
  | .error (.located actual (.undefinedVariable (.long a (.short b)))) =>
      actual == loc && a == ofString "A" && b == ofString "foo"
  | _ => false

#guard renderUndefinedVariable (ofString "val x = A.foo;").explode (.located loc (.undefinedVariable qname)) ==
  some (ofString "### ERROR: type error\nUndefined variable: A.foo at line 1\n\nval x = A.foo;\n           ^^^^^\n\nProgram exited with nonzero exit code.\n").explode

#guard renderSourceTypeError (ofString "val x = A.foo;").explode
    (.located loc (.sourceTypeMessage (ofString "Undefined type constructor: A.foo"))) ==
  some (ofString "### ERROR: type error\nUndefined type constructor: A.foo at line 1\n\nval x = A.foo;\n           ^^^^^\n\nProgram exited with nonzero exit code.\n").explode

-- The executable inference path calls the source structured-error checker.
#guard match Flapjack.CakeParser.Frontend.parseSourceFuel 500 500
    (ofString "val x : missing = 1;").explode with
  | .success decls => match inferProgramFuel 500 500 decls with
    | .error (.located _ (.sourceTypeMessage message)) =>
        message == ofString "Undefined type constructor: missing"
    | _ => false
  | _ => false

#guard match Flapjack.CakeParser.Frontend.parseSourceFuel 500 500
    (ofString "type 'a wrap = 'a; val x : (int,int) wrap = 1;").explode with
  | .success decls => match inferProgramFuel 500 500 decls with
    | .error (.located _ (.sourceTypeMessage message)) =>
        message == ofString "Type constructor wrap given 2 arguments, but expected 1"
    | _ => false
  | _ => false

#guard sourceLocation (ofString "val x =\n missing;").explode
    (some (.locs (.posn 1 1) (.posn 1 8))) ==
  (ofString "line 2\n\n missing;\n ^^^^^^^^\n").explode

#guard renderTypeMismatch (ofString "val x = 1 + True;").explode
    (.located (.locs (.posn 0 11) (.posn 0 20))
      (.typeMismatch (.app [.app [] 5, .app [] 5] 4) (.app [.app [] 1, .uvar 1] 4))) ==
  some (ofString "### ERROR: type error\nType mismatch between int -> int and bool -> _1 at line 1\n\nval x = 1 + True;\n           ^^^^^^^^^^\n\nProgram exited with nonzero exit code.\n").explode

-- A type hidden by a local declaration is printed by numeric identifier.
#guard renderTypeMismatch [] (.located loc (.typeMismatch (.app [] 5) (.app [] 15))) ==
  some (ofString "### ERROR: type error\nType mismatch between int and 15 at line 1\n\n\n           ^^^^^\n\nProgram exited with nonzero exit code.\n").explode

#guard renderTypeMismatch [] (.located loc (.typeMismatch (.app [.app [] 15] 6) (.app [] 4))) ==
  some (ofString "### ERROR: type error\nType mismatch between 15 list and <bad function type> at line 1\n\n\n           ^^^^^\n\nProgram exited with nonzero exit code.\n").explode

#guard renderTypeMismatch [] (.located loc
    (.typeMismatchEnv (.bind [] [(ofString "M", .bind [(ofString "t", ([], .app [] 15))] [])])
      (.app [] 5) (.app [] 15))) ==
  some (ofString "### ERROR: type error\nType mismatch between int and M.t at line 1\n\n\n           ^^^^^\n\nProgram exited with nonzero exit code.\n").explode

-- Original cake_type_display_probe.out captures both arbitrary bytes and
-- searching a later entry with a duplicated type name.
#guard renderTypeMismatch [] (.located loc
    (.typeMismatchEnv (.bind [(.implode [255, 0], ([], .app [] 15))] []) (.app [] 5) (.app [] 15))) ==
  some ((ofString "### ERROR: type error\nType mismatch between int and ").explode ++
    [255, 0] ++ (ofString " at line 1\n\n\n           ^^^^^\n\nProgram exited with nonzero exit code.\n").explode)

#guard renderTypeMismatch [] (.located loc
    (.typeMismatchEnv (.bind [(ofString "first", ([], .app [] 15)),
                               (ofString "first", ([], .app [] 16))] [])
      (.app [] 5) (.app [] 16))) ==
  some (ofString "### ERROR: type error\nType mismatch between int and first at line 1\n\n\n           ^^^^^\n\nProgram exited with nonzero exit code.\n").explode

-- The nested function, tuple and variable formatting is captured in
-- cake_type_diagnostic_probe.out from the original inferencer.
#guard renderTypeMismatch [] (.located loc
    (.typeMismatch (.app [.app [.app [] 5, .app [] 1] 4] 6) (.app [.app [] 1, .app [] 5] 9))) ==
  some (ofString "### ERROR: type error\nType mismatch between (int -> bool) list and bool * int at line 1\n\n\n           ^^^^^\n\nProgram exited with nonzero exit code.\n").explode

-- The original check chooses the first name that appears again later.
#guard match Flapjack.CakeParser.Frontend.parseSourceFuel 500 500
    (ofString "datatype t = A | B | A | B;").explode with
  | .success decls => match inferProgramFuel 500 500 decls with
    | .error (.located _ (.sourceTypeMessage message)) =>
        message == ofString "Duplicate constructor A in the definition of type t"
    | _ => false
  | _ => false

-- Constructor duplication is reported before duplicate type variables or
-- invalid constructor argument types, as in the source checker.
#guard match Flapjack.CakeParser.Frontend.parseSourceFuel 500 500
    (ofString "datatype ('a,'a) t = A missing | A;").explode with
  | .success decls => match inferProgramFuel 500 500 decls with
    | .error (.located _ (.sourceTypeMessage message)) =>
        message == ofString "Duplicate constructor A in the definition of type t"
    | _ => false
  | _ => false

-- The inferred pattern environment is reversed: find_dup selects b first.
-- Declaration patterns and match patterns retain distinct diagnostics.
#guard match Flapjack.CakeParser.Frontend.parseSourceFuel 500 500
    (ofString "val (a,b,a,b) = (1,2,3,4);").explode with
  | .success decls => match inferProgramFuel 500 500 decls with
    | .error (.located _ (.duplicateDefinitionVariable name)) => name == ofString "b"
    | _ => false
  | _ => false

#guard renderBindingError (ofString "val (x,x) = (1,2);").explode
    (.located (.locs (.posn 0 0) (.posn 0 17)) (.duplicateDefinitionVariable (ofString "x"))) ==
  some (ofString "### ERROR: type error\nDuplicate variable x in the left-hand side of a definition at line 1\n\nval (x,x) = (1,2);\n^^^^^^^^^^^^^^^^^^\n\nProgram exited with nonzero exit code.\n").explode

#guard renderSourceTypeError [] (.located loc (.sourceTypeMessage
    (ofString "Type constructor A.foo given 2 arguments, but expected 1"))) ==
  some (ofString "### ERROR: type error\nType constructor A.foo given 2 arguments, but expected 1 at line 1\n\n\n           ^^^^^\n\nProgram exited with nonzero exit code.\n").explode

end Flapjack.Test.CakeDiagnosticParity
