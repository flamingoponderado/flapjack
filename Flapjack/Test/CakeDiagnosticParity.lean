import Flapjack.Compiler.Inference.Infer.Diagnostics
import Flapjack.CakeParser.Frontend

/-! Original inferencer message and source-location formatting for undefined
variables and selected built-in type mismatches. -/
namespace Flapjack.Test.CakeDiagnosticParity
open Flapjack Flapjack.AstHOL Flapjack.Misc.Location
open Flapjack.Compiler.Inference.Infer Flapjack.Compiler.Inference.Infer.Core
open Flapjack.Compiler.Inference.Infer.Diagnostics Flapjack.Basis.Pure.MlString

private def loc : Locs := .locs (.posn 0 11) (.posn 0 15)
private def qname : NamespaceHOL.Ident MlString MlString := .long (ofString "A") (.short (ofString "foo"))

#guard match inferExprFuel 100 100 emptyEnv (.lannot (.var qname) loc) ⟨0, .ln, 15⟩ with
  | .error (.located actual (.undefinedVariable (.long a (.short b)))) =>
      actual == loc && a == ofString "A" && b == ofString "foo"
  | _ => false

#guard renderUndefinedVariable (ofString "val x = A.foo;").explode (.located loc (.undefinedVariable qname)) ==
  some (ofString "### ERROR: type error\nUndefined variable: A.foo at line 1\n\nval x = A.foo;\n           ^^^^^\n\nProgram exited with nonzero exit code.\n").explode

#guard renderUndefinedConstructor (ofString "val x = A.foo;").explode
    (.located loc (.undefinedTypeConstructor qname)) ==
  some (ofString "### ERROR: type error\nUndefined type constructor: A.foo at line 1\n\nval x = A.foo;\n           ^^^^^\n\nProgram exited with nonzero exit code.\n").explode

#guard sourceLocation (ofString "val x =\n missing;").explode
    (some (.locs (.posn 1 1) (.posn 1 8))) ==
  (ofString "line 2\n\n missing;\n ^^^^^^^^\n").explode

#guard renderTypeMismatch (ofString "val x = 1 + True;").explode
    (.located (.locs (.posn 0 11) (.posn 0 20))
      (.typeMismatch (.app [.app [] 5, .app [] 5] 4) (.app [.app [] 1, .uvar 1] 4))) ==
  some (ofString "### ERROR: type error\nType mismatch between int -> int and bool -> _1 at line 1\n\nval x = 1 + True;\n           ^^^^^^^^^^\n\nProgram exited with nonzero exit code.\n").explode

-- A user-defined type needs a name from the inference environment.
#guard (renderTypeMismatch [] (.located loc (.typeMismatch (.app [] 5) (.app [] 15)))).isNone

#guard renderTypeMismatch [] (.located loc
    (.typeMismatchNames [(15, ofString "M.t")] (.app [] 5) (.app [] 15))) ==
  some (ofString "### ERROR: type error\nType mismatch between int and M.t at line 1\n\n\n           ^^^^^\n\nProgram exited with nonzero exit code.\n").explode

-- The nested function, tuple and variable formatting is captured in
-- cake_type_diagnostic_probe.out from the original inferencer.
#guard renderTypeMismatch [] (.located loc
    (.typeMismatch (.app [.app [.app [] 5, .app [] 1] 4] 6) (.app [.app [] 1, .app [] 5] 9))) ==
  some (ofString "### ERROR: type error\nType mismatch between (int -> bool) list and bool * int at line 1\n\n\n           ^^^^^\n\nProgram exited with nonzero exit code.\n").explode

-- The original check chooses the first name that appears again later.
#guard match Flapjack.CakeParser.Frontend.parseSourceFuel 500 500
    (ofString "datatype t = A | B | A | B;").explode with
  | .success decls => match inferProgramFuel 500 500 decls with
    | .error (.located _ (.duplicateConstructor name typ)) => name == ofString "A" && typ == ofString "t"
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

#guard renderBindingError [] (.located loc (.typeConstructorArity qname 2 1)) ==
  some (ofString "### ERROR: type error\nType constructor A.foo given 2 arguments, but expected 1 at line 1\n\n\n           ^^^^^\n\nProgram exited with nonzero exit code.\n").explode

end Flapjack.Test.CakeDiagnosticParity
