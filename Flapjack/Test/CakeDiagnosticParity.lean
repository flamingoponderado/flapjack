import Flapjack.Compiler.Inference.Infer.Diagnostics
import Flapjack.CakeParser.Frontend

/-! Original inferencer message and source-location formatting for undefined
variables, including qualified and multiline names. -/
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

#guard sourceLocation (ofString "val x =\n missing;").explode
    (some (.locs (.posn 1 1) (.posn 1 8))) ==
  (ofString "line 2\n\n missing;\n ^^^^^^^^\n").explode

end Flapjack.Test.CakeDiagnosticParity
