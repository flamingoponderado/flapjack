import Flapjack.Compiler.Inference.Infer.Core

/-! Byte-oriented rendering for the original compiler's undefined-variable
diagnostic. Other failure messages and parser diagnostics remain incomplete. -/
namespace Flapjack.Compiler.Inference.Infer.Diagnostics
open Flapjack.Basis.Pure.MlString Flapjack.NamespaceHOL Flapjack.Misc.Location
open Flapjack.Compiler.Inference.Infer.Core

private def ascii (s : String) : List HolChar := (ofString s).explode

private def nameBytes : Ident MlString MlString → List HolChar
  | .short name => name.explode
  | .long name rest => name.explode ++ ascii "." ++ nameBytes rest

private def lineAt (input : List HolChar) (row : Nat) : List HolChar :=
  let lines := input.splitOn 10
  (lines[row]?).getD []

/-- Render the byte-level source excerpt used by `compiler$locs_to_string`.
Input and output retain all original HOL byte characters. -/
def sourceLocation (input : List HolChar) : Option Locs → List HolChar
  | none => ascii "unknown location"
  | some (.locs (.posn row col) last) =>
      let line := lineAt input row
      let stop := match last with
        | .posn row' col' => if row == row' then col' else line.length
        | _ => line.length
      ascii ("line " ++ toString (row + 1) ++ "\n\n") ++ line ++ ascii "\n" ++
        List.replicate col 32 ++ List.replicate (stop - col + 1) 94 ++ ascii "\n"
  | some _ => ascii "unknown location"

/-- Render the supported undefined-variable case using the CakeML compiler's
message and the standalone executable's nonzero-exit notice. -/
def renderUndefinedVariable (input : List HolChar) : Error → Option (List HolChar)
  | .undefinedVariable name => some (ascii "### ERROR: type error\nUndefined variable: " ++
      nameBytes name ++ ascii " at " ++ sourceLocation input none ++
      ascii "\nProgram exited with nonzero exit code.\n")
  | .located loc (.undefinedVariable name) => some (ascii "### ERROR: type error\nUndefined variable: " ++
      nameBytes name ++ ascii " at " ++ sourceLocation input (some loc) ++
      ascii "\nProgram exited with nonzero exit code.\n")
  | _ => none

end Flapjack.Compiler.Inference.Infer.Diagnostics
