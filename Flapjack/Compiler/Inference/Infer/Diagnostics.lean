import Flapjack.Compiler.Inference.Infer.Core

/-! Byte-oriented rendering for undefined variables and selected type
mismatches. Other failure messages remain incomplete. -/
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

private def builtinTypeName : Nat → Option String
  | 0 => some "Array.array" | 1 => some "bool" | 2 => some "char"
  | 3 => some "exn" | 5 => some "int" | 6 => some "list"
  | 7 => some "ref" | 8 => some "string" | 10 => some "Vector.vector"
  | 11 => some "Word64.word" | 12 => some "Word8.word" | 13 => some "byte_array"
  | 14 => some "Double.double" | _ => none

private def parens (threshold : Nat) (part : String × Nat) : String :=
  if threshold < part.2 then "(" ++ part.1 ++ ")" else part.1

/- Only built-in type constructors are rendered here; user-defined type names
require the original inference error environment and are left unsupported. -/
mutual
private def builtinTypeString : InferT → Option (String × Nat)
  | .uvar n => some ("_" ++ toString n, 0)
  | .varDb n => some ("'" ++ (if n < 28 then String.singleton (Char.ofNat (n + 97)) else toString n), 0)
  | .app ts 4 => match ts with
    | [a, b] => do
      let a ← builtinTypeString a
      let b ← builtinTypeString b
      some (parens 2 a ++ " -> " ++ parens 3 b, 3)
    | _ => none
  | .app ts 9 => match ts with
    | [] => some ("unit", 0)
    | [t] => builtinTypeString t
    | a :: b :: rest => do
      let parts ← builtinTypeStrings (a :: b :: rest)
      some (String.intercalate " * " (parts.map (parens 1)), 2)
  | .app ts name => do
    let name ← builtinTypeName name
    match ts with
    | [] => some (name, 0)
    | [t] => do
      let part ← builtinTypeString t
      some (parens 1 part ++ " " ++ name, 1)
    | a :: b :: rest => do
      let parts ← builtinTypeStrings (a :: b :: rest)
      some ("(" ++ String.intercalate ", " (parts.map (parens 5)) ++ ") " ++ name, 1)
termination_by t => sizeOf t

private def builtinTypeStrings : List InferT → Option (List (String × Nat))
  | [] => some []
  | t :: ts => do
    let t ← builtinTypeString t
    let ts ← builtinTypeStrings ts
    some (t :: ts)
termination_by ts => sizeOf ts
end

/-- Render failed constraints when both normalized types use built-in type
constructors. Unknown user-defined type names remain unsupported. -/
def renderTypeMismatch (input : List HolChar) : Error → Option (List HolChar)
  | .located loc (.typeMismatch left right) => do
    let left ← builtinTypeString left
    let right ← builtinTypeString right
    some (ascii "### ERROR: type error\nType mismatch between " ++ ascii left.1 ++
      ascii " and " ++ ascii right.1 ++ ascii " at " ++ sourceLocation input (some loc) ++
      ascii "\nProgram exited with nonzero exit code.\n")
  | _ => none

end Flapjack.Compiler.Inference.Infer.Diagnostics
