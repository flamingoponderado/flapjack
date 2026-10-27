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

/-- Render missing constructor and type-constructor names. -/
def renderUndefinedConstructor (input : List HolChar) : Error → Option (List HolChar)
  | .located loc error => do
    let (kind, name) ← match error with
      | .undefinedConstructor name => some ("constructor", name)
      | .undefinedTypeConstructor name => some ("type constructor", name)
      | _ => none
    some (ascii ("### ERROR: type error\nUndefined " ++ kind ++ ": ") ++ nameBytes name ++
      ascii " at " ++ sourceLocation input (some loc) ++ ascii "\nProgram exited with nonzero exit code.\n")
  | _ => none

private def builtinTypeName : Nat → Option String
  | 0 => some "Array.array" | 1 => some "bool" | 2 => some "char"
  | 3 => some "exn" | 5 => some "int" | 6 => some "list"
  | 7 => some "ref" | 8 => some "string" | 10 => some "Vector.vector"
  | 11 => some "Word64.word" | 12 => some "Word8.word" | 13 => some "byte_array"
  | 14 => some "Double.double" | _ => none

private def parens (threshold : Nat) (part : String × Nat) : String :=
  if threshold < part.2 then "(" ++ part.1 ++ ")" else part.1

/- The supplied names preserve the lookup order of the inference environment.
If the bounded traversal did not retain a name, rendering remains unsupported. -/
mutual
private def typeString (names : List (Nat × MlString)) : InferT → Option (String × Nat)
  | .uvar n => some ("_" ++ toString n, 0)
  | .varDb n => some ("'" ++ (if n < 28 then String.singleton (Char.ofNat (n + 97)) else toString n), 0)
  | .app ts 4 => match ts with
    | [a, b] => do
      let a ← typeString names a
      let b ← typeString names b
      some (parens 2 a ++ " -> " ++ parens 3 b, 3)
    | _ => none
  | .app ts 9 => match ts with
    | [] => some ("unit", 0)
    | [t] => typeString names t
    | a :: b :: rest => do
      let parts ← typeStrings names (a :: b :: rest)
      some (String.intercalate " * " (parts.map (parens 1)), 2)
  | .app ts name => do
    let name ← match builtinTypeName name with
      | some name => some name
      | none => (names.lookup name).map toStringOfBytes
    match ts with
    | [] => some (name, 0)
    | [t] => do
      let part ← typeString names t
      some (parens 1 part ++ " " ++ name, 1)
    | a :: b :: rest => do
      let parts ← typeStrings names (a :: b :: rest)
      some ("(" ++ String.intercalate ", " (parts.map (parens 5)) ++ ") " ++ name, 1)
termination_by t => sizeOf t

private def typeStrings (names : List (Nat × MlString)) : List InferT → Option (List (String × Nat))
  | [] => some []
  | t :: ts => do
    let t ← typeString names t
    let ts ← typeStrings names ts
    some (t :: ts)
termination_by ts => sizeOf ts
end

private def renderTypes (input : List HolChar) (loc : Locs) (names : List (Nat × MlString))
    (left right : InferT) : Option (List HolChar) := do
    let left ← typeString names left
    let right ← typeString names right
    some (ascii "### ERROR: type error\nType mismatch between " ++ ascii left.1 ++
      ascii " and " ++ ascii right.1 ++ ascii " at " ++ sourceLocation input (some loc) ++
      ascii "\nProgram exited with nonzero exit code.\n")

/-- Render failed constraints when their type names were retained from the
inference environment. Unknown names remain unsupported. -/
def renderTypeMismatch (input : List HolChar) : Error → Option (List HolChar)
  | .located loc (.typeMismatch left right) => renderTypes input loc [] left right
  | .located loc (.typeMismatchNames names left right) => renderTypes input loc names left right
  | _ => none

/-- Render unbound type variables at the point where the source type is checked. -/
def renderUnboundTypeVariable (input : List HolChar) : Error → Option (List HolChar)
  | .located loc error => do
    let message ← match error with
      | .annotationTypeVariable name => some (ascii "Type variable " ++ name.explode ++
          ascii " found in type annotation. Type variables are not supported in type annotations.")
      | .abbreviationTypeVariable name typ => some (ascii "Unbound type variable " ++ name.explode ++
          ascii " in type abbreviation " ++ typ.explode)
      | .datatypeTypeVariable name ctor => some (ascii "Unbound type variable " ++ name.explode ++
          ascii " in type definition with constructor " ++ ctor.explode)
      | .exceptionTypeVariable name ctor => some (ascii "Type variable " ++ name.explode ++
          ascii " found in declaration of exception " ++ ctor.explode ++
          ascii ". Type variables are not allowed in exception declarations.")
      | _ => none
    some (ascii "### ERROR: type error\n" ++ message ++ ascii " at " ++
      sourceLocation input (some loc) ++ ascii "\nProgram exited with nonzero exit code.\n")
  | _ => none

/-- Render the original inference errors for unsafe and thunk primitives. -/
def renderUnsupportedPrimitive (input : List HolChar) (error : Error) : Option (List HolChar) := do
  let (loc, message) ← match error with
    | .located loc .unsafeOperation => some (some loc, "Unsafe ops do not have a type")
    | .located loc .thunkOperation => some (some loc, "Thunk ops do not have a type")
    | .unsafeOperation => some (none, "Unsafe ops do not have a type")
    | .thunkOperation => some (none, "Thunk ops do not have a type")
    | _ => none
  some (ascii "### ERROR: type error\n" ++ ascii message ++ ascii " at " ++
    sourceLocation input loc ++ ascii "\nProgram exited with nonzero exit code.\n")

/-- Render the value restriction at the declaration location. -/
def renderValueRestriction (input : List HolChar) : Error → Option (List HolChar)
  | .located loc .valueRestriction => some (ascii "### ERROR: type error\nValue restriction violated at " ++
      sourceLocation input (some loc) ++ ascii "\nProgram exited with nonzero exit code.\n")
  | _ => none

/-- Render duplicate names rejected by datatype definitions. -/
def renderDatatypeError (input : List HolChar) : Error → Option (List HolChar)
  | .located loc error => do
    let message ← match error with
      | .duplicateTypeName name => some (ascii "Duplicate type constructor " ++ name.explode ++
          ascii " in a mutually recursive type definition")
      | .duplicateConstructor name typ => some (ascii "Duplicate constructor " ++ name.explode ++
          ascii " in the definition of type " ++ typ.explode)
      | .duplicateTypeVariable name typ => some (ascii "Duplicate type variable binding " ++ name.explode ++
          ascii " in the definition of type " ++ typ.explode)
      | _ => none
    some (ascii "### ERROR: type error\n" ++ message ++ ascii " at " ++
      sourceLocation input (some loc) ++ ascii "\nProgram exited with nonzero exit code.\n")
  | _ => none

/-- Render duplicate bindings and type-constructor arity errors. -/
def renderBindingError (input : List HolChar) : Error → Option (List HolChar)
  | .located loc error => do
    let message ← match error with
      | .duplicatePatternVariable name => some (ascii "Duplicate variable " ++ name.explode ++ ascii " in pattern")
      | .duplicateDefinitionVariable name => some (ascii "Duplicate variable " ++ name.explode ++ ascii " in the left-hand side of a definition")
      | .duplicateFunctionName name isLocal => some (ascii "Duplicate function name " ++ name.explode ++
          ascii (if isLocal then " in mutually recursive function definition" else " a mutually recursive function definition"))
      | .duplicateAbbreviationVariable name typ => some (ascii "Duplicate type variable bindings for " ++ name.explode ++ ascii " in type abbreviation " ++ typ.explode)
      | .constructorArity name actual expected => some (ascii "Constructor " ++ nameBytes name ++
          ascii (" given " ++ toString actual ++ " arguments, but expected " ++ toString expected))
      | .typeConstructorArity name actual expected => some (ascii "Type constructor " ++ nameBytes name ++
          ascii (" given " ++ toString actual ++ " arguments, but expected " ++ toString expected))
      | _ => none
    some (ascii "### ERROR: type error\n" ++ message ++ ascii " at " ++
      sourceLocation input (some loc) ++ ascii "\nProgram exited with nonzero exit code.\n")
  | _ => none

end Flapjack.Compiler.Inference.Infer.Diagnostics
