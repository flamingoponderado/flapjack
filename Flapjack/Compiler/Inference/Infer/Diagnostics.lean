module

public import Flapjack.Compiler.Inference.Infer.Core
public import Flapjack.Compiler.Inference.InferT.Display

@[expose] public section

-- Public declarations below use private helpers.
set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

/-! Byte-oriented rendering for undefined variables and selected type
mismatches. Other failure messages remain incomplete. -/
namespace Flapjack.Compiler.Inference.Infer.Diagnostics
open Flapjack.Basis.Pure.MlString Flapjack.NamespaceHOL Flapjack.Misc.Location
open Flapjack.Compiler.Inference.Infer.Core

private def ascii (s : String) : List HolChar := (ofString s).explode

private def nameBytes : Ident MlString MlString → List HolChar
  | .short name => name.explode
  | .long name rest => name.explode ++ ascii "." ++ nameBytes rest

/-- The executable diagnostic's identifier bytes are the source renderer's
    bytes, including every module separator. -/
theorem nameBytes_eq_idToString (id : Ident MlString MlString) :
    nameBytes id = (Flapjack.Compiler.Inference.InferTDisplay.idToString id).explode := by
  induction id with
  | short name => rfl
  | long name rest ih =>
    cases name with
    | implode bytes =>
      cases found : Flapjack.Compiler.Inference.InferTDisplay.idToString rest with
      | implode restBytes =>
        simp [nameBytes, Flapjack.Compiler.Inference.InferTDisplay.idToString,
          MlString.concat, MlString.explode, ascii, found] at ih ⊢
        exact ih

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

/-- Render missing constructors and source type-name-check diagnostics. -/
def renderSourceTypeError (input : List HolChar) : Error → Option (List HolChar)
  | .sourceTypeMessage message => some (ascii "### ERROR: type error\n" ++ message.explode ++
      ascii " at " ++ sourceLocation input none ++ ascii "\nProgram exited with nonzero exit code.\n")
  | .located loc (.sourceTypeMessage message) => some (ascii "### ERROR: type error\n" ++
      message.explode ++ ascii " at " ++ sourceLocation input (some loc) ++
      ascii "\nProgram exited with nonzero exit code.\n")
  | .located loc error => do
    let (kind, name) ← match error with
      | .undefinedConstructor name => some ("constructor", name)
      | _ => none
    some (ascii ("### ERROR: type error\nUndefined " ++ kind ++ ": ") ++ nameBytes name ++
      ascii " at " ++ sourceLocation input (some loc) ++ ascii "\nProgram exited with nonzero exit code.\n")
  | _ => none

private def renderTypes (input : List HolChar) (loc : Locs) (names : Flapjack.TypeSystemHOL.TenvAbbrev)
    (left right : InferT) : List HolChar :=
  let leftBytes := (Flapjack.Compiler.Inference.InferTDisplay.inferTypeToString names left).explode
  let rightBytes := (Flapjack.Compiler.Inference.InferTDisplay.inferTypeToString names right).explode
  ascii "### ERROR: type error\nType mismatch between " ++ leftBytes ++
    ascii " and " ++ rightBytes ++ ascii " at " ++ sourceLocation input (some loc) ++
    ascii "\nProgram exited with nonzero exit code.\n"

/-- Render failed constraints using the source inference-type renderer. -/
def renderTypeMismatch (input : List HolChar) : Error → Option (List HolChar)
  | .located loc (.typeMismatch left right) => some (renderTypes input loc nsEmpty left right)
  | .located loc (.typeMismatchEnv names left right) => some (renderTypes input loc names left right)
  | _ => none

/-- The executable framing preserves the bytes of the source-shaped mismatch message. -/
theorem renderTypeMismatch_message (input : List HolChar) (loc : Locs)
    (names : Flapjack.TypeSystemHOL.TenvAbbrev) (a b : InferT) :
    renderTypeMismatch input (.located loc (.typeMismatchEnv names a b)) =
      some ((ofString "### ERROR: type error\n").explode ++
        (MlString.concat [ofString "Type mismatch between ",
          Flapjack.Compiler.Inference.InferTDisplay.inferTypeToString names a,
          ofString " and ",
          Flapjack.Compiler.Inference.InferTDisplay.inferTypeToString names b]).explode ++
        (ofString " at ").explode ++ sourceLocation input (some loc) ++
        (ofString "\nProgram exited with nonzero exit code.\n").explode) := by
  have hp : (ofString "### ERROR: type error\nType mismatch between ").explode =
      (ofString "### ERROR: type error\n").explode ++
        (ofString "Type mismatch between ").explode := by decide
  simp [renderTypeMismatch, renderTypes, ascii, MlString.concat, MlString.explode,
    List.append_assoc] at hp ⊢
  rw [hp, List.append_assoc]

/-- Render unbound type variables at the point where the source type is checked. -/
def renderUnboundTypeVariable (input : List HolChar) : Error → Option (List HolChar)
  | .located loc error => do
    let message ← match error with
      | .annotationTypeVariable name => some (ascii "Type variable " ++ name.explode ++
          ascii " found in type annotation. Type variables are not supported in type annotations.")
      | .abbreviationTypeVariable name typ => some (ascii "Unbound type variable " ++ name.explode ++
          ascii " in type abbreviation " ++ typ.explode)
      | .exceptionTypeVariable name ctor => some (ascii "Type variable " ++ name.explode ++
          ascii " found in declaration of exception " ++ ctor.explode ++
          ascii ". Type variables are not allowed in exception declarations.")
      | _ => none
    some (ascii "### ERROR: type error\n" ++ message ++ ascii " at " ++
      sourceLocation input (some loc) ++ ascii "\nProgram exited with nonzero exit code.\n")
  | _ => none

/-- Render primitive and constraint-list inference errors with their locations. -/
def renderUnsupportedPrimitive (input : List HolChar) (error : Error) : Option (List HolChar) := do
  let (loc, message) ← match error with
    | .located loc .unsafeOperation => some (some loc, "Unsafe ops do not have a type")
    | .located loc .thunkOperation => some (some loc, "Thunk ops do not have a type")
    | .located loc .primitiveTypeMismatch => some (some loc, "Type mismatch")
    | .located loc .badConstraintLists => some (some loc, "Internal error: Bad call to add_constraints")
    | .located loc (.primitiveArity name actual expected) => some (some loc,
        s!"Primitive {name} given {actual} arguments, but expects {expected}")
    | .unsafeOperation => some (none, "Unsafe ops do not have a type")
    | .thunkOperation => some (none, "Thunk ops do not have a type")
    | .primitiveTypeMismatch => some (none, "Type mismatch")
    | .badConstraintLists => some (none, "Internal error: Bad call to add_constraints")
    | .primitiveArity name actual expected => some (none,
        s!"Primitive {name} given {actual} arguments, but expects {expected}")
    | _ => none
  some (ascii "### ERROR: type error\n" ++ ascii message ++ ascii " at " ++
    sourceLocation input loc ++ ascii "\nProgram exited with nonzero exit code.\n")

/-- The original inference pass rejects `Denv` with no source location. -/
def renderUnsupportedDeclaration : Error → Option (List HolChar)
  | .envDeclaration => some (ascii "### ERROR: type error\nEnv declaration (Denv) is not supported. at unknown location\nProgram exited with nonzero exit code.\n")
  | _ => none

/-- Render rejected float patterns and empty case/handler rows at the current
inference location, as in the original inference pass. -/
def renderPatternError (input : List HolChar) (error : Error) : Option (List HolChar) := do
  let (loc, error) := match error with
    | .located loc error => (some loc, error)
    | error => (none, error)
  let message ← match error with
    | .floatPattern => some "Floats cannot be used in patterns"
    | .emptyCase => some "No patterns in case"
    | .emptyHandle => some "No patterns in handle"
    | _ => none
  some (ascii "### ERROR: type error\n" ++ ascii message ++ ascii " at " ++
    sourceLocation input loc ++ ascii "\nProgram exited with nonzero exit code.\n")

/-- Render the value restriction at the declaration location. -/
def renderValueRestriction (input : List HolChar) : Error → Option (List HolChar)
  | .located loc .valueRestriction => some (ascii "### ERROR: type error\nValue restriction violated at " ++
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
      | _ => none
    some (ascii "### ERROR: type error\n" ++ message ++ ascii " at " ++
      sourceLocation input (some loc) ++ ascii "\nProgram exited with nonzero exit code.\n")
  | _ => none

end Flapjack.Compiler.Inference.Infer.Diagnostics
