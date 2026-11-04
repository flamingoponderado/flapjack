import Flapjack.RiscV.Calls
import Flapjack.RiscV.Ffi

/-!
The first RISC-V linker layer for Flapjack function artifacts. Function labels
are assigned byte addresses from the emitted instruction lengths; unresolved
artifacts fail explicitly. The resulting entry table feeds
`wordCallToRiscVLabel`, which resolves a Word call target before selecting its
RISC-V sequence.
-/

namespace Flapjack.RiscV

def wordFunctionReturnNames [NeZero width] :
    WordProg (Word width) → Option (List Nat)
  | .return _ values => some values
  | .seq first second =>
      match wordFunctionReturnNames first with
      | some values => some values
      | none => wordFunctionReturnNames second
  | .ite _ _ _ thenBranch elseBranch =>
      match wordFunctionReturnNames thenBranch, wordFunctionReturnNames elseBranch with
      | some thenReturns, some elseReturns =>
          if thenReturns == elseReturns then some thenReturns else none
      | _, _ => none
  | .loop _ body _ =>
      match wordFunctionReturnNames body with
      | some values => some values
      | none => some []
  | _ => none
  termination_by program => sizeOf program

def lookupWordFunctionBody [NeZero width] (label : Nat) :
    List (Nat × List Nat × WordProg (Word width)) →
      Option (WordProg (Word width))
  | [] => none
  | (candidate, _, body) :: functions =>
      if label == candidate then some body
      else lookupWordFunctionBody label functions

def wordFunctionReturnNamesWithCalls [NeZero width]
    (functions : List (Nat × List Nat × WordProg (Word width))) :
    WordProg (Word width) → Option (List Nat)
  | .call (some ([], _)) (some label) _ none => do
      let body ← lookupWordFunctionBody label functions
      wordFunctionReturnNames body
  | .call none (some label) _ none => do
      let body ← lookupWordFunctionBody label functions
      wordFunctionReturnNames body
  | .call (some (_, _)) _ _ none => some []
  | .seq first second =>
      match wordFunctionReturnNamesWithCalls functions first with
      | some values => some values
      | none => wordFunctionReturnNamesWithCalls functions second
  | .ite _ _ _ thenBranch elseBranch => do
      let thenReturns ← wordFunctionReturnNamesWithCalls functions thenBranch
      let elseReturns ← wordFunctionReturnNamesWithCalls functions elseBranch
      if thenReturns == elseReturns then some thenReturns else none
  | .loop _ body _ =>
      match wordFunctionReturnNamesWithCalls functions body with
      | some values => some values
      | none => some []
  | .return _ values => some values
  | _ => none
termination_by program => sizeOf program

/-! Carry the compiler witness through the first linker cell.  This is the
    boundary used by correctness clients that need the actual entry address,
    rather than only the instruction list returned by the selector. -/

def wordFunctionTargetSignaturesAux [NeZero width]
    (allFunctions : List (Nat × List Nat × WordProg (Word width))) :
    List (Nat × List Nat × WordProg (Word width)) →
      Option (List (Nat × Word width × List Nat × List Nat))
  | [] => some []
  | (label, parameters, body) :: functions => do
      let returns ← wordFunctionReturnNamesWithCalls allFunctions body
      let rest ← wordFunctionTargetSignaturesAux allFunctions functions
      pure ((label, 0, parameters, returns) :: rest)

def wordFunctionTargetSignaturesWithCalls [NeZero width]
    (functions : List (Nat × List Nat × WordProg (Word width))) :
      Option (List (Nat × Word width × List Nat × List Nat)) :=
  wordFunctionTargetSignaturesAux functions functions

def wordFunctionTargetSignatures [NeZero width] :
    List (Nat × List Nat × WordProg (Word width)) →
      Option (List (Nat × Word width × List Nat × List Nat))
  | [] => some []
  | (label, parameters, body) :: functions => do
      let returns ← wordFunctionReturnNames body
      let rest ← wordFunctionTargetSignatures functions
      pure ((label, 0, parameters, returns) :: rest)

/-!
Linking for the FFI-aware selector mirrors the ordinary call-aware linker but
retains the service table throughout both provisional and final compilation.
This keeps function entry addresses stable while allowing an FFI operation in
any supported straight-line or loop body.
-/

theorem wordFunctionReturnNames_return [NeZero width] (values : List Nat) :
    wordFunctionReturnNames (.return 0 values : WordProg (Word width)) = some values := by
  simp [wordFunctionReturnNames]

end Flapjack.RiscV
