module

public import Flapjack.Pancake.WordLang

@[expose] public section

/-!
# Word-to-stack invariant guard

`word_to_stack$comp_def` (`compNative` in `NativeCompile.lean`) silently
lowers several constructs to `Skip`: the final catch-all arm (marked
`(* impossible *)` in the source) covers a remaining `Assign`/`Store`; a `Set`
of `BitmapBase` (also marked impossible) and a `Set` whose expression is not a
`Var` are dropped; and a `ShareInst` whose expression is not an address
(`exp_to_addr` returns `NONE`) becomes `Skip`.  A program that reached one of
these arms would compile without its intended effect and with no error.

This module is Flapjack-only driver infrastructure: it recognises exactly the
programs those arms would swallow, so the driver can reject them with a
located error before `compileNative` runs.  It changes no reviewed `@[hol]`
definition and is a no-op on every program the pass actually supports; the
traversal mirrors `compNative`'s recursion (nested `mustTerminate`, `seq`,
`ite`, `loop`, call continuations and handlers), so a construct nested in a
sub-program is reported too.  There is no separately named HOL declaration
for this guard.
-/

namespace Flapjack.Compiler.Backend.WordToStack

open Flapjack

/-- The word-level construct `compNative` would silently lower to `Skip`. -/
inductive WordStackGuardKind where
  | assign
  | store
  | setBitmapBase
  | setNonVar
  | shareInstNonAddress
  deriving DecidableEq, Repr

/-- A located word-to-stack guard failure.  `functionName` is the word-level
function number of the containing program (the first component of the
`(nameNum, argCount, prog)` row the pass consumes); it is a pipeline-local
identity, resolved to a source name only by the driver's symbol table. -/
inductive WordStackGuardFailure where
  | unsupported (functionName : Nat) (kind : WordStackGuardKind)
  deriving DecidableEq, Repr

/-- Human-readable description of the offending construct. -/
def wordStackGuardKindDescription : WordStackGuardKind → String
  | .assign => "a remaining Assign, which word-to-stack would drop"
  | .store => "a remaining Store, which word-to-stack would drop"
  | .setBitmapBase => "a Set of BitmapBase, which word-to-stack would drop"
  | .setNonVar =>
      "a Set whose expression is not a Var, which word-to-stack would drop"
  | .shareInstNonAddress =>
      "a ShareInst whose expression is not an address, which word-to-stack would drop"

/-- Human-readable description of a located word-to-stack guard failure. -/
def wordStackGuardFailureDescription : WordStackGuardFailure → String
  | .unsupported functionName kind =>
      "word-to-stack: function " ++ toString functionName ++ " contains " ++
        wordStackGuardKindDescription kind

/-- The first construct in `program` that `compNative` would silently lower to
`Skip`, if any.  Recursion follows `compNative`'s own traversal. -/
def firstUnsupported {width : Nat} (functionName : Nat) :
    WordLangProgHOL (BitVec width) → Option WordStackGuardFailure
  | .assign _ _ => some (.unsupported functionName .assign)
  | .store _ _ => some (.unsupported functionName .store)
  | .set .bitmapBase _ => some (.unsupported functionName .setBitmapBase)
  | .set _ (.var _) => none
  | .set _ _ => some (.unsupported functionName .setNonVar)
  | .shareInst _ _ address =>
      if (expToAddrHOL address).isSome then none
      else some (.unsupported functionName .shareInstNonAddress)
  | .mustTerminate body => firstUnsupported functionName body
  | .seq first second =>
      match firstUnsupported functionName first with
      | some failure => some failure
      | none => firstUnsupported functionName second
  | .ite _ _ _ first second =>
      match firstUnsupported functionName first with
      | some failure => some failure
      | none => firstUnsupported functionName second
  | .loop _ body _ => firstUnsupported functionName body
  | .call returns _ _ handler =>
      let retGuard :=
        match returns with
        | none => none
        | some (_, _, retCode, _, _) => firstUnsupported functionName retCode
      match retGuard with
      | some failure => some failure
      | none =>
          match handler with
          | none => none
          | some (_, handleCode, _, _) => firstUnsupported functionName handleCode
  | _ => none

/-- The first function row whose program contains a construct `compNative`
would silently drop, in list order. -/
def firstUncompilableAux {width : Nat} :
    List (Nat × Nat × WordLangProgHOL (BitVec width)) →
      Option WordStackGuardFailure
  | [] => none
  | (functionName, _, program) :: rest =>
      match firstUnsupported functionName program with
      | some failure => some failure
      | none => firstUncompilableAux rest

/-- The word-to-stack guard: `none` exactly when every row is fully lowered by
`compNative` with no silent `Skip` substitution. -/
def firstUncompilable {width : Nat}
    (programs : List (Nat × Nat × WordLangProgHOL (BitVec width))) :
    Option WordStackGuardFailure :=
  firstUncompilableAux programs

end Flapjack.Compiler.Backend.WordToStack
