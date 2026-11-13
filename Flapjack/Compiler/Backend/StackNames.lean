module

public import Flapjack.Compiler.Backend.StackLang
public import Flapjack.Compiler.Backend.StackLang.Prog
public import Flapjack.Compiler.Encoders.Asm
public import Flapjack.Pancake.WordLang
public import Flapjack.FiniteMap.Basic
public import Flapjack.HolRef

@[expose] public section

/-!
# StackNames lookup helper

Counterpart of `cakeml/compiler/backend/stack_namesScript.sml`. HOL looks
registers up with `misc$tlookup` on a `num num_map` (`Spt Nat`). The exact
Spt-carried definitions and their `@[hol]` tags live in the `StackNames`
submodules (`OperandNames`, `InstructionNames`, `ProgramNames`, `NamesOk`),
where `findNameSpt` is the direct `tlookup` rendering.

This module keeps the function view of that lookup: `findName` takes an
unrestricted map function and returns the register unchanged on a miss, which
is how the proofs identify the renaming with an explicit total map such as
`arm8NameMap`. It is Flapjack infrastructure and carries no HOL tag.
-/

namespace Flapjack.Compiler.Backend.StackNames

open Flapjack
open Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Encoders.Asm

/-- Function view of `misc$tlookup` at the register map: rename a register when
it is in the domain, otherwise keep it. `findNameSpt_eq_lookupHelper` relates it
to the exact `Spt` lookup. -/
def findName (names : FiniteMap Nat Nat) (register : Nat) : Nat :=
  match FLOOKUP names register with
  | some value => value
  | none => register

end Flapjack.Compiler.Backend.StackNames
