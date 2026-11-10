module

public import Flapjack.Stack

@[expose] public section

/-!
# Production StackProg word-payload boundary

Flapjack-only carrier infrastructure: this is not a HOL datatype or theorem
port. Only fields whose production type is the shared word parameter are
converted. Register indices, labels, counts, String names and the Nat-only
`const`/`arith`/`shift` macros are retained, not silently reduced modulo the
machine width. Those macros still need a separate reviewed projection before
the executed StackNames route can use the canonical program codec.

The two directions distinguish an exact width-typed image roundtrip from a
Nat roundtrip that needs an explicit bound on every word-valued payload.
Neither law establishes executable transition equivalence or full compiler
routing. In particular this module does not approve shMem store aliases,
FFI/Install length renaming or arbitrary String-to-mlstring inputs.
-/
namespace Flapjack.Compiler.Backend.StackLang.WordPayloads
open Flapjack

def mapRegImm (f : α → β) : WordRegImm α → WordRegImm β
  | .imm value => .imm (f value)
  | .reg register => .reg register

def regImmValues : WordRegImm α → List α
  | .imm value => [value]
  | .reg _ => []

theorem mapRegImm_inverseOn (f : α → β) (g : β → α) (operand : WordRegImm α)
    (h : ∀ x ∈ regImmValues operand, g (f x) = x) :
    mapRegImm g (mapRegImm f operand) = operand := by
  cases operand <;> simp_all [mapRegImm, regImmValues]

theorem regImmValues_mapRegImm (f : α → β) (operand : WordRegImm α) :
    regImmValues (mapRegImm f operand) = (regImmValues operand).map f := by
  cases operand <;> rfl

end Flapjack.Compiler.Backend.StackLang.WordPayloads
