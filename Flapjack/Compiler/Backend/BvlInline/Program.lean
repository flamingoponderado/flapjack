module

public import Flapjack.Compiler.Backend.BvlInline.TickInline
public import Flapjack.Compiler.Backend.BvlInline.Recursion

@[expose] public section

/-! Total source-shaped BVL program inlining. -/
namespace Flapjack.Compiler.Backend.BvlInline
open Bvl

/-- Inline program entries in order, accumulating their transformed bodies. -/
@[hol "cakeml/compiler/backend/bvl_inlineScript.sml" "tick_inline_all_def"]
def tickInlineAll (limit : Nat) : Spt (Nat × Exp) → List (Nat × Nat × Exp) →
    List (Nat × Nat × Exp) → Spt (Nat × Exp) × List (Nat × Nat × Exp)
  | cache, [], acc => (cache, acc.reverse)
  | cache, (name, arity, body) :: rest, acc =>
    let body := tickInlineSing cache body
    let cache := if mustInline name limit body then sptInsert name (arity, body) cache else cache
    tickInlineAll limit cache rest ((name, arity, body) :: acc)

/-- Compile all entries with the supplied initial inlining cache. -/
@[hol "cakeml/compiler/backend/bvl_inlineScript.sml" "tick_compile_prog_def"]
def tickCompileProg (limit : Nat) (cache : Spt (Nat × Exp))
    (program : List (Nat × Nat × Exp)) : Spt (Nat × Exp) × List (Nat × Nat × Exp) :=
  tickInlineAll limit cache program []

/-- The original program-level inlining equations, with the singleton
inlining used for each body. -/
@[hol "cakeml/compiler/backend/bvl_inlineScript.sml" "tick_inline_all_eq"]
theorem tick_inline_all_eq :
    (∀ (limit : Nat) (cache : Spt (Nat × Exp)) (aux : List (Nat × Nat × Exp)),
      tickInlineAll limit cache [] aux = (cache, aux.reverse)) ∧
    (∀ (xs : List (Nat × Nat × Exp)) (n : Nat) (limit : Nat) (e1 : Exp)
      (cache : Spt (Nat × Exp)) (aux : List (Nat × Nat × Exp)) (arity : Nat),
      tickInlineAll limit cache ((n, arity, e1) :: xs) aux =
        (let e2 := tickInlineSing cache e1
         let cache2 := if mustInline n limit e2 then sptInsert n (arity, e2) cache else cache
         tickInlineAll limit cache2 xs ((n, arity, e2) :: aux))) := by
  constructor
  · intro limit cache aux
    rfl
  · intro xs n limit e1 cache aux arity
    rfl

end Flapjack.Compiler.Backend.BvlInline
