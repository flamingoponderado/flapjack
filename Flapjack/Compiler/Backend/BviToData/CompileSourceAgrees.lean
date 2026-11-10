module

public import Flapjack.Compiler.Backend.BviToData.CompileSource
public import Mathlib.Tactic

@[expose] public section

/-! Agreement of the source traversal with the executable single/list rewrites. -/
namespace Flapjack.Compiler.Backend.BviToData
open Classical

/-- The source traversal agrees with the single-expression and non-tail list
rewrites used by the executable compiler. -/
theorem compileSource_agrees (n : Nat) (env : List Nat) (tail : Bool) (live : List Nat)
    (xs : List Bvi.Exp) :
    compileSource n env tail live xs =
      match xs with
      | [] => (.skip, [], n)
      | [x] => let (code, name, next) := compileSing n env tail live x; (code, [name], next)
      | _ => compileList n env live xs := by
  fun_induction compileSource n env tail live xs <;>
    simp_all [compileSing, compileList, Flapjack.holHd] <;>
    aesop (add simp [compileList, Flapjack.holHd])

end Flapjack.Compiler.Backend.BviToData
