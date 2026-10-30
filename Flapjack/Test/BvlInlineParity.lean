import Flapjack.Compiler.Backend.BvlInline
import Flapjack.Compiler.Backend.BvlInline.TickInline

/-! Replay `bvl_inline_frontend_probe.out` from pinned CakeML/HOL. -/
namespace Flapjack.Test.BvlInlineParity
open Flapjack.Compiler.Backend
open BvlInline

-- Original `mk_tick_zero` and `mk_tick_three` observations from the pinned
-- bvl_inline_state_rel probe; these use the production tick constructor.
example : Bvl.mkTick 0 (.var 4) = .var 4 := rfl
example : Bvl.mkTick 3 (.var 4) = .tick (.tick (.tick (.var 4))) := rfl

-- Original tick_inline_generic_cache and tick_inline_uncached observations.
example : tickInlineSing (sptInsert 3 (true, Bvl.Exp.var 8) .ln)
    (.call 2 (some 3) [.var 1]) = .let [.var 1] (.tick (.tick (.tick (.var 8)))) := by
  simp [tickInlineSing, tickInlineList, sptInsert, sptLookup, Bvl.mkTick]
example : tickInlineSing (.ln : Spt (Bool × Bvl.Exp)) (.call 2 (some 3) [.var 1]) =
    .call 2 (some 3) [.var 1] := by
  simp [tickInlineSing, tickInlineList, sptLookup]

#guard match tickInlineAllFuel 100 8 .ln
    [(1, 1, .var 0), (2, 1, .call 2 (some 1) [.var 0]),
     (3, 0, .call 0 (some 3) []), (4, 1, .call 0 (some 3) [.var 0])] with
  | some (_, [(1, 1, .var 0), (2, 1, .let [.var 0] (.tick (.tick (.tick (.var 0))))),
      (3, 0, .call 0 (some 3) []), (4, 1, .call 0 (some 3) [.var 0])]) => true
  | _ => false

private def sized : Bvl.Exp :=
  .let [.var 0, .tick (.var 1)] (.call 0 (some 4) [.var 0])
#guard [0, 1, 2, 3, 4].map (fun n => smallExpFuel 100 n sized) ==
  [some 0, some 0, some 0, some 1, some 2]
#guard match letOpFuel 100 (.let [.var 8, .var 9]
    (.op (.intOp .add) [.var 0, .var 1])) with
  | some (.op (.intOp .add) [.var 8, .var 9]) => true
  | _ => false
#guard match removeTicksFuel 100 (.tick (.call 3 (some 2) [.tick (.var 1)])) with
  | some (.call 0 (some 2) [.var 1]) => true
  | _ => false
#guard (inlineExpFuel 0 .ln (.var 0)).isNone

end Flapjack.Test.BvlInlineParity
