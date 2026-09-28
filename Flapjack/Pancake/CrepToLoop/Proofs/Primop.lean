import Flapjack.Pancake.CrepToLoop.StateRel
import Flapjack.Pancake.Semantics.CrepSem.Primop
import Flapjack.Pancake.Semantics.LoopSemStateExact

/-!
# crep_to_loopProof primitive-operator preservation

Counterpart of `cakeml/pancake/proofs/crep_to_loopProofScript.sml`'s
`crep_primop_loop_primop` (`:2337-2355`), the local Primitive case of
`ncompile_correct`.

The HOL statement is

    ∀pop ws (res_ws : 'a word_lab list).
      crep_primop pop ws = SOME res_ws ⇒
      loop_primop pop (MAP wlab_wloc ws) = SOME (MAP wlab_wloc res_ws)

over the exact `panSem$word_lab` / `wordLang$word_loc` carriers.  The exact
Lean source primitive is `crepPrimopHOLExact` (`HolWordLab`), the exact Lean
target primitive is `LoopSemStateFiniteExact.loopPrimop` (`WordLocW`, the exact
`word_loc` carrier), and their value bridge is `wlabWlocHOL`.  Both primitives
have the same single `AddCarry` equation, so the only content is the
`HolWordLab`/`WordLocW` `word`-constructor correspondence: the arity guard and
the `wordAddCarryHOL` payload computation are identical on both sides.
-/

namespace Flapjack

/-- Exact port of HOL `crep_primop_loop_primop[local]`
    (`cakeml/pancake/proofs/crep_to_loopProofScript.sml:2337-2355`): a successful
    Crep primitive evaluation is preserved by the Crepe-to-Loop lowering after
    mapping the `word_lab` arguments and results through `wlab_wloc`.

    `pop` is the shared `panLang$primop`, so the Lean port uses `PrimOp`.  The
    target is the exact `word_loc`-valued `loop_primop` port
    `LoopSemStateFiniteExact.loopPrimop`, because `wlabWlocHOL` maps
    `HolWordLab` (`word_lab`) to `WordLocW` (`word_loc`); `loopPrimopHOL` is the
    separate Flapjack `LoopValue`-valued rendering and does not have the exact
    HOL `word_loc` codomain. -/
@[hol "cakeml/pancake/proofs/crep_to_loopProofScript.sml" "crep_primop_loop_primop"]
theorem crepPrimopLoopPrimopHOL {width : Nat} [NeZero width]
    (pop : PrimOp) (ws resWs : List (HolWordLab width))
    (h : crepPrimopHOLExact pop ws = some resWs) :
    LoopSemStateFiniteExact.loopPrimop pop (ws.map wlabWlocHOL) =
      some (resWs.map wlabWlocHOL) := by
  cases pop
  cases ws with
  | nil => exact absurd h (by simp [crepPrimopHOLExact])
  | cons a rest =>
      cases a with
      | word av =>
        cases rest with
        | nil => exact absurd h (by simp [crepPrimopHOLExact])
        | cons b rest =>
            cases b with
            | word bv =>
              cases rest with
              | nil => exact absurd h (by simp [crepPrimopHOLExact])
              | cons c rest =>
                  cases c with
                  | word cv =>
                    cases rest with
                    | nil =>
                        simp only [crepPrimopHOLExact,
                          LoopSemStateFiniteExact.loopPrimop,
                          List.map_cons, List.map_nil, wlabWlocHOL] at h ⊢
                        rw [Option.some.injEq] at h
                        rw [← h]
                        simp [List.map_cons, List.map_nil, wlabWlocHOL]
                    | cons d rest => exact absurd h (by simp [crepPrimopHOLExact])

end Flapjack
