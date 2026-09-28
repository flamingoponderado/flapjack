import Flapjack.Pancake.CrepToLoop
import Flapjack.Pancake.LoopLive

namespace Flapjack

/-! The optimised Crepe-to-Loop entry point corresponding to
    `crep_to_loop$ocompile` (`crep_to_loopScript.sml:216`). -/
def oCompile [OfNat α 0] [OfNat α 1]
    (context : LoopContext α) (live : List Nat) (program : CrepProg α) :
    LoopProg α :=
  loopLiveOptimise (compileCrepToLoop context live program)

/-! Production helper corresponding to the shape of CakeML Pancake's
    `comp_func_def` (`crep_to_loopScript.sml:235`). It is intentionally
    untagged: it uses RISC-V `Architecture`, String-keyed production function
    maps, and the generic executable `LoopProg`, while HOL uses `asm$architecture`,
    `mlstring` keys, and `HolLoopProg`; moreover it calls the production
    `compileCrepToLoop`/`loopLiveOptimise`, not an exact `compile_def` port.
    The exact `comp_func_def` remains blocked on the faithful program compiler
    tracked by `flapjack-pxn.18.5.6.28`. -/
def crepCompFunc [OfNat α 0] [OfNat α 1]
    (target : RiscV.Architecture) (functions : InfoMap (Nat × Nat))
    (params : List Nat) (body : CrepProg α) : LoopProg α :=
  let context : LoopContext α := crepMkCtxt target (crepMakeVmap params)
    functions (params.length - 1)
  oCompile context (List.range params.length) body

theorem oCompile_skip [OfNat α 0] [OfNat α 1]
    (context : LoopContext α) (live : List Nat) :
    oCompile context live (.skip : CrepProg α) = .mark .skip := by
  simp [oCompile, compileCrepToLoop, loopCompileProg, loopLiveOptimise,
    loopLiveComp, loopShrink, loopShrinkLeaf, loopMarkAll, LoopCall.comp]

end Flapjack
