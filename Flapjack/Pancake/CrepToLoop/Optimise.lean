import Flapjack.Pancake.CrepToLoop
import Flapjack.Pancake.LoopLive
import Flapjack.Pancake.CrepToLoop.ContextExact
import Flapjack.Pancake.CrepLang.Prog
import Flapjack.Pancake.LoopLang

namespace Flapjack

/-! The optimised Crepe-to-Loop entry point corresponding to
    `crep_to_loop$ocompile` (`crep_to_loopScript.sml:216`). -/
def oCompile [OfNat α 0] [OfNat α 1]
    (context : LoopContext α) (live : List Nat) (program : CrepProg α) :
    LoopProg α :=
  loopLiveOptimise (compileCrepToLoop context live program)

/-! ## Exact-carrier executable bridge

This per-function exact boundary is available for callers that need the exact
`ocompile_def` result and can prove the byte-range premises.
It is usable only when the program and every function-map key satisfy the checked
`CrepNameRanged` codec premise. Without those premises, `MlString.ofString`
can truncate a non-byte Lean `String`, so callers must keep using the generic
implementation. The returned program is the canonical executable projection
of the exact HOL-shaped output; this bridge does not assert equality with the
generic compiler for arbitrary inputs.
-/

/-- Execute the exact `ocompile_def` port for a production RISC-V context on
the codec-supported name fragment. `hProgramNames` and `hFunctionNames` are
deliberate boundary obligations: `crepProgToHOL` and
`productionLoopContextToExact` preserve names only under these byte-range
facts. This declaration is Flapjack bridge infrastructure, not a HOL port. -/
def oCompileThroughHOLExact {width : Nat} [NeZero width]
    (context : LoopContext (BitVec width)) (live : List Nat)
    (program : CrepProg (BitVec width))
    (_hProgramNames : CrepProgNameRanged program)
    (_hFunctionNames : ∀ entry ∈ context.functions, CrepNameRanged entry.1) :
    LoopProg (BitVec width) :=
  holLoopProgToExecutableCanonical
    (ocompileHOLExact (productionLoopContextToExact context)
      (listToNumSetHOLExact live) (crepProgToHOL program))

/-- The exact-route result is related to the reviewed HOL-shaped
`ocompileHOLExact` result by the checked structural projection. The name
premises are retained in the public statement so callers cannot mistake this
bridge for a total `String`/`mlstring` conversion. -/
theorem oCompileThroughHOLExact_rel {width : Nat} [NeZero width]
    (context : LoopContext (BitVec width)) (live : List Nat)
    (program : CrepProg (BitVec width))
    (hProgramNames : CrepProgNameRanged program)
    (hFunctionNames : ∀ entry ∈ context.functions, CrepNameRanged entry.1) :
    loopProgExecRel
      (oCompileThroughHOLExact context live program hProgramNames hFunctionNames)
      (ocompileHOLExact (productionLoopContextToExact context)
        (listToNumSetHOLExact live) (crepProgToHOL program)) := by
  exact holLoopProgToExecutableCanonical_rel _

theorem oCompile_skip [OfNat α 0] [OfNat α 1]
    (context : LoopContext α) (live : List Nat) :
    oCompile context live (.skip : CrepProg α) = .mark .skip := by
  simp [oCompile, compileCrepToLoop, loopCompileProg, loopLiveOptimise,
    loopLiveComp, loopShrink, loopShrinkLeaf, loopMarkAll, LoopCall.comp]

end Flapjack
