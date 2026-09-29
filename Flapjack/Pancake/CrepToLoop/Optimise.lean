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

/-! Production helper corresponding to the shape of CakeML Pancake's
    `comp_func_def` (`crep_to_loopScript.sml:235`). It is intentionally
    untagged: it uses RISC-V `Architecture`, String-keyed production function
    maps, and the generic executable `LoopProg`, while HOL uses `asm$architecture`,
    `mlstring` keys, and `HolLoopProg`; moreover it calls the production
    `compileCrepToLoop`/`loopLiveOptimise`, not an exact `compile_def` port.
    The parser-backed source pipeline instead calls exact whole-program
    `compileProgHOLExact` over checked `MlString`/width carriers. -/
def crepCompFunc [OfNat α 0] [OfNat α 1]
    (target : RiscV.Architecture) (functions : InfoMap (Nat × Nat))
    (params : List Nat) (body : CrepProg α) : LoopProg α :=
  let context : LoopContext α := crepMkCtxt target (crepMakeVmap params)
    functions (params.length - 1)
  oCompile context (List.range params.length) body

/-! ## Exact-carrier executable bridge

The parser-backed source compiler uses exact whole-program
`compileProgHOLExact`. This per-function boundary remains available for callers
that need the exact `ocompile_def` result and can prove the byte-range premises.
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

/-- Exact-carrier route for the production `crepCompFunc`, retaining the
byte-range obligations required at the `String`/HOL `mlstring` boundary. It
executes the reviewed `comp_func_def` and then the reviewed `optimise_def`.
Callers without the name evidence continue through the generic helper above. -/
def crepCompFuncThroughHOLExact {width : Nat} [NeZero width]
    (target : RiscV.Architecture) (functions : InfoMap (Nat × Nat))
    (params : List Nat) (body : CrepProg (BitVec width))
    (_hProgramNames : CrepProgNameRanged body)
    (_hFunctionNames : ∀ entry ∈ functions, CrepNameRanged entry.1) :
    LoopProg (BitVec width) :=
  let context : LoopContext (BitVec width) :=
    crepMkCtxt target (crepMakeVmap params) functions (params.length - 1)
  let exactContext := productionLoopContextToExact context
  holLoopProgToExecutableCanonical
    (optimiseHOL
      (compFuncHOLExact exactContext.target exactContext.funcs params (crepProgToHOL body)))

/-- Structural relation for the exact-carrier `comp_func` route. -/
theorem crepCompFuncThroughHOLExact_rel {width : Nat} [NeZero width]
    (target : RiscV.Architecture) (functions : InfoMap (Nat × Nat))
    (params : List Nat) (body : CrepProg (BitVec width))
    (hProgramNames : CrepProgNameRanged body)
    (hFunctionNames : ∀ entry ∈ functions, CrepNameRanged entry.1) :
    loopProgExecRel
      (crepCompFuncThroughHOLExact target functions params body
        hProgramNames hFunctionNames)
      (optimiseHOL
        (compFuncHOLExact
          (productionLoopContextToExact (α := BitVec width)
            (crepMkCtxt (α := BitVec width) target (crepMakeVmap params)
              functions (params.length - 1))).target
          (productionLoopContextToExact (α := BitVec width)
            (crepMkCtxt (α := BitVec width) target (crepMakeVmap params)
              functions (params.length - 1))).funcs
          params (crepProgToHOL body))) := by
  exact holLoopProgToExecutableCanonical_rel _

theorem oCompile_skip [OfNat α 0] [OfNat α 1]
    (context : LoopContext α) (live : List Nat) :
    oCompile context live (.skip : CrepProg α) = .mark .skip := by
  simp [oCompile, compileCrepToLoop, loopCompileProg, loopLiveOptimise,
    loopLiveComp, loopShrink, loopShrinkLeaf, loopMarkAll, LoopCall.comp]

end Flapjack
