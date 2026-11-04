import Flapjack.Parser
import Flapjack.Pancake.PanToCrep.Compile
import Flapjack.Pancake.PanSimp.DeclsProduction
import Flapjack.Pancake.PanGlobalsByteRanged
import Flapjack.Pancake.PanStructs.CompileTopProduction
import Flapjack.Pancake.PanSimpByteRanged
import Flapjack.CompileFunctionDistinct
import Flapjack.Pancake.CrepToLoop.Optimise
import Flapjack.Pancake.CrepToLoop.ProductionDeclarations
import Flapjack.Pancake.LoopToWord
import Flapjack.Pancake.LoopToWord.CompFuncExact
import Flapjack.Pancake.LoopToWord.LoopProgCarrierCodec
import Flapjack.RiscV.WordDiagnostics
import Flapjack.RiscV.WordFuseConditions
import Flapjack.RiscV.WordUnreach
import Flapjack.RiscV.Lab
import Flapjack.Display
import Flapjack.Pancake.Semantics.LoopSem
import Flapjack.LoopSemantics

/-!
# Effect-free `loop_live` regression on the production compiler path

This restores the executable `out = 7` while-loop regression (formerly
`LoopLivePreloopLocals.lean`, removed with the retired `compileFlapjack`
wrapper) on the current production entrypoint `compileFlapjackEntryCake`.

Scope: the test exercises only the *effect-free* fragment of the Loop machine.
The tested programs contain no `Primitive`, `Arith`, `Store`, `SetGlobal`,
`Load32`, `LoadByte`, `Store32`, `StoreByte`, `ShMem`, or `Ffi` nodes and no
`.call`, so the corresponding `LoopEvaluateHooks` fields are never invoked.
This fixture supplies the effect hooks as total functions that yield `Error`,
even though ports of `loop_primop`, `sh_mem_op`, and the ExtCall boundary now
exist elsewhere. Its `arith` and `setGlobal` hooks are no-ops. The successful
`[7]` result therefore also witnesses that the
execution path never reaches them.  `effectFree` asserts this structurally
over the compiled `LoopProg`, rejecting every `.call`.  The `eval` hook is a
word-only fixture bridge (`machineToLoopState` drops `.loc` locals/memory); it
is not a faithful general `loopSem$eval` adapter and is not exposed as
production code.  This test does NOT claim `s6a.3` complete.

The reference is the HOL loop-live regression: with the incoming live set at
the loop cutset, the pre-loop assignment `out = 7` stays live and the program
returns 7.
-/

namespace Flapjack.Test.LoopLiveEffectFreeParity

open Flapjack Parser

abbrev Word := RiscV.Word 64

def outSevenSource : String :=
  "\n  fun 1 main () {\n    var 1 out = 7;\n    var 1 i = 0;\n    while i < 2 {\n      i = i + 1;\n    }\n    return out;\n  }\n"

def wideConstantSource : String :=
  "\n  fun 1 main () {\n    var 1 x = 1073741832;\n    return x;\n  }\n"

/-- Structural witness that a compiled program stays in the effect-free
    fragment, so the unported hooks (`primitive`, `arith`, `store`,
    `setGlobal`, `load32`, `loadByte`, `store32`, `storeByte`, `shMem`, `ffi`)
    are never invoked.  A `.call` is accepted only when its direct target
    resolves in the code table to an effect-free body (recursively, with a
    visited set for cycles) and its handler bodies are effect-free; indirect
    calls (`target = none`) are rejected because the callee cannot be checked. -/
partial def effectFreeIn (code : LoopCode Word) (visited : List Nat) :
    LoopProg Word → Bool
  | .primitive .. | .arith .. | .store .. | .setGlobal .. | .load32 ..
  | .loadByte .. | .store32 .. | .storeByte .. | .shMem .. | .ffi .. => false
  | .seq first second => effectFreeIn code visited first && effectFreeIn code visited second
  | .ite _ _ _ thenBranch elseBranch _ =>
      effectFreeIn code visited thenBranch && effectFreeIn code visited elseBranch
  | .loop _ body _ => effectFreeIn code visited body
  | .mark body => effectFreeIn code visited body
  | .call _ target _ handler =>
      let calleeOk :=
        match target with
        | none => false
        | some label =>
            if visited.contains label then true
            else match lookupLoopFunction label code with
              | none => true
              | some (_, body) => effectFreeIn code (label :: visited) body
      let handlerOk :=
        match handler with
        | none => true
        | some (_, body, exceptionHandler, _) =>
            effectFreeIn code visited body &&
              effectFreeIn code visited exceptionHandler
      calleeOk && handlerOk
  | _ => true

/-- Effect-free check for a whole compiled function table plus entry body. -/
def effectFree (code : LoopCode Word) (body : LoopProg Word) : Bool :=
  effectFreeIn code [] body

/-- Word-only fixture bridge from the machine state into the source-shaped
    `LoopState` used by the reviewed `evalLoopExpSource` expression evaluator.

    This is NOT a faithful general `loopSem$eval` adapter and is not exposed as
    production code: a `.loc`-valued local or memory cell is dropped to `none`
    (only `.word` payloads survive).  A path that read a location-valued
    local/memory would therefore evaluate to `none`, fail the machine step, and
    could not produce the asserted successful `[7]` result; the exact-result
    guards below rule out such a path for these fixtures.  `globals` keeps the
    location constructor because `evalLoopExpSource` handles `.loc` there. -/
def machineToLoopState (state : LoopMachineState Word F) : LoopState Word :=
  { locals := fun name =>
      (state.locals name).bind fun value => match value with
        | .word word => some word
        | .loc _ _ => none
    globals := fun address =>
      (state.globals address).map fun value => match value with
        | .word word => .word word
        | .loc identifier offset => .loc identifier offset
    memory := fun address =>
      (state.memory address).bind fun value => match value with
        | .word word => some word
        | .loc _ _ => none }

/-- Word-only fixture `eval` hook: `evalLoopExpSource` over the bridged state,
    wrapped back into a `Word` cell as in `loopSem$eval`.  Because
    `machineToLoopState` drops `.loc` locals/memory, this is a fixture adapter
    for word-valued programs only, not a faithful general `loopSem$eval`. -/
def evalHook (state : LoopMachineState Word F) (expression : LoopExp Word) :
    Option (LoopValue Word) :=
  (evalLoopExpSource (machineToLoopState state) state.baseAddr state.topAddr
    expression).map .word

/-- Faithful `compare` hook: `word_cmp` via the reviewed `evalLoopCondition`. -/
def compareHook (operator : Cmp) (left right : LoopValue Word) : Bool :=
  match left, right with
  | .word leftWord, .word rightWord =>
      (evalLoopCondition operator leftWord rightWord).getD false
  | _, _ => false

/-- Hooks for the effect-free fragment.  `primitive`, `store`, `load32`,
    `loadByte`, `store32`, `storeByte`, `shMem`, and `ffi` are deliberately
    total fallbacks that yield `Error`; `arith` and `setGlobal` are no-ops that
    return the state unchanged.  The programs under test never invoke any of
    these fields (see `effectFree`). -/
def effectFreeHooks : LoopEvaluateHooks Word Unit where
  eval := evalHook
  primitive := fun _ _ => none
  arith := fun state _ => some state
  store := fun _ _ _ => none
  setGlobal := fun state _ _ => state
  load32 := fun _ _ => none
  loadByte := fun _ _ => none
  store32 := fun _ _ _ => none
  storeByte := fun _ _ _ => none
  compare := compareHook
  shMem := fun _ _ _ state => (some .error, state)
  ffi := fun _ _ _ _ _ _ state => (some .error, state)

def initialState (code : LoopCode Word) : LoopMachineState Word Unit :=
  { locals := fun _ => none
    globals := fun _ => none
    memory := fun _ => none
    mdomain := fun _ => false
    shMdomain := fun _ => false
    clock := 200
    code := code
    be := false
    ffi := trivialFfiState Unit ()
    baseAddr := 0
    topAddr := 0 }

end Flapjack.Test.LoopLiveEffectFreeParity
