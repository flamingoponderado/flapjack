import Flapjack.Pancake.Semantics.LoopSemStateExact.Evaluate

/-!
# Production/exact Loop FFI case under explicit hook refinement

This compares the HOL-shaped `LoopSemStateFiniteExact.evaluate` FFI clause
(`cakeml/pancake/semantics/loopSemScript.sml:426-440`, implemented at
`Flapjack/Pancake/Semantics/LoopSemStateExact/Evaluate.lean` under
`| .ffi ... =>`) with the production `Flapjack.evaluateLoop` FFI branch
(`Flapjack/Pancake/Semantics/LoopSem.lean:244-252`).

The two evaluators run on different carriers: the exact program is a
`HolLoopProg` whose FFI constructor carries an exact `MlString` name and a
`NumSet` cut set, while the production program is a `LoopProg (BitVec width)`
whose FFI constructor carries a `String` name and a `List Nat` live set.  The
production run therefore uses the compiler projection
`Flapjack.Basis.Pure.MlString.toStringOfBytes function` for the name and a
caller-supplied `live : List Nat` for the live set.

The only genuinely semantic gap isolated here is the executed FFI hook: the
arbitrary production hook `hooks.ffi` is not proved to compute the exact
`callFFIHOL` clause.  That gap is made explicit as `hffi`, a hook-refinement
premise relating `hooks.ffi` on a post-cut production state to the exact
post-cut computation `ffiPost` transported through `prodRel`.  The
`cut_state`/`cut_loop_state` correspondence is likewise made explicit as
`hcutNone`/`hcutSome` (no cut bridge lemma exists yet).  This is
Flapjack-specific bridge infrastructure, not a standalone HOL theorem or a
whole-evaluator simulation; it carries no `@[hol]` tag.
-/

namespace Flapjack
namespace LoopSemStateFiniteExact.EvaluateCases

/-- Result relation for the FFI case.  Both evaluators return `Error` on a
failed local lookup, a failed byte read, or a failed `cut_state`; the exact
`none` (continue) and `finalFfi` outcomes match the production hook's `none`
and `finalFfi` outcomes, with final FFI events related by `FfiFinalEventRel`
(production first, exact second). -/
def ffiResultRel {width : Nat} [NeZero width]
    (exact : Option (LoopResultExact width))
    (production : Option (LoopMachineResult (BitVec width))) : Prop :=
  match exact, production with
  | some .error, some .error => True
  | none, none => True
  | some (.finalFfi holEvent), some (.finalFfi prodEvent) =>
      FfiFinalEventRel prodEvent holEvent
  | _, _ => False

/-- The exact HOL FFI clause after `cut_state` has produced `s'` and the four
local words (`configurationAddress`, `arrayAddress`, `configurationSize`,
`arraySize`) have been read.  This is the post-cut body of the tagged exact
`evaluate` FFI clause (`loopSemScript.sml:427-440`): read both byte arrays from
`s'`, call `callFFIHOL`, clear locals on `FFI_final`, and write the returned
bytes to the second array on `FFI_return`. -/
def ffiPost {width : Nat} [NeZero width] {F : Type}
    (s' : LoopSemStateFiniteExact width F)
    (function : Flapjack.Basis.Pure.MlString.MlString)
    (configurationAddress arrayAddress : BitVec width)
    (configurationSize arraySize : BitVec width) :
    Option (LoopResultExact width) × LoopSemStateFiniteExact width F :=
  match readBytearrayWordHOL configurationAddress configurationSize.toNat
          (memLoadByteAuxExact s'.memory s'.mdomain s'.be),
      readBytearrayWordHOL arrayAddress arraySize.toNat
          (memLoadByteAuxExact s'.memory s'.mdomain s'.be) with
  | some bytes, some bytes2 =>
      match callFFIHOL s'.ffi (.extCall function) bytes bytes2 with
      | .final outcome => (some (.finalFfi outcome), callEnv [] s')
      | .ret newFfi newBytes =>
          (none, { s' with
            memory := writeBytearrayExact arrayAddress newBytes s'.memory s'.mdomain s'.be,
            ffi := newFfi })
  | _, _ => (some .error, s')

/-- Bundle of the FFI-case result relation and the post-state `prodRel`, so a
hook-refinement premise can state both halves at once. -/
def ffiStepRel {width : Nat} [NeZero width] {F : Type}
    (exact : Option (LoopResultExact width) × LoopSemStateFiniteExact width F)
    (production : LoopMachineStep (BitVec width) F) : Prop :=
  ffiResultRel exact.1 production.1 ∧ exact.2.prodRel production.2

/-- Relate the FFI control/effect case of exact HOL evaluation to the
production Loop evaluator under `prodRel` plus explicit refinement premises.
Positive fuel (`machine.clock + 1`) reaches the production FFI clause.  The
`cutset`/`live` correspondence is supplied by `hcutNone`/`hcutSome`; the
executed hook is related to the exact post-cut computation by `hffi`.  No other
evaluator constructor or hook is assumed correct. -/
theorem evaluateFfi_prodRel {width : Nat} [NeZero width] {F : Type}
    {state : LoopSemStateFiniteExact width F}
    {machine : LoopMachineState (BitVec width) F}
    (hooks : LoopEvaluateHooks (BitVec width) F)
    (hrel : state.prodRel machine)
    (function : Flapjack.Basis.Pure.MlString.MlString)
    (configuration configurationLength array arrayLength : Nat)
    (cutset : NumSet) (live : List Nat)
    (hcutNone : cutState cutset state = none → cutLoopState live machine = none)
    (hcutSome : ∀ s' : LoopSemStateFiniteExact width F,
        cutState cutset state = some s' →
        ∃ m' : LoopMachineState (BitVec width) F,
          cutLoopState live machine = some m' ∧ s'.prodRel m')
    (hffi : ∀ (configurationSize configurationAddress arraySize arrayAddress : BitVec width)
        (s' : LoopSemStateFiniteExact width F) (m' : LoopMachineState (BitVec width) F),
        s'.prodRel m' →
        ffiStepRel (ffiPost s' function configurationAddress arrayAddress
            configurationSize arraySize)
          (hooks.ffi (Flapjack.Basis.Pure.MlString.toStringOfBytes function)
            configurationSize configurationAddress arraySize arrayAddress live m')) :
    let exactStep := LoopSemStateFiniteExact.evaluate
      (.ffi function configuration configurationLength array arrayLength cutset) state
    let productionStep := Flapjack.evaluateLoop (machine.clock + 1) hooks
      (.ffi (Flapjack.Basis.Pure.MlString.toStringOfBytes function)
        configuration configurationLength array arrayLength live) machine
    ffiResultRel exactStep.1 productionStep.1 ∧
      exactStep.2.prodRel productionStep.2 := by
  cases h1 : sptLookup configurationLength state.locals with
  | none =>
      constructor
      · simp [LoopSemStateFiniteExact.evaluate, Flapjack.evaluateLoop, ffiResultRel,
          hrel.1 configurationLength, h1]
      · simpa [LoopSemStateFiniteExact.evaluate, Flapjack.evaluateLoop,
          hrel.1 configurationLength, h1] using hrel
  | some v1 =>
      cases v1 with
      | loc identifier offset =>
          constructor
          · simp [LoopSemStateFiniteExact.evaluate, Flapjack.evaluateLoop, ffiResultRel,
              hrel.1 configurationLength, h1, loopValueOfWordLocW]
          · simpa [LoopSemStateFiniteExact.evaluate, Flapjack.evaluateLoop,
              hrel.1 configurationLength, h1, loopValueOfWordLocW] using hrel
      | word w =>
          cases h2 : sptLookup configuration state.locals with
          | none =>
              constructor
              · simp [LoopSemStateFiniteExact.evaluate, Flapjack.evaluateLoop, ffiResultRel,
                  hrel.1 configurationLength, hrel.1 configuration, h1, h2,
                  loopValueOfWordLocW]
              · simpa [LoopSemStateFiniteExact.evaluate, Flapjack.evaluateLoop,
                  hrel.1 configurationLength, hrel.1 configuration, h1, h2,
                  loopValueOfWordLocW] using hrel
          | some v2 =>
              cases v2 with
              | loc identifier offset =>
                  constructor
                  · simp [LoopSemStateFiniteExact.evaluate, Flapjack.evaluateLoop,
                      ffiResultRel, hrel.1 configurationLength, hrel.1 configuration,
                      h1, h2, loopValueOfWordLocW]
                  · simpa [LoopSemStateFiniteExact.evaluate, Flapjack.evaluateLoop,
                      hrel.1 configurationLength, hrel.1 configuration, h1, h2,
                      loopValueOfWordLocW] using hrel
              | word w2 =>
                  cases h3 : sptLookup arrayLength state.locals with
                  | none =>
                      constructor
                      · simp [LoopSemStateFiniteExact.evaluate, Flapjack.evaluateLoop,
                          ffiResultRel, hrel.1 configurationLength, hrel.1 configuration,
                          hrel.1 arrayLength, h1, h2, h3, loopValueOfWordLocW]
                      · simpa [LoopSemStateFiniteExact.evaluate, Flapjack.evaluateLoop,
                          hrel.1 configurationLength, hrel.1 configuration,
                          hrel.1 arrayLength, h1, h2, h3, loopValueOfWordLocW] using hrel
                  | some v3 =>
                      cases v3 with
                      | loc identifier offset =>
                          constructor
                          · simp [LoopSemStateFiniteExact.evaluate, Flapjack.evaluateLoop,
                              ffiResultRel, hrel.1 configurationLength,
                              hrel.1 configuration, hrel.1 arrayLength, h1, h2, h3,
                              loopValueOfWordLocW]
                          · simpa [LoopSemStateFiniteExact.evaluate, Flapjack.evaluateLoop,
                              hrel.1 configurationLength, hrel.1 configuration,
                              hrel.1 arrayLength, h1, h2, h3, loopValueOfWordLocW] using hrel
                      | word w3 =>
                          cases h4 : sptLookup array state.locals with
                          | none =>
                              constructor
                              · simp [LoopSemStateFiniteExact.evaluate, Flapjack.evaluateLoop,
                                  ffiResultRel, hrel.1 configurationLength,
                                  hrel.1 configuration, hrel.1 arrayLength, hrel.1 array,
                                  h1, h2, h3, h4, loopValueOfWordLocW]
                              · simpa [LoopSemStateFiniteExact.evaluate, Flapjack.evaluateLoop,
                                  hrel.1 configurationLength, hrel.1 configuration,
                                  hrel.1 arrayLength, hrel.1 array, h1, h2, h3, h4,
                                  loopValueOfWordLocW] using hrel
                          | some v4 =>
                              cases v4 with
                              | loc identifier offset =>
                                  constructor
                                  · simp [LoopSemStateFiniteExact.evaluate,
                                      Flapjack.evaluateLoop, ffiResultRel,
                                      hrel.1 configurationLength, hrel.1 configuration,
                                      hrel.1 arrayLength, hrel.1 array, h1, h2, h3, h4,
                                      loopValueOfWordLocW]
                                  · simpa [LoopSemStateFiniteExact.evaluate,
                                      Flapjack.evaluateLoop, hrel.1 configurationLength,
                                      hrel.1 configuration, hrel.1 arrayLength, hrel.1 array,
                                      h1, h2, h3, h4, loopValueOfWordLocW] using hrel
                              | word w4 =>
                                  cases hc : cutState cutset state with
                                  | none =>
                                      have hcutEq : cutLoopState live machine = none :=
                                        hcutNone hc
                                      constructor
                                      · simp [LoopSemStateFiniteExact.evaluate,
                                          Flapjack.evaluateLoop, ffiResultRel,
                                          hrel.1 configurationLength, hrel.1 configuration,
                                          hrel.1 arrayLength, hrel.1 array, h1, h2, h3, h4,
                                          hc, hcutEq, loopValueOfWordLocW]
                                      · simpa [LoopSemStateFiniteExact.evaluate,
                                          Flapjack.evaluateLoop, hrel.1 configurationLength,
                                          hrel.1 configuration, hrel.1 arrayLength,
                                          hrel.1 array, h1, h2, h3, h4, hc, hcutEq,
                                          loopValueOfWordLocW] using hrel
                                  | some s' =>
                                      obtain ⟨m', hcutEq, hrel'⟩ := hcutSome s' hc
                                      have hstep := hffi w w2 w3 w4 s' m' hrel'
                                      simp only [LoopSemStateFiniteExact.evaluate,
                                        Flapjack.evaluateLoop, hrel.1 configurationLength,
                                        hrel.1 configuration, hrel.1 arrayLength,
                                        hrel.1 array, h1, h2, h3, h4, hc, hcutEq,
                                        Option.map_some, loopValueOfWordLocW]
                                      exact hstep

end LoopSemStateFiniteExact.EvaluateCases
end Flapjack