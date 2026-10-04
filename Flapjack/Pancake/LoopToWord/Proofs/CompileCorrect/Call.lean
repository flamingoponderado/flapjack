import Flapjack.HolRef
import Flapjack.Pancake.LoopToWord.Proofs.CompileCorrect.Call.TailCall
import Flapjack.Pancake.LoopToWord.Proofs.CompileCorrect.Call.NoHandler
import Flapjack.Pancake.LoopToWord.Proofs.CompileCorrect.Call.SomeHandler

/-!
# The `Call` case of `loop_to_word`'s `compile_correct`

This is the full `Call` case of HOL `compile_correct`
(`cakeml/pancake/proofs/loop_to_wordProofScript.sml:57-97`, resumed at
`:1017-1407`), bead `flapjack-pxn.18.5.9.27.4`.  The statement is HOL's
`loopSem$evaluate_ind` `Call` conjunct with all four induction-hypothesis
premise sets, as one conjunction as in HOL:
1. the Result-handler continuation;
2. the Exception-handler continuation;
3. the callee body;
4. the tail call.

The goal is written out as in `CompileCorrect/Base.lean`.  The proof
follows HOL's `Cases_on ret` and `Cases_on handler`, dispatching to the
tagged pieces `compileCorrect_Call_TailCall`, `compileCorrect_Call_NOhandler`
and `compileCorrect_Call_SOMEhandler`.
-/

namespace Flapjack

open LoopToWord.CompileCorrect

namespace LoopToWordCompileCorrectCallAssemblyWitnesses

/-- Same-module roundtrip for the relation qualifier's loopSem state fields. -/
theorem holFmapAsFiniteSupportRelationWitness_LoopSemStateFiniteExact
    {width : Nat} [NeZero width] {F : Type} :
    (∀ (state : LoopSemStateBroad width F) (h : state.FiniteSupport),
        (LoopSemStateBroad.ofBroad state h).toBroad = state) ∧
      (∀ state : LoopSemStateFiniteExact width F,
        LoopSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  LoopSemStateFiniteExact.holFmapAsFiniteSupportWitness

/-- Same-module roundtrip for the relation qualifier's wordSem state fields. -/
theorem holFmapAsFiniteSupportRelationWitness_WordSemStateFiniteExact
    {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : WordSemStateBroad width C F) (h : state.FiniteSupport),
        (WordSemStateBroad.ofBroad state h).toBroad = state) ∧
      (∀ state : WordSemStateFiniteExact width C F,
        WordSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  WordSemStateExact.holFmapAsFiniteSupportWitness

end LoopToWordCompileCorrectCallAssemblyWitnesses

/-- The `Call` case of HOL `compile_correct`
    (`loop_to_wordProofScript.sml:57-97`, resumed at `:1017-1407`). -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem compileCorrect_Call {width : Nat} [NeZero width] {C F : Type}
    (ret : Option (List Nat × NumSet)) (dest : Option Nat) (argvars : List Nat)
    (handler : Option (Nat × HolLoopProg width × HolLoopProg width × NumSet)) (s : LoopSemStateFiniteExact width F)
    (ih : (∀ (argvals : List (WordLocW width))
      (v7 : Spt (WordLocW width) × HolLoopProg width) (env : Spt (WordLocW width))
      (prog : HolLoopProg width) (v6 : List Nat × NumSet) (ns' : List Nat) (live' : NumSet)
      (v9 : Option (LoopSemStateFiniteExact.LoopResultExact width))
      (s' : LoopSemStateFiniteExact width F)
      (v8 : Option (LoopSemStateFiniteExact.LoopResultExact width))
      (st : LoopSemStateFiniteExact width F) (v11 : LoopSemStateFiniteExact.LoopResultExact width)
      (retvs : List (WordLocW width)) (v : Nat × HolLoopProg width × HolLoopProg width × NumSet)
      (v1 : Nat) (v2 : HolLoopProg width × HolLoopProg width × NumSet) (v3 : HolLoopProg width)
      (v4 : HolLoopProg width × NumSet) (r : HolLoopProg width) (live_out : NumSet),
      LoopSemStateFiniteExact.getVars argvars s = some argvals ∧
        LoopSemStateFiniteExact.findCode dest argvals s.code = some v7 ∧ v7 = (env, prog) ∧
        ret = some v6 ∧ v6 = (ns', live') ∧ ns'.Nodup ∧
        LoopSemStateFiniteExact.cutRes live' (none, s) = (v9, s') ∧ v9 = none ∧
        LoopSemStateFiniteExact.evaluate prog { s' with locals := env } = (v8, st) ∧
        v8 = some v11 ∧ v11 = .result retvs ∧ retvs.length = ns'.length ∧
        handler = some v ∧ v = (v1, v2) ∧ v2 = (v3, v4) ∧ v4 = (r, live_out) →
      PropertyAt C r (LoopSemStateFiniteExact.setVars ns' retvs { st with locals := s'.locals })) ∧
      (∀ (argvals : List (WordLocW width))
      (v7 : Spt (WordLocW width) × HolLoopProg width) (env : Spt (WordLocW width))
      (prog : HolLoopProg width) (v6 : List Nat × NumSet) (ns' : List Nat) (live' : NumSet)
      (v9 : Option (LoopSemStateFiniteExact.LoopResultExact width))
      (s' : LoopSemStateFiniteExact width F)
      (v8 : Option (LoopSemStateFiniteExact.LoopResultExact width))
      (st : LoopSemStateFiniteExact width F) (v11 : LoopSemStateFiniteExact.LoopResultExact width)
      (exn : WordLocW width) (v : Nat × HolLoopProg width × HolLoopProg width × NumSet)
      (n : Nat) (v2 : HolLoopProg width × HolLoopProg width × NumSet) (h : HolLoopProg width)
      (v4 : HolLoopProg width × NumSet) (v5 : HolLoopProg width) (live_out : NumSet),
      LoopSemStateFiniteExact.getVars argvars s = some argvals ∧
        LoopSemStateFiniteExact.findCode dest argvals s.code = some v7 ∧ v7 = (env, prog) ∧
        ret = some v6 ∧ v6 = (ns', live') ∧ ns'.Nodup ∧
        LoopSemStateFiniteExact.cutRes live' (none, s) = (v9, s') ∧ v9 = none ∧
        LoopSemStateFiniteExact.evaluate prog { s' with locals := env } = (v8, st) ∧
        v8 = some v11 ∧ v11 = .exception exn ∧
        handler = some v ∧ v = (n, v2) ∧ v2 = (h, v4) ∧ v4 = (v5, live_out) →
      PropertyAt C h (LoopSemStateFiniteExact.setVar n exn { st with locals := s'.locals })) ∧
      (∀ (argvals : List (WordLocW width))
      (v7 : Spt (WordLocW width) × HolLoopProg width) (env : Spt (WordLocW width))
      (prog : HolLoopProg width) (v6 : List Nat × NumSet) (ns' : List Nat) (live' : NumSet)
      (v9 : Option (LoopSemStateFiniteExact.LoopResultExact width))
      (s' : LoopSemStateFiniteExact width F),
      LoopSemStateFiniteExact.getVars argvars s = some argvals ∧
        LoopSemStateFiniteExact.findCode dest argvals s.code = some v7 ∧ v7 = (env, prog) ∧
        ret = some v6 ∧ v6 = (ns', live') ∧ ns'.Nodup ∧
        LoopSemStateFiniteExact.cutRes live' (none, s) = (v9, s') ∧ v9 = none →
      PropertyAt C prog { s' with locals := env }) ∧
      (∀ (argvals : List (WordLocW width))
      (v7 : Spt (WordLocW width) × HolLoopProg width) (env : Spt (WordLocW width))
      (prog : HolLoopProg width),
      LoopSemStateFiniteExact.getVars argvars s = some argvals ∧
        LoopSemStateFiniteExact.findCode dest argvals s.code = some v7 ∧ v7 = (env, prog) ∧
        ret = none ∧ handler = none ∧ s.clock ≠ 0 →
      PropertyAt C prog { LoopSemStateFiniteExact.decClock s with locals := env })) :
    ∀ (res : Option (LoopSemStateFiniteExact.LoopResultExact width))
      (s1 : LoopSemStateFiniteExact width F) (t : WordSemStateFiniteExact width C F)
      (ctxt : Spt Nat) (retv : WordLocW width) (l : Nat × Nat),
      LoopSemStateFiniteExact.evaluate (.call ret dest argvars handler) s = (res, s1) ∧ res ≠ some .error ∧
        loopToWordStateRelHOLExact s t ∧ LoopToWord.localsRelHOL ctxt s.locals t.locals ∧
        sptLookup 0 t.locals = some retv ∧
        goodDimindex width ∧
        ¬ wordSemIsWordLoc retv = true ∧
        (∀ k, sptMem k (accVarsHOL (width := width) (.call ret dest argvars handler) .ln) → sptMem k ctxt) →
      ∃ t1 res1,
        WordSemStateFiniteExact.evaluate (LoopToWord.compHOL ctxt (.call ret dest argvars handler) l).1 t = (res1, t1) ∧
          t1.ffi = s1.ffi ∧
          resultCase ctxt retv t res s1 res1 t1 := by
  obtain ⟨ihR, ihE, ihC, ihT⟩ := ih
  cases ret with
  | none =>
    exact compileCorrect_Call_TailCall dest argvars handler s
      (fun argvals v7 env prog h => ihT argvals v7 env prog h)
  | some v =>
    obtain ⟨ns, live⟩ := v
    cases handler with
    | none =>
      exact compileCorrect_Call_NOhandler ns live dest argvars s
        (fun a b c d e f g h i hh => ihC a b c d e f g h i hh)
    | some hv =>
      obtain ⟨hn, hh, hr, lo⟩ := hv
      exact compileCorrect_Call_SOMEhandler ns live dest argvars hn hh hr lo s
        (fun a b c d e f g h i j k l m n o p q r u w hx => ihR a b c d e f g h i j k l m n o p q r u w hx)
        (fun a b c d e f g h i j k l m n o p q r u w hx => ihE a b c d e f g h i j k l m n o p q r u w hx)
        (fun a b c d e f g h i hx => ihC a b c d e f g h i hx)

end Flapjack
