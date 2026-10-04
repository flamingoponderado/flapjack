import Flapjack.HolRef
import Flapjack.Pancake.LoopToWord.Proofs.CompileCorrect.Base
import Flapjack.Pancake.LoopToWord.Proofs.CompileCorrect.ReturnRaise
import Flapjack.Pancake.LoopToWord.Proofs.CompileCorrect.Assign
import Flapjack.Pancake.LoopToWord.Proofs.CompileCorrect.Arith
import Flapjack.Pancake.LoopToWord.Proofs.CompileCorrect.Memory
import Flapjack.Pancake.LoopToWord.Proofs.CompileCorrect.ShMem
import Flapjack.Pancake.LoopToWord.Proofs.CompileCorrect.FFI
import Flapjack.Pancake.LoopToWord.Proofs.CompileCorrect.If
import Flapjack.Pancake.LoopToWord.Proofs.CompileCorrect.Loop
import Flapjack.Pancake.LoopToWord.Proofs.CompileCorrect.Seq
import Flapjack.Pancake.LoopToWord.Proofs.CompileCorrect.Call
import Flapjack.Pancake.Semantics.LoopSemStateExact.EvaluateInd

/-!
# `loop_to_word` `compile_correct`: assembly of the `evaluate_ind` cases

HOL states `compile_correct` (`cakeml/pancake/proofs/loop_to_wordProofScript.sml:57-97`)
as the conclusion of `loopSem$evaluate_ind` specialised to `goal`, and proves it
by `match_mp_tac` of that induction theorem.  This module applies the tagged
Lean port `LoopSemStateFiniteExact.evaluate_induct` (`evaluate_ind`) with
`P := PropertyAt C` to the 24 tagged constructor case theorems of this
directory (bead `flapjack-pxn.18.5.9.32`).

Lean case theorems whose induction hypotheses are a conjunction (`Seq`,
`Loop`, `Call`) are applied through curried-to-conjunction adapters, because
`evaluate_induct` presents each HOL premise conjunct curried.
-/

namespace Flapjack

open LoopToWord.CompileCorrect

namespace LoopToWordCompileCorrectAssemblyWitnesses

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

end LoopToWordCompileCorrectAssemblyWitnesses

/-- `PropertyAt C p s` for every `(p, s)`: `evaluate_induct` applied to the
    constructor cases.  Untagged helper of `compileCorrect`. -/
theorem compileCorrect_all {width : Nat} [NeZero width] {C F : Type} :
    ∀ (p : HolLoopProg width) (s : LoopSemStateFiniteExact width F), PropertyAt C p s := by
  intro p s
  exact LoopSemStateFiniteExact.evaluate_induct (fun ps => PropertyAt C ps.1 ps.2)
    (fun s => compileCorrect_Skip s) (fun s => compileCorrect_Fail s)
    (fun v e s => compileCorrect_Assign v e s)
    (fun a b c s => compileCorrect_Primitive a b c s)
    (fun a s => compileCorrect_Arith a s)
    (fun e v s => compileCorrect_Store e v s)
    (fun d e s => compileCorrect_SetGlobal d e s)
    (fun a v s => compileCorrect_Load32 a v s)
    (fun a v s => compileCorrect_LoadByte a v s)
    (fun a w s => compileCorrect_Store32 a w s)
    (fun a w s => compileCorrect_StoreByte a w s)
    (fun c1 c2 s h1 h2 => compileCorrect_Seq c1 c2 s ⟨fun res s1 h => h1 res s1 h.1 h.2, h2⟩)
    (fun cmp r1 ri c1 c2 live s ih => compileCorrect_If cmp r1 ri c1 c2 live s ih)
    (fun p s h => compileCorrect_Mark p s h)
    (fun k s => compileCorrect_Break k s)
    (fun k s => compileCorrect_Continue k s)
    (fun li b lo s h1 h2 h3 => compileCorrect_Loop li b lo s
      ⟨fun a b' c d e f h => h1 a b' c d e f h.1 h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2.1 h.2.2.2.2.2,
       fun a b' c d h => h2 a b' c d h.1 h.2.1 h.2.2.1 h.2.2.2,
       fun a b' h => h3 a b' h.1 h.2⟩)
    (fun n s => compileCorrect_Raise n s)
    (fun ns s => compileCorrect_Return ns s)
    (fun op v ad s => compileCorrect_ShMem op v ad s)
    (fun s => compileCorrect_Tick s)
    (fun r l1 s => compileCorrect_LocValue r l1 s)
    (fun ret dest args handler s h1 h2 h3 h4 => compileCorrect_Call ret dest args handler s
      ⟨fun a b c d e f g h i j k l' m n o p' q r u w hx =>
          h1 a b c d e f g h i j k l' m n o p' q r u w hx.1 hx.2.1 hx.2.2.1 hx.2.2.2.1
            hx.2.2.2.2.1 hx.2.2.2.2.2.1 hx.2.2.2.2.2.2.1 hx.2.2.2.2.2.2.2.1 hx.2.2.2.2.2.2.2.2.1
            hx.2.2.2.2.2.2.2.2.2.1 hx.2.2.2.2.2.2.2.2.2.2.1 hx.2.2.2.2.2.2.2.2.2.2.2.1
            hx.2.2.2.2.2.2.2.2.2.2.2.2.1 hx.2.2.2.2.2.2.2.2.2.2.2.2.2.1
            hx.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 hx.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2,
       fun a b c d e f g h i j k l' m n o p' q r u w hx =>
          h2 a b c d e f g h i j k l' m n o p' q r u w hx.1 hx.2.1 hx.2.2.1 hx.2.2.2.1
            hx.2.2.2.2.1 hx.2.2.2.2.2.1 hx.2.2.2.2.2.2.1 hx.2.2.2.2.2.2.2.1 hx.2.2.2.2.2.2.2.2.1
            hx.2.2.2.2.2.2.2.2.2.1 hx.2.2.2.2.2.2.2.2.2.2.1 hx.2.2.2.2.2.2.2.2.2.2.2.1
            hx.2.2.2.2.2.2.2.2.2.2.2.2.1 hx.2.2.2.2.2.2.2.2.2.2.2.2.2.1
            hx.2.2.2.2.2.2.2.2.2.2.2.2.2.2,
       fun a b c d e f g h i hx =>
          h3 a b c d e f g h i hx.1 hx.2.1 hx.2.2.1 hx.2.2.2.1 hx.2.2.2.2.1 hx.2.2.2.2.2.1
            hx.2.2.2.2.2.2.1 hx.2.2.2.2.2.2.2,
       fun a b c d hx => h4 a b c d hx.1 hx.2.1 hx.2.2.1 hx.2.2.2.1 hx.2.2.2.2.1 hx.2.2.2.2.2⟩)
    (fun a b c d e f s => compileCorrect_FFI a b c d e f s) p s

/-- HOL `compile_correct` (`loop_to_wordProofScript.sml:57-97`): the conclusion
    of `loopSem$evaluate_ind` specialised to `goal`, i.e. `goal (prog, s)` for
    all `prog` and `s`, with `goal` written out.  The binders are HOL's
    `prog s res s1 t ctxt retv l`, the premise is `goal`'s conjunction, and the
    conclusion is `goal`'s existential with the `case res of` rendered by
    `resultCase` (`CompileCorrect/Property.lean`).  There is no additional
    premise. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem compileCorrect {width : Nat} [NeZero width] {C F : Type} :
    ∀ (prog : HolLoopProg width) (s : LoopSemStateFiniteExact width F)
      (res : Option (LoopSemStateFiniteExact.LoopResultExact width))
      (s1 : LoopSemStateFiniteExact width F) (t : WordSemStateFiniteExact width C F)
      (ctxt : Spt Nat) (retv : WordLocW width) (l : Nat × Nat),
      LoopSemStateFiniteExact.evaluate prog s = (res, s1) ∧ res ≠ some .error ∧
        loopToWordStateRelHOLExact s t ∧ LoopToWord.localsRelHOL ctxt s.locals t.locals ∧
        sptLookup 0 t.locals = some retv ∧
        goodDimindex width ∧
        ¬ wordSemIsWordLoc retv = true ∧
        (∀ k, sptMem k (accVarsHOL prog .ln) → sptMem k ctxt) →
      ∃ t1 res1,
        WordSemStateFiniteExact.evaluate (LoopToWord.compHOL ctxt prog l).1 t = (res1, t1) ∧
          t1.ffi = s1.ffi ∧
          resultCase ctxt retv t res s1 res1 t1 :=
  fun prog s => compileCorrect_all (C := C) prog s

end Flapjack
