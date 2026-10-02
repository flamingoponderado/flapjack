import Flapjack.Compiler.Backend.Semantics.StackSem.EvaluateDef
import Flapjack.Misc.LprefixLub

/-!
# HOL `stackSem` observational semantics

Counterpart of `cakeml/compiler/backend/semantics/stackSemScript.sml:1116-1143`:
`semantics_def` over the tagged exact StackSem `evaluate`, using the `llist`/`lprefix_lub`
renderings shared with the wordSem, loopSem and crepSem semantics ports.
-/

namespace Flapjack.StackSemEvaluate

open Flapjack.Compiler.Backend.StackLang

namespace StackSemSemanticsSupport

/-- Canonical imported StackSem carrier roundtrip for the tagged `semantics`. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : StackSemStateBroad width C F) (h : state.FiniteSupport),
        (StackSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : StackSemStateFiniteExact width C F,
        StackSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  StackSemStateOps.holFmapAsFiniteSupportWitness

end StackSemSemanticsSupport

/-- Exact HOL `stackSem$semantics_def` (`stackSemScript.sml:1116-1143`):

    ```
    semantics start s =
      let prog = Call NONE (INL start) NONE in
      if ∃k. let res = FST (evaluate (prog, s with clock := k)) in
               res <> SOME TimeOut /\ res <> SOME (Result (Loc 1 0)) /\
               (!w. res <> SOME (Halt (Word w))) /\ !f. res <> SOME (FinalFFI f)
      then Fail
      else
        case some res.
          ∃k t r outcome.
            evaluate (prog, s with clock := k) = (SOME r,t) ∧
            (case r of
             | FinalFFI e => outcome = FFI_outcome e
             | Halt w => outcome = if w = Word 0w then Success
                                   else Resource_limit_hit
             | Result _ => outcome = Success
             | _ => F) ∧
            res = Terminate outcome t.ffi.io_events
          of
        | SOME res => res
        | NONE =>
          Diverge
             (build_lprefix_lub
               (IMAGE (λk. fromList (SND (evaluate (prog,s with clock := k))).ffi.io_events) UNIV))
    ```

    HOL's `some` is `holOptionSome`, and `build_lprefix_lub`/`fromList` are the renderings
    of HOL's `lprefix_lub`/`llist` libraries. The set `IMAGE f UNIV` is the predicate
    `fun l => ∃ k, l = f k`. HOL's `=`/`<>` on results and `word_loc` are decided
    classically. The definition is noncomputable, as HOL's classical definition is. -/
@[hol "cakeml/compiler/backend/semantics/stackSemScript.sml" "semantics_def"
  (fmap_as_finite_support := [regs, fpRegs, store]) (words_as_type_indexed_bitvec)]
noncomputable def semantics {width : Nat} [NeZero width] {C F : Type}
    (start : Nat) (s : StackSemStateFiniteExact width C F) : HolBehaviour :=
  let prog : HolProg width := .call none (.inl start) none
  open Classical in
  if ∃ k, let res := (evaluate (prog, { s with clock := k })).1
      res ≠ some .timeOut ∧ res ≠ some (.result (.loc 1 0)) ∧
      (∀ w, res ≠ some (.halt (.word w))) ∧ ∀ e, res ≠ some (.finalFFI e)
  then .fail
  else
    match holOptionSome (fun res => ∃ k t r outcome,
        evaluate (prog, { s with clock := k }) = (some r, t) ∧
        (match r with
         | .finalFFI e => outcome = HolOutcome.ffiOutcome e
         | .halt w => outcome =
             if w = .word 0 then HolOutcome.success else HolOutcome.resourceLimitHit
         | .result _ => outcome = HolOutcome.success
         | _ => False) ∧
        res = HolBehaviour.terminate outcome t.ffi.ioEvents) with
    | some res => res
    | none => .diverge (HolLList.buildLprefixLub (fun l => ∃ k,
        l = HolLList.fromList (evaluate (prog, { s with clock := k })).2.ffi.ioEvents))

/-- The body of `semantics` as a function of the clock-indexed entry-call evaluations
(Flapjack infrastructure; `semantics_eq_aux` unfolds `semantics` to it). -/
noncomputable def semanticsAux {width : Nat} [NeZero width] {C F : Type}
    (E : Nat → Option (StackSemResult width) × StackSemStateFiniteExact width C F) :
    HolBehaviour :=
  open Classical in
  if ∃ k, let res := (E k).1
      res ≠ some .timeOut ∧ res ≠ some (.result (.loc 1 0)) ∧
      (∀ w, res ≠ some (.halt (.word w))) ∧ ∀ e, res ≠ some (.finalFFI e)
  then .fail
  else
    match holOptionSome (fun res => ∃ k t r outcome,
        E k = (some r, t) ∧
        (match r with
         | .finalFFI e => outcome = HolOutcome.ffiOutcome e
         | .halt w => outcome =
             if w = .word 0 then HolOutcome.success else HolOutcome.resourceLimitHit
         | .result _ => outcome = HolOutcome.success
         | _ => False) ∧
        res = HolBehaviour.terminate outcome t.ffi.ioEvents) with
    | some res => res
    | none => .diverge (HolLList.buildLprefixLub (fun l => ∃ k,
        l = HolLList.fromList (E k).2.ffi.ioEvents))

theorem semantics_eq_aux {width : Nat} [NeZero width] {C F : Type}
    (start : Nat) (s : StackSemStateFiniteExact width C F) :
    semantics start s = semanticsAux (fun k =>
      evaluate ((.call none (.inl start) none : HolProg width), { s with clock := k })) := rfl

/-- `semanticsAux` only observes results and final FFI states (Flapjack infrastructure). -/
theorem semanticsAux_congr {width : Nat} [NeZero width] {C F : Type}
    (E : Nat → Option (StackSemResult width) × StackSemStateFiniteExact width C F)
    (g : StackSemStateFiniteExact width C F → StackSemStateFiniteExact width C F)
    (hg : ∀ t, (g t).ffi = t.ffi) :
    semanticsAux (fun k => ((E k).1, g (E k).2)) = semanticsAux E := by
  have hP : (fun res => ∃ k t r outcome,
        ((E k).1, g (E k).2) = (some r, t) ∧
        (match r with
         | .finalFFI e => outcome = HolOutcome.ffiOutcome e
         | .halt w => outcome =
             if w = .word 0 then HolOutcome.success else HolOutcome.resourceLimitHit
         | .result _ => outcome = HolOutcome.success
         | _ => False) ∧
        res = HolBehaviour.terminate outcome t.ffi.ioEvents) =
      (fun res => ∃ k t r outcome,
        E k = (some r, t) ∧
        (match r with
         | .finalFFI e => outcome = HolOutcome.ffiOutcome e
         | .halt w => outcome =
             if w = .word 0 then HolOutcome.success else HolOutcome.resourceLimitHit
         | .result _ => outcome = HolOutcome.success
         | _ => False) ∧
        res = HolBehaviour.terminate outcome t.ffi.ioEvents) := by
    funext res
    apply propext
    constructor
    · rintro ⟨k, t, r, o, he, hm, hr⟩
      simp only [Prod.mk.injEq] at he
      obtain ⟨he1, he2⟩ := he
      refine ⟨k, (E k).2, r, o, Prod.ext he1 rfl, hm, ?_⟩
      rw [hr, ← he2, hg]
    · rintro ⟨k, t, r, o, he, hm, hr⟩
      refine ⟨k, g t, r, o, by rw [he], hm, ?_⟩
      rw [hr, hg]
  unfold semanticsAux
  simp only [hg]
  rw [hP]

/-- Two states whose entry-call evaluations agree in result, and in final state up to an
FFI-preserving map, have the same semantics (Flapjack infrastructure). -/
theorem semantics_congr {width : Nat} [NeZero width] {C F : Type}
    (start : Nat) (s s' : StackSemStateFiniteExact width C F)
    (g : StackSemStateFiniteExact width C F → StackSemStateFiniteExact width C F)
    (hg : ∀ t, (g t).ffi = t.ffi)
    (h : ∀ k, evaluate ((.call none (.inl start) none : HolProg width), { s' with clock := k }) =
      ((evaluate ((.call none (.inl start) none : HolProg width), { s with clock := k })).1,
        g (evaluate ((.call none (.inl start) none : HolProg width), { s with clock := k })).2)) :
    semantics start s' = semantics start s := by
  rw [semantics_eq_aux, semantics_eq_aux, funext h]
  exact semanticsAux_congr _ g hg

end Flapjack.StackSemEvaluate
