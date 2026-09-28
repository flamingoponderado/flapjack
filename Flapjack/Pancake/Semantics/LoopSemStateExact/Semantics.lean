import Flapjack.Pancake.Semantics.LoopSemStateExact.Evaluate
import Flapjack.Misc.LprefixLub

namespace Flapjack
namespace LoopSemStateFiniteExact

namespace LoopSemanticsFiniteSupport

/-- Local same-module witness for the canonical finite-support
`LoopSemStateFiniteExact` carrier used by the `fmap_as_finite_support := [globals]`
qualified ports in this module (re-exports the checked witness of
`Flapjack/Pancake/Semantics/LoopSemStateExact.lean`). -/
theorem holFmapAsFiniteSupportWitness {width : Nat} [NeZero width] {F : Type} :
    (∀ (state : LoopSemStateBroad width F) (h : state.FiniteSupport),
        (LoopSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : LoopSemStateFiniteExact width F,
        LoopSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  Flapjack.LoopSemStateFiniteExact.holFmapAsFiniteSupportWitness

end LoopSemanticsFiniteSupport

/-- Exact HOL `loopSem$semantics_def` (`loopSemScript.sml:508-533`):

    ```
    semantics s start =
     let prog = Call NONE (SOME start) [] NONE in
      if ∃k. case FST(evaluate (prog,s with clock := k)) of
              | SOME TimeOut => F | SOME (FinalFFI _) => F | SOME (Result _) => F | _ => T
      then Fail
      else
       case some res. ∃k t r outcome.
          evaluate (prog, s with clock := k) = (r,t) ∧
          (case r of
           | (SOME (FinalFFI e)) => outcome = FFI_outcome e
           | (SOME (Result _))   => outcome = Success
           | _ => F) ∧
          res = Terminate outcome t.ffi.io_events
        of
      | SOME res => res
      | NONE => Diverge (build_lprefix_lub
          (IMAGE (λk. fromList (SND (evaluate (prog,s with clock := k))).ffi.io_events) UNIV))
    ```

    HOL's `some` is `holOptionSome`, `build_lprefix_lub`/`fromList` are the
    renderings of HOL's `lprefix_lub`/`llist` libraries, and the set
    `IMAGE f UNIV` is the predicate `fun l => ∃ k, l = f k`.  Noncomputable,
    exactly as HOL's classical definition. -/
@[hol "cakeml/pancake/semantics/loopSemScript.sml" "semantics_def"
  (fmap_as_finite_support := [globals]) (words_as_type_indexed_bitvec)]
noncomputable def semantics {width : Nat} [NeZero width] {F : Type}
    (s : LoopSemStateFiniteExact width F) (start : Nat) : HolBehaviour :=
  let prog : HolLoopProg width := .call none (some start) [] none
  open Classical in
  if ∃ k, (match (evaluate prog { s with clock := k }).1 with
      | some .timeOut => False
      | some (.finalFfi _) => False
      | some (.result _) => False
      | _ => True)
  then .fail
  else
    match holOptionSome (fun res => ∃ k t r outcome,
        evaluate prog { s with clock := k } = (r, t) ∧
        (match r with
         | some (.finalFfi e) => outcome = HolOutcome.ffiOutcome e
         | some (.result _) => outcome = HolOutcome.success
         | _ => False) ∧
        res = HolBehaviour.terminate outcome t.ffi.ioEvents) with
    | some res => res
    | none => .diverge (HolLList.buildLprefixLub (fun l => ∃ k,
        l = HolLList.fromList (evaluate prog { s with clock := k }).2.ffi.ioEvents))

end LoopSemStateFiniteExact
end Flapjack
