import Flapjack.Pancake.Semantics.PanSem.StateExactFiniteMap
import Flapjack.Misc.LprefixLub
import Flapjack.Pancake.Semantics.PanSem.DeclContextExact

/-!
# HOL `panSem` observational semantics

Counterpart of `cakeml/pancake/semantics/panSemScript.sml:785-809`
(`semantics_def`, bead `flapjack-pxn.18.4.3.77.17.1`) and `:861-869`
(`semantics_decls_def`, bead `flapjack-pxn.18.4.3.77.17.2`), over the exact
finite-map evaluator `evaluateHOLFiniteState`, whose `evaluate_def` equations
are tagged.  It uses the same `holOptionSome` and `HolLList` renderings as the
tagged loopSem, crepSem and wordSem `semantics_def` ports.
-/

namespace Flapjack

open Flapjack.Pancake.PanLang (MlS ProgHOL DeclHOL)

namespace PanSemStateFiniteExact

namespace PanSemanticsFiniteSupport

/-- Same-module canonical finite-support witness for the `locals`/`globals`/
    `code`/`eshapes` fields named by the tagged definition of this module. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} {σ : Type} [NeZero width] :
    (∀ (state : PanSemStateExact width σ) (h : state.FiniteSupport),
        (ofExact state h).toExact = state) ∧
    (∀ state : PanSemStateFiniteExact width σ,
        ofExact state.toExact state.toExact_finiteSupport = state) :=
  Flapjack.PanSemStateFiniteExact.holFmapAsFiniteSupportWitness

end PanSemanticsFiniteSupport

/-- Exact HOL `panSem$semantics_def` (`panSemScript.sml:785-809`):

    ```
    semantics s start =
     let prog = Call NONE start [] in
      if ∃k. case FST (evaluate (prog,s with clock := k)) of
              | SOME TimeOut => F
              | SOME (FinalFFI _) => F
              | SOME (Return _) => F
              | _ => T
      then Fail
      else
       case some res.
        ∃k t r outcome.
          evaluate (prog, s with clock := k) = (r,t) ∧
          (case r of
           | (SOME (FinalFFI e)) => outcome = FFI_outcome e
           | (SOME (Return _))   => outcome = Success
           | _ => F) ∧
          res = Terminate outcome t.ffi.io_events
        of
      | SOME res => res
      | NONE =>
        Diverge
           (build_lprefix_lub
             (IMAGE (λk. fromList
                (SND (evaluate (prog,s with clock := k))).ffi.io_events) UNIV))
    ```

    `evaluate` is `evaluateHOLFiniteState`.  HOL's `some` is `holOptionSome`,
    and `build_lprefix_lub`/`fromList` are the `HolLList` renderings of HOL's
    `lprefix_lub`/`llist` libraries.  The set `IMAGE f UNIV` is the predicate
    `fun l => ∃ k, l = f k`.  The entry name `start` is an `mlstring`, so it
    is `MlS`.  The definition is noncomputable, as HOL's classical one is. -/
@[hol "cakeml/pancake/semantics/panSemScript.sml" "semantics_def"
  (fmap_as_finite_support := [locals, globals, code, eshapes])
  (words_as_type_indexed_bitvec)]
noncomputable def semantics {width : Nat} {σ : Type} [NeZero width]
    (s : PanSemStateFiniteExact width σ) (start : MlS) : HolBehaviour :=
  let prog : ProgHOL width := .call none start []
  open Classical in
  if ∃ k, (match (evaluateHOLFiniteState { s with clock := k } prog).1 with
      | some .timeOut => False
      | some (.finalFfi _) => False
      | some (.returned _) => False
      | _ => True)
  then .fail
  else
    match holOptionSome (fun res => ∃ k t r outcome,
        evaluateHOLFiniteState { s with clock := k } prog = (r, t) ∧
        (match r with
         | some (.finalFfi e) => outcome = HolOutcome.ffiOutcome e
         | some (.returned _) => outcome = HolOutcome.success
         | _ => False) ∧
        res = HolBehaviour.terminate outcome t.ffi.ioEvents) with
    | some res => res
    | none => .diverge (HolLList.buildLprefixLub (fun l => ∃ k,
        l = HolLList.fromList (evaluateHOLFiniteState { s with clock := k } prog).2.ffi.ioEvents))

/-- Exact HOL `panSem$semantics_decls_def` (`panSemScript.sml:861-869`):

    ```
    semantics_decls s start decls =
      case decs_stcnames [] decls of
      | NONE => Fail
      | SOME st_ctxt =>
        case evaluate_decls (s with structs := st_ctxt) decls of
        | NONE => Fail
        | SOME s' => semantics s' start
    ```

    `decs_stcnames` is the tagged `decsStcnamesHOLExact` and `evaluate_decls`
    the tagged `evaluateDeclsHOLFinite`.  The latter takes Lean's operational
    `DecidablePred` evidence for the memory domain.  That evidence is chosen
    classically here, which adds no premise, since `DecidablePred` instances
    are subsingletons. -/
@[hol "cakeml/pancake/semantics/panSemScript.sml" "semantics_decls_def"
  (fmap_as_finite_support := [locals, globals, code, eshapes])
  (words_as_type_indexed_bitvec)]
noncomputable def semanticsDecls {width : Nat} {σ : Type} [NeZero width]
    (s : PanSemStateFiniteExact width σ) (start : MlS) (decls : List (DeclHOL width)) :
    HolBehaviour :=
  match decsStcnamesHOLExact [] decls with
  | none => .fail
  | some stCtxt =>
    open Classical in
    match evaluateDeclsHOLFinite { s with structs := stCtxt } decls with
    | none => .fail
    | some s' => semantics s' start

end PanSemStateFiniteExact

end Flapjack
