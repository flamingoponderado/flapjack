import Flapjack.Pancake.CrepToLoop.ContextExact
import Flapjack.Pancake.LoopLive
import Flapjack.Pancake.LoopLive.Fixedpoint

/-!
Flapjack-only structural facts for the runtime-only `HolLoopProg.locValue`
constructor.  This module deliberately carries no HOL tags: the predicate is
infrastructure for a future source/runtime correspondence argument, not an
HOL theorem port.
-/

namespace Flapjack

/-- A nested `HolLoopProg` contains no `locValue` constructor, including in
either program stored inside an optional call handler. -/
def holLoopProgLocValueFree {width : Nat} [NeZero width] :
    HolLoopProg width → Prop
  | .locValue _ _ => False
  | .seq first second => holLoopProgLocValueFree first ∧ holLoopProgLocValueFree second
  | .ite _ _ _ thenBranch elseBranch _ =>
      holLoopProgLocValueFree thenBranch ∧ holLoopProgLocValueFree elseBranch
  | .loop _ body _ => holLoopProgLocValueFree body
  | .mark body => holLoopProgLocValueFree body
  | .call _ _ _ none => True
  | .call _ _ _ (some (_, handler, normal, _)) =>
      holLoopProgLocValueFree handler ∧ holLoopProgLocValueFree normal
  | _ => True
termination_by program => sizeOf program
decreasing_by
  simp_wf
  all_goals first
    | decreasing_trivial
    | (simp_all only [HolLoopProg.call.sizeOf_spec]; omega)

/-- The exact loop-call optimizer does not introduce `locValue` into a
program that was recursively free of it.  The live-set parameter is
generalized so the `Seq` case can use the second induction hypothesis at the
live set returned by compiling the first child. -/
theorem loopCallCompHOL_preserves_locValueFree {width : Nat} [NeZero width]
    (program : HolLoopProg width) (live : Spt Nat)
    (hfree : holLoopProgLocValueFree program) :
    holLoopProgLocValueFree (loopCallCompHOL live program).1 := by
  let mProg : HolLoopProg width → Prop := fun p =>
    ∀ live, holLoopProgLocValueFree p →
      holLoopProgLocValueFree (loopCallCompHOL live p).1
  let mPair : HolLoopProg width × NumSet → Prop := fun _ => True
  let mTriple : HolLoopProg width × HolLoopProg width × NumSet → Prop := fun _ => True
  let mQuad : Nat × HolLoopProg width × HolLoopProg width × NumSet → Prop := fun _ => True
  let mHandler : Option (Nat × HolLoopProg width × HolLoopProg width × NumSet) → Prop :=
    fun _ => True
  have hgeneral : mProg program := by
    refine HolLoopProg.rec
        (motive_1 := mProg) (motive_2 := mHandler) (motive_3 := mQuad)
        (motive_4 := mTriple) (motive_5 := mPair)
        ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
        ?_ ?_ ?_ ?_ ?_ ?_ ?_ program
    case refine_2 =>
      intro name value live
      intro hfree
      cases value with
      | var m => simp [loopCallCompHOL.eq_5, holLoopProgLocValueFree]
      | const value => simp [loopCallCompHOL.eq_6, holLoopProgLocValueFree]
      | lookup address => simp [loopCallCompHOL.eq_6, holLoopProgLocValueFree]
      | load address => simp [loopCallCompHOL.eq_6, holLoopProgLocValueFree]
      | op operator args => simp [loopCallCompHOL.eq_6, holLoopProgLocValueFree]
      | shift operator left right => simp [loopCallCompHOL.eq_6, holLoopProgLocValueFree]
      | baseAddr => simp [loopCallCompHOL.eq_6, holLoopProgLocValueFree]
      | topAddr => simp [loopCallCompHOL.eq_6, holLoopProgLocValueFree]
    case refine_4 =>
      intro operation live
      intro hfree
      cases operation with
      | longMul => simp [loopCallCompHOL.eq_19, holLoopProgLocValueFree]
      | longDiv => simp [loopCallCompHOL.eq_20, holLoopProgLocValueFree]
      | div => simp [loopCallCompHOL.eq_21, holLoopProgLocValueFree]
    case refine_23 =>
      intro returns target arguments handler ih live hfree
      cases handler with
      | none =>
          cases target with
          | some target => simp [loopCallCompHOL.eq_2, holLoopProgLocValueFree]
          | none =>
              cases hlast : arguments.getLast? with
              | none =>
                  simp [loopCallCompHOL.eq_3, hlast, holLoopProgLocValueFree]
              | some last =>
                  cases hlookup : sptLookup last live <;>
                    simp [loopCallCompHOL.eq_3, hlast, hlookup,
                      holLoopProgLocValueFree]
      | some entry =>
          rcases entry with ⟨exception, handler, normal, liveOut⟩
          simp only [holLoopProgLocValueFree] at hfree
          cases target with
          | some target =>
              simpa [loopCallCompHOL.eq_2, holLoopProgLocValueFree] using hfree
          | none =>
              cases hlast : arguments.getLast? with
              | none =>
                  simp [loopCallCompHOL.eq_3, hlast, holLoopProgLocValueFree]
              | some last =>
                  cases hlookup : sptLookup last live <;>
                    simp [loopCallCompHOL.eq_3, hlast, hlookup,
                      holLoopProgLocValueFree, hfree]
    all_goals simp_all [mProg, mPair, mTriple, mQuad, mHandler,
      holLoopProgLocValueFree, loopCallCompHOL.eq_1, loopCallCompHOL.eq_2,
      loopCallCompHOL.eq_3, loopCallCompHOL.eq_4, loopCallCompHOL.eq_5,
      loopCallCompHOL.eq_6, loopCallCompHOL.eq_7, loopCallCompHOL.eq_8,
      loopCallCompHOL.eq_9, loopCallCompHOL.eq_10, loopCallCompHOL.eq_11,
      loopCallCompHOL.eq_12, loopCallCompHOL.eq_13, loopCallCompHOL.eq_14,
      loopCallCompHOL.eq_15, loopCallCompHOL.eq_16, loopCallCompHOL.eq_17,
      loopCallCompHOL.eq_18, loopCallCompHOL.eq_19, loopCallCompHOL.eq_20,
      loopCallCompHOL.eq_21, loopCallCompHOL.eq_22]
  exact hgeneral live hfree

/-- `shrinkHOL` cannot introduce the runtime-only `locValue` constructor.
This is Flapjack-specific infrastructure: it supplies the optimizer half of
the parser-routed compile-path invariant and is not an additional HOL result.
The loop branch uses the reviewed `fixedpoint_thm` equation to reduce a
successful fixedpoint result to one structural `shrinkHOL` call on its body. -/
theorem shrinkHOL_preserves_locValueFree {width : Nat} [NeZero width]
    (program : HolLoopProg width) (live : NumSet)
    (hfree : holLoopProgLocValueFree program) :
    holLoopProgLocValueFree (shrinkHOL [] program live).1 := by
  let mProg : HolLoopProg width → Prop := fun p =>
    ∀ lt live, holLoopProgLocValueFree p →
      holLoopProgLocValueFree (shrinkHOL lt p live).1
  let mPair : HolLoopProg width × NumSet → Prop := fun p => mProg p.1
  let mTriple : HolLoopProg width × HolLoopProg width × NumSet → Prop :=
    fun p => mProg p.1 ∧ mProg p.2.1
  let mQuad : Nat × HolLoopProg width × HolLoopProg width × NumSet → Prop :=
    fun p => mTriple p.2
  let mHandler : Option (Nat × HolLoopProg width × HolLoopProg width × NumSet) → Prop
    | none => True
    | some entry => mQuad entry
  have hgeneral : mProg program := by
    refine HolLoopProg.rec
        (motive_1 := mProg) (motive_2 := mHandler) (motive_3 := mQuad)
        (motive_4 := mTriple) (motive_5 := mPair)
        ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
        ?_ ?_ ?_ ?_ ?_ ?_ ?_ program
    case refine_2 =>
      intro name value lt live hfree
      simp only [shrinkHOL.eq_15]
      cases hlookup : sptLookup name live <;>
        simp [holLoopProgLocValueFree]
    case refine_12 =>
      intro operator condition right thenBranch elseBranch branchLive
        ihThen ihElse lt live hfree
      simp only [holLoopProgLocValueFree] at hfree
      rcases hfree with ⟨hthen, helse⟩
      cases right with
      | reg r =>
          simp only [shrinkHOL.eq_3]
          rcases hsThen : shrinkHOL lt thenBranch (sptInter live branchLive) with
            ⟨then', liveThen⟩
          rcases hsElse : shrinkHOL lt elseBranch (sptInter live branchLive) with
            ⟨else', liveElse⟩
          have hthenFree := ihThen lt (sptInter live branchLive) hthen
          have helseFree := ihElse lt (sptInter live branchLive) helse
          rw [hsThen] at hthenFree
          rw [hsElse] at helseFree
          simp only [holLoopProgLocValueFree]
          exact ⟨hthenFree, helseFree⟩
      | imm value =>
          simp only [shrinkHOL.eq_4]
          rcases hsThen : shrinkHOL lt thenBranch (sptInter live branchLive) with
            ⟨then', liveThen⟩
          rcases hsElse : shrinkHOL lt elseBranch (sptInter live branchLive) with
            ⟨else', liveElse⟩
          have hthenFree := ihThen lt (sptInter live branchLive) hthen
          have helseFree := ihElse lt (sptInter live branchLive) helse
          rw [hsThen] at hthenFree
          rw [hsElse] at helseFree
          simp only [holLoopProgLocValueFree]
          exact ⟨hthenFree, helseFree⟩
    case refine_13 =>
      intro liveIn body liveOut ihBody lt live hfree
      simp only [shrinkHOL.eq_2]
      have hfreeBody : holLoopProgLocValueFree body := by
        simpa [holLoopProgLocValueFree] using hfree
      cases hfp : fixedpointHOL lt liveIn .ln
          (sptUnion liveIn (sptInter liveOut live)) body with
      | none =>
          have hbody := ihBody ((liveIn, sptInter liveOut live) :: lt)
            (sptUnion liveIn (sptInter liveOut live)) hfreeBody
          simp only [holLoopProgLocValueFree]
          exact hbody
      | some result =>
          rcases result with ⟨body', liveBody⟩
          have hfixed := fixedpoint_thm lt liveIn .ln
            (sptUnion liveIn (sptInter liveOut live)) body liveBody body' hfp
          have hfreeBody' : holLoopProgLocValueFree body' := by
            have h := ihBody
              ((sptInter liveIn liveBody, sptUnion liveIn (sptInter liveOut live)) :: lt)
              (sptUnion liveIn (sptInter liveOut live)) hfreeBody
            rw [hfixed] at h
            exact h
          simp only [holLoopProgLocValueFree]
          exact hfreeBody'
    case refine_23 =>
      intro returns target arguments handler hHandler lt live hfree
      cases returns with
      | none => simp only [shrinkHOL.eq_19, holLoopProgLocValueFree]
      | some returnData =>
          rcases returnData with ⟨returnNames, returnLive⟩
          cases handler with
          | none => simp only [shrinkHOL.eq_20, holLoopProgLocValueFree]
          | some entry =>
              rcases entry with ⟨exception, handler, normal, liveOut⟩
              rw [shrinkHOL.eq_21]
              rcases hHandler with ⟨ihHandler, ihNormal⟩
              simp only [holLoopProgLocValueFree] at hfree
              rcases hfree with ⟨hHandlerFree, hNormalFree⟩
              rcases hsNormal : shrinkHOL lt normal live with ⟨normal', liveNormal⟩
              rcases hsHandler : shrinkHOL lt handler live with ⟨handler', liveHandler⟩
              have hNormal' := ihNormal lt live hNormalFree
              have hHandler' := ihHandler lt live hHandlerFree
              rw [hsNormal] at hNormal'
              rw [hsHandler] at hHandler'
              simp only [holLoopProgLocValueFree]
              exact ⟨hHandler', hNormal'⟩
    all_goals
      simp_all [mProg, mPair, mTriple, mQuad, mHandler,
        holLoopProgLocValueFree, shrinkHOL, shrinkHOL.eq_1, shrinkHOL.eq_2,
        shrinkHOL.eq_3, shrinkHOL.eq_4, shrinkHOL.eq_5, shrinkHOL.eq_6,
        shrinkHOL.eq_7, shrinkHOL.eq_8, shrinkHOL.eq_9, shrinkHOL.eq_10,
        shrinkHOL.eq_11, shrinkHOL.eq_12, shrinkHOL.eq_13, shrinkHOL.eq_14,
        shrinkHOL.eq_15, shrinkHOL.eq_16, shrinkHOL.eq_17, shrinkHOL.eq_18,
        shrinkHOL.eq_19, shrinkHOL.eq_20, shrinkHOL.eq_21, shrinkHOL.eq_22,
        shrinkHOL.eq_23, shrinkHOL.eq_24, shrinkHOL.eq_25, shrinkHOL.eq_26,
        shrinkHOL.eq_27]
  exact hgeneral [] live hfree

/-- `markAllHOL` preserves the Flapjack-only recursive absence of `locValue`,
including in both programs stored by a call handler. This is infrastructure
for the parser-routed compile-path invariant, not an additional HOL result. -/
theorem markAllHOL_preserves_locValueFree {width : Nat} [NeZero width]
    (program : HolLoopProg width)
    (hfree : holLoopProgLocValueFree program) :
    holLoopProgLocValueFree (markAllHOL program).1 := by
  let mProg : HolLoopProg width → Prop := fun p =>
    holLoopProgLocValueFree p →
      holLoopProgLocValueFree (markAllHOL p).1
  let mPair : HolLoopProg width × NumSet → Prop := fun p => mProg p.1
  let mTriple : HolLoopProg width × HolLoopProg width × NumSet → Prop :=
    fun p => mProg p.1 ∧ mProg p.2.1
  let mQuad : Nat × HolLoopProg width × HolLoopProg width × NumSet → Prop :=
    fun p => mTriple p.2
  let mHandler : Option (Nat × HolLoopProg width × HolLoopProg width × NumSet) → Prop
    | none => True
    | some entry => mQuad entry
  have hgeneral : mProg program := by
    refine HolLoopProg.rec
        (motive_1 := mProg) (motive_2 := mHandler) (motive_3 := mQuad)
        (motive_4 := mTriple) (motive_5 := mPair)
        ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
        ?_ ?_ ?_ ?_ ?_ ?_ ?_ program
    case refine_11 =>
      intro first second ihFirst ihSecond hfree
      simp only [holLoopProgLocValueFree] at hfree
      rcases hfree with ⟨hFirst, hSecond⟩
      have hFirst' := ihFirst hFirst
      have hSecond' := ihSecond hSecond
      simp only [markAllHOL]
      cases hmarkFirst : markAllHOL first with
      | mk first' firstMarked =>
              cases hmarkSecond : markAllHOL second with
              | mk second' secondMarked =>
              rw [hmarkFirst] at hFirst'
              rw [hmarkSecond] at hSecond'
              cases firstMarked <;> cases secondMarked <;>
                simp [holLoopProgLocValueFree, hFirst', hSecond']
    case refine_12 =>
      intro operator condition right thenBranch elseBranch branchLive ihThen ihElse hfree
      simp only [holLoopProgLocValueFree] at hfree
      rcases hfree with ⟨hthen, helse⟩
      have hthen' := ihThen hthen
      have helse' := ihElse helse
      simp only [markAllHOL]
      cases hmarkThen : markAllHOL thenBranch with
      | mk then' thenMarked =>
          cases hmarkElse : markAllHOL elseBranch with
          | mk else' elseMarked =>
              rw [hmarkThen] at hthen'
              rw [hmarkElse] at helse'
              cases thenMarked <;> cases elseMarked <;>
                simp [holLoopProgLocValueFree, hthen', helse']
    case refine_23 =>
      intro returns target arguments handler hHandler hfree
      cases handler with
      | none => simp only [markAllHOL, holLoopProgLocValueFree]
      | some entry =>
          rcases entry with ⟨exception, handler, normal, liveOut⟩
          rcases hHandler with ⟨ihHandler, ihNormal⟩
          simp only [holLoopProgLocValueFree] at hfree
          rcases hfree with ⟨hHandlerFree, hNormalFree⟩
          have hHandler' := ihHandler hHandlerFree
          have hNormal' := ihNormal hNormalFree
          simp only [markAllHOL]
          cases hmarkHandler : markAllHOL handler with
          | mk handler' handlerMarked =>
              cases hmarkNormal : markAllHOL normal with
              | mk normal' normalMarked =>
                  rw [hmarkHandler] at hHandler'
                  rw [hmarkNormal] at hNormal'
                  cases handlerMarked <;> cases normalMarked <;>
                    simp [holLoopProgLocValueFree, hHandler', hNormal']
    all_goals
      intros
      simp_all [mProg, mPair, mTriple, mQuad, mHandler,
        holLoopProgLocValueFree, markAllHOL]
  exact hgeneral hfree

end Flapjack
