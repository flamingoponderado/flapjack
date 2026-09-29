import Flapjack.Pancake.CrepToLoop.ContextExact
import Flapjack.Pancake.LoopLive

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
    (program : HolLoopProg width)
    (hfree : holLoopProgLocValueFree program) :
    holLoopProgLocValueFree (loopCallCompHOL (.ln : Spt Nat) program).1 := by
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
  exact hgeneral .ln hfree

end Flapjack
