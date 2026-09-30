import Flapjack.Pancake.Proofs.CrepInline
import Flapjack.Pancake.Semantics.CrepSem.EvaluateIndWhile

namespace Flapjack.CrepInlineWhileInduction
open Flapjack.CrepInlineExact

/-- Flapjack assembly motive for the original inline correctness conclusion.
No standalone HOL original; this packages the already reviewed case statement. -/
def InlineGoal {width : Nat} [NeZero width] {σ : Type}
    (program : CrepProgHOL width) (s : CrepSemHOLState width σ) : Prop :=
  ∀ (r : Option (CrepResultHOLExact width)) (s' : CrepSemHOLState width σ)
    (inlFs : HolFiniteMapExact CrepInlineMapHOLName (List Nat × CrepProgHOL width))
    (t : CrepSemHOLState width σ)
    (inlBag : HolFiniteMapExact CrepInlineMapHOLName (List Nat × CrepProgHOL width)),
    evalCrepSemHOLProgExact s program = (r, s') → r ≠ some .error →
    HolFiniteMapExact.submap inlFs s.code → HolFiniteMapExact.submap inlBag inlFs →
    crepInlineStateRelCodeExact s t → crepInlineLocalsStrongRelExact s t →
    crepInlineCodeInlRelExact inlFs s t →
    ∃ t', evalCrepSemHOLProgExact t
        (CrepInlineCanonical.inlineProgHOLExact inlBag program) = (r, t') ∧
      crepInlineStateRelCodeExact s' t' ∧ crepInlineCodeInlRelExact inlFs s' t' ∧
      match r with
      | none => crepInlineLocalsStrongRelExact s' t'
      | some (.break _) => crepInlineLocalsStrongRelExact s' t'
      | some (.continue _) => crepInlineLocalsStrongRelExact s' t'
      | some .error => False
      | _ => True

/-- Flapjack-specific partial assembly, with no standalone HOL original.
The While case is discharged from genuine body and plain-state re-entry IHs,
not supplied as an extra correctness premise. Remaining constructor obligations
are explicit in `hother`; full inline_prog_correct remains a separate open port. -/
theorem assembleWhile {width : Nat} [NeZero width] {σ : Type}
    (hother : ∀ (program : CrepProgHOL width) (state : CrepSemHOLState width σ),
      (∀ condition body, program ≠ .while condition body) →
      (∀ (program' : CrepProgHOL width) (state' : CrepSemHOLState width σ),
        Prod.Lex Nat.lt Nat.lt (state'.clock, sizeOf program')
          (state.clock, sizeOf program) → InlineGoal program' state') →
      InlineGoal program state) :
    ∀ (program : CrepProgHOL width) (state : CrepSemHOLState width σ),
      InlineGoal program state := by
  apply evalCrepSemHOLProgExact_inductWhile (motive := InlineGoal) hother
  intro condition body state ihBody ihWhile
  intro result post inlFs target inlBag hrun herror hsub hbag hstate hlocals hcode
  obtain ⟨targetPost, targetRun, targetState, targetCode, targetLocals⟩ :=
    inlineProgCorrectWhileCaseExact condition body state inlFs inlBag target result post
    hrun herror hsub hbag hstate hlocals hcode
    (fun w hc hw hclk => ihBody w hc hw hclk)
    (fun w hc hw hclk loopState loopResult heval hres =>
      ihWhile w loopResult loopState hc hw hclk heval hres)
  refine ⟨targetPost, targetRun, targetState, targetCode, ?_⟩
  cases result with
  | none => exact targetLocals
  | some result => cases result <;> exact targetLocals

end Flapjack.CrepInlineWhileInduction
