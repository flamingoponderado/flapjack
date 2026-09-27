import Flapjack.Pancake.CrepInline.Pass

/-! Direct HOL-EVAL guards for the structural clauses of `inline_prog_def`.
The exact-carrier helper is only a partial assembly utility: these fixtures use
the empty inline map, so the source `inline_prog` leaves the structural
examples unchanged. -/

namespace Flapjack.Test.CrepInlineStructuralHOLParity

open Flapjack

private def exactSkip : CrepProgHOL 8 := .skip

private def exactDec : CrepProgHOL 8 := .dec 1 (.const 1) exactSkip

private def exactSeq : CrepProgHOL 8 := .seq exactDec exactSkip

private def exactIf : CrepProgHOL 8 := .ite (.const 1) exactDec exactSkip

private def exactWhile : CrepProgHOL 8 := .while (.const 0) exactSeq

private def recurseByIdentity : CrepInlineFmapHOL 8 →
    CrepProgHOL 8 → CrepProgHOL 8 := fun _ program => program

def structuralClausesGuard : Bool :=
  let empty := CrepInlineFmapHOL.empty
  let decOk := match inlineProgStructuralHOL recurseByIdentity empty exactDec with
    | .dec 1 (.const 1) .skip => true
    | _ => false
  let seqOk := match inlineProgStructuralHOL recurseByIdentity empty exactSeq with
    | .seq (.dec 1 (.const 1) .skip) .skip => true
    | _ => false
  let ifOk := match inlineProgStructuralHOL recurseByIdentity empty exactIf with
    | .ite (.const 1) (.dec 1 (.const 1) .skip) .skip => true
    | _ => false
  let whileOk := match inlineProgStructuralHOL recurseByIdentity empty exactWhile with
    | .while (.const 0) (.seq (.dec 1 (.const 1) .skip) .skip) => true
    | _ => false
  decOk && seqOk && ifOk && whileOk

#guard structuralClausesGuard
#eval structuralClausesGuard

def runChecks : IO Bool := do
  if structuralClausesGuard then
    IO.println "PASS exact Crep inline_prog structural clauses match direct HOL rows"
  else
    IO.println "FAIL exact Crep inline_prog structural clauses"
  pure structuralClausesGuard

end Flapjack.Test.CrepInlineStructuralHOLParity
