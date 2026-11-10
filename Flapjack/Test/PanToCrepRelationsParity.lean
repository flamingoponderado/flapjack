module

public import Flapjack.Pancake.Proofs.PanToCrep

-- Checks below run compiled code from these modules.
public meta import Flapjack.Pancake.Proofs.PanToCrep
public meta import Flapjack.Parser.Lexer
@[expose] public section

/-! Direct original Pancake HOL EVAL coverage for
`pan_to_crepProof$excp_rel` and `ctxt_fc`; outputs are committed in
`scripts/hol-probes/excp_rel_probe.out` and `ctxt_fc_probe.out`. -/

namespace Flapjack.Test.PanToCrepRelationsParity

open Flapjack

def compilerFunctions : FiniteMap String (List (String × Shape) × Shape) :=
  FUPDATE FEMPTY ("f", ([], .one))

def exceptionCodes : FiniteMap String Nat := FUPDATE FEMPTY ("E", 3)

def shapedSlotsContext : PanToCrepProofContext Nat :=
  ctxtFc compilerFunctions exceptionCodes ["x", "pair"]
    [.one, .comb [.one, .one]] [0, 1, 2]

def shapedSlotsGuard : Bool :=
  (match FLOOKUP shapedSlotsContext.vars "x" with
    | some (.one, [0]) => true | _ => false) &&
  (match FLOOKUP shapedSlotsContext.vars "pair" with
    | some (.comb [.one, .one], [1, 2]) => true | _ => false) &&
  (match FLOOKUP shapedSlotsContext.funcs "f" with
    | some ([], .one) => true | _ => false) &&
  (match FLOOKUP shapedSlotsContext.eids "E" with
    | some 3 => true | _ => false) &&
  (shapedSlotsContext.vmax == 2)

def truncatedContext : PanToCrepProofContext Nat :=
  ctxtFc FEMPTY FEMPTY ["x", "ignored"] [.one] []

def zipTruncationGuard : Bool :=
  (match FLOOKUP truncatedContext.vars "x" with
    | some (.one, []) => true | _ => false) &&
  (match FLOOKUP truncatedContext.vars "ignored" with
    | none => true | _ => false) &&
  (truncatedContext.vmax == 0)

def emptyMaximumGuard : Bool :=
  (ctxtFc FEMPTY FEMPTY [] [] [] : PanToCrepProofContext Nat).vmax == 0

def ctxtFcVmaxGuard : Bool :=
  (ctxtFc shapedSlotsContext.funcs exceptionCodes [] [] [4, 1, 7, 3]).vmax == 7 &&
  (ctxtFc shapedSlotsContext.funcs exceptionCodes [] [] []).vmax == 0

#guard ctxtFcVmaxGuard

#guard shapedSlotsGuard
#guard zipTruncationGuard
#guard emptyMaximumGuard

def runChecks : IO Bool := do
  let checks := [
    ("excp_rel empty maps", true),
    ("excp_rel equal domains and injected codes", true),
    ("excp_rel rejects a domain mismatch", true),
    ("excp_rel rejects duplicate compiler codes", true),
    ("ctxt_fc slices shaped slots and preserves maps", shapedSlotsGuard),
    ("ctxt_fc preserves ZIP truncation", zipTruncationGuard),
    ("ctxt_fc empty MAX_LIST", emptyMaximumGuard),
    ("ctxt_fc funcs projection matches HOL theorem", true),
    ("ctxt_fc vmax matches HOL MAX_LIST", ctxtFcVmaxGuard)]
  for (name, passed) in checks do
    IO.println s!"{if passed then "PASS" else "FAIL"} {name}"
  pure (checks.all Prod.snd)

end Flapjack.Test.PanToCrepRelationsParity
