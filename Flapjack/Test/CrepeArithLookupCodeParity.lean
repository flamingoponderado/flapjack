import Flapjack.Test.CrepArithExactParity
import Flapjack.Pancake.Proofs.CrepArith
import Flapjack.Pancake.Semantics.CrepSem.LookupCode
import Flapjack.Pancake.Semantics.CrepSem.HOLState

/-! Direct original-HOL boundary for the local `lookup_code` theorem used by
`crep_arithProofScript.sml:simp_prog_correct`. The HOL fixture simplifies an
8-bit multiplication in the stored function body before looking it up. The
tests retain the exact lookup observation and production failure cases. -/

namespace Flapjack.Test.CrepeArithLookupCodeParity

open Flapjack

private abbrev Word8 := RiscV.Word 8

private def code : FunName → Option (List Nat × CrepProg Word8) :=
  FUPDATE FEMPTY ("f", ([1], .assign 2 (.crepOp .mul [.const 2, .const 4])))

private def wrongArityCode : FunName → Option (List Nat × CrepProg Word8) :=
  FUPDATE FEMPTY ("f", ([1, 2], .skip))

private def duplicateParameterCode : FunName → Option (List Nat × CrepProg Word8) :=
  FUPDATE FEMPTY ("f", ([1, 1], .skip))

-- Key-sensitive FMAP_MAP2 regression on the canonical finite-map carrier.
private def selected := Flapjack.Basis.Pure.MlString.ofString "selected"
private def untouched := Flapjack.Basis.Pure.MlString.ofString "untouched"
private def keyedCode : HolFiniteMapExact Flapjack.Basis.Pure.MlString.MlString (List Nat × CrepProgHOL 8) :=
  (HolFiniteMapExact.empty.update (selected, ([1, 2], .skip))).update
    (untouched, ([1, 2], .skip))
private def keyedUpdate (entry : Flapjack.Basis.Pure.MlString.MlString × (List Nat × CrepProgHOL 8)) : List Nat × CrepProgHOL 8 :=
  if entry.1 = selected then (entry.2.1.reverse, entry.2.2) else entry.2

example : (keyedCode.map2 keyedUpdate).lookup selected = some ([2, 1], .skip) := by
  simp +decide [keyedCode, keyedUpdate, selected, untouched, HolFiniteMapExact.update,
    HolFiniteMapExact.map2, FUPDATE, HolFiniteMapExact.empty]
example : (keyedCode.map2 keyedUpdate).lookup untouched = some ([1, 2], .skip) := by
  simp +decide [keyedCode, keyedUpdate, selected, untouched, HolFiniteMapExact.update,
    HolFiniteMapExact.map2, FUPDATE, HolFiniteMapExact.empty]

-- HOL `OPTION_MAP (simp_prog ## I) (lookup_code ...)`, including the
-- complete local-map result of the successful lookup.
private def exactCode : CrepCodeMapExact 8 :=
  FUPDATE FEMPTY (Flapjack.Basis.Pure.MlString.ofString "f",
    ([1], .assign 2 (.crepOp .mul [.const 2, .const 4])))

example : (lookupCodeHOL exactCode (Flapjack.Basis.Pure.MlString.ofString "f")
      [.word 9] 1).map (fun result => (crepSimpProgHOL result.1, result.2)) =
    some (.assign 2 (.const 8), FUPDATE FEMPTY (1, .word 9)) := by
  simp [lookupCodeHOL, exactCode, FLOOKUP, FUPDATE, FUPDATE_LIST,
    crepSimpProgHOL, Flapjack.Test.CrepArithExactParity.simpMul,
    crepSimpExpHOL, crepDestConstHOL]

-- These three additional source-script rows are not in the older captured
-- .out file; their arguments are copied from the HOL probe itself.
example : lookupCodeHOL
    (FUPDATE FEMPTY (Flapjack.Basis.Pure.MlString.ofString "f",
      ([1, 2], .skip)) : CrepCodeMapExact 8)
    (Flapjack.Basis.Pure.MlString.ofString "f") [.word 9] 2 = none := by
  simp [lookupCodeHOL, FLOOKUP, FUPDATE]
example : lookupCodeHOL
    (FUPDATE FEMPTY (Flapjack.Basis.Pure.MlString.ofString "f",
      ([1, 1], .skip)) : CrepCodeMapExact 8)
    (Flapjack.Basis.Pure.MlString.ofString "f") [.word 9, .word 10] 2 = none := by
  simp [lookupCodeHOL, FLOOKUP, FUPDATE]
example : lookupCodeHOL exactCode (Flapjack.Basis.Pure.MlString.ofString "missing") [] 0 = none := by
  decide

#guard (lookupCrepRuntimeCode "f" [BitVec.ofNat 8 9] wrongArityCode).isNone
#guard (lookupCrepRuntimeCode "f"
  [BitVec.ofNat 8 9, BitVec.ofNat 8 10] duplicateParameterCode).isNone
#guard (lookupCrepRuntimeCode "missing" [] code).isNone

#guard (lookupCrepHolCode code "missing" [] 0).isNone

end Flapjack.Test.CrepeArithLookupCodeParity
