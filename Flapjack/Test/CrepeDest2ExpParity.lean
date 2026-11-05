import Flapjack.Pancake.Proofs.CrepArith

namespace Flapjack.Test.CrepeDest2ExpParity

open Flapjack.RiscV

/-! Direct parity for `crep_arith$dest_2exp_def`
    (`crep_arithScript.sml:15`). -/
def word (value : Nat) : RiscV.Word 8 := BitVec.ofNat 8 value

@[instance_reducible] def finiteWordDimension8 : HolFiniteDimension (Fin 8) :=
  inferInstance

def parityGuard : Bool :=
  crepDest2Exp 0 (word 0) == none &&
  crepDest2Exp 3 (word 1) == some 3 &&
  crepDest2Exp 0 (word 1) == some 0 &&
  crepDest2Exp 0 (word 2) == some 1 &&
  crepDest2Exp 4 (word 4) == some 6 &&
  crepDest2Exp 0 (word 4) == some 2 &&
  crepDest2Exp 0 (word 8) == some 3 &&
  crepDest2Exp 0 (word 3) == none &&
  crepDest2Exp 0 (word 6) == none &&
  crepDest2Exp 0 (word 255) == none

#eval parityGuard
#guard parityGuard

/-! The bounded production helper agrees with the reviewed HOL definition
    on every direct HOL-EVAL row above, including rejected odd values and the
    all-ones boundary. These rows also exercise the runtime path. -/
def reviewedDefinitionParity : Bool :=
  (crepDest2Exp 0 (word 0) == crepDest2ExpHOL 0 (word 0)) &&
  (crepDest2Exp 3 (word 1) == crepDest2ExpHOL 3 (word 1)) &&
  (crepDest2Exp 0 (word 1) == crepDest2ExpHOL 0 (word 1)) &&
  (crepDest2Exp 0 (word 2) == crepDest2ExpHOL 0 (word 2)) &&
  (crepDest2Exp 4 (word 4) == crepDest2ExpHOL 4 (word 4)) &&
  (crepDest2Exp 0 (word 4) == crepDest2ExpHOL 0 (word 4)) &&
  (crepDest2Exp 0 (word 8) == crepDest2ExpHOL 0 (word 8)) &&
  (crepDest2Exp 0 (word 3) == crepDest2ExpHOL 0 (word 3)) &&
  (crepDest2Exp 0 (word 6) == crepDest2ExpHOL 0 (word 6)) &&
  (crepDest2Exp 0 (word 255) == crepDest2ExpHOL 0 (word 255))

#eval reviewedDefinitionParity
#guard reviewedDefinitionParity

/-! These are the three successful input/exponent rows also recorded by the
    direct HOL destination-recognizer probe above. They exercise the wrapped
    `BitVec.ofNat` image of HOL `word_log2` on the same width-8 inputs. -/
def boundParity : Bool :=
  (3 : Nat) ≤ 3 + (BitVec.ofNat 8 (Nat.log2 (word 1).toNat)).toNat &&
  (6 : Nat) ≤ 4 + (BitVec.ofNat 8 (Nat.log2 (word 4).toNat)).toNat &&
  (3 : Nat) ≤ 0 + (BitVec.ofNat 8 (Nat.log2 (word 8).toNat)).toNat

#eval boundParity
#guard boundParity

end Flapjack.Test.CrepeDest2ExpParity
