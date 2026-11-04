import Flapjack.PanSimpOthers

namespace Flapjack.Test.PanSimpOthersParity

open Flapjack

/-! `compile_Others` parity: the program constructs that Cake's `compile`
    (`pan_simpProofScript.sml:667-1015`) leaves unchanged are also left
    unchanged by `panSimpProg`, and therefore evaluate identically. -/

def returnUnchangedParity : Bool :=
  match panSimpProg (.return (.var .local "x") : Prog Nat) with
  | .return (.var .local "x") => true
  | _ => false

def breakUnchangedParity : Bool :=
  match panSimpProg (.break : Prog Nat) with
  | .break => true
  | _ => false

#eval returnUnchangedParity
#eval breakUnchangedParity
#guard returnUnchangedParity
#guard breakUnchangedParity

end Flapjack.Test.PanSimpOthersParity
