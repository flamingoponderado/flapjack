import Flapjack.Pancake.LoopLive

/-! Direct parity for `loop_live$arith_vars_def` at
`cakeml/pancake/loop_liveScript.sml:50`. -/
namespace Flapjack.Test.LoopArithVarsParity

def parityGuard : Bool :=
  arithVars (.longMul 1 2 3 4) [1, 2, 6] == [3, 4, 6] &&
  arithVars (.div 1 2 3) [1, 5] == [2, 3, 5] &&
  arithVars (.longDiv 1 2 3 4 5) [1, 2, 8] == [3, 4, 5, 8]

#eval parityGuard
#guard parityGuard

/-! Direct parity for the exact `arithVarsHOL` over the faithful `NumSet`
carrier, replaying the three rows of `scripts/hol-probes/arith_vars_probe.out`
(`long_mul=⦕ 3; 4; 6 ⦖`, `div=⦕ 2; 3; 5 ⦖`, `long_div=⦕ 3; 4; 5; 8 ⦖`). -/
def numSetOf (keys : List Nat) : NumSet := sptListInsert keys .ln

def numSetHas (tree : NumSet) (keys : List Nat) : Bool :=
  keys.all (fun key => (sptLookup key tree).isSome) && sptSize tree == keys.length

def exactArithVarsGuard : Bool :=
  numSetHas (arithVarsHOL (.longMul 1 2 3 4) (numSetOf [1, 2, 6])) [3, 4, 6] &&
  numSetHas (arithVarsHOL (.div 1 2 3) (numSetOf [1, 5])) [2, 3, 5] &&
  numSetHas (arithVarsHOL (.longDiv 1 2 3 4 5) (numSetOf [1, 2, 8])) [3, 4, 5, 8]

#guard exactArithVarsGuard

end Flapjack.Test.LoopArithVarsParity
