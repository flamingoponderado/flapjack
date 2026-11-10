module

public import Flapjack.Compiler.Backend.WordToStack.ProductionCutsetMaximum

@[expose] public section

/-! Same-input kernel replay of twelve original cutset maximum observations.
Includes duplicate/root keys, differing list orders, overlap and unbounded
names above 2^80. The native computation is justified by the full unconditional
codec theorem; no caller-supplied maximum equality is used. -/
namespace Flapjack.Test.WordToStackCutsetMaximumParity
open Flapjack
private def inputs : List (List Nat × List Nat) :=
  [([], []),
   ([0], []),
   ([7], []),
   ([], [7]),
   ([5,5,1], [2,2]),
   ([1,9,3], [8,2]),
   ([3,9,1], [2,8]),
   ([0,17,17,4], [18,18,0]),
   ([1208925819614629174706176,3], [1208925819614629174706177]),
   ([7,2,7], [7,1]),
   ([0,1,2,3,4,5,6,7,8,9], []),
   ([10000,2,10000], [9999])]
private def expected : List Nat := [0,0,7,7,5,9,9,18,1208925819614629174706177,7,9,10000]

end Flapjack.Test.WordToStackCutsetMaximumParity
