import Flapjack.Pancake.LoopToWord.Proofs.LabelHandlers

namespace Flapjack.Test.LoopToWordLabelHandlersParity
open Flapjack Flapjack.LoopToWord

def leaf {width : Nat} [NeZero width] : HolLoopProg width :=
  .call (some ([], .ln)) (some 5) [1] none

def nested {width : Nat} [NeZero width] : HolLoopProg width :=
  .call (some ([2], .ln)) none [1]
    (some (3, leaf, .seq (.locValue 4 6) (.mark leaf), .ln))

def expectedLeaf {width : Nat} (owner next : Nat) : WordLangProgHOL (BitVec width) :=
  .call (some ([], (Spt.ls (), .ln), .skip, owner, next)) (some 5) [0] none

def expectedNested {width : Nat} (owner next : Nat) : WordLangProgHOL (BitVec width) :=
  .seq
    (.call (some ([0], (Spt.ls (), .ln),
      .seq (.locValue 0 6) (expectedLeaf owner (next + 2)), owner, next))
      none [0] (some (0, expectedLeaf owner (next + 1), owner, next + 3))) .tick

-- Complete compiler output, including both handler programs and all label pairs.
example {width : Nat} [NeZero width] (owner next : Nat) :
    LoopToWord.compHOL .ln (nested : HolLoopProg width) (owner,next) =
      (expectedNested owner next, (owner,next+4)) := by
  simp [nested, leaf, expectedNested, expectedLeaf, LoopToWord.compHOL, findVarHOL,
    sptLookup, mkNewCutsetHOL, toNumSetHOL, fromNumSetHOL, sptToAList, sptFoldi,
    Nat.add_assoc]

example {width : Nat} [NeZero width] :
    goodHandlersHOL 42 (LoopToWord.compHOL .ln (nested : HolLoopProg width) (42,9)).1 = true :=
  loopToWordGoodHandlersComp .ln nested (42,9)

example {width : Nat} [NeZero width] : (LoopToWord.compHOL .ln (nested : HolLoopProg width) (42,9)).2.1 = 42 :=
  loopToWordCompLInvariant .ln nested (42,9) _ _ rfl

example {width : Nat} [NeZero width] : 9 ≤ (LoopToWord.compHOL .ln (nested : HolLoopProg width) (42,9)).2.2 :=
  loopToWordCompSndLE .ln nested (42,9) _ _ rfl

-- A tail Call ignores arbitrary handler bodies and consumes no fresh labels.
example {width : Nat} [NeZero width] :
    LoopToWord.compHOL .ln (.call none (some 5) [1]
      (some (3, nested, nested, .ln)) : HolLoopProg width) (42,9) =
    (.call none (some 5) [0,0] none, (42,9)) := by
  simp [LoopToWord.compHOL, findVarHOL, sptLookup]

example :
    (loopToWordCompileProgHOL [(42, [], (nested : HolLoopProg 64)),
      (42, [1], leaf)]).all (fun row => goodHandlersHOL row.1 row.2.2) = true :=
  loopToWordGoodHandlers _ _ rfl

example : goodHandlersHOL 42
    (.call (some ([], (Spt.ln,Spt.ln), .skip, 42,9)) none []
      (some (0, .skip, 43,10)) : WordLangProgHOL (BitVec 64)) = false := by decide

end Flapjack.Test.LoopToWordLabelHandlersParity
