import Flapjack.CakeParser.PegChecks

/-! Replay `cake_peg_checks_probe.out` from pinned HOL. -/
namespace Flapjack.Test.CakePegChecksParity
open Flapjack.CakeParser Flapjack.CakeParser.Grammar Flapjack.CakeParser.PegChecks
open Flapjack.Basis.Pure.MlString Flapjack.Misc.Location

#guard ["", "+", "|", "||", "=", "==", ":", ":=", "::", "~", "~~", "!", "*", "@"].map
    (fun s => let b := (ofString s).explode
      (validMultSym b, validAddSym b, validRelSym b, validListSym b, validPrefixSym b)) ==
  [(false,false,false,false,false), (false,true,false,false,false), (false,false,false,false,false),
   (false,true,false,false,false), (false,false,false,false,false), (false,false,true,false,false),
   (false,false,false,false,false), (false,false,false,false,false), (false,false,false,true,false),
   (false,false,false,false,true), (false,false,true,false,false), (false,false,false,false,true),
   (true,false,false,false,false), (false,false,false,true,false)]

#guard ["", "Name", "value", "before", "div", "mod", "o", "_x"].map
    (fun s => [AlphaCheck.nonempty, .upperInitial, .lowerInitialNotReserved].map (fun p => evalAlpha p (ofString s))) ==
  [[false,false,false], [true,true,false], [true,false,true], [true,false,false],
   [true,false,false], [true,false,false], [true,false,false], [true,false,true]]

#guard [evalToken (.eq .valT) (.valT, unknownLoc), evalToken .isInt (.intT 5, unknownLoc),
    evalToken (.alpha .lowerInitialNotReserved) (.alphaT (ofString "mod"), unknownLoc),
    evalToken (.symbol .validList) (.symbolT (ofString "::"), unknownLoc),
    evalToken (.longid .ctorUpperInitial) (.longidT (.mod (ofString "M") .end) (ofString "Name"), unknownLoc),
    evalToken (.longid .tailNonemptyHeadAlphaNotUpper) (.longidT .end (ofString "+"), unknownLoc),
    evalToken .opidAlphaNonempty (.alphaT (ofString ""), unknownLoc)] == [true,true,false,true,true,true,false]

end Flapjack.Test.CakePegChecksParity
