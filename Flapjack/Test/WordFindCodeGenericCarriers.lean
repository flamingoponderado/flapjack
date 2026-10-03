import Flapjack.Compiler.Backend.WordRemove.Proofs.CompileState

namespace Flapjack.Test.WordFindCodeGenericCarriers
open Flapjack Flapjack.Compiler.Backend.WordRemove

/-! Regression for original HOL's independent payload carriers. These concrete
Bool/List Nat code types and String size payload cannot typecheck against the
former monomorphic declarations. String here is an arbitrary size payload,
not a model of a HOL mlstring identifier. No standalone HOL original. -/
example {width : Nat} [NeZero width] (destination : Option Nat)
    (arguments : List (WordLocW width)) (transform : Bool → List Nat)
    (code : Spt (Nat × Bool)) (sizes : Spt String) :
    wordSemFindCode destination arguments
      (sptMap (fun entry => (entry.1, transform entry.2)) code) sizes =
    (wordSemFindCode destination arguments code sizes).map
      (fun result => (result.1, transform result.2.1, result.2.2)) :=
  findCode_map_I destination arguments transform code sizes

#guard wordSemFindCode (width := 64) (some 3) []
  (sptInsert 3 (0, true) .ln) (sptInsert 3 "arbitrary-size" .ln) ==
    some ([], true, some "arbitrary-size")
#guard wordSemFindCode (width := 64) none [.loc 3 0]
  (sptInsert 3 (0, true) .ln) (sptInsert 3 "arbitrary-size" .ln) ==
    some ([], true, some "arbitrary-size")

end Flapjack.Test.WordFindCodeGenericCarriers
