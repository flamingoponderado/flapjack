import Flapjack.RiscV.WordCopyCodecDomain

/-! Same-input kernel replay of original copy-propagation observations, plus
Flapjack-only five-register AddCarry and nested codec rejection sentinels. -/
namespace Flapjack.Test.WordCopyCodecDomainParity
open Flapjack RiscV
private abbrev load16 : WordProg (BitVec 8) := .inst (.memOffset .load16 3 5 7)
private abbrev store16 : WordProg (BitVec 8) := .inst (.memOffset .store16 3 5 7)
private abbrev carry : WordProg (BitVec 8) := .inst (.arith (.cakeAddCarry 1 2 3 4))
example : wordCopyProp carry = carry := by simp only [wordCopyProp, wordCopyProg, wordCopyInst] <;> rfl
example : wordCopyProp load16 = load16 := by simp only [wordCopyProp, wordCopyProg, wordCopyInst] <;> rfl
example : wordCopyProp store16 = store16 := by simp only [wordCopyProp, wordCopyProg, wordCopyInst] <;> rfl
example : wordCopyProp (.seq (.move 0 [(1,5)]) (.raise 5) : WordProg (BitVec 8)) =
    .seq (.move 0 [(1,5)]) (.raise 1) := by simp [wordCopyProp, wordCopyProg, wordCopyMoves, wordCopyLookup, wordCopySet, wordCopyRemove, wordCopyEmpty, wordCopyLookupIndexed, wordCopyIsAlloc] <;> rfl
example : wordCopyProp (.ite .equal 3 (.reg 5) load16 store16) =
    .ite .equal 3 (.reg 5) load16 store16 := by simp only [wordCopyProp, wordCopyProg, wordCopyInst] <;> rfl
example : wordCopyProp (.loop [] load16 []) = .loop [] load16 [] := by simp only [wordCopyProp, wordCopyProg, wordCopyInst] <;> rfl
example : wordCopyProp (.mustTerminate carry) = .mustTerminate carry := by simp only [wordCopyProp, wordCopyProg, wordCopyInst] <;> rfl
example : wordCopyProp (.call (some ([3],([],[]),load16,19,23)) (some 17) [5]
    (some (7,store16,29,31))) =
    .call (some ([3],([],[]),load16,19,23)) (some 17) [5]
      (some (7,store16,29,31)) := by simp only [wordCopyProp, wordCopyProg]

private abbrev five : WordProg (BitVec 8) := .inst (.arith (.addCarry 1 2 3 4 5))
private def casesToCheck : List (WordProg (BitVec 8)) :=
  [carry,load16,store16,five,.seq (.move 0 [(1,5)]) five,
   .ite .equal 1 (.imm 0) .skip five,.loop [] five [],
   .call (some ([],([],[]),five,2,3)) none [] none,
   .call none none [] (some (1,five,2,3))]
example : casesToCheck.map (fun p => (wordLangProgToHOL p).isSome) =
    [true,true,true,false,false,false,false,false,false] := by decide +kernel
example : casesToCheck.map (fun p => (wordLangProgToHOL (wordCopyProp p)).isSome) =
    [true,true,true,false,false,false,false,false,false] := by
  simp only [wordCopyProp_codecDomain]
  decide +kernel
example {width : Nat} [WordCseHash (BitVec width)] (state : WordCopyState)
    (program : WordProg (BitVec width)) :
    (wordLangProgToHOL (wordCopyProg state program).1).isSome =
      (wordLangProgToHOL program).isSome := wordCopyProg_codecDomain state program
end Flapjack.Test.WordCopyCodecDomainParity
