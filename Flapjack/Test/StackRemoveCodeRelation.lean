import Flapjack.Compiler.Backend.StackRemove.Proofs.CodeRelation

namespace Flapjack.Test.StackRemoveCodeRelation
open Flapjack Flapjack.Compiler.Backend.StackLang Flapjack.Compiler.Backend.StackRemove

def stubs (width : Nat) [NeZero width] : Spt (HolProg width) :=
  sptFromAList [(0, .skip), (1, .skip), (2, .skip)]

-- Kernel checks quantify over every lookup key; no finite sampling of the
-- relation's domain equality or source-program clause is substituted.
theorem emptyRelation {width : Nat} [NeZero width] (jump : Bool)
    (bounds : BitVec width × BitVec width) (pointer : Nat) :
    codeRelHOL jump bounds pointer .ln (stubs width) := by
  constructor
  · intro name program found
    simp [sptLookup] at found
  · funext name
    apply propext
    simp only [stubs, sptDomain, sptLookup_sptFromAList, sptAListLookup, sptLookup]
    repeat' (split <;> simp_all)

theorem missingStub {width : Nat} [NeZero width] (jump : Bool)
    (bounds : BitVec width × BitVec width) (pointer : Nat) :
    ¬ codeRelHOL jump bounds pointer .ln (sptFromAList [(0, .skip), (1, .skip)]) := by
  intro related
  have atTwo := congrFun related.2 2
  simp [sptDomain, sptLookup_sptFromAList, sptAListLookup, sptLookup] at atTwo

theorem extraTarget {width : Nat} [NeZero width] (jump : Bool)
    (bounds : BitVec width × BitVec width) (pointer : Nat) :
    ¬ codeRelHOL jump bounds pointer .ln
      (sptFromAList [(0, .skip), (1, .skip), (2, .skip), (99, .tick)]) := by
  intro related
  have atExtra := congrFun related.2 99
  simp [sptDomain, sptLookup_sptFromAList, sptAListLookup, sptLookup] at atExtra

theorem tickRelation {width : Nat} [NeZero width] (jump : Bool)
    (bounds : BitVec width × BitVec width) (pointer : Nat) :
    codeRelHOL jump bounds pointer (sptFromAList [(9, .tick)])
      (sptFromAList [(0, .skip), (1, .skip), (2, .skip), (9, .tick)]) := by
  constructor
  · intro name program found
    by_cases key : name = 9
    · subst name
      simp [sptLookup_sptFromAList, sptAListLookup] at found
      subst program
      simp [Flapjack.Compiler.Backend.StackProps.regBound,
        sptLookup_sptFromAList, sptAListLookup, comp]
    · simp [sptLookup_sptFromAList, sptAListLookup, key] at found
  · funext name
    apply propext
    simp only [sptDomain, sptLookup_sptFromAList, sptAListLookup]
    repeat' (split <;> simp_all)

theorem wrongBody {width : Nat} [NeZero width] (jump : Bool)
    (bounds : BitVec width × BitVec width) (pointer : Nat) :
    ¬ codeRelHOL jump bounds pointer (sptFromAList [(9, .tick)])
      (sptFromAList [(0, .skip), (1, .skip), (2, .skip), (9, .skip)]) := by
  intro related
  have compiled := (related.1 9 .tick
    (by simp [sptLookup_sptFromAList, sptAListLookup])).2
  simp [sptLookup_sptFromAList, sptAListLookup, comp] at compiled

theorem badRegister {width : Nat} [NeZero width] (jump : Bool)
    (bounds : BitVec width × BitVec width) :
    ¬ codeRelHOL jump bounds 24 (sptFromAList [(9, .get 24 .currHeap)])
      (sptFromAList [(0, .skip), (1, .skip), (2, .skip),
        (9, .inst (.arith (.binop .or 24 26 (.reg 26))))]) := by
  intro related
  have bounded := (related.1 9 (.get 24 .currHeap)
    (by simp [sptLookup_sptFromAList, sptAListLookup])).1
  simp [Flapjack.Compiler.Backend.StackProps.regBound] at bounded

theorem reservedSource {width : Nat} [NeZero width] (jump : Bool)
    (bounds : BitVec width × BitVec width) (pointer : Nat) :
    codeRelHOL jump bounds pointer (sptFromAList [(0, .tick)])
      (sptFromAList [(0, .tick), (1, .skip), (2, .skip)]) := by
  constructor
  · intro name program found
    by_cases key : name = 0
    · subst name
      simp [sptLookup_sptFromAList, sptAListLookup] at found
      subst program
      simp [Flapjack.Compiler.Backend.StackProps.regBound,
        sptLookup_sptFromAList, sptAListLookup, comp]
    · simp [sptLookup_sptFromAList, sptAListLookup, key] at found
  · funext name
    apply propext
    simp only [sptDomain, sptLookup_sptFromAList, sptAListLookup]
    repeat' (split <;> simp_all)

theorem malformedSource {width : Nat} [NeZero width] (jump : Bool)
    (bounds : BitVec width × BitVec width) (pointer : Nat) :
    codeRelHOL jump bounds pointer (.bn .ln .ln) (stubs width) := by
  constructor
  · intro name program found
    simp [sptLookup] at found
  · have domains : sptDomain (.bn .ln .ln : Spt (HolProg width)) = sptDomain (.ln : Spt (HolProg width)) := by
      funext name
      simp [sptDomain, sptLookup]
    rw [domains]
    exact (emptyRelation jump bounds pointer).2

example : codeRelHOL (width := 1) true (0, 0) 24 .ln (stubs 1) := emptyRelation _ _ _
example : codeRelHOL (width := 8) false (0, 0) 24 .ln (stubs 8) := emptyRelation _ _ _
example : codeRelHOL (width := 32) true (0, 0) 24 .ln (stubs 32) := emptyRelation _ _ _
example : codeRelHOL (width := 64) false (0, 0) 24 .ln (stubs 64) := emptyRelation _ _ _
example : codeRelHOL (width := 80) true (0, 0) 24 .ln (stubs 80) := emptyRelation _ _ _

end Flapjack.Test.StackRemoveCodeRelation
