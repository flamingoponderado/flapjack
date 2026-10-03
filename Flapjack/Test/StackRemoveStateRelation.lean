import Flapjack.Compiler.Backend.StackRemove.Proofs.StateRelation

/-! Kernel regression checks for the full native state relation. These
specialized exclusions are Flapjack-specific tests, not separately named HOL
ports. The original probe independently proves the same exclusions. -/
namespace Flapjack.Test.StackRemoveStateRelation
open Flapjack Flapjack.Compiler.Backend.StackRemove

example {C F : Type} (jump : Bool) (bounds : BitVec 1 × BitVec 1) (pointer : Nat)
    (source target : StackSemStateFiniteExact 1 C F) :
    ¬ stateRelHOL jump bounds pointer source target := by
  simp [stateRelHOL, goodDimindex]

example {C F : Type} (jump : Bool) (bounds : BitVec 8 × BitVec 8) (pointer : Nat)
    (source target : StackSemStateFiniteExact 8 C F) :
    ¬ stateRelHOL jump bounds pointer source target := by
  simp [stateRelHOL, goodDimindex]

example {C F : Type} (jump : Bool) (bounds : BitVec 80 × BitVec 80) (pointer : Nat)
    (source target : StackSemStateFiniteExact 80 C F) :
    ¬ stateRelHOL jump bounds pointer source target := by
  simp [stateRelHOL, goodDimindex]

example {width : Nat} [NeZero width] {C F : Type} (jump : Bool)
    (bounds : BitVec width × BitVec width) (pointer : Nat)
    (source target : StackSemStateFiniteExact width C F) :
    ¬ stateRelHOL jump bounds pointer {source with useStack := false} target := by
  simp [stateRelHOL]

example {width : Nat} [NeZero width] {C F : Type} (jump : Bool)
    (bounds : BitVec width × BitVec width) (pointer : Nat)
    (source target : StackSemStateFiniteExact width C F) :
    ¬ stateRelHOL jump bounds pointer {source with useStore := false} target := by
  simp [stateRelHOL]

example {width : Nat} [NeZero width] {C F : Type} (jump : Bool)
    (bounds : BitVec width × BitVec width) (pointer : Nat)
    (source target : StackSemStateFiniteExact width C F) :
    ¬ stateRelHOL jump bounds pointer source {target with useStack := true} := by
  simp [stateRelHOL]

example {width : Nat} [NeZero width] {C F : Type} (jump : Bool)
    (bounds : BitVec width × BitVec width) (pointer : Nat)
    (source target : StackSemStateFiniteExact width C F) :
    ¬ stateRelHOL jump bounds pointer source {target with useStore := true} := by
  simp [stateRelHOL]

example {width : Nat} [NeZero width] {C F : Type} (jump : Bool)
    (bounds : BitVec width × BitVec width) (pointer : Nat)
    (source target : StackSemStateFiniteExact width C F) :
    ¬ stateRelHOL jump bounds pointer {source with useAlloc := true} target := by
  simp [stateRelHOL]

example {width : Nat} [NeZero width] {C F : Type} (jump : Bool)
    (bounds : BitVec width × BitVec width) (pointer : Nat)
    (source target : StackSemStateFiniteExact width C F) :
    ¬ stateRelHOL jump bounds pointer source {target with useAlloc := true} := by
  simp [stateRelHOL]

example {width : Nat} [NeZero width] {C F : Type} (jump : Bool)
    (bounds : BitVec width × BitVec width) (pointer : Nat)
    (source target : StackSemStateFiniteExact width C F)
    (invalid : source.stack.length < source.stackSpace) :
    ¬ stateRelHOL jump bounds pointer source target := by
  simp [stateRelHOL, Nat.not_le.mpr invalid]

example {width : Nat} [NeZero width] {C F : Type} (jump : Bool)
    (bounds : BitVec width × BitVec width) (pointer : Nat)
    (source target : StackSemStateFiniteExact width C F)
    (missing : source.store.lookup .bitmapBase = none) :
    ¬ stateRelHOL jump bounds pointer source target := by
  simp [stateRelHOL, missing, isSomeWord]

example {width : Nat} [NeZero width] {C F : Type} (jump : Bool)
    (bounds : BitVec width × BitVec width) (pointer block offset : Nat)
    (source target : StackSemStateFiniteExact width C F)
    (location : source.store.lookup .bitmapBase = some (.loc block offset)) :
    ¬ stateRelHOL jump bounds pointer source target := by
  simp [stateRelHOL, location, wordLocWToGeneric, isSomeWord]

example {width : Nat} [NeZero width] {C F : Type} (jump : Bool)
    (bounds : BitVec width × BitVec width) (pointer : Nat)
    (source target : StackSemStateFiniteExact width C F)
    (missing : target.regs.lookup (pointer + 1) = none) :
    ¬ stateRelHOL jump bounds pointer source target := by
  simp [stateRelHOL, missing]

example {width : Nat} [NeZero width] {C F : Type} (jump : Bool)
    (bounds : BitVec width × BitVec width) (pointer block offset : Nat)
    (source target : StackSemStateFiniteExact width C F)
    (location : target.regs.lookup (pointer + 1) = some (.loc block offset)) :
    ¬ stateRelHOL jump bounds pointer source target := by
  simp [stateRelHOL, location]

end Flapjack.Test.StackRemoveStateRelation
