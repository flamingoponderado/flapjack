import Flapjack.Compiler.Backend.Semantics.StackSem.StateOps
import Flapjack.Compiler.Backend.BackendCommon

/-! Assembly infrastructure for the size/bitmap clauses at stackSemScript
1010-1021. These are right-hand-side fragments, with no separate HOL original
or total evaluator equation; hence they remain untagged. Full `evaluate_def`
assembly and the production route are still open on the dependency graph. -/
namespace Flapjack.StackSemSizeBitmapCases
open StackSemStateOps

/-- Size-setting fragment: only an out-of-bounds Word clears the environment;
missing and Loc-valued registers return Error with the unchanged state. -/
def stackSetSize {width : Nat} [NeZero width] {C F : Type}
    (r : Nat) (s : StackSemStateFiniteExact width C F) :
    Option (StackSemResult width) × StackSemStateFiniteExact width C F :=
  if !s.useStack then (some .error, s)
  else match getVar r s with
    | some (.word word) =>
        if s.stack.length ≤ word.toNat then (some .error, emptyEnv s)
        else (none, setVar r (.word (word <<< wordShiftAmount width))
          {s with stackSpace := word.toNat})
    | _ => (some .error, s)

/-- Bitmap fragment: the alias guard precedes register lookup, and both lookup
and bound failures preserve the entire state. Bitmap lists use HOL indices. -/
def bitmapLoad {width : Nat} [NeZero width] {C F : Type}
    (r v : Nat) (s : StackSemStateFiniteExact width C F) :
    Option (StackSemResult width) × StackSemStateFiniteExact width C F :=
  if !s.useStack || r == v then (some .error, s)
  else match getVar v s with
    | some (.word word) =>
        if h : s.bitmaps.length ≤ word.toNat then (some .error, s)
        else (none, setVar r (.word s.bitmaps[word.toNat]) s)
    | _ => (some .error, s)

/-- Assembly certificate covering every enabled, disabled, lookup and bounds
branch: neither fragment changes clock, memory, bitmaps, FFI or code. -/
theorem sizeBitmap_frame {width : Nat} [NeZero width] {C F : Type}
    (r v : Nat) (s : StackSemStateFiniteExact width C F) :
    (stackSetSize r s).2.clock = s.clock ∧
    (stackSetSize r s).2.memory = s.memory ∧
    (stackSetSize r s).2.bitmaps = s.bitmaps ∧
    (stackSetSize r s).2.ffi = s.ffi ∧
    (stackSetSize r s).2.code = s.code ∧
    (bitmapLoad r v s).2.clock = s.clock ∧
    (bitmapLoad r v s).2.memory = s.memory ∧
    (bitmapLoad r v s).2.stack = s.stack ∧
    (bitmapLoad r v s).2.stackSpace = s.stackSpace ∧
    (bitmapLoad r v s).2.bitmaps = s.bitmaps ∧
    (bitmapLoad r v s).2.ffi = s.ffi ∧
    (bitmapLoad r v s).2.code = s.code := by
  simp only [stackSetSize, bitmapLoad]
  repeat' constructor
  all_goals repeat' split
  all_goals rfl

/-- Exact-size boundary fails and clears regs/stack, retaining stackSpace. -/
theorem stackSetSize_boundary {width : Nat} [NeZero width] {C F : Type}
    (r : Nat) (word : BitVec width) (s : StackSemStateFiniteExact width C F)
    (hUse : s.useStack = true) (hReg : s.regs.lookup r = some (.word word))
    (hBound : s.stack.length = word.toNat) :
    stackSetSize r s = (some .error, emptyEnv s) := by
  simp [stackSetSize, hUse, getVar, hReg, hBound]

/-- Successful setting writes the shifted modular word into the same register. -/
theorem stackSetSize_success {width : Nat} [NeZero width] {C F : Type}
    (r : Nat) (word : BitVec width) (s : StackSemStateFiniteExact width C F)
    (hUse : s.useStack = true) (hReg : s.regs.lookup r = some (.word word))
    (hBound : word.toNat < s.stack.length) :
    stackSetSize r s = (none, setVar r (.word (word <<< wordShiftAmount width))
      {s with stackSpace := word.toNat}) := by
  simp [stackSetSize, hUse, getVar, hReg, Nat.not_le_of_lt hBound]

/-- Aliasing is rejected even when the source lookup could succeed. -/
theorem bitmapLoad_alias {width : Nat} [NeZero width] {C F : Type}
    (r : Nat) (s : StackSemStateFiniteExact width C F) :
    bitmapLoad r r s = (some .error, s) := by
  simp [bitmapLoad]

/-- The bitmap's exact-length boundary preserves the entire state. -/
theorem bitmapLoad_boundary {width : Nat} [NeZero width] {C F : Type}
    (r v : Nat) (word : BitVec width) (s : StackSemStateFiniteExact width C F)
    (hReg : s.regs.lookup v = some (.word word))
    (hBound : s.bitmaps.length = word.toNat) :
    bitmapLoad r v s = (some .error, s) := by
  simp only [bitmapLoad]
  split
  · rfl
  · simp [getVar, hReg, hBound]

end Flapjack.StackSemSizeBitmapCases
