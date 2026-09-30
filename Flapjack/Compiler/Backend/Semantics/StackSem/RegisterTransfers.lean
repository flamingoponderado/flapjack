import Flapjack.Compiler.Backend.Semantics.StackSem.Expressions

/-! Source-matched Get/Set/OpCurrHeap clauses of stackSemScript.sml
 evaluate_def:793-807. Outer NONE means unsupported constructor. This extra
 Option-shaped dispatcher is untagged assembly infrastructure; the total
 evaluator is tracked by flapjack-y19g, which depends on flapjack-y19g.10. -/
namespace Flapjack.StackSemRegisterTransfers
open StackSemStateOps StackSemExpressions Compiler.Backend.StackLang

/-- Constructor-preserving codec between the two existing store-name carriers.
Flapjack infrastructure: both represent the same fixed-width HOL datatype. -/
def storeOfSyntax : StoreName → WordStoreHOL
  | .nextFree => .nextFree
  | .endOfHeap => .endOfHeap
  | .triggerGC => .triggerGC
  | .heapLength => .heapLength
  | .progStart => .progStart
  | .bitmapBase => .bitmapBase
  | .currHeap => .currHeap
  | .otherHeap => .otherHeap
  | .allocSize => .allocSize
  | .globals => .globals
  | .globReal => .globReal
  | .handler => .handler
  | .genStart => .genStart
  | .codeBuffer => .codeBuffer
  | .codeBufferEnd => .codeBufferEnd
  | .bitmapBuffer => .bitmapBuffer
  | .bitmapBufferEnd => .bitmapBufferEnd
  | .temp value => .temp value

def storeToSyntax : WordStoreHOL → StoreName
  | .nextFree => .nextFree
  | .endOfHeap => .endOfHeap
  | .triggerGC => .triggerGC
  | .heapLength => .heapLength
  | .progStart => .progStart
  | .bitmapBase => .bitmapBase
  | .currHeap => .currHeap
  | .otherHeap => .otherHeap
  | .allocSize => .allocSize
  | .globals => .globals
  | .globReal => .globReal
  | .handler => .handler
  | .genStart => .genStart
  | .codeBuffer => .codeBuffer
  | .codeBufferEnd => .codeBufferEnd
  | .bitmapBuffer => .bitmapBuffer
  | .bitmapBufferEnd => .bitmapBufferEnd
  | .temp value => .temp value

/-- The store codec preserves every constructor, including the 5-bit Temp. -/
theorem storeToSyntax_storeOfSyntax (name : StoreName) :
    storeToSyntax (storeOfSyntax name) = name := by cases name <;> rfl

/-- The reverse store codec roundtrip is unconditional. -/
theorem storeOfSyntax_storeToSyntax (name : WordStoreHOL) :
    storeOfSyntax (storeToSyntax name) = name := by cases name <;> rfl

def evaluateRegister {width : Nat} [NeZero width] {C F : Type}
    (program : HolProg width) (s : StackSemStateFiniteExact width C F) :
    Option (Option (StackSemResult width) × StackSemStateFiniteExact width C F) :=
  match program with
  | .get register name =>
      if ¬s.useStore then some (some .error, s) else
      match s.store.lookup (storeOfSyntax name) with
      | some value => some (none, setVar register value s)
      | none => some (some .error, s)
  | .set name register =>
      if ¬s.useStore then some (some .error, s) else
      match getVar register s with
      | some value => some (none, setStore (storeOfSyntax name) value s)
      | none => some (some .error, s)
  | .opCurrHeap operator destination source =>
      if ¬s.useStore then some (some .error, s) else
      match wordExp s (.op operator [.var source, .lookup .currHeap]) with
      | some value => some (none, setVar destination (.word value) s)
      | none => some (some .error, s)
  | _ => none

/-- Flapjack assembly equation for HOL Get, including the use_store guard. -/
theorem evaluateRegister_get {width : Nat} [NeZero width] {C F : Type}
    (register : Nat) (name : StoreName) (s : StackSemStateFiniteExact width C F) :
    evaluateRegister (.get register name) s =
      (if ¬s.useStore then some (some .error, s) else
       match s.store.lookup (storeOfSyntax name) with
       | some value => some (none, setVar register value s)
       | none => some (some .error, s)) := rfl

/-- Flapjack assembly equation for HOL Set; Loc payloads are preserved. -/
theorem evaluateRegister_set {width : Nat} [NeZero width] {C F : Type}
    (register : Nat) (name : StoreName) (s : StackSemStateFiniteExact width C F) :
    evaluateRegister (.set name register) s =
      (if ¬s.useStore then some (some .error, s) else
       match getVar register s with
       | some value => some (none, setStore (storeOfSyntax name) value s)
       | none => some (some .error, s)) := rfl

/-- Flapjack assembly equation retaining HOL's exact operand order. -/
theorem evaluateRegister_opCurrHeap {width : Nat} [NeZero width] {C F : Type}
    (operator : BinOp) (destination source : Nat)
    (s : StackSemStateFiniteExact width C F) :
    evaluateRegister (.opCurrHeap operator destination source) s =
      (if ¬s.useStore then some (some .error, s) else
       match wordExp s (.op operator [.var source, .lookup .currHeap]) with
       | some value => some (none, setVar destination (.word value) s)
       | none => some (some .error, s)) := rfl

/-- These nonrecursive source clauses preserve the input clock exactly. -/
theorem evaluateRegister_clock_eq {width : Nat} [NeZero width] {C F : Type}
    (program : HolProg width) (s : StackSemStateFiniteExact width C F)
    (result : Option (StackSemResult width)) (t : StackSemStateFiniteExact width C F)
    (h : evaluateRegister program s = some (result, t)) : t.clock = s.clock := by
  cases program <;> simp only [evaluateRegister] at h
  all_goals try contradiction
  all_goals repeat' (split at h)
  all_goals cases h
  all_goals rfl

end Flapjack.StackSemRegisterTransfers
