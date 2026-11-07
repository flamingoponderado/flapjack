import Flapjack.Compiler.Backend.Semantics.DataSem.Value
import Flapjack.Misc.Sptree
import Flapjack.SemanticPrimitivesHOL.Operations

/-! Reference-aware equality for timestamped data-language values. -/
namespace Flapjack.Compiler.Backend.DataSem
open Flapjack
open Flapjack.SemanticPrimitivesHOL (EqResult)
open Classical
noncomputable section

/-- A nonempty block with a closure or partial-closure tag is a closure. -/
@[hol "cakeml/compiler/backend/semantics/dataSemScript.sml" "isClos_def"]
def isClosure {α : Type} (tag : Nat) (values : List α) : Prop :=
  (tag = 30 ∨ tag = 31) ∧ values ≠ []

mutual
/-- Compare data-language values, ignoring block timestamps while preserving
closure and immutable-byte-array behavior. -/
@[hol "cakeml/compiler/backend/semantics/dataSemScript.sml" "do_eq_def"]
def doEq {α : Type} (refs : Spt (BvlSem.Ref α)) (first second : Value) : EqResult :=
  match first, second with
  | .number a, .number b => .val (decide (a = b))
  | .word64 a, .word64 b => .val (decide (a = b))
  | .refPtr a x, .refPtr b y =>
      if a && b then
        match sptLookup x refs, sptLookup y refs with
        | some (.byteArray true xs), some (.byteArray true ys) => .val (decide (xs = ys))
        | some (.byteArray true _), _ | _, some (.byteArray true _) => .typeError
        | _, _ => .val (decide (x = y))
      else .typeError
  | .block _ a xs, .block _ b ys =>
      if isClosure a xs ∨ isClosure b ys then
        if isClosure a xs ∧ isClosure b ys then .val true else .typeError
      else if a = b ∧ xs.length = ys.length then doEqList refs xs ys else .val false
  | _, _ => .typeError
termination_by sizeOf first

/-- Compare value lists from left to right, propagating equality errors. -/
@[hol "cakeml/compiler/backend/semantics/dataSemScript.sml" "do_eq_def"]
def doEqList {α : Type} (refs : Spt (BvlSem.Ref α)) (first second : List Value) : EqResult :=
  match first, second with
  | [], [] => .val true
  | x :: xs, y :: ys => match doEq refs x y with
    | .val true => doEqList refs xs ys
    | result => result
  | _, _ => .val false
termination_by sizeOf first
end
end
end Flapjack.Compiler.Backend.DataSem
