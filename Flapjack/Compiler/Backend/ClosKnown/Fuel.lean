module

public import Flapjack.Compiler.Backend.ClosKnown.Inline
public import Flapjack.Compiler.Backend.ClosKnown.KnownOp
public import Flapjack.Compiler.Backend.ClosFvs
public import Flapjack.Compiler.Backend.ClosTicks
public import Flapjack.Compiler.Backend.ClosLetop
public import Flapjack.Compiler.Backend.ClosOp

@[expose] public section

/-! Helpers shared by the total known-function traversal. Full HOL
correctness remains unproved. -/
namespace Flapjack.Compiler.Backend.ClosKnown
open ClosLang

/-- Insert the source tick sequence, numbering from the supplied trace index. -/
@[hol "cakeml/compiler/backend/clos_knownScript.sml" "mk_Ticks_def"]
def ticks (trace : BackendCommon.Tra) : Nat → Nat → Exp → Exp
  | _, 0, e => e
  | index, n + 1, e => ticks trace (index + 1) n (.tick (BackendCommon.mkCons trace index) e)

/-- Generate non-inlineable approximations for a recursive closure group. -/
@[hol "cakeml/compiler/backend/clos_knownScript.sml" "clos_gen_noinline_def"]
def closGenNoInline {α : Type} (loc index : Nat) : List (Nat × α) → List ValApprox
  | [] => []
  | (arity, _) :: rest =>
      .closNoInline (loc + 2 * index) arity :: closGenNoInline loc (index + 1) rest

def noInline (loc : Nat) (fns : List (Nat × Exp)) : List ValApprox :=
  closGenNoInline loc 0 fns

/-- The source recursion agrees with the previous indexed-list implementation. -/
theorem closGenNoInline_eq_zipIdx {α : Type} (loc index : Nat) (fns : List (Nat × α)) :
    closGenNoInline loc index fns =
      (fns.zipIdx index).map (fun ((arity, _), i) => .closNoInline (loc + 2 * i) arity) := by
  induction fns generalizing index with
  | nil => rfl
  | cons p rest ih =>
    cases p
    simp [closGenNoInline, ih]

/-- Switching to the source recursion preserves the previous executable result. -/
theorem noInline_eq_zip (loc : Nat) (fns : List (Nat × Exp)) :
    noInline loc fns =
      (fns.zip (List.range fns.length)).map
        (fun ((arity, _), i) => .closNoInline (loc + 2 * i) arity) := by
  rw [noInline, closGenNoInline_eq_zipIdx, List.zipIdx_eq_zip_range']
  rw [List.range_eq_range']

end Flapjack.Compiler.Backend.ClosKnown
