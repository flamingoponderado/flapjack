import Flapjack.Compiler.Backend.Bvi.Syntax
import Flapjack.Compiler.Backend.Bvi.Budget
import Flapjack.Compiler.Backend.BackendCommon.BvlStubs
import Flapjack.HolRef

/-! Executable infrastructure for BVI tail-modulo-constructor lowering.
`Proofs.Total` proves structural traversal bounds for the checked code;
source correspondence and the correctness theorem remain unported. -/
namespace Flapjack.Compiler.Backend.BviTmc
open Bvi

/-- Skeleton of a constructor containing a recursive call. -/
@[hol "cakeml/compiler/backend/bvi_tmcScript.sml" "call_block"]
inductive CallBlock where
  | callBlock : Nat → List Nat → CallBlock → List Nat → CallBlock
  | rCall : Nat → List Nat → CallBlock

/-- Check whether an operation is pure under the source TMC analysis. -/
@[hol "cakeml/compiler/backend/bvi_tmcScript.sml" "pure_op_def"]
def pureOp (op : ClosLang.Op) (args : List Exp) : Bool :=
  match op, args with
  | .intOp (.const n), [] => -268435457 ≤ n && n ≤ 268435457
  | .blockOp (.cons _), _ => true
  | _, _ => false

/-- Bounded form of the source's purity test. -/
def pureFuel : Nat → Nat → Exp → Option Bool
  | 0, _, _ => none
  | fuel + 1, n, e => do
      let visit := pureFuel fuel n
      let all := fun xs => xs.foldlM (fun yes x => if yes then visit x else pure false) true
      match e with
      | .var v => pure (v < n)
      | .let xs body => if ← visit body then all xs else pure false
      | .op op xs => if pureOp op xs then all xs else pure false
      | _ => pure false

/-- Retry exhausted purity checks with a structural bound while preserving
all results computed with the original fuel. -/
def pureBounded (fuel n : Nat) (e : Exp) : Option Bool :=
  match pureFuel fuel n e with
  | some result => some result
  | none => pureFuel (max fuel (expBudget e + 1)) n e

/-- Shift each variable index by the size of an added environment prefix. -/
@[hol "cakeml/compiler/backend/bvi_tmcScript.sml" "shift_vars_def"]
def shiftVars (n : Nat) (xs : List Nat) := xs.map (· + n)

/-- Shift every variable index in a call-block skeleton. -/
@[hol "cakeml/compiler/backend/bvi_tmcScript.sml" "shift_cb_def"]
def shiftBlock (n : Nat) : CallBlock → CallBlock
  | .rCall ticks args => .rCall ticks (shiftVars n args)
  | .callBlock tag left child right =>
      .callBlock tag (shiftVars n left) (shiftBlock n child) (shiftVars n right)

private def callToBlock (loc ticks : Nat) (dest : Option Nat) (args : List Exp)
    (handler : Option Exp) : Option (List Exp × CallBlock) :=
  match dest, handler with
  | some d, none => if d == loc then some (args, .rCall ticks (List.range args.length)) else none
  | _, _ => none

private abbrev Extract := List Exp × Sum (List Nat) CallBlock

mutual
  /-- Extract one constructor argument, distinguishing extraction failure from
  fuel exhaustion using the nested `Option`. -/
  def extractOneFuel : Nat → Nat → Nat → Nat → Exp → Option (Option Extract)
    | 0, _, _, _, _ => none
    | fuel + 1, n, loc, tag, e => do
      match e with
      | .call ticks dest args handler =>
          match callToBlock loc ticks dest args handler with
          | some (bs, cb) => pure (some (bs, .inr (.callBlock tag [] cb [])))
          | none => pure none
      | .op (.blockOp (.cons childTag)) args =>
          match ← extractListFuel fuel n loc childTag args with
          | none => pure none
          | some (_, .inl _) =>
              if ← pureBounded fuel n e then pure (some ([e], .inl [0])) else pure none
          | some (bs, .inr cb) => pure (some (bs, .inr (.callBlock tag [] cb [])))
      | _ => if ← pureBounded fuel n e then pure (some ([e], .inl [0])) else pure none

  /-- Extract arguments from right to left, preserving source binding order. -/
  def extractListFuel : Nat → Nat → Nat → Nat → List Exp → Option (Option Extract)
    | _, _, _, _, [] => some (some ([], .inl []))
    | 0, _, _, _, _ :: _ => none
    | fuel + 1, n, loc, tag, [x] => extractOneFuel fuel n loc tag x
    | fuel + 1, n, loc, tag, x :: y :: xs => do
      match ← extractListFuel fuel n loc tag (y :: xs) with
      | none => pure none
      | some (bs2, .inl vs2) =>
          match ← extractOneFuel fuel n loc tag x with
          | none => pure none
          | some (bs1, .inl vs1) =>
              if vs1.length + vs2.length ≤ 268435457 then
                pure (some (bs1 ++ bs2, .inl (vs1 ++ shiftVars bs1.length vs2)))
              else pure none
          | some (bs1, .inr (.callBlock _ [] child [])) =>
              pure (some (bs1 ++ bs2, .inr (.callBlock tag [] child (shiftVars bs1.length vs2))))
          | some (_, .inr _) => pure none
      | some (bs2, .inr cb) =>
          match shiftBlock 1 cb with
          | .callBlock t left child right => pure (some (x :: bs2, .inr (.callBlock t (0 :: left) child right)))
          | _ => pure none
end

/-- Preserve successful extraction and retry exhausted operand traversals
with a structural bound. The inner `none` remains the pass's ordinary
decision that extraction is not applicable. -/
def extractListBounded (fuel n loc tag : Nat) (xs : List Exp) : Option (Option Extract) :=
  match extractListFuel fuel n loc tag xs with
  | some result => some result
  | none => extractListFuel (max fuel (listBudget xs + 1)) n loc tag xs

/-- Extract a direct recursive call or a constructor containing one. -/
def toBlockFuel (fuel n loc : Nat) (e : Exp) : Option (Option (List Exp × CallBlock)) := do
  match e with
  | .call ticks dest args handler => pure (callToBlock loc ticks dest args handler)
  | .op (.blockOp (.cons tag)) xs =>
      match ← extractListBounded fuel n loc tag xs with
      | some (bs, .inr cb) => pure (some (bs, cb))
      | _ => pure none
  | _ => pure none

private def const (n : Nat) : Exp := .op (.intOp (.const (Int.ofNat n))) []
private def mutCons (tag : Nat) (left right : List Nat) : Exp :=
  .op (.memOp (.mutCons tag right.length)) (left.map .var ++ [const 0] ++ right.map .var)
private def updateCons (ptr idx val : Exp) : Exp := .op (.memOp .updateCons) [val, idx, ptr]
private def fillHole (ptr idx : Nat) (e : Exp) : Exp := updateCons (.var ptr) (.var idx) e
private def optimiseCall (ticks dest : Nat) (args : List Nat) (ptr idx : Exp) : Exp :=
  .call ticks (some dest) (args.map .var ++ [ptr, idx]) none

/-- Build the nested mutable-constructor worker without repeatedly shifting
the skeleton; the shift accumulator is the source's equivalent alternate form. -/
@[hol "cakeml/compiler/backend/bvi_tmcScript.sml" "cb_to_bvi_worker_aux_alt_def"]
def workerAux (shift : Nat) : CallBlock → Nat → Nat → Nat → Exp
  | .rCall ticks args, dest, ptr, idx => optimiseCall ticks dest (shiftVars shift args) (.var ptr) (const idx)
  | .callBlock tag left child right, dest, ptr, idx =>
      .let [mutCons tag (shiftVars shift left) (shiftVars shift right)]
        (.let [updateCons (.var (ptr + 1)) (const idx) (.var 0)]
          (workerAux (shift + 2) child dest 1 right.length))

private def workerBlock (cb : CallBlock) (dest ptr idx : Nat) : Exp :=
  match cb with
  | .rCall ticks args => optimiseCall ticks dest args (.var ptr) (.var idx)
  | .callBlock tag left child right =>
      .let [mutCons tag left right]
        (.let [updateCons (.var (ptr + 1)) (.var (idx + 1)) (.var 0)]
          (workerAux 2 child dest 1 right.length))

private def wrapperBlock (tag : Nat) (left : List Nat) (child : CallBlock) (right : List Nat) (dest : Nat) : Exp :=
  .let [mutCons tag left right]
    (.let [workerAux 1 child dest 0 right.length] (.op (.memOp .finaliseCons) [.var 1]))

/-- Construct a wrapper only when a constructor contains an eligible call. -/
def rewriteWrapperFuel : Nat → Nat → Nat → Nat → Exp → Option (Option Exp)
  | 0, _, _, _, _ => none
  | fuel + 1, loc, next, n, e => do
      match e with
      | .ifThenElse cond yes no =>
          let y ← rewriteWrapperFuel fuel loc next n yes
          let z ← rewriteWrapperFuel fuel loc next n no
          match y, z with
          | none, none => pure none
          | _, _ => pure (some (.ifThenElse cond (y.getD yes) (z.getD no)))
      | .let xs body =>
          pure ((← rewriteWrapperFuel fuel loc next (n + xs.length) body).map (.let xs))
      | .tick x => pure ((← rewriteWrapperFuel fuel loc next n x).map .tick)
      | .op _ _ =>
          match ← toBlockFuel fuel n loc e with
          | some (bs, .callBlock tag left child right) => pure (some (.let bs (wrapperBlock tag left child right next)))
          | _ => pure none
      | _ => pure none

/-- Build the worker body after a successful wrapper check. -/
def rewriteWorkerFuel : Nat → Nat → Nat → Nat → Nat → Nat → Exp → Option Exp
  | 0, _, _, _, _, _, _ => none
  | fuel + 1, loc, next, ptr, idx, n, e => do
      match e with
      | .ifThenElse cond yes no => do
          pure (.ifThenElse cond (← rewriteWorkerFuel fuel loc next ptr idx n yes)
            (← rewriteWorkerFuel fuel loc next ptr idx n no))
      | .let xs body => do
          pure (.let xs (← rewriteWorkerFuel fuel loc next (ptr + xs.length) (idx + xs.length) (n + xs.length) body))
      | .raise x => pure (.raise x)
      | .tick x => do pure (.tick (← rewriteWorkerFuel fuel loc next ptr idx n x))
      | .op _ _ | .call _ _ _ _ =>
          match ← toBlockFuel fuel n loc e with
          | some (bs, cb) => pure (.let bs (workerBlock cb next (bs.length + ptr) (bs.length + idx)))
          | none => pure (fillHole ptr idx e)
      | _ => pure (fillHole ptr idx e)

/-- Compile one function, with nested `Option` distinguishing fuel exhaustion
from the original pass's decision not to rewrite. -/
def compileExpFuel (fuel loc next arity : Nat) (e : Exp) : Option (Option (Exp × Exp)) := do
  match ← rewriteWrapperFuel fuel loc next arity e with
  | none => pure none
  | some wrapper => pure (some (wrapper, ← rewriteWorkerFuel fuel loc next arity (arity + 1) arity e))

/-- Retry exhausted TMC conversion using a structural bound, preserving the
ordinary inner `none` decision and every previously successful result. -/
def compileExpBounded (fuel loc next arity : Nat) (e : Exp) : Option (Option (Exp × Exp)) :=
  match compileExpFuel fuel loc next arity e with
  | some result => some result
  | none => compileExpFuel (max fuel (expBudget e + 1)) loc next arity e

/-- Compile functions in order, allocating worker locations in source order. -/
def compileEachFuel (fuel : Nat) : Nat → List (Nat × Nat × Exp) → Option (Nat × List (Nat × Nat × Exp))
  | next, [] => some (next, [])
  | next, (loc, arity, body) :: rest => do
      match ← compileExpBounded fuel loc next arity body with
      | none =>
          let (next, rest) ← compileEachFuel fuel next rest
          pure (next, (loc, arity, body) :: rest)
      | some (wrapper, worker) =>
          let (next', rest) ← compileEachFuel fuel (next + Flapjack.bvlToBviNamespaces) rest
          pure (next', (loc, arity, wrapper) :: (next, arity + 2, worker) :: rest)

def compileProgFuel (fuel : Nat) (enabled : Bool) (next : Nat)
    (code : List (Nat × Nat × Exp)) : Option (Nat × List (Nat × Nat × Exp)) :=
  if enabled then compileEachFuel fuel next code else some (next, code)

/-- Every variable index is within the given environment size. -/
@[hol "cakeml/compiler/backend/bvi_tmcScript.sml" "wf_vars_def"]
def wfVars (n : Nat) (indices : List Nat) : Prop := ∀ index ∈ indices, index < n

/-- The empty list of variables is well formed in any environment. -/
@[hol "cakeml/compiler/backend/bvi_tmcScript.sml" "wf_vars_empty"]
theorem wfVars_empty (n : Nat) : wfVars n [] := by simp [wfVars]

/-- Enlarging the environment preserves well-formed indices. -/
@[hol "cakeml/compiler/backend/bvi_tmcScript.sml" "wf_vars_expand"]
theorem wfVars_expand (n1 n2 : Nat) (indices : List Nat) (wellFormed : wfVars n1 indices)
    (bound : n1 ≤ n2) : wfVars n2 indices := by
  intro index member
  have := wellFormed index member
  omega

/-- A prefix shifts all well-formed indices into the enlarged environment. -/
@[hol "cakeml/compiler/backend/bvi_tmcScript.sml" "wf_vars_shift"]
theorem wfVars_shift (n1 n2 : Nat) (indices : List Nat) (wellFormed : wfVars n1 indices) :
    wfVars (n2 + n1) (shiftVars n2 indices) := by
  intro index member
  obtain ⟨old, present, rfl⟩ := List.mem_map.mp member
  have := wellFormed old present
  omega

/-- Concatenating well-formed index lists preserves their bounds. -/
@[hol "cakeml/compiler/backend/bvi_tmcScript.sml" "wf_vars_append"]
theorem wfVars_append (n : Nat) (left right : List Nat) (leftOk : wfVars n left)
    (rightOk : wfVars n right) : wfVars n (left ++ right) := by
  intro index member
  rcases List.mem_append.mp member with inLeft | inRight
  · exact leftOk index inLeft
  · exact rightOk index inRight

end Flapjack.Compiler.Backend.BviTmc
