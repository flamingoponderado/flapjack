import Flapjack.Compiler.Backend.ClosToBvl.Proofs.EvaluateBlockCons

/-! List encodings in the closure-to-BVL value relation. -/
namespace Flapjack.Compiler.Backend.ClosToBvl
open Flapjack.Compiler.Backend.BackendCommon
open Flapjack.SemanticPrimitivesHOL

/-- Decoding a source list recovers its canonical encoding. -/
theorem sourceList_inverse (value : ClosSem.Value) (values : List ClosSem.Value)
    (decode : ClosSem.valueToList value = some values) : ClosSem.listToValue values = value := by
  cases value with
  | block tag fields =>
    cases fields with
    | nil =>
      simp only [ClosSem.valueToList] at decode
      split at decode
      · rename_i equal
        simp only [Option.some.injEq] at decode
        subst values
        subst tag
        rfl
      · contradiction
    | cons head tail =>
      cases tail with
      | nil => simp [ClosSem.valueToList] at decode
      | cons next rest =>
        cases rest with
        | cons other rest => simp [ClosSem.valueToList] at decode
        | nil =>
          simp only [ClosSem.valueToList] at decode
          split at decode
          · rename_i equal
            cases nextDecode : ClosSem.valueToList next with
            | none => simp [nextDecode] at decode
            | some vs =>
              simp [nextDecode] at decode
              subst values
              have ih := sourceList_inverse next vs nextDecode
              subst tag
              simp [ClosSem.listToValue, ih]
          · contradiction
  | _ => simp [ClosSem.valueToList] at decode
termination_by sizeOf value


/-- Encoding pointwise related lists produces related list values. -/
theorem listToValue_related {maxApp : Nat} {f : HolFiniteMapExact Nat Nat}
    {refs : HolFiniteMapExact Nat (BvlSem.Ref BvlSem.Value)} {code : Spt (Nat × Bvl.Exp)}
    {xs : List ClosSem.Value} {ys : List BvlSem.Value}
    (related : List.Forall₂ (vRel maxApp f refs code) xs ys) :
    vRel maxApp f refs code (ClosSem.listToValue xs) (BvlSem.listToValue ys) := by
  induction related with
  | nil => exact .block .nil
  | cons head tail ih => exact .block (.cons head (.cons ih .nil))

/-- Decoding a related target list preserves the source elements and order. -/
theorem valueToList_related {maxApp : Nat} {f : HolFiniteMapExact Nat Nat}
    {refs : HolFiniteMapExact Nat (BvlSem.Ref BvlSem.Value)} {code : Spt (Nat × Bvl.Exp)}
    (xs : List ClosSem.Value) (target : BvlSem.Value)
    (related : vRel maxApp f refs code (ClosSem.listToValue xs) target) :
    ∃ ys, BvlSem.valueToList target = some ys ∧ List.Forall₂ (vRel maxApp f refs code) xs ys := by
  induction xs generalizing target with
  | nil =>
    obtain ⟨fields, targetEq, fieldsRel⟩ := vRel_block_inv related
    cases fieldsRel
    subst target
    exact ⟨[], by simp [BvlSem.valueToList, closTagShift, nilTag], .nil⟩
  | cons x xs ih =>
    obtain ⟨fields, targetEq, fieldsRel⟩ := vRel_block_inv related
    cases fieldsRel with
    | @cons _ targetHead _ _ head tail =>
      cases tail with
      | cons list tail =>
        cases tail
        obtain ⟨ys, decode, listRel⟩ := ih _ list
        subst target
        refine ⟨targetHead :: ys, ?_, .cons head listRel⟩
        simpa [BvlSem.valueToList, closTagShift, consTag] using congrArg (Option.map (targetHead :: ·)) decode

/-- Related list values decode to pointwise related lists. -/
theorem decodedList_related {maxApp : Nat} {f : HolFiniteMapExact Nat Nat}
    {refs : HolFiniteMapExact Nat (BvlSem.Ref BvlSem.Value)} {code : Spt (Nat × Bvl.Exp)}
    (source : ClosSem.Value) (target : BvlSem.Value) (xs : List ClosSem.Value)
    (related : vRel maxApp f refs code source target) (decode : ClosSem.valueToList source = some xs) :
    ∃ ys, BvlSem.valueToList target = some ys ∧ List.Forall₂ (vRel maxApp f refs code) xs ys := by
  have sourceEq := sourceList_inverse source xs decode
  rw [← sourceEq] at related
  exact valueToList_related xs target related

/-- List construction operations that retain the current state. -/
inductive BlockListOp where
  | fromList : Nat → BlockListOp
  | append : BlockListOp

/-- Closure operator for a list primitive. -/
def BlockListOp.op : BlockListOp → ClosLang.Op
  | .fromList tag => .blockOp (.fromList tag)
  | .append => .blockOp .listAppend

private theorem forall₂_append {α β : Type} {R : α → β → Prop}
    {xs zs : List α} {ys ws : List β} (first : List.Forall₂ R xs ys)
    (second : List.Forall₂ R zs ws) : List.Forall₂ R (xs ++ zs) (ys ++ ws) := by
  induction first with
  | nil => exact second
  | cons head tail ih => exact .cons head ih

/-- A successful list operation produces related results without state changes. -/
theorem blockList_dispatch {C F : Type} {f : HolFiniteMapExact Nat Nat}
    (op : BlockListOp) (args : List ClosSem.Value) (targets : List BvlSem.Value)
    (s next : ClosSem.State C F) (t : BvlSem.State C F)
    (related : List.Forall₂ (vRel s.maxApp f t.refs t.code) args targets)
    (value : ClosSem.Value) (run : ClosSem.doApp op.op args s = .val (value, next)) :
    ∃ targetValue, BvlSem.doApp (compileOp op.op) targets t = .val (targetValue, t) ∧
      next = s ∧ vRel s.maxApp f t.refs t.code value targetValue := by
  cases op with
  | fromList tag =>
    cases args with
    | nil => simp [BlockListOp.op, ClosSem.doApp, ClosSem.applyBlock] at run
    | cons a rest =>
      cases rest with
      | nil =>
        cases related with
        | cons first tail =>
          cases tail
          cases decode : ClosSem.valueToList a with
          | none => simp [BlockListOp.op, ClosSem.doApp, ClosSem.applyBlock, decode] at run
          | some xs =>
            obtain ⟨ys, targetDecode, listsRel⟩ := decodedList_related a _ xs first decode
            simp [BlockListOp.op, ClosSem.doApp, ClosSem.applyBlock, decode] at run
            rcases run with ⟨rfl, rfl⟩
            refine ⟨.block (closTagShift tag) ys, ?_, rfl, .block listsRel⟩
            simp [BlockListOp.op, compileOp, BvlSem.doApp, BvlSem.applyBlock, targetDecode]
      | cons b rest => simp [BlockListOp.op, ClosSem.doApp, ClosSem.applyBlock] at run
  | append =>
    cases args with
    | nil => simp [BlockListOp.op, ClosSem.doApp, ClosSem.applyBlock] at run
    | cons a rest =>
      cases rest with
      | nil => simp [BlockListOp.op, ClosSem.doApp, ClosSem.applyBlock] at run
      | cons b rest =>
        cases rest with
        | nil =>
          cases related with
          | cons first tail =>
            cases tail with
            | cons second tail =>
              cases tail
              cases decodeA : ClosSem.valueToList a with
              | none => simp [BlockListOp.op, ClosSem.doApp, ClosSem.applyBlock, decodeA] at run
              | some xs =>
                cases decodeB : ClosSem.valueToList b with
                | none => simp [BlockListOp.op, ClosSem.doApp, ClosSem.applyBlock, decodeA, decodeB] at run
                | some more =>
                  obtain ⟨ys, targetA, firstRel⟩ := decodedList_related a _ xs first decodeA
                  obtain ⟨moreTarget, targetB, secondRel⟩ := decodedList_related b _ more second decodeB
                  simp [BlockListOp.op, ClosSem.doApp, ClosSem.applyBlock, decodeA, decodeB] at run
                  rcases run with ⟨rfl, rfl⟩
                  refine ⟨BvlSem.listToValue (ys ++ moreTarget), ?_, rfl, ?_⟩
                  · simp [BlockListOp.op, compileOp, BvlSem.doApp, BvlSem.applyBlock, targetA, targetB]
                  · exact listToValue_related (forall₂_append firstRel secondRel)
        | cons c rest => simp [BlockListOp.op, ClosSem.doApp, ClosSem.applyBlock] at run

/-- A list primitive failure is a type error. -/
theorem blockList_error {C F : Type} (op : BlockListOp) (args : List ClosSem.Value)
    (s : ClosSem.State C F) (error : ErrorResult ClosSem.Value)
    (run : ClosSem.doApp op.op args s = .err error) : error = .abort .typeError := by
  cases op <;> cases args with
  | nil => simpa [BlockListOp.op, ClosSem.doApp, ClosSem.applyBlock] using run.symm
  | cons a rest =>
    cases rest with
    | nil =>
      simp [BlockListOp.op, ClosSem.doApp, ClosSem.applyBlock] at run
      all_goals try (exact run.symm)
      all_goals repeat' (split at run <;> simp_all)
    | cons b rest =>
      cases rest with
      | nil =>
        simp [BlockListOp.op, ClosSem.doApp, ClosSem.applyBlock] at run
        all_goals try (exact run.symm)
        all_goals repeat' (split at run <;> simp_all)
      | cons c rest => simpa [BlockListOp.op, ClosSem.doApp, ClosSem.applyBlock] using run.symm

/-- Evaluation executes the arguments before a list primitive. -/
theorem evaluate_blockList {C F : Type} (trace : BackendCommon.Tra) (op : BlockListOp)
    (args : List ClosLang.Exp) (env : List ClosSem.Value) (s : ClosSem.State C F) :
    ClosSem.evaluate [.op trace op.op args] env s =
      match ClosSem.evaluate args env s with
      | (.err error, next) => (.err error, next)
      | (.val values, next) => match ClosSem.doApp op.op values.reverse next with
        | .err error => (.err error, next)
        | .val (value, last) => (.val [value], last) := by
  cases op <;> rw [ClosSem.evaluate, ClosSem.fixClock_evaluate] <;>
    simp only [BlockListOp.op] <;> cases h : ClosSem.evaluate args env s with
  | mk result next => cases result <;> rfl


end Flapjack.Compiler.Backend.ClosToBvl
