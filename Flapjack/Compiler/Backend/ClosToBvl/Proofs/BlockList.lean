module

public import Flapjack.Compiler.Backend.ClosToBvl.Proofs.EvaluateBlockCons
public import Mathlib.Data.List.Forall2
public import Flapjack.FiniteMap.BroadCodec

@[expose] public section

/-! List encodings in the closure-to-BVL value relation. -/
namespace Flapjack.Compiler.Backend.ClosToBvl
open Flapjack.Compiler.Backend.BackendCommon
open Flapjack.SemanticPrimitivesHOL

/-- Shifting constructor tags preserves exactly the nil and cons tags. -/
@[hol "cakeml/compiler/backend/proofs/clos_to_bvlProofScript.sml" "clos_tag_shift_eq_nil_tag"]
theorem closTagShift_eq_nilTag (tag : Nat) :
    (closTagShift tag = nilTag ↔ tag = nilTag) ∧
      (closTagShift tag = consTag ↔ tag = consTag) := by
  simp only [closTagShift, nilTag, consTag]
  split <;> omega

/-- Canonical finite-map roundtrip for the source relation. -/
theorem holFmapAsFiniteSupportParamWitness_listToValue_related_f
    (f : HolFiniteMapExact Nat Nat) (key : Nat) :
    (FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad f)).lookup key = f.lookup key ∧
    (FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad f)).finiteSupport = f.finiteSupport ∧
    FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad f) = f :=
  holFmapAsFiniteSupportParamWitness_vRel_f f key

/-- Canonical finite-map roundtrip for the source relation. -/
theorem holFmapAsFiniteSupportParamWitness_listToValue_related_refs
    (refs : HolFiniteMapExact Nat (BvlSem.Ref BvlSem.Value)) (key : Nat) :
    (FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad refs)).lookup key = refs.lookup key ∧
    (FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad refs)).finiteSupport = refs.finiteSupport ∧
    FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad refs) = refs :=
  holFmapAsFiniteSupportParamWitness_vRel_refs refs key

/-- Canonical finite-map roundtrip for the source relation. -/
theorem holFmapAsFiniteSupportParamWitness_decodedList_related_f
    (f : HolFiniteMapExact Nat Nat) (key : Nat) :
    (FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad f)).lookup key = f.lookup key ∧
    (FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad f)).finiteSupport = f.finiteSupport ∧
    FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad f) = f :=
  holFmapAsFiniteSupportParamWitness_vRel_f f key

/-- Canonical finite-map roundtrip for the source relation. -/
theorem holFmapAsFiniteSupportParamWitness_decodedList_related_refs
    (refs : HolFiniteMapExact Nat (BvlSem.Ref BvlSem.Value)) (key : Nat) :
    (FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad refs)).lookup key = refs.lookup key ∧
    (FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad refs)).finiteSupport = refs.finiteSupport ∧
    FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad refs) = refs :=
  holFmapAsFiniteSupportParamWitness_vRel_refs refs key

/-- Encoding pointwise related lists produces related list values. -/
@[hol "cakeml/compiler/backend/proofs/clos_to_bvlProofScript.sml" "list_to_v_v_rel"
  (fmap_as_finite_support_parameters := [f, refs])]
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
@[hol "cakeml/compiler/backend/proofs/clos_to_bvlProofScript.sml" "v_to_list"
  (fmap_as_finite_support_parameters := [f, refs])]
theorem decodedList_related {maxApp : Nat} {f : HolFiniteMapExact Nat Nat}
    {refs : HolFiniteMapExact Nat (BvlSem.Ref BvlSem.Value)} {code : Spt (Nat × Bvl.Exp)}
    (source : ClosSem.Value) (xs : List ClosSem.Value) (target : BvlSem.Value)
    (premises : ClosSem.valueToList source = some xs ∧ vRel maxApp f refs code source target) :
    ∃ ys, BvlSem.valueToList target = some ys ∧ List.Forall₂ (vRel maxApp f refs code) xs ys := by
  obtain ⟨decode, related⟩ := premises
  have sourceEq := ClosSem.listToValue_valueToList source xs decode
  rw [← sourceEq] at related
  exact valueToList_related xs target related

/-- Flapjack inversion for small target tags: closure-specific tags cannot
occur, so related fields come from a source block with the same tag. -/
private theorem related_target_smallBlock {maxApp : Nat} {f : HolFiniteMapExact Nat Nat}
    {refs : HolFiniteMapExact Nat (BvlSem.Ref BvlSem.Value)} {code : Spt (Nat × Bvl.Exp)}
    (tag : Nat) (small : tag < 30) (fields : List BvlSem.Value) (source : ClosSem.Value)
    (related : vRel maxApp f refs code source (.block tag fields)) :
    ∃ xs, source = .block tag xs ∧ List.Forall₂ (vRel maxApp f refs code) xs fields := by
  cases related with
  | @block actualTag xs ys related =>
    have eq : closTagShift actualTag = actualTag := by
      by_cases low : actualTag < 30
      · simp [closTagShift, low]
      · have impossible : actualTag + 2 < 30 := by simpa [closTagShift, low] using small
        omega
    exact ⟨xs, by rw [eq], related⟩
  | closure _ _ => omega
  | partialClosure _ _ _ _ _ _ _ _ => omega

/-- Flapjack reverse list-decoding support: a related encoded BVL list has a
source list with pointwise related elements. HOL unfolds the relation in its
byte- and word-decoding proofs. -/
theorem valueToList_related_reverse {maxApp : Nat} {f : HolFiniteMapExact Nat Nat}
    {refs : HolFiniteMapExact Nat (BvlSem.Ref BvlSem.Value)} {code : Spt (Nat × Bvl.Exp)}
    (ys : List BvlSem.Value) (source : ClosSem.Value)
    (related : vRel maxApp f refs code source (BvlSem.listToValue ys)) :
    ∃ xs, ClosSem.valueToList source = some xs ∧ List.Forall₂ (vRel maxApp f refs code) xs ys := by
  induction ys generalizing source with
  | nil =>
    obtain ⟨xs, rfl, fields⟩ := related_target_smallBlock nilTag (by decide) [] source
      (by simpa [BvlSem.listToValue] using related)
    cases fields
    exact ⟨[], by simp [ClosSem.valueToList], .nil⟩
  | cons y ys ih =>
    obtain ⟨xs, rfl, fields⟩ := related_target_smallBlock consTag (by decide) [y, BvlSem.listToValue ys] source
      (by simpa [BvlSem.listToValue] using related)
    cases fields with
    | cons head fields =>
      cases fields with
      | cons tail fields =>
        cases fields
        obtain ⟨xs, decoded, rel⟩ := ih _ tail
        exact ⟨_ :: xs, by simp [ClosSem.valueToList, decoded], .cons head rel⟩

/-- List construction operations that retain the current state. -/
inductive BlockListOp where
  | fromList : Nat → BlockListOp
  | append : BlockListOp

/-- Closure operator for a list primitive. -/
def BlockListOp.op : BlockListOp → ClosLang.Op
  | .fromList tag => .blockOp (.fromList tag)
  | .append => .blockOp .listAppend

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
            obtain ⟨ys, targetDecode, listsRel⟩ := decodedList_related a xs _ ⟨decode, first⟩
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
                  obtain ⟨ys, targetA, firstRel⟩ := decodedList_related a xs _ ⟨decodeA, first⟩
                  obtain ⟨moreTarget, targetB, secondRel⟩ := decodedList_related b more _ ⟨decodeB, second⟩
                  simp [BlockListOp.op, ClosSem.doApp, ClosSem.applyBlock, decodeA, decodeB] at run
                  rcases run with ⟨rfl, rfl⟩
                  refine ⟨BvlSem.listToValue (ys ++ moreTarget), ?_, rfl, ?_⟩
                  · simp [BlockListOp.op, compileOp, BvlSem.doApp, BvlSem.applyBlock, targetA, targetB]
                  · exact listToValue_related (List.rel_append firstRel secondRel)
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
