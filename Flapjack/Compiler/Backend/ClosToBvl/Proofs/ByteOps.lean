import Flapjack.Compiler.Backend.ClosToBvl.Proofs.BlockList
import Flapjack.Compiler.Backend.ClosToBvl.Proofs.BlockCompare

/-! Byte-vector list conversion and comparison. -/
namespace Flapjack.Compiler.Backend.ClosToBvl
open Flapjack.SemanticPrimitivesHOL

/-- Byte numbers are related pointwise on source and target. -/
theorem byteNumbers_related {maxApp : Nat} {f : HolFiniteMapExact Nat Nat}
    {refs : HolFiniteMapExact Nat (BvlSem.Ref BvlSem.Value)} {code : Spt (Nat × Bvl.Exp)}
    (bytes : List (BitVec 8)) :
    List.Forall₂ (vRel maxApp f refs code)
      (bytes.map (fun b => .number b.toNat)) (bytes.map (fun b => .number b.toNat)) := by
  induction bytes with
  | nil => exact .nil
  | cons byte rest ih => exact .cons (.number _) ih

/-- A successful byte-vector-to-list conversion produces related list values. -/
theorem byteToList_dispatch {C F : Type} {f : HolFiniteMapExact Nat Nat}
    (args : List ClosSem.Value) (targets : List BvlSem.Value)
    (s next : ClosSem.State C F) (t : BvlSem.State C F)
    (related : List.Forall₂ (vRel s.maxApp f t.refs t.code) args targets)
    (value : ClosSem.Value) (run : ClosSem.doApp (.memOp .toListByte) args s = .val (value, next)) :
    ∃ target, BvlSem.doApp (.memOp .toListByte) targets t = .val (target, t) ∧
      next = s ∧ vRel s.maxApp f t.refs t.code value target := by
  cases args with
  | nil => simp [ClosSem.doApp, ClosSem.applyMemory] at run
  | cons first rest =>
    cases rest with
    | cons second rest => simp [ClosSem.doApp, ClosSem.applyMemory] at run
    | nil =>
      cases first <;> simp only [ClosSem.doApp, ClosSem.applyMemory] at run
      all_goals try contradiction
      case byteVector bytes =>
        simp at run
        rcases run with ⟨rfl, rfl⟩
        cases related with
        | cons head tail =>
          cases tail
          obtain ⟨ptr, rfl, found⟩ := vRel_byteVector_inv head
          refine ⟨BvlSem.listToValue (bytes.map fun b => .number b.toNat), ?_, rfl,
            listToValue_related (byteNumbers_related bytes)⟩
          simp [BvlSem.doApp, BvlSem.applyMemory, found]

/-- Failed byte-vector-to-list conversion reports a source type error. -/
theorem byteToList_error {C F : Type} (args : List ClosSem.Value)
    (s : ClosSem.State C F) (error : ErrorResult ClosSem.Value)
    (run : ClosSem.doApp (.memOp .toListByte) args s = .err error) : error = .abort .typeError := by
  simp only [ClosSem.doApp] at run
  cases h : ClosSem.applyMemory .toListByte args s <;> simp [h] at run
  exact run.symm

/-- Related byte vectors compare identically on source and target. -/
theorem byteStringCmp_dispatch {C F : Type} {f : HolFiniteMapExact Nat Nat}
    (fast : Bool) (op : Flapjack.Opb) (args : List ClosSem.Value) (targets : List BvlSem.Value)
    (s next : ClosSem.State C F) (t : BvlSem.State C F)
    (related : List.Forall₂ (vRel s.maxApp f t.refs t.code) args targets)
    (value : ClosSem.Value) (run : ClosSem.doApp (.memOp (.stringCmp fast op)) args s = .val (value, next)) :
    ∃ target, BvlSem.doApp (.memOp (.stringCmp fast op)) targets t = .val (target, t) ∧
      next = s ∧ vRel s.maxApp f t.refs t.code value target := by
  cases args with
  | nil => simp [ClosSem.doApp, ClosSem.applyMemory] at run
  | cons first rest =>
    cases rest with
    | nil => simp [ClosSem.doApp, ClosSem.applyMemory] at run
    | cons second rest =>
      cases rest with
      | cons third rest => simp [ClosSem.doApp, ClosSem.applyMemory] at run
      | nil =>
        cases first <;> cases second <;> simp only [ClosSem.doApp, ClosSem.applyMemory] at run
        all_goals try contradiction
        case byteVector.byteVector firstBytes secondBytes =>
          simp at run
          rcases run with ⟨rfl, rfl⟩
          cases related with
          | cons firstRel tail =>
            cases tail with
            | cons secondRel tail =>
              cases tail
              obtain ⟨firstPtr, rfl, firstFound⟩ := vRel_byteVector_inv firstRel
              obtain ⟨secondPtr, rfl, secondFound⟩ := vRel_byteVector_inv secondRel
              refine ⟨BvlSem.boolValue (strCmp fast op (.implode firstBytes) (.implode secondBytes)), ?_, rfl, vRel_bool _⟩
              simp [BvlSem.doApp, BvlSem.applyMemory, firstFound, secondFound]

/-- Failed string comparison reports a source type error. -/
theorem byteStringCmp_error {C F : Type} (fast : Bool) (op : Flapjack.Opb) (args : List ClosSem.Value)
    (s : ClosSem.State C F) (error : ErrorResult ClosSem.Value)
    (run : ClosSem.doApp (.memOp (.stringCmp fast op)) args s = .err error) : error = .abort .typeError := by
  simp only [ClosSem.doApp] at run
  cases h : ClosSem.applyMemory (.stringCmp fast op) args s <;> simp [h] at run
  exact run.symm

end Flapjack.Compiler.Backend.ClosToBvl
