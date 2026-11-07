import Flapjack.Compiler.Backend.ClosToBvl.Proofs.BlockList
import Flapjack.Compiler.Backend.ClosToBvl.Proofs.BlockCompare
import Flapjack.Compiler.Backend.ClosToBvl.Proofs.FreshTargetRefs

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

/-- Successful source numeric-byte decoding is reproduced by the related
target list. -/
theorem byteNumbers_decode_related {maxApp : Nat} {f : HolFiniteMapExact Nat Nat}
    {refs : HolFiniteMapExact Nat (BvlSem.Ref BvlSem.Value)} {code : Spt (Nat × Bvl.Exp)}
    {source : List ClosSem.Value} {target : List BvlSem.Value}
    (related : List.Forall₂ (vRel maxApp f refs code) source target)
    (bytes : List (BitVec 8)) (decoded : ClosSem.byteNumbers source = some bytes) :
    BvlSem.byteNumbers target = some bytes := by
  induction related generalizing bytes with
  | nil => simpa [ClosSem.byteNumbers, BvlSem.byteNumbers] using decoded.symm
  | @cons first targetFirst rest targetRest head tail ih =>
    cases first <;> simp only [ClosSem.byteNumbers] at decoded
    all_goals try contradiction
    case number n =>
      have targetEq := vRel_number_inv head
      subst targetFirst
      cases byteRun : ClosSem.intToByte n with
      | none => simp [byteRun] at decoded
      | some byte =>
        cases restRun : ClosSem.byteNumbers rest with
        | none => simp [byteRun, restRun] at decoded
        | some restBytes =>
          simp [byteRun, restRun] at decoded
          subst bytes
          have targetRun := ih restBytes restRun
          simp [BvlSem.byteNumbers, byteRun, targetRun]

/-- Source byte-vector lists decode to the same sequence of target frozen
byte arrays. -/
theorem byteVectors_decode_related {maxApp : Nat} {f : HolFiniteMapExact Nat Nat}
    {refs : HolFiniteMapExact Nat (BvlSem.Ref BvlSem.Value)} {code : Spt (Nat × Bvl.Exp)}
    {source : List ClosSem.Value} {target : List BvlSem.Value}
    (related : List.Forall₂ (vRel maxApp f refs code) source target)
    (chunks : List (List (BitVec 8))) (decoded : ClosSem.byteVectors source = some chunks) :
    BvlSem.byteArrays refs target = some chunks := by
  induction related generalizing chunks with
  | nil => simpa [ClosSem.byteVectors, BvlSem.byteArrays] using decoded.symm
  | @cons first targetFirst rest targetRest head tail ih =>
    cases first <;> simp only [ClosSem.byteVectors] at decoded
    all_goals try contradiction
    case byteVector bytes =>
      obtain ⟨ptr, rfl, found⟩ := vRel_byteVector_inv head
      cases restRun : ClosSem.byteVectors rest with
      | none => simp [restRun] at decoded
      | some restChunks =>
        simp [restRun] at decoded
        subst chunks
        have targetRun := ih restChunks restRun
        simp [BvlSem.byteArrays, found, targetRun]

/-- Byte-vector constructors whose target operation allocates a frozen array. -/
inductive ByteConstruct where
  | fromList
  | concat

def ByteConstruct.op : ByteConstruct → ClosLang.MemOp
  | .fromList => .fromListByte
  | .concat => .concatByteVec

/-- Successful byte-vector construction has a corresponding BVL allocation
and preserves the candidate state relation and reference frame. -/
theorem byteConstruct_dispatch {C F : Type} {f : HolFiniteMapExact Nat Nat}
    (op : ByteConstruct) (args : List ClosSem.Value) (targets : List BvlSem.Value)
    (s next : ClosSem.State C F) (t : BvlSem.State C F) (states : stateRel f s t)
    (related : List.Forall₂ (vRel s.maxApp f t.refs t.code) args targets)
    (value : ClosSem.Value) (run : ClosSem.doApp (.memOp op.op) args s = .val (value, next)) :
    ∃ target targetNext,
      BvlSem.doApp (.memOp op.op) targets t = .val (target, targetNext) ∧ next = s ∧
      vRel s.maxApp f targetNext.refs targetNext.code value target ∧ stateRel f s targetNext ∧
      unmappedRefsSubmap t.refs targetNext.refs f f ∧ targetNext.clock = t.clock ∧ targetNext.code = t.code := by
  cases args with
  | nil => cases op <;> simp [ByteConstruct.op, ClosSem.doApp, ClosSem.applyMemory] at run
  | cons first rest =>
    cases rest with
    | cons second rest => cases op <;> simp [ByteConstruct.op, ClosSem.doApp, ClosSem.applyMemory] at run
    | nil =>
      cases related with
      | cons firstRel tail =>
        cases tail
        cases decoded : ClosSem.valueToList first with
        | none => cases op <;> simp [ByteConstruct.op, ClosSem.doApp, ClosSem.applyMemory, decoded] at run
        | some sourceValues =>
          obtain ⟨targetValues, targetDecoded, listsRel⟩ := decodedList_related first _ sourceValues firstRel decoded
          cases op with
          | fromList =>
            cases sourceBytes : ClosSem.byteNumbers sourceValues with
            | none => simp [ByteConstruct.op, ClosSem.doApp, ClosSem.applyMemory, decoded, sourceBytes] at run
            | some bytes =>
              have targetBytes := byteNumbers_decode_related listsRel bytes sourceBytes
              simp [ByteConstruct.op, ClosSem.doApp, ClosSem.applyMemory, decoded, sourceBytes] at run
              rcases run with ⟨rfl, rfl⟩
              let ptr := BvlSem.leastUnusedRef t.refs
              let targetNext := { t with refs := t.refs.updateEq (ptr, .byteArray true bytes) }
              have fresh := stateRel_targetRefs_allocate s t f (.byteArray true bytes) states
              change stateRel f s targetNext ∧ unmappedRefsSubmap t.refs targetNext.refs f f ∧
                (¬ ∃ sourcePtr, f.lookup sourcePtr = some ptr) ∧ targetNext.refs.lookup ptr = some (.byteArray true bytes) at fresh
              refine ⟨.refPtr true ptr, targetNext, ?_, rfl, .byteVector fresh.2.2.2 fresh.2.2.1, fresh.1, fresh.2.1, rfl, rfl⟩
              simp [ByteConstruct.op, BvlSem.doApp, BvlSem.applyMemory, targetDecoded, targetBytes, ptr, targetNext]
          | concat =>
            cases sourceChunks : ClosSem.byteVectors sourceValues with
            | none => simp [ByteConstruct.op, ClosSem.doApp, ClosSem.applyMemory, decoded, sourceChunks] at run
            | some chunks =>
              have targetChunks := byteVectors_decode_related listsRel chunks sourceChunks
              simp [ByteConstruct.op, ClosSem.doApp, ClosSem.applyMemory, decoded, sourceChunks] at run
              rcases run with ⟨rfl, rfl⟩
              let ptr := BvlSem.leastUnusedRef t.refs
              let targetNext := { t with refs := t.refs.updateEq (ptr, .byteArray true chunks.flatten) }
              have fresh := stateRel_targetRefs_allocate s t f (.byteArray true chunks.flatten) states
              change stateRel f s targetNext ∧ unmappedRefsSubmap t.refs targetNext.refs f f ∧
                (¬ ∃ sourcePtr, f.lookup sourcePtr = some ptr) ∧ targetNext.refs.lookup ptr = some (.byteArray true chunks.flatten) at fresh
              refine ⟨.refPtr true ptr, targetNext, ?_, rfl, .byteVector fresh.2.2.2 fresh.2.2.1, fresh.1, fresh.2.1, rfl, rfl⟩
              simp [ByteConstruct.op, BvlSem.doApp, BvlSem.applyMemory, targetDecoded, targetChunks, ptr, targetNext]

/-- A failed byte-vector construction reports a source type error. -/
theorem byteConstruct_error {C F : Type} (op : ByteConstruct) (args : List ClosSem.Value)
    (s : ClosSem.State C F) (error : ErrorResult ClosSem.Value)
    (run : ClosSem.doApp (.memOp op.op) args s = .err error) : error = .abort .typeError := by
  simp only [ClosSem.doApp] at run
  cases h : ClosSem.applyMemory op.op args s <;> simp [h] at run
  exact run.symm

end Flapjack.Compiler.Backend.ClosToBvl
