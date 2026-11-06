import Flapjack.Compiler.Backend.ClosToBvl.Proofs.ByteOps
import Flapjack.Compiler.Backend.ClosToBvl.Proofs.MappedRefsUpdate

/-! Byte-copy correspondence for closure-to-BVL. -/
namespace Flapjack.Compiler.Backend.ClosToBvl
open Flapjack.SemanticPrimitivesHOL

/-- View either source representation accepted by byte-copy as its bytes. -/
def sourceByteView {C F : Type} (state : ClosSem.State C F) : ClosSem.Value → Option (List (BitVec 8))
  | .byteVector bytes => some bytes
  | .refPtr _ ptr => match state.refs.lookup ptr with
    | some (.byteArray bytes) => some bytes
    | _ => none
  | _ => none

/-- The byte-copy source representation is matched by a target byte-array
reference, whether the source is immutable or mutable. -/
theorem sourceByteView_related {C F : Type} {f : HolFiniteMapExact Nat Nat}
    (s : ClosSem.State C F) (t : BvlSem.State C F) (states : stateRel f s t)
    (source : ClosSem.Value) (target : BvlSem.Value)
    (related : vRel s.maxApp f t.refs t.code source target)
    (bytes : List (BitVec 8)) (view : sourceByteView s source = some bytes) :
    ∃ flag ptr frozen, target = .refPtr flag ptr ∧ t.refs.lookup ptr = some (.byteArray frozen bytes) := by
  cases source with
  | byteVector data =>
    simp [sourceByteView] at view
    subst bytes
    obtain ⟨ptr, rfl, found⟩ := vRel_byteVector_inv related
    exact ⟨true, ptr, true, rfl, found⟩
  | refPtr flag ptr =>
    obtain ⟨targetPtr, rfl, mapped⟩ := vRel_refPtr_inv related
    cases found : s.refs.lookup ptr with
    | none => simp [sourceByteView, found] at view
    | some cell =>
      cases cell with
      | valueArray values => simp [sourceByteView, found] at view
      | thunk mode value => simp [sourceByteView, found] at view
      | byteArray data =>
        simp [sourceByteView, found] at view
        subst bytes
        exact ⟨flag, targetPtr, false, rfl, stateRel_bytes_lookup states ptr targetPtr data mapped found⟩
  | _ => simp [sourceByteView] at view

/-- Source byte-copy-to-vector factors through the source byte view. -/
theorem copyByteNew_source {C F : Type} (s : ClosSem.State C F)
    (source : ClosSem.Value) (offset length : Int) :
    ClosSem.applyMemory (.copyByte true) [source, .number offset, .number length] s =
      (sourceByteView s source).bind (fun bytes =>
        (copyArray (bytes, offset) length none).bind (fun result => some (.byteVector result, s))) := by
  cases source <;> simp [ClosSem.applyMemory, sourceByteView]
  case refPtr flag ptr =>
    cases found : s.refs.lookup ptr <;> simp
    case some cell => cases cell <;> simp

/-- Successful copy-to-vector uses exactly one readable source and a valid
copy range. -/
theorem copyByteNew_success {C F : Type} (args : List ClosSem.Value)
    (s next : ClosSem.State C F) (value : ClosSem.Value)
    (run : ClosSem.doApp (.memOp (.copyByte true)) args s = .val (value, next)) :
    ∃ (source : ClosSem.Value) (offset length : Int) (bytes result : List (BitVec 8)),
      args = [source, .number offset, .number length] ∧ sourceByteView s source = some bytes ∧
      copyArray (bytes, offset) length none = some result ∧ value = .byteVector result ∧ next = s := by
  cases args with
  | nil => simp [ClosSem.doApp, ClosSem.applyMemory] at run
  | cons first rest =>
    cases rest with
    | nil => simp [ClosSem.doApp, ClosSem.applyMemory] at run
    | cons second rest =>
      cases rest with
      | nil => simp [ClosSem.doApp, ClosSem.applyMemory] at run
      | cons third rest =>
        cases rest with
        | cons fourth rest => simp [ClosSem.doApp, ClosSem.applyMemory] at run
        | nil =>
          cases second <;> cases third <;> simp only [ClosSem.doApp] at run
          all_goals try (simp [ClosSem.applyMemory] at run; done)
          case number.number offset length =>
            rw [copyByteNew_source] at run
            cases view : sourceByteView s first with
            | none => simp [view] at run
            | some bytes =>
              cases copied : copyArray (bytes, offset) length none with
              | none => simp [view, copied] at run
              | some result =>
                simp [view, copied] at run
                exact ⟨first, offset, length, bytes, result, rfl, view, copied, run.1.symm, run.2.symm⟩

/-- Copying a readable source to a fresh vector preserves the state relation
and target-only reference frame. -/
theorem copyByteNew_dispatch {C F : Type} {f : HolFiniteMapExact Nat Nat}
    (args : List ClosSem.Value) (targets : List BvlSem.Value)
    (s next : ClosSem.State C F) (t : BvlSem.State C F) (states : stateRel f s t)
    (related : List.Forall₂ (vRel s.maxApp f t.refs t.code) args targets)
    (value : ClosSem.Value) (run : ClosSem.doApp (.memOp (.copyByte true)) args s = .val (value, next)) :
    ∃ target targetNext,
      BvlSem.doApp (.memOp (.copyByte true)) targets t = .val (target, targetNext) ∧ next = s ∧
      vRel s.maxApp f targetNext.refs targetNext.code value target ∧ stateRel f s targetNext ∧
      unmappedRefsSubmap t.refs targetNext.refs f f ∧ targetNext.clock = t.clock := by
  obtain ⟨source, offset, length, bytes, result, rfl, view, copied, rfl, stateEq⟩ :=
    copyByteNew_success args s next value run
  subst next
  cases related with
  | cons sourceRel tail =>
    cases tail with
    | cons offsetRel tail =>
      cases tail with
      | cons lengthRel tail =>
        cases tail
        obtain ⟨flag, ptr, frozen, rfl, found⟩ := sourceByteView_related s t states source _ sourceRel bytes view
        have offsetEq := vRel_number_inv offsetRel
        have lengthEq := vRel_number_inv lengthRel
        subst_vars
        let newPtr := BvlSem.leastUnusedRef t.refs
        let targetNext := { t with refs := t.refs.updateEq (newPtr, .byteArray true result) }
        have fresh := stateRel_targetRefs_allocate s t f (.byteArray true result) states
        change stateRel f s targetNext ∧ unmappedRefsSubmap t.refs targetNext.refs f f ∧
          (¬ ∃ sourcePtr, f.lookup sourcePtr = some newPtr) ∧ targetNext.refs.lookup newPtr = some (.byteArray true result) at fresh
        refine ⟨.refPtr true newPtr, targetNext, ?_, rfl, .byteVector fresh.2.2.2 fresh.2.2.1, fresh.1, fresh.2.1, rfl⟩
        simp [BvlSem.doApp, BvlSem.applyMemory, found, copied, newPtr, targetNext]

/-- Failed copy-to-vector reports a source type error. -/
theorem copyByteNew_error {C F : Type} (args : List ClosSem.Value)
    (s : ClosSem.State C F) (error : ErrorResult ClosSem.Value)
    (run : ClosSem.doApp (.memOp (.copyByte true)) args s = .err error) : error = .abort .typeError := by
  simp only [ClosSem.doApp] at run
  cases h : ClosSem.applyMemory (.copyByte true) args s <;> simp [h] at run
  exact run.symm

/-- Source byte-copy into a mutable destination factors through the same
source view, including the case where the two pointers alias. -/
theorem copyByteInto_source {C F : Type} (s : ClosSem.State C F)
    (source : ClosSem.Value) (offset length : Int) (flag : Bool) (dst : Nat) (dstOffset : Int) :
    ClosSem.applyMemory (.copyByte false)
        [source, .number offset, .number length, .refPtr flag dst, .number dstOffset] s =
      (sourceByteView s source).bind (fun bytes =>
        (s.refs.lookup dst).bind (fun cell => match cell with
          | .byteArray old => (copyArray (bytes, offset) length (some (old, dstOffset))).bind
              (fun result => some (ClosSem.unitValue, { s with refs := s.refs.updateEq (dst, .byteArray result) }))
          | _ => none)) := by
  cases source <;> simp [ClosSem.applyMemory, sourceByteView]
  all_goals try (cases h : s.refs.lookup dst <;> simp; case some cell => cases cell <;> simp)
  case refPtr flag ptr =>
    cases found : s.refs.lookup ptr <;> simp
    case some cell =>
      cases cell <;> simp
      case byteArray bytes =>
        cases h : s.refs.lookup dst <;> simp
        case some cell => cases cell <;> simp

/-- Copying bytes into a mapped mutable destination preserves the state
relation. The source and destination may denote the same byte array. -/
theorem doApp_copyByteInto_related {C F : Type} {f : HolFiniteMapExact Nat Nat}
    (s : ClosSem.State C F) (t : BvlSem.State C F) (states : stateRel f s t)
    (source : ClosSem.Value) (targetSource : BvlSem.Value)
    (sourceRel : vRel s.maxApp f t.refs t.code source targetSource)
    (offset length dstOffset : Int) (flag : Bool) (dst targetDst : Nat)
    (mapped : f.lookup dst = some targetDst) (bytes old result : List (BitVec 8))
    (view : sourceByteView s source = some bytes) (found : s.refs.lookup dst = some (.byteArray old))
    (copied : copyArray (bytes, offset) length (some (old, dstOffset)) = some result) :
    ∃ targetNext,
      BvlSem.doApp (.memOp (.copyByte false))
        [targetSource, .number offset, .number length, .refPtr flag targetDst, .number dstOffset] t =
        .val (BvlSem.unitValue, targetNext) ∧
      stateRel f { s with refs := s.refs.updateEq (dst, .byteArray result) } targetNext ∧
      vRel s.maxApp f targetNext.refs targetNext.code ClosSem.unitValue BvlSem.unitValue ∧
      unmappedRefsSubmap t.refs targetNext.refs f f ∧ targetNext.clock = t.clock := by
  obtain ⟨srcFlag, srcPtr, frozen, rfl, sourceFound⟩ := sourceByteView_related s t states source targetSource sourceRel bytes view
  have dstFound := stateRel_bytes_lookup states dst targetDst old mapped found
  let targetNext := { t with refs := t.refs.updateEq (targetDst, .byteArray false result) }
  refine ⟨targetNext, ?_, ?_, .block .nil, mappedUpdate_frame f t.refs dst targetDst mapped _, rfl⟩
  · simp [BvlSem.doApp, BvlSem.applyMemory, sourceFound, dstFound, copied, targetNext]
  · exact stateRel_update_mapped s t f dst targetDst _ _ states mapped (by simp) ⟨rfl, rfl⟩

/-- A successful in-place copy has a readable source, mutable destination,
and valid copy range. -/
theorem copyByteInto_success {C F : Type} (args : List ClosSem.Value)
    (s next : ClosSem.State C F) (value : ClosSem.Value)
    (run : ClosSem.doApp (.memOp (.copyByte false)) args s = .val (value, next)) :
    ∃ (source : ClosSem.Value) (offset length dstOffset : Int) (flag : Bool) (dst : Nat)
      (bytes old result : List (BitVec 8)),
      args = [source, .number offset, .number length, .refPtr flag dst, .number dstOffset] ∧
      sourceByteView s source = some bytes ∧ s.refs.lookup dst = some (.byteArray old) ∧
      copyArray (bytes, offset) length (some (old, dstOffset)) = some result ∧
      value = ClosSem.unitValue ∧ next = { s with refs := s.refs.updateEq (dst, .byteArray result) } := by
  cases args with
  | nil => simp [ClosSem.doApp, ClosSem.applyMemory] at run
  | cons first rest =>
    cases rest with
    | nil => simp [ClosSem.doApp, ClosSem.applyMemory] at run
    | cons second rest =>
      cases rest with
      | nil => simp [ClosSem.doApp, ClosSem.applyMemory] at run
      | cons third rest =>
        cases rest with
        | nil => simp [ClosSem.doApp, ClosSem.applyMemory] at run
        | cons fourth rest =>
          cases rest with
          | nil => simp [ClosSem.doApp, ClosSem.applyMemory] at run
          | cons fifth rest =>
            cases rest with
            | cons sixth rest => simp [ClosSem.doApp, ClosSem.applyMemory] at run
            | nil =>
              cases second <;> try (cases first <;> simp [ClosSem.doApp, ClosSem.applyMemory] at run; done)
              case number offset =>
                cases third <;> try (cases first <;> simp [ClosSem.doApp, ClosSem.applyMemory] at run; done)
                case number length =>
                  cases fourth <;> try (cases first <;> simp [ClosSem.doApp, ClosSem.applyMemory] at run; done)
                  case refPtr flag dst =>
                    cases fifth <;> try (cases first <;> simp [ClosSem.doApp, ClosSem.applyMemory] at run; done)
                    case number dstOffset =>
                      simp only [ClosSem.doApp] at run
                      rw [copyByteInto_source] at run
                      cases view : sourceByteView s first with
                      | none => simp [view] at run
                      | some bytes =>
                        cases found : s.refs.lookup dst with
                        | none => simp [view, found] at run
                        | some cell =>
                          cases cell with
                          | valueArray values => simp [view, found] at run
                          | thunk mode value => simp [view, found] at run
                          | byteArray old =>
                            cases copied : copyArray (bytes, offset) length (some (old, dstOffset)) with
                            | none => simp [view, found, copied] at run
                            | some result =>
                              simp [view, found, copied] at run
                              exact ⟨first, offset, length, dstOffset, flag, dst, bytes, old, result,
                                rfl, view, found, copied, run.1.symm, run.2.symm⟩

/-- Failed in-place copy reports a source type error. -/
theorem copyByteInto_error {C F : Type} (args : List ClosSem.Value)
    (s : ClosSem.State C F) (error : ErrorResult ClosSem.Value)
    (run : ClosSem.doApp (.memOp (.copyByte false)) args s = .err error) : error = .abort .typeError := by
  simp only [ClosSem.doApp] at run
  cases h : ClosSem.applyMemory (.copyByte false) args s <;> simp [h] at run
  exact run.symm

end Flapjack.Compiler.Backend.ClosToBvl
