import Flapjack.Compiler.Backend.StackRemove.Proofs.CompCorrect.ShMemOp
import Flapjack.Compiler.Backend.StackRemove.Proofs.BytearrayReads
import Flapjack.Compiler.Backend.StackRemove.Proofs.WriteBytearrayFrame
import Flapjack.Compiler.Backend.StackRemove

namespace Flapjack.Compiler.Backend.StackRemove.CompCorrect.FFI
open Flapjack Compiler.Backend.StackLang StackSemEvaluate StackSemStateOps

/-- Flapjack-specific factoring of the returning FFI case; no independent HOL
declaration is claimed. The original relation supplies every saved reserved
register and the separated memory frame. Only the actual successful read
needed by the original bytearray frame theorem is required. -/
theorem stateRelFfiWriteback {width : Nat} [NeZero width] {C F : Type}
    (jump : Bool) (bounds : BitVec width × BitVec width) (pointer : Nat)
    (source target : StackSemStateFiniteExact width C F)
    (address : BitVec width) (bytes readBytes : List (BitVec 8)) (ffi : HolFfiState F)
    (relation : stateRelHOL jump bounds pointer source target)
    (read : readBytearrayWordHOL address bytes.length
      (memLoadByteAuxExact source.memory source.mdomain source.be) = some readBytes) :
    stateRelHOL jump bounds pointer
      {source with
        memory := writeBytearrayExact address bytes source.memory source.mdomain source.be
        regs := restrictIn source.regs source.ffiSaveRegs
        fpRegs := HolFiniteMapExact.empty
        ffi := ffi}
      {target with
        memory := writeBytearrayExact address bytes target.memory target.mdomain target.be
        regs := restrictIn target.regs target.ffiSaveRegs
        fpRegs := HolFiniteMapExact.empty
        ffi := ffi} := by
  simp only [stateRelHOL] at relation
  rcases relation with ⟨h0,h1,h2,h3,h4,h5,h6,h7,h8,h9,h10,h11,h12,h13,h14,h15,h16,h17,h18,h19,h20,h21,h22,h23,h24,h25⟩
  have registers : ∀ register, register < pointer →
      (restrictIn target.regs target.ffiSaveRegs).lookup register =
      (restrictIn source.regs source.ffiSaveRegs).lookup register := by
    intro register below
    simp only [restrictIn_lookup, h10, h18 register below]
  have heapSave := h22 (pointer + 2) (Or.inr (Or.inr rfl))
  have baseSave := h22 (pointer + 1) (Or.inr (Or.inl rfl))
  have pointerSave := h22 pointer (Or.inl rfl)
  simp only [stateRelHOL, restrictIn_lookup, heapSave, baseSave, pointerSave, ite_true]
  refine ⟨h0,h1,h2,h3,h4,h5,h6,h7,h8,True.intro,h10,True.intro,h12,h13,h14,h15,h16,h17,registers,h19,h20,h21,h22,h23,h24,?_⟩
  cases baseRead : target.regs.lookup (pointer + 1) with
  | none => simp [baseRead] at h25
  | some value =>
    cases value with
    | loc block offset => simp [baseRead] at h25
    | word base =>
      simp only [baseRead] at h25 ⊢
      refine ⟨h25.1,h25.2.1,h25.2.2.1,h25.2.2.2.1,?_⟩
      simp only [← SetSep.starAssoc] at h25 ⊢
      have updated := writeBytearrayFrame bytes address source.memory source.mdomain source.be readBytes
        _ target.memory target.mdomain ⟨h25.2.2.2.2, read⟩
      simpa only [h6] using updated

/-- Canonical owning-state roundtrip for the representation qualifier;
Flapjack infrastructure with no independent HOL declaration. -/
theorem holFmapAsFiniteSupportRelationWitness_StackSemStateFiniteExact
    {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : StackSemStateBroad width C F) (h : state.FiniteSupport),
      (StackSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : StackSemStateFiniteExact width C F,
      StackSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  StackSemStateSupport.holFmapAsFiniteSupportWitness

/-- Full original FFI case (2081–2098), with the original four premises,
actual mlstring identifier, native evaluator and FFI result. Byte reads and
framed writeback on the target are proved from the original relation. -/
@[hol "cakeml/compiler/backend/proofs/stack_removeProofScript.sml" "comp_correct"
  (fmap_as_finite_support_relation := [StackSemStateFiniteExact.regs,
    StackSemStateFiniteExact.fpRegs, StackSemStateFiniteExact.store])
  (words_as_type_indexed_bitvec)]
theorem compCorrectFFI {width : Nat} [NeZero width] {C F : Type}
    (name : Basis.Pure.MlString.MlString) (ptr len ptr2 len2 ret : Nat)
    (source : StackSemStateFiniteExact width C F) (result : Option (StackSemResult width))
    (postSource target : StackSemStateFiniteExact width C F)
    (pointer : Nat) (bounds : BitVec width × BitVec width) (jump : Bool)
    (hypothesis : evaluate (.ffi name ptr len ptr2 len2 ret, source) = (result, postSource) ∧
      result ≠ some .error ∧ stateRelHOL jump bounds pointer source target ∧
      StackProps.regBound (.ffi name ptr len ptr2 len2 ret : HolProg width) pointer) :
    ∃ clock postTarget,
      evaluate (comp jump bounds pointer (.ffi name ptr len ptr2 len2 ret),
        {target with clock := clock + target.clock}) = (result, postTarget) ∧
      (match result with
       | some (.halt _) | some .timeOut | some (.finalFFI _) => postTarget.ffi = postSource.ffi
       | _ => stateRelHOL jump bounds pointer postSource postTarget) := by
  rcases hypothesis with ⟨sourceRun, notError, relation, bound⟩
  change ptr < pointer ∧ len < pointer ∧ ptr2 < pointer ∧ len2 < pointer ∧ ret < pointer at bound
  have ptrEq := RelationLaws.stateRelGetVar jump bounds pointer ptr source target ⟨relation,bound.1⟩
  have lenEq := RelationLaws.stateRelGetVar jump bounds pointer len source target ⟨relation,bound.2.1⟩
  have ptr2Eq := RelationLaws.stateRelGetVar jump bounds pointer ptr2 source target ⟨relation,bound.2.2.1⟩
  have len2Eq := RelationLaws.stateRelGetVar jump bounds pointer len2 source target ⟨relation,bound.2.2.2.1⟩
  have ffiEq : target.ffi = source.ffi :=
    (RelationLaws.stateRelConst jump bounds pointer source target relation).2.2.2.2.1
  rw [evaluate_ffi] at sourceRun
  cases readLen : getVar len source with
  | none =>
    simp only [readLen] at sourceRun
    exact False.elim (notError (Prod.mk.inj sourceRun).1.symm)
  | some value =>
    cases value with
    | loc block offset =>
      simp only [readLen] at sourceRun
      exact False.elim (notError (Prod.mk.inj sourceRun).1.symm)
    | word length1 =>
      cases readPtr : getVar ptr source with
      | none =>
        simp only [readLen, readPtr] at sourceRun
        exact False.elim (notError (Prod.mk.inj sourceRun).1.symm)
      | some value =>
        cases value with
        | loc block offset =>
          simp only [readLen, readPtr] at sourceRun
          exact False.elim (notError (Prod.mk.inj sourceRun).1.symm)
        | word address1 =>
          cases readLen2 : getVar len2 source with
          | none =>
            simp only [readLen, readPtr, readLen2] at sourceRun
            exact False.elim (notError (Prod.mk.inj sourceRun).1.symm)
          | some value =>
            cases value with
            | loc block offset =>
              simp only [readLen, readPtr, readLen2] at sourceRun
              exact False.elim (notError (Prod.mk.inj sourceRun).1.symm)
            | word length2 =>
              cases readPtr2 : getVar ptr2 source with
              | none =>
                simp only [readLen, readPtr, readLen2, readPtr2] at sourceRun
                exact False.elim (notError (Prod.mk.inj sourceRun).1.symm)
              | some value =>
                cases value with
                | loc block offset =>
                  simp only [readLen, readPtr, readLen2, readPtr2] at sourceRun
                  exact False.elim (notError (Prod.mk.inj sourceRun).1.symm)
                | word address2 =>
                  simp only [readLen, readPtr, readLen2, readPtr2] at sourceRun
                  cases read1 : readBytearrayWordHOL address1 length1.toNat (memLoadByteAuxExact source.memory source.mdomain source.be) with
                  | none =>
                    simp only [read1] at sourceRun
                    exact False.elim (notError (Prod.mk.inj sourceRun).1.symm)
                  | some config =>
                    cases read2 : readBytearrayWordHOL address2 length2.toNat (memLoadByteAuxExact source.memory source.mdomain source.be) with
                    | none =>
                      simp only [read1,read2] at sourceRun
                      exact False.elim (notError (Prod.mk.inj sourceRun).1.symm)
                    | some bytes =>
                      have targetRead1 := BytearrayReads.readBytearrayImp jump bounds pointer length1.toNat address1 source target config ⟨relation,read1⟩
                      have targetRead2 := BytearrayReads.readBytearrayImp jump bounds pointer length2.toNat address2 source target bytes ⟨relation,read2⟩
                      simp only [read1,read2] at sourceRun
                      cases call : callFFIHOL source.ffi (.extCall name) config bytes with
                      | final outcome =>
                        simp only [call] at sourceRun
                        rcases Prod.mk.inj sourceRun with ⟨resultEq,postEq⟩
                        subst result
                        subst postSource
                        refine ⟨0,target,?_,ffiEq⟩
                        simpa only [comp,Nat.zero_add] using
                          (evaluate_ffi name ptr len ptr2 len2 ret target).trans (by
                            simp only [← lenEq,← ptrEq,← len2Eq,← ptr2Eq,readLen,readPtr,readLen2,readPtr2,targetRead1,targetRead2,ffiEq,call])
                      | ret newFfi newBytes =>
                        simp only [call] at sourceRun
                        rcases Prod.mk.inj sourceRun with ⟨resultEq,postEq⟩
                        subst result
                        subst postSource
                        have returnedLength := callFFILengthHOL source.ffi (.extCall name) config bytes newBytes newFfi call
                        have readLength := readBytearrayWordHOL_length address2 length2.toNat
                          (memLoadByteAuxExact source.memory source.mdomain source.be) bytes read2
                        have writeRead : readBytearrayWordHOL address2 newBytes.length
                            (memLoadByteAuxExact source.memory source.mdomain source.be) = some bytes := by
                          rw [returnedLength,readLength]
                          exact read2
                        refine ⟨0,{target with
                          memory := writeBytearrayExact address2 newBytes target.memory target.mdomain target.be
                          regs := restrictIn target.regs target.ffiSaveRegs
                          fpRegs := HolFiniteMapExact.empty
                          ffi := newFfi},?_,?_⟩
                        · simpa only [comp,Nat.zero_add] using
                            (evaluate_ffi name ptr len ptr2 len2 ret target).trans (by
                              simp only [← lenEq,← ptrEq,← len2Eq,← ptr2Eq,readLen,readPtr,readLen2,readPtr2,targetRead1,targetRead2,ffiEq,call])
                        · exact stateRelFfiWriteback jump bounds pointer source target address2 newBytes bytes newFfi relation writeRead

end Flapjack.Compiler.Backend.StackRemove.CompCorrect.FFI
