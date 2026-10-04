import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSASemanticControl
import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSAExpressions
import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSALocalsGetVar
import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSALocalsInsert

namespace Flapjack.Compiler.Backend.WordAlloc

namespace SemanticShareInstWitnesses

/-- Canonical roundtrip of the imported native finite-map state carrier. -/
theorem holFmapAsFiniteSupportRelationWitness_WordSemStateFiniteExact
    {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : WordSemStateBroad width C F) (h : state.FiniteSupport),
      (WordSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : WordSemStateFiniteExact width C F,
      WordSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  WordSemStateExact.holFmapAsFiniteSupportWitness

end SemanticShareInstWitnesses

/-- Full original ShareInst constructor simulation across all native shared
memory operators. Inherits evaluator reals_as_rational_cuts, SOUNDNESS item 8.
Source success, domain guards and oracle outcomes are proved
by evaluator cases; no target execution is assumed. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem ssaCcTransCorrectShareInst {width : Nat} [NeZero width] {C F : Type}
    (source target : WordSemStateFiniteExact width C F)
    (ssa : Spt Nat) (next name : Nat) (operator : WordMemOp)
    (expr : WordLangExpHOL (BitVec width))
    (tables : List (Spt Nat × Spt Unit × Spt Unit))
    (h : Flapjack.WordAlloc.wordStateEqRel source target ∧
      ssaLocalsRel next ssa source.locals target.locals ∧ isAllocVar next ∧
      everyVarHOL (fun key => decide (key < next)) (.shareInst operator name expr) = true ∧
      ssaMapOK next ssa ∧ ltOK tables) :
    ssaSimulation (.shareInst operator name expr) source target ssa next tables := by
  have bound : name < next := by
    have checked := h.2.2.2.1
    simp only [everyVarHOL,Bool.and_eq_true,decide_eq_true_eq] at checked
    exact checked.1
  let permuted := {source with permute := target.permute}
  have frame : Flapjack.WordAlloc.wordStateEqRel permuted target := by
    simpa [permuted,Flapjack.WordAlloc.wordStateEqRel] using h.1
  refine ⟨target.permute,?_⟩
  cases found : WordSemStateFiniteExact.wordExp permuted expr with
  | none => simp [WordSemStateFiniteExact.evaluate,permuted,found]
  | some value =>
    cases value with
    | loc p q => simp [WordSemStateFiniteExact.evaluate,permuted,found]
    | word address =>
      have targetExpr := ssaCcTransExpCorrect permuted expr target ssa next (.word address)
        ⟨found,frame,h.2.1⟩
      cases operator with
      | store =>
        cases read : WordSemStateFiniteExact.getVar name permuted with
        | none =>
          simp [WordSemStateFiniteExact.evaluate,permuted,found,
            WordSemStateFiniteExact.shareInst,read]
        | some value =>
          cases value with
          | loc p q =>
            simp [WordSemStateFiniteExact.evaluate,permuted,found,
              WordSemStateFiniteExact.shareInst,read]
          | word word =>
            have targetRead := ssaLocalsRelGetVar next ssa permuted target name (.word word)
              ⟨h.2.1,read⟩
            by_cases domain : permuted.shMdomain address
            · cases called : callFFIHOL permuted.ffi (.sharedMem .mappedWrite) [0]
                (panWordToBytesHOL word false ++ panWordToBytesHOL address false) <;>
                simp_all [WordSemStateFiniteExact.evaluate,ssaCcTrans,
                  WordSemStateFiniteExact.shareInst,WordSemStateFiniteExact.shMemStore,
                  WordSemStateFiniteExact.flushState,Flapjack.WordAlloc.wordStateEqRel,permuted]
            · simp_all [WordSemStateFiniteExact.evaluate,
                WordSemStateFiniteExact.shareInst,WordSemStateFiniteExact.shMemStore,
                Flapjack.WordAlloc.wordStateEqRel,permuted]
      | store8 =>
        cases read : WordSemStateFiniteExact.getVar name permuted with
        | none =>
          simp [WordSemStateFiniteExact.evaluate,permuted,found,
            WordSemStateFiniteExact.shareInst,read]
        | some value =>
          cases value with
          | loc p q =>
            simp [WordSemStateFiniteExact.evaluate,permuted,found,
              WordSemStateFiniteExact.shareInst,read]
          | word word =>
            have targetRead := ssaLocalsRelGetVar next ssa permuted target name (.word word)
              ⟨h.2.1,read⟩
            by_cases domain : permuted.shMdomain (riscvByteAlignHOL address)
            · cases called : callFFIHOL permuted.ffi (.sharedMem .mappedWrite) [1]
                ([getByteHOL8 0 word false] ++ panWordToBytesHOL address false) <;>
                simp_all [WordSemStateFiniteExact.evaluate,ssaCcTrans,
                  WordSemStateFiniteExact.shareInst,WordSemStateFiniteExact.shMemStoreByte,
                  WordSemStateFiniteExact.flushState,Flapjack.WordAlloc.wordStateEqRel,permuted]
            · simp_all [WordSemStateFiniteExact.evaluate,
                WordSemStateFiniteExact.shareInst,WordSemStateFiniteExact.shMemStoreByte,
                Flapjack.WordAlloc.wordStateEqRel,permuted]
      | store16 =>
        cases read : WordSemStateFiniteExact.getVar name permuted with
        | none =>
          simp [WordSemStateFiniteExact.evaluate,permuted,found,
            WordSemStateFiniteExact.shareInst,read]
        | some value =>
          cases value with
          | loc p q =>
            simp [WordSemStateFiniteExact.evaluate,permuted,found,
              WordSemStateFiniteExact.shareInst,read]
          | word word =>
            have targetRead := ssaLocalsRelGetVar next ssa permuted target name (.word word)
              ⟨h.2.1,read⟩
            by_cases domain : permuted.shMdomain (riscvByteAlignHOL address)
            · cases called : callFFIHOL permuted.ffi (.sharedMem .mappedWrite) [2]
                ((panWordToBytesHOL word false).take 2 ++ panWordToBytesHOL address false) <;>
                simp_all [WordSemStateFiniteExact.evaluate,ssaCcTrans,
                  WordSemStateFiniteExact.shareInst,WordSemStateFiniteExact.shMemStore16,
                  WordSemStateFiniteExact.flushState,Flapjack.WordAlloc.wordStateEqRel,permuted]
            · simp_all [WordSemStateFiniteExact.evaluate,
                WordSemStateFiniteExact.shareInst,WordSemStateFiniteExact.shMemStore16,
                Flapjack.WordAlloc.wordStateEqRel,permuted]
      | store32 =>
        cases read : WordSemStateFiniteExact.getVar name permuted with
        | none =>
          simp [WordSemStateFiniteExact.evaluate,permuted,found,
            WordSemStateFiniteExact.shareInst,read]
        | some value =>
          cases value with
          | loc p q =>
            simp [WordSemStateFiniteExact.evaluate,permuted,found,
              WordSemStateFiniteExact.shareInst,read]
          | word word =>
            have targetRead := ssaLocalsRelGetVar next ssa permuted target name (.word word)
              ⟨h.2.1,read⟩
            by_cases domain : permuted.shMdomain (riscvByteAlignHOL address)
            · cases called : callFFIHOL permuted.ffi (.sharedMem .mappedWrite) [4]
                ((panWordToBytesHOL word false).take 4 ++ panWordToBytesHOL address false) <;>
                simp_all [WordSemStateFiniteExact.evaluate,ssaCcTrans,
                  WordSemStateFiniteExact.shareInst,WordSemStateFiniteExact.shMemStore32,
                  WordSemStateFiniteExact.flushState,Flapjack.WordAlloc.wordStateEqRel,permuted]
            · simp_all [WordSemStateFiniteExact.evaluate,
                WordSemStateFiniteExact.shareInst,WordSemStateFiniteExact.shMemStore32,
                Flapjack.WordAlloc.wordStateEqRel,permuted]
      | load =>
        by_cases domain : permuted.shMdomain address
        · cases called : callFFIHOL permuted.ffi (.sharedMem .mappedRead) [0]
            (panWordToBytesHOL address false) with
          | final outcome =>
            simp_all [WordSemStateFiniteExact.evaluate,ssaCcTrans,nextVarRename,
              WordSemStateFiniteExact.shareInst,WordSemStateFiniteExact.shMemLoad,
              WordSemStateFiniteExact.shMemSetVar,WordSemStateFiniteExact.flushState,
              Flapjack.WordAlloc.wordStateEqRel,permuted]
          | ret newFfi newBytes =>
            have locals := ssaLocalsRelSetVar next ssa source.locals target.locals name
              (.word (panWordOfBytesHOL false 0 newBytes)) ⟨h.2.1,h.2.2.2.2.1,bound⟩
            simp_all [WordSemStateFiniteExact.evaluate,ssaCcTrans,nextVarRename,
              WordSemStateFiniteExact.shareInst,WordSemStateFiniteExact.shMemLoad,
              WordSemStateFiniteExact.shMemSetVar,WordSemStateFiniteExact.setVar,
              Flapjack.WordAlloc.wordStateEqRel,permuted]
        · simp_all [WordSemStateFiniteExact.evaluate,
            WordSemStateFiniteExact.shareInst,WordSemStateFiniteExact.shMemLoad,
            WordSemStateFiniteExact.shMemSetVar,Flapjack.WordAlloc.wordStateEqRel,permuted]
      | load8 =>
        by_cases domain : permuted.shMdomain (riscvByteAlignHOL address)
        · cases called : callFFIHOL permuted.ffi (.sharedMem .mappedRead) [1]
            (panWordToBytesHOL address false) with
          | final outcome =>
            simp_all [WordSemStateFiniteExact.evaluate,ssaCcTrans,nextVarRename,
              WordSemStateFiniteExact.shareInst,WordSemStateFiniteExact.shMemLoadByte,
              WordSemStateFiniteExact.shMemSetVar,WordSemStateFiniteExact.flushState,
              Flapjack.WordAlloc.wordStateEqRel,permuted]
          | ret newFfi newBytes =>
            have locals := ssaLocalsRelSetVar next ssa source.locals target.locals name
              (.word (panWordOfBytesHOL false 0 newBytes)) ⟨h.2.1,h.2.2.2.2.1,bound⟩
            simp_all [WordSemStateFiniteExact.evaluate,ssaCcTrans,nextVarRename,
              WordSemStateFiniteExact.shareInst,WordSemStateFiniteExact.shMemLoadByte,
              WordSemStateFiniteExact.shMemSetVar,WordSemStateFiniteExact.setVar,
              Flapjack.WordAlloc.wordStateEqRel,permuted]
        · simp_all [WordSemStateFiniteExact.evaluate,
            WordSemStateFiniteExact.shareInst,WordSemStateFiniteExact.shMemLoadByte,
            WordSemStateFiniteExact.shMemSetVar,Flapjack.WordAlloc.wordStateEqRel,permuted]
      | load16 =>
        by_cases domain : permuted.shMdomain (riscvByteAlignHOL address)
        · cases called : callFFIHOL permuted.ffi (.sharedMem .mappedRead) [2]
            (panWordToBytesHOL address false) with
          | final outcome =>
            simp_all [WordSemStateFiniteExact.evaluate,ssaCcTrans,nextVarRename,
              WordSemStateFiniteExact.shareInst,WordSemStateFiniteExact.shMemLoad16,
              WordSemStateFiniteExact.shMemSetVar,WordSemStateFiniteExact.flushState,
              Flapjack.WordAlloc.wordStateEqRel,permuted]
          | ret newFfi newBytes =>
            have locals := ssaLocalsRelSetVar next ssa source.locals target.locals name
              (.word (panWordOfBytesHOL false 0 newBytes)) ⟨h.2.1,h.2.2.2.2.1,bound⟩
            simp_all [WordSemStateFiniteExact.evaluate,ssaCcTrans,nextVarRename,
              WordSemStateFiniteExact.shareInst,WordSemStateFiniteExact.shMemLoad16,
              WordSemStateFiniteExact.shMemSetVar,WordSemStateFiniteExact.setVar,
              Flapjack.WordAlloc.wordStateEqRel,permuted]
        · simp_all [WordSemStateFiniteExact.evaluate,
            WordSemStateFiniteExact.shareInst,WordSemStateFiniteExact.shMemLoad16,
            WordSemStateFiniteExact.shMemSetVar,Flapjack.WordAlloc.wordStateEqRel,permuted]
      | load32 =>
        by_cases domain : permuted.shMdomain (riscvByteAlignHOL address)
        · cases called : callFFIHOL permuted.ffi (.sharedMem .mappedRead) [4]
            (panWordToBytesHOL address false) with
          | final outcome =>
            simp_all [WordSemStateFiniteExact.evaluate,ssaCcTrans,nextVarRename,
              WordSemStateFiniteExact.shareInst,WordSemStateFiniteExact.shMemLoad32,
              WordSemStateFiniteExact.shMemSetVar,WordSemStateFiniteExact.flushState,
              Flapjack.WordAlloc.wordStateEqRel,permuted]
          | ret newFfi newBytes =>
            have locals := ssaLocalsRelSetVar next ssa source.locals target.locals name
              (.word (panWordOfBytesHOL false 0 newBytes)) ⟨h.2.1,h.2.2.2.2.1,bound⟩
            simp_all [WordSemStateFiniteExact.evaluate,ssaCcTrans,nextVarRename,
              WordSemStateFiniteExact.shareInst,WordSemStateFiniteExact.shMemLoad32,
              WordSemStateFiniteExact.shMemSetVar,WordSemStateFiniteExact.setVar,
              Flapjack.WordAlloc.wordStateEqRel,permuted]
        · simp_all [WordSemStateFiniteExact.evaluate,
            WordSemStateFiniteExact.shareInst,WordSemStateFiniteExact.shMemLoad32,
            WordSemStateFiniteExact.shMemSetVar,Flapjack.WordAlloc.wordStateEqRel,permuted]

end Flapjack.Compiler.Backend.WordAlloc
