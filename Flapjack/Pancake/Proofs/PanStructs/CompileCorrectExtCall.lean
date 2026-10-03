import Flapjack.Pancake.Proofs.PanStructs.FlattenConversion
import Flapjack.Pancake.Proofs.PanStructs.CompileExpCorrectExact
import Flapjack.Pancake.Proofs.PanStructs.ValueShapeConversion
import Flapjack.Pancake.PanStructs.CompileProgExact
namespace Flapjack.Pancake.Proofs.PanStructs.CompileCorrectExtCall
open Flapjack
open Flapjack.Pancake.PanLang
open Flapjack.Pancake.PanStructs.CompileShapeExact
open Flapjack.Pancake.Proofs.PanStructs.ConvertState
open Flapjack.Pancake.Proofs.PanStructs.ShapeMap
open Flapjack.Pancake.Proofs.PanStructs.StructInfosOkExact

/-- Canonical imported state-carrier roundtrip for this representation qualifier.
Flapjack infrastructure, not an independent HOL declaration. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} {σ : Type} [NeZero width] :
    (∀ (state : PanSemStateExact width σ) (h : state.FiniteSupport),
      (PanSemStateFiniteExact.ofExact state h).toExact = state) ∧
    (∀ state : PanSemStateFiniteExact width σ,
      PanSemStateFiniteExact.ofExact state.toExact state.toExact_finiteSupport = state) :=
  PanSemStateFiniteExact.holFmapAsFiniteSupportWitness


/-- Full original ExtCall case: all ten premises/seven conclusions and no IH.
The four compiled word expressions and two byte-array reads use the original
source guards. Conversion preserves the memory, domain, endian and FFI state,
so both evaluations call the same FFI operation. Final clears locals; ret writes
returned bytes and changes FFI only. No target outcome or oracle premise is added. -/
@[hol "cakeml/pancake/proofs/pan_structsProofScript.sml" "compile_correct"
  (fmap_as_finite_support := [locals, globals, code, eshapes])
  (words_as_type_indexed_bitvec)]
theorem compileCorrectExtCall {width : Nat} {σ : Type} [NeZero width]
    (source post : PanSemStateFiniteExact width σ) (context : ContextExact)
    (function : MlS) (configuration configurationLength array arrayLength : ExpHOL width)
    (res : Option (PanSemResultExact width))
    (h : PanSemStateFiniteExact.evaluateHOLFiniteState source (.extCall function configuration configurationLength array arrayLength : ProgHOL width) = (res, post) ∧
      context.structs = source.structs.map (fun entry => (entry.1, entry.2.fields)) ∧
      feveryHOL (fun entry => valueFldsOkHOLExact source.structs entry.2) source.locals ∧
      feveryHOL (fun entry => valueFldsOkHOLExact source.structs entry.2) source.globals ∧
      feveryHOL (fun entry => isWfShapeValueHOLExact source.structs entry.2) source.locals ∧
      feveryHOL (fun entry => isWfShapeValueHOLExact source.structs entry.2) source.globals ∧
      structInfosOkHOLExact source.structs ∧
      shapeMap context.locals = source.locals.map2 (fun entry => shapeOfHOLExact entry.2) ∧
      shapeMap context.globals = source.globals.map2 (fun entry => shapeOfHOLExact entry.2) ∧
      res ≠ some .error) :
    PanSemStateFiniteExact.evaluateHOLFiniteState (convertStateExact context source)
      (compileProgExact context (.extCall function configuration configurationLength array arrayLength : ProgHOL width)) = (convertResHOL res, convertStateExact context post) ∧
    feveryHOL (fun entry => valueFldsOkHOLExact post.structs entry.2) post.locals ∧
    feveryHOL (fun entry => valueFldsOkHOLExact post.structs entry.2) post.globals ∧
    shapeMap context.globals = post.globals.map2 (fun entry => shapeOfHOLExact entry.2) ∧
    (isContResHOL res = true →
      shapeMap context.locals = post.locals.map2 (fun entry => shapeOfHOLExact entry.2)) ∧
    (∀ value ∈ resVsHOL res, valueFldsOkHOLExact post.structs value = true) ∧
    (∀ value ∈ resVsHOL res, isWfShapeValueHOLExact post.structs value = true) := by
  classical
  rcases h with ⟨heval,hstructs,hlocal,hglobal,hwlocal,hwglobal,hinfo,hlocals,hglobals,herror⟩
  rw [PanSemStateFiniteExact.evaluateHOLFiniteState_extCall_source] at heval
  simp only [PanSemStateFiniteExact.evalHOLFinite] at heval
  cases he1 : @evalHOLExact width σ _ source.toExact
      (fun a => Classical.propDecidable (source.memaddrs a)) configuration with
  | none =>
    simp only [he1,Prod.mk.injEq] at heval
    exact False.elim (herror heval.1.symm)
  | some value1 =>
    rw [he1] at heval
    cases value1 with
    | rStruct fields =>
      simp only [Prod.mk.injEq] at heval
      exact False.elim (herror heval.1.symm)
    | nStruct name fields =>
      simp only [Prod.mk.injEq] at heval
      exact False.elim (herror heval.1.symm)
    | val payload =>
      cases payload with
      | word address1 =>
        cases he2 : @evalHOLExact width σ _ source.toExact
            (fun a => Classical.propDecidable (source.memaddrs a)) configurationLength with
        | none =>
          simp only [he2,Prod.mk.injEq] at heval
          exact False.elim (herror heval.1.symm)
        | some value2 =>
          rw [he2] at heval
          cases value2 with
          | rStruct fields =>
            simp only [Prod.mk.injEq] at heval
            exact False.elim (herror heval.1.symm)
          | nStruct name fields =>
            simp only [Prod.mk.injEq] at heval
            exact False.elim (herror heval.1.symm)
          | val payload =>
            cases payload with
            | word length1 =>
              cases he3 : @evalHOLExact width σ _ source.toExact
                  (fun a => Classical.propDecidable (source.memaddrs a)) array with
              | none =>
                simp only [he3,Prod.mk.injEq] at heval
                exact False.elim (herror heval.1.symm)
              | some value3 =>
                rw [he3] at heval
                cases value3 with
                | rStruct fields =>
                  simp only [Prod.mk.injEq] at heval
                  exact False.elim (herror heval.1.symm)
                | nStruct name fields =>
                  simp only [Prod.mk.injEq] at heval
                  exact False.elim (herror heval.1.symm)
                | val payload =>
                  cases payload with
                  | word address2 =>
                    cases he4 : @evalHOLExact width σ _ source.toExact
                        (fun a => Classical.propDecidable (source.memaddrs a)) arrayLength with
                    | none =>
                      simp only [he4,Prod.mk.injEq] at heval
                      exact False.elim (herror heval.1.symm)
                    | some value4 =>
                      rw [he4] at heval
                      cases value4 with
                      | rStruct fields =>
                        simp only [Prod.mk.injEq] at heval
                        exact False.elim (herror heval.1.symm)
                      | nStruct name fields =>
                        simp only [Prod.mk.injEq] at heval
                        exact False.elim (herror heval.1.symm)
                      | val payload =>
                        cases payload with
                        | word length2 =>
                          have hexp1 := CompileExpCorrectExact.compileExpCorrectExact source context configuration (.val (.word address1))
                            ⟨he1,hlocals,hglobals,hstructs,hlocal,hglobal,hinfo⟩
                          have ht1 := hexp1.2.2
                          simp only [PanSemStateFiniteExact.evalHOLFinite,convertV] at ht1
                          have hexp2 := CompileExpCorrectExact.compileExpCorrectExact source context configurationLength (.val (.word length1))
                            ⟨he2,hlocals,hglobals,hstructs,hlocal,hglobal,hinfo⟩
                          have ht2 := hexp2.2.2
                          simp only [PanSemStateFiniteExact.evalHOLFinite,convertV] at ht2
                          have hexp3 := CompileExpCorrectExact.compileExpCorrectExact source context array (.val (.word address2))
                            ⟨he3,hlocals,hglobals,hstructs,hlocal,hglobal,hinfo⟩
                          have ht3 := hexp3.2.2
                          simp only [PanSemStateFiniteExact.evalHOLFinite,convertV] at ht3
                          have hexp4 := CompileExpCorrectExact.compileExpCorrectExact source context arrayLength (.val (.word length2))
                            ⟨he4,hlocals,hglobals,hstructs,hlocal,hglobal,hinfo⟩
                          have ht4 := hexp4.2.2
                          simp only [PanSemStateFiniteExact.evalHOLFinite,convertV] at ht4
                          dsimp only at heval
                          cases hr1 : readBytearrayWordHOL (byteWidth := 8) address1 length1.toNat
                              (@panMemLoadByteWord8HOL width _ source.memory source.memaddrs
                                (fun a => Classical.propDecidable (source.memaddrs a)) source.be) with
                          | none =>
                            simp only [hr1,Prod.mk.injEq] at heval
                            exact False.elim (herror heval.1.symm)
                          | some bytes1 =>
                            rw [hr1] at heval
                            cases hr2 : readBytearrayWordHOL (byteWidth := 8) address2 length2.toNat
                                (@panMemLoadByteWord8HOL width _ source.memory source.memaddrs
                                  (fun a => Classical.propDecidable (source.memaddrs a)) source.be) with
                            | none =>
                              simp only [hr2,Prod.mk.injEq] at heval
                              exact False.elim (herror heval.1.symm)
                            | some bytes2 =>
                              rw [hr2] at heval
                              dsimp only at heval
                              have htread1 : readBytearrayWordHOL (byteWidth := 8) address1 length1.toNat
                                  (@panMemLoadByteWord8HOL width _ (convertStateExact context source).memory
                                    (convertStateExact context source).memaddrs
                                    (fun a => Classical.propDecidable ((convertStateExact context source).memaddrs a))
                                    (convertStateExact context source).be) = some bytes1 := hr1
                              have htread2 : readBytearrayWordHOL (byteWidth := 8) address2 length2.toNat
                                  (@panMemLoadByteWord8HOL width _ (convertStateExact context source).memory
                                    (convertStateExact context source).memaddrs
                                    (fun a => Classical.propDecidable ((convertStateExact context source).memaddrs a))
                                    (convertStateExact context source).be) = some bytes2 := hr2
                              cases hf : callFFIHOL source.ffi (.extCall function) bytes1 bytes2 with
                              | final event =>
                                rw [hf] at heval
                                rcases Prod.mk.inj heval with ⟨hr,hp⟩
                                subst res
                                subst post
                                refine ⟨?_,?_,hglobal,hglobals,?_,?_,?_⟩
                                · rw [compileProgExact,PanSemStateFiniteExact.evaluateHOLFiniteState_extCall_source]
                                  simp only [PanSemStateFiniteExact.evalHOLFinite]
                                  rw [ht1,ht2,ht3,ht4]
                                  dsimp only
                                  rw [htread1,htread2]
                                  dsimp only
                                  have htffi : callFFIHOL (convertStateExact context source).ffi (.extCall function)
                                      bytes1 bytes2 = .final event := hf
                                  rw [htffi]
                                  rfl
                                · simp [PanSemStateFiniteExact.emptyLocalsHOLFinite,feveryHOL]
                                · simp [isContResHOL]
                                · simp [resVsHOL]
                                · simp [resVsHOL]
                              | ret newFfi newBytes =>
                                rw [hf] at heval
                                dsimp only at heval
                                rcases Prod.mk.inj heval with ⟨hr,hp⟩
                                subst res
                                subst post
                                refine ⟨?_,hlocal,hglobal,hglobals,?_,?_,?_⟩
                                · rw [compileProgExact,PanSemStateFiniteExact.evaluateHOLFiniteState_extCall_source]
                                  simp only [PanSemStateFiniteExact.evalHOLFinite]
                                  rw [ht1,ht2,ht3,ht4]
                                  dsimp only
                                  rw [htread1,htread2]
                                  dsimp only
                                  have htffi : callFFIHOL (convertStateExact context source).ffi (.extCall function)
                                      bytes1 bytes2 = .ret newFfi newBytes := hf
                                  rw [htffi]
                                  rfl
                                · intro _
                                  apply HolFiniteMapExact.ext
                                  exact congrArg HolFiniteMapExact.lookup hlocals
                                · simp [resVsHOL]
                                · simp [resVsHOL]
end Flapjack.Pancake.Proofs.PanStructs.CompileCorrectExtCall
