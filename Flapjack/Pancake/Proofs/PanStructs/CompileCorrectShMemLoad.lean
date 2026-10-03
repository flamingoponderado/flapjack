import Flapjack.Pancake.Proofs.PanStructs.CompileCorrectAssign
import Flapjack.Pancake.Proofs.PanStructs.FlattenConversion
import Flapjack.Pancake.Proofs.PanStructs.CompileExpCorrectExact
import Flapjack.Pancake.Proofs.PanStructs.ValueShapeConversion
import Flapjack.Pancake.PanStructs.CompileProgExact
namespace Flapjack.Pancake.Proofs.PanStructs.CompileCorrectShMemLoad
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


/-- Full original ShMemLoad case, all ten premises/seven conclusions and no IH.
Address evaluation, existing word lookup, byte-count and shared-domain guards
are source-derived. Conversion preserves actual mapped-read FFI arguments;
final clears locals, ret installs the returned word and updates FFI. The
literal assignment correctness needed for the update is proved internally
from the existing word lookup. No oracle agreement or target execution premise. -/
@[hol "cakeml/pancake/proofs/pan_structsProofScript.sml" "compile_correct"
  (fmap_as_finite_support := [locals, globals, code, eshapes])
  (words_as_type_indexed_bitvec)]
theorem compileCorrectShMemLoad {width : Nat} {σ : Type} [NeZero width]
    (source post : PanSemStateFiniteExact width σ) (context : ContextExact)
    (operator : OpSize) (kind : VarKind) (name : MlS) (addressExpression : ExpHOL width)
    (res : Option (PanSemResultExact width))
    (h : PanSemStateFiniteExact.evaluateHOLFiniteState source (.shMemLoad operator kind name addressExpression : ProgHOL width) = (res, post) ∧
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
      (compileProgExact context (.shMemLoad operator kind name addressExpression : ProgHOL width)) = (convertResHOL res, convertStateExact context post) ∧
    feveryHOL (fun entry => valueFldsOkHOLExact post.structs entry.2) post.locals ∧
    feveryHOL (fun entry => valueFldsOkHOLExact post.structs entry.2) post.globals ∧
    shapeMap context.globals = post.globals.map2 (fun entry => shapeOfHOLExact entry.2) ∧
    (isContResHOL res = true →
      shapeMap context.locals = post.locals.map2 (fun entry => shapeOfHOLExact entry.2)) ∧
    (∀ value ∈ resVsHOL res, valueFldsOkHOLExact post.structs value = true) ∧
    (∀ value ∈ resVsHOL res, isWfShapeValueHOLExact post.structs value = true) := by
  classical
  rcases h with ⟨heval,hstructs,hlocal,hglobal,hwlocal,hwglobal,hinfo,hlocals,hglobals,herror⟩
  rw [PanSemStateFiniteExact.evaluateHOLFiniteState_shMemLoad_source] at heval
  simp only [PanSemStateFiniteExact.evalHOLFinite] at heval
  cases hv : @evalHOLExact width σ _ source.toExact
      (fun a => Classical.propDecidable (source.memaddrs a)) addressExpression with
  | none =>
    simp only [hv,Prod.mk.injEq] at heval
    exact False.elim (herror heval.1.symm)
  | some value =>
    rw [hv] at heval
    cases value with
    | rStruct fields =>
      simp only [Prod.mk.injEq] at heval
      exact False.elim (herror heval.1.symm)
    | nStruct tag fields =>
      simp only [Prod.mk.injEq] at heval
      exact False.elim (herror heval.1.symm)
    | val payload =>
      cases payload with
      | word address =>
        cases ho : PanSemStateFiniteExact.lookupKvarHOLFinite kind name source with
        | none =>
          simp only [ho,Prod.mk.injEq] at heval
          exact False.elim (herror heval.1.symm)
        | some old =>
          rw [ho] at heval
          cases old with
          | rStruct fields =>
            simp only [Prod.mk.injEq] at heval
            exact False.elim (herror heval.1.symm)
          | nStruct tag fields =>
            simp only [Prod.mk.injEq] at heval
            exact False.elim (herror heval.1.symm)
          | val payload =>
            cases payload with
            | word oldWord =>
              have hexp := CompileExpCorrectExact.compileExpCorrectExact source context addressExpression (.val (.word address))
                ⟨hv,hlocals,hglobals,hstructs,hlocal,hglobal,hinfo⟩
              have ht := hexp.2.2
              simp only [PanSemStateFiniteExact.evalHOLFinite,convertV] at ht
              have hlookup : PanSemStateFiniteExact.lookupKvarHOLFinite kind name
                  (convertStateExact context source) = some (.val (.word oldWord)) := by
                cases kind <;> simp only [PanSemStateFiniteExact.lookupKvarHOLFinite] at ho ⊢ <;>
                  simp only [convertStateExact,HolFiniteMapExact.lookup_map2,ho,Option.map_some,convertV]
              dsimp only at heval
              simp only [PanSemStateFiniteExact.shMemLoadHOLFiniteExact] at heval
              by_cases hn : nbOpHOL operator = 0
              · rw [if_pos hn] at heval
                by_cases ha : source.shMemaddrs address
                · rw [if_pos ha] at heval
                  cases hf : callFFIHOL source.ffi (.sharedMem .mappedRead)
                      [BitVec.ofNat 8 (nbOpHOL operator)] (panWordToBytesHOL address false) with
                  | final event =>
                    rw [hf] at heval
                    rcases Prod.mk.inj heval with ⟨hr,hp⟩
                    subst res
                    subst post
                    refine ⟨?_,?_,hglobal,hglobals,?_,?_,?_⟩
                    · rw [compileProgExact,PanSemStateFiniteExact.evaluateHOLFiniteState_shMemLoad_source]
                      simp only [PanSemStateFiniteExact.evalHOLFinite]
                      rw [ht]
                      dsimp only
                      rw [hlookup]
                      dsimp only
                      simp only [PanSemStateFiniteExact.shMemLoadHOLFiniteExact]
                      rw [if_pos hn]
                      have htargetDomain : (convertStateExact context source).shMemaddrs address := ha
                      rw [if_pos htargetDomain]
                      have htargetFfi : callFFIHOL (convertStateExact context source).ffi (.sharedMem .mappedRead)
                          [BitVec.ofNat 8 (nbOpHOL operator)] (panWordToBytesHOL address false) = .final event := hf
                      rw [htargetFfi]
                      rfl
                    · simp [PanSemStateFiniteExact.emptyLocalsHOLFinite,feveryHOL]
                    · simp [isContResHOL]
                    · simp [resVsHOL]
                    · simp [resVsHOL]
                  | ret newFfi newBytes =>
                    let word : RiscV.Word width := panWordOfBytesHOL false 0 newBytes
                    have hassignEval : PanSemStateFiniteExact.evaluateHOLFiniteState source
                        (.assign kind name (.const word) : ProgHOL width) =
                        (none,PanSemStateFiniteExact.setKvarHOLFinite kind name (.val (.word word)) source) := by
                      rw [PanSemStateFiniteExact.evaluateHOLFiniteState_assign]
                      simp only [evalHOLExact]
                      have hvalid : PanSemStateFiniteExact.isValidValueHOLFinite source kind name
                          (.val (.word word)) = true := by
                        rw [PanSemStateFiniteExact.isValidValueHOLFinite,ho]
                        dsimp only
                        apply (shapeEqHOL_eq_true _ _).mpr
                        simp only [shapeOfHOLExact_val]
                      rw [hvalid]
                      rfl
                    have hassign := CompileCorrectAssign.compileCorrectAssign source
                        (PanSemStateFiniteExact.setKvarHOLFinite kind name (.val (.word word)) source)
                        context kind name (.const word) none
                        ⟨hassignEval,hstructs,hlocal,hglobal,hwlocal,hwglobal,hinfo,hlocals,hglobals,by simp⟩
                    have htargetValid : PanSemStateFiniteExact.isValidValueHOLFinite
                        (convertStateExact context source) kind name (.val (.word word)) = true := by
                      rw [PanSemStateFiniteExact.isValidValueHOLFinite,hlookup]
                      dsimp only
                      apply (shapeEqHOL_eq_true _ _).mpr
                      simp only [shapeOfHOLExact_val]
                    have hupdate := hassign.1
                    rw [compileProgExact,PanSemStateFiniteExact.evaluateHOLFiniteState_assign] at hupdate
                    simp only [compileExpExact,evalHOLExact] at hupdate
                    rw [htargetValid] at hupdate
                    simp only [ite_true,convertResHOL] at hupdate
                    have hcomm := (Prod.mk.inj hupdate).2
                    rw [hf] at heval
                    rcases Prod.mk.inj heval with ⟨hr,hp⟩
                    subst res
                    subst post
                    refine ⟨?_,hassign.2.1,hassign.2.2.1,hassign.2.2.2.1,?_,?_,?_⟩
                    · rw [compileProgExact,PanSemStateFiniteExact.evaluateHOLFiniteState_shMemLoad_source]
                      simp only [PanSemStateFiniteExact.evalHOLFinite]
                      rw [ht]
                      dsimp only
                      rw [hlookup]
                      dsimp only
                      simp only [PanSemStateFiniteExact.shMemLoadHOLFiniteExact]
                      rw [if_pos hn]
                      have htargetDomain : (convertStateExact context source).shMemaddrs address := ha
                      rw [if_pos htargetDomain]
                      have htargetFfi : callFFIHOL (convertStateExact context source).ffi (.sharedMem .mappedRead)
                          [BitVec.ofNat 8 (nbOpHOL operator)] (panWordToBytesHOL address false) = .ret newFfi newBytes := hf
                      rw [htargetFfi]
                      apply Prod.ext
                      · rfl
                      · change { PanSemStateFiniteExact.setKvarHOLFinite kind name (.val (.word word))
                            (convertStateExact context source) with ffi := newFfi } = _
                        rw [hcomm]
                        rfl
                    · exact hassign.2.2.2.2.1
                    · simp [resVsHOL]
                    · simp [resVsHOL]
                · rw [if_neg ha] at heval
                  exact False.elim (herror (Prod.mk.inj heval).1.symm)
              · rw [if_neg hn] at heval
                by_cases ha : source.shMemaddrs (panByteAlignHOL address)
                · rw [if_pos ha] at heval
                  cases hf : callFFIHOL source.ffi (.sharedMem .mappedRead)
                      [BitVec.ofNat 8 (nbOpHOL operator)] (panWordToBytesHOL address false) with
                  | final event =>
                    rw [hf] at heval
                    rcases Prod.mk.inj heval with ⟨hr,hp⟩
                    subst res
                    subst post
                    refine ⟨?_,?_,hglobal,hglobals,?_,?_,?_⟩
                    · rw [compileProgExact,PanSemStateFiniteExact.evaluateHOLFiniteState_shMemLoad_source]
                      simp only [PanSemStateFiniteExact.evalHOLFinite]
                      rw [ht]
                      dsimp only
                      rw [hlookup]
                      dsimp only
                      simp only [PanSemStateFiniteExact.shMemLoadHOLFiniteExact]
                      rw [if_neg hn]
                      have htargetDomain : (convertStateExact context source).shMemaddrs (panByteAlignHOL address) := ha
                      rw [if_pos htargetDomain]
                      have htargetFfi : callFFIHOL (convertStateExact context source).ffi (.sharedMem .mappedRead)
                          [BitVec.ofNat 8 (nbOpHOL operator)] (panWordToBytesHOL address false) = .final event := hf
                      rw [htargetFfi]
                      rfl
                    · simp [PanSemStateFiniteExact.emptyLocalsHOLFinite,feveryHOL]
                    · simp [isContResHOL]
                    · simp [resVsHOL]
                    · simp [resVsHOL]
                  | ret newFfi newBytes =>
                    let word : RiscV.Word width := panWordOfBytesHOL false 0 newBytes
                    have hassignEval : PanSemStateFiniteExact.evaluateHOLFiniteState source
                        (.assign kind name (.const word) : ProgHOL width) =
                        (none,PanSemStateFiniteExact.setKvarHOLFinite kind name (.val (.word word)) source) := by
                      rw [PanSemStateFiniteExact.evaluateHOLFiniteState_assign]
                      simp only [evalHOLExact]
                      have hvalid : PanSemStateFiniteExact.isValidValueHOLFinite source kind name
                          (.val (.word word)) = true := by
                        rw [PanSemStateFiniteExact.isValidValueHOLFinite,ho]
                        dsimp only
                        apply (shapeEqHOL_eq_true _ _).mpr
                        simp only [shapeOfHOLExact_val]
                      rw [hvalid]
                      rfl
                    have hassign := CompileCorrectAssign.compileCorrectAssign source
                        (PanSemStateFiniteExact.setKvarHOLFinite kind name (.val (.word word)) source)
                        context kind name (.const word) none
                        ⟨hassignEval,hstructs,hlocal,hglobal,hwlocal,hwglobal,hinfo,hlocals,hglobals,by simp⟩
                    have htargetValid : PanSemStateFiniteExact.isValidValueHOLFinite
                        (convertStateExact context source) kind name (.val (.word word)) = true := by
                      rw [PanSemStateFiniteExact.isValidValueHOLFinite,hlookup]
                      dsimp only
                      apply (shapeEqHOL_eq_true _ _).mpr
                      simp only [shapeOfHOLExact_val]
                    have hupdate := hassign.1
                    rw [compileProgExact,PanSemStateFiniteExact.evaluateHOLFiniteState_assign] at hupdate
                    simp only [compileExpExact,evalHOLExact] at hupdate
                    rw [htargetValid] at hupdate
                    simp only [ite_true,convertResHOL] at hupdate
                    have hcomm := (Prod.mk.inj hupdate).2
                    rw [hf] at heval
                    rcases Prod.mk.inj heval with ⟨hr,hp⟩
                    subst res
                    subst post
                    refine ⟨?_,hassign.2.1,hassign.2.2.1,hassign.2.2.2.1,?_,?_,?_⟩
                    · rw [compileProgExact,PanSemStateFiniteExact.evaluateHOLFiniteState_shMemLoad_source]
                      simp only [PanSemStateFiniteExact.evalHOLFinite]
                      rw [ht]
                      dsimp only
                      rw [hlookup]
                      dsimp only
                      simp only [PanSemStateFiniteExact.shMemLoadHOLFiniteExact]
                      rw [if_neg hn]
                      have htargetDomain : (convertStateExact context source).shMemaddrs (panByteAlignHOL address) := ha
                      rw [if_pos htargetDomain]
                      have htargetFfi : callFFIHOL (convertStateExact context source).ffi (.sharedMem .mappedRead)
                          [BitVec.ofNat 8 (nbOpHOL operator)] (panWordToBytesHOL address false) = .ret newFfi newBytes := hf
                      rw [htargetFfi]
                      apply Prod.ext
                      · rfl
                      · change { PanSemStateFiniteExact.setKvarHOLFinite kind name (.val (.word word))
                            (convertStateExact context source) with ffi := newFfi } = _
                        rw [hcomm]
                        rfl
                    · exact hassign.2.2.2.2.1
                    · simp [resVsHOL]
                    · simp [resVsHOL]
                · rw [if_neg ha] at heval
                  exact False.elim (herror (Prod.mk.inj heval).1.symm)
end Flapjack.Pancake.Proofs.PanStructs.CompileCorrectShMemLoad
