import Flapjack.Pancake.Proofs.PanStructs.FlattenConversion
import Flapjack.Pancake.Proofs.PanStructs.CompileExpCorrectExact
import Flapjack.Pancake.Proofs.PanStructs.ValueShapeConversion
import Flapjack.Pancake.PanStructs.CompileProgExact
namespace Flapjack.Pancake.Proofs.PanStructs.CompileCorrectShMemStore
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


/-- Finite carrier repacking follows a proved broad-state equality; no
independent HOL declaration and no extra simulation assumption. -/
private theorem repack {width : Nat} {σ : Type} [NeZero width]
    (broad : PanSemStateExact width σ) (finite : PanSemStateFiniteExact width σ)
    (heq : broad = finite.toExact) (support : broad.FiniteSupport) :
    PanSemStateFiniteExact.ofExact broad support = finite := by
  cases heq
  exact PanSemStateFiniteExact.ofExact_toExact finite

/-- Full original ShMemStore case, retaining ten premises/seven conclusions
and no recursive IH. Source word arguments supply target arguments through full
expression correctness. Original zero/nonzero nb, shared-memory domain, aligned
address, byte payload and actual MappedWrite FFI final/ret branches are preserved.
Canonical state repacking follows each proved original operation result; final
keeps the source state and ret updates only ffi, which commutes with conversion.
No oracle agreement, target outcome/success/run or extra width premise is added. -/
@[hol "cakeml/pancake/proofs/pan_structsProofScript.sml" "compile_correct"
  (fmap_as_finite_support := [locals, globals, code, eshapes])
  (words_as_type_indexed_bitvec)]
theorem compileCorrectShMemStore {width : Nat} {σ : Type} [NeZero width]
    (source post : PanSemStateFiniteExact width σ) (context : ContextExact)
    (operator : OpSize) (destination valueExpression : ExpHOL width)
    (res : Option (PanSemResultExact width))
    (h : PanSemStateFiniteExact.evaluateHOLFiniteState source (.shMemStore operator destination valueExpression : ProgHOL width) = (res, post) ∧
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
      (compileProgExact context (.shMemStore operator destination valueExpression : ProgHOL width)) = (convertResHOL res, convertStateExact context post) ∧
    feveryHOL (fun entry => valueFldsOkHOLExact post.structs entry.2) post.locals ∧
    feveryHOL (fun entry => valueFldsOkHOLExact post.structs entry.2) post.globals ∧
    shapeMap context.globals = post.globals.map2 (fun entry => shapeOfHOLExact entry.2) ∧
    (isContResHOL res = true →
      shapeMap context.locals = post.locals.map2 (fun entry => shapeOfHOLExact entry.2)) ∧
    (∀ value ∈ resVsHOL res, valueFldsOkHOLExact post.structs value = true) ∧
    (∀ value ∈ resVsHOL res, isWfShapeValueHOLExact post.structs value = true) := by
  classical
  rcases h with ⟨heval,hstructs,hlocal,hglobal,hwlocal,hwglobal,hinfo,hlocals,hglobals,herror⟩
  rw [PanSemStateFiniteExact.evaluateHOLFiniteState_shMemStore_total] at heval
  dsimp only at heval
  cases hd : @evalHOLExact width σ _ source.toExact
      (fun a => Classical.propDecidable (source.memaddrs a)) destination with
  | none =>
    simp only [hd,Prod.mk.injEq] at heval
    exact False.elim (herror heval.1.symm)
  | some dval =>
    rw [hd] at heval
    cases dval with
    | rStruct fields =>
      simp only [Prod.mk.injEq] at heval
      exact False.elim (herror heval.1.symm)
    | nStruct name fields =>
      simp only [Prod.mk.injEq] at heval
      exact False.elim (herror heval.1.symm)
    | val payload =>
      cases payload with
      | word address =>
        cases hs : @evalHOLExact width σ _ source.toExact
            (fun a => Classical.propDecidable (source.memaddrs a)) valueExpression with
        | none =>
          simp only [hs,Prod.mk.injEq] at heval
          exact False.elim (herror heval.1.symm)
        | some sval =>
          rw [hs] at heval
          cases sval with
          | rStruct fields =>
            simp only [Prod.mk.injEq] at heval
            exact False.elim (herror heval.1.symm)
          | nStruct name fields =>
            simp only [Prod.mk.injEq] at heval
            exact False.elim (herror heval.1.symm)
          | val payload =>
            cases payload with
            | word bytes =>
              dsimp only at heval
              have hdexp := CompileExpCorrectExact.compileExpCorrectExact source context destination (.val (.word address))
                ⟨hd,hlocals,hglobals,hstructs,hlocal,hglobal,hinfo⟩
              have hsexp := CompileExpCorrectExact.compileExpCorrectExact source context valueExpression (.val (.word bytes))
                ⟨hs,hlocals,hglobals,hstructs,hlocal,hglobal,hinfo⟩
              have hdtarget := hdexp.2.2
              have hstarget := hsexp.2.2
              simp only [PanSemStateFiniteExact.evalHOLFinite,convertV] at hdtarget hstarget
              let sourceOut := @shMemStoreHOLExact width σ _ source.toExact
                (fun key => Classical.propDecidable (source.shMemaddrs key)) bytes address (nbOpHOL operator)
              let sourceSupport : sourceOut.2.FiniteSupport :=
                @shMemStoreHOLExact_finiteSupport width σ _ source.toExact
                  (fun key => Classical.propDecidable (source.shMemaddrs key)) bytes address
                  (nbOpHOL operator) source.toExact_finiteSupport
              by_cases hn : nbOpHOL operator = 0
              · by_cases ha : source.shMemaddrs address
                · cases hf : callFFIHOL source.ffi (.sharedMem .mappedWrite)
                    [BitVec.ofNat 8 0] (panWordToBytesHOL bytes false ++ panWordToBytesHOL address false) with
                  | final event =>
                    have hop : sourceOut = (some (.finalFfi event),(source).toExact) := by
                      simp only [sourceOut,shMemStoreHOLExact,hn,ite_true]
                      rw [if_pos ha,hf]
                    have hpost : PanSemStateFiniteExact.ofExact sourceOut.2 sourceSupport = source :=
                      repack sourceOut.2 source (congrArg Prod.snd hop) sourceSupport
                    change (sourceOut.1,PanSemStateFiniteExact.ofExact sourceOut.2 sourceSupport) = (res,post) at heval
                    rw [hpost,congrArg Prod.fst hop] at heval
                    rcases Prod.mk.inj heval with ⟨hr,hp⟩
                    subst res
                    subst post
                    refine ⟨?_,hlocal,hglobal,hglobals,?_,?_,?_⟩
                    · rw [compileProgExact,PanSemStateFiniteExact.evaluateHOLFiniteState_shMemStore_total]
                      dsimp only
                      rw [hdtarget,hstarget]
                      dsimp only
                      let targetOut := @shMemStoreHOLExact width σ _ (convertStateExact context source).toExact
                        (fun key => Classical.propDecidable ((convertStateExact context source).shMemaddrs key))
                        bytes address (nbOpHOL operator)
                      have htout : targetOut = (some (.finalFfi event),(convertStateExact context source).toExact) := by
                        simp only [targetOut,shMemStoreHOLExact,convertStateExact,
                          PanSemStateFiniteExact.toExact,hn,ite_true]
                        rw [if_pos ha,hf]
                      let targetSupport : targetOut.2.FiniteSupport :=
                        @shMemStoreHOLExact_finiteSupport width σ _ (convertStateExact context source).toExact
                          (fun key => Classical.propDecidable ((convertStateExact context source).shMemaddrs key))
                          bytes address (nbOpHOL operator) (convertStateExact context source).toExact_finiteSupport
                      apply Prod.ext
                      · simpa only [convertResHOL] using
                          congrArg (fun pair : Option (PanSemResultExact width) × PanSemStateExact width σ => pair.1) htout
                      · exact repack targetOut.2 _ (congrArg Prod.snd htout) targetSupport
                    · intro _
                      exact hlocals
                    · simp [resVsHOL]
                    · simp [resVsHOL]
                  | ret newFfi newBytes =>
                    have hop : sourceOut = (none,(({source with ffi := newFfi} : PanSemStateFiniteExact width σ)).toExact) := by
                      simp only [sourceOut,shMemStoreHOLExact,hn,ite_true]
                      rw [if_pos ha,hf]
                    have hpost : PanSemStateFiniteExact.ofExact sourceOut.2 sourceSupport = ({source with ffi := newFfi} : PanSemStateFiniteExact width σ) :=
                      repack sourceOut.2 ({source with ffi := newFfi} : PanSemStateFiniteExact width σ) (congrArg Prod.snd hop) sourceSupport
                    change (sourceOut.1,PanSemStateFiniteExact.ofExact sourceOut.2 sourceSupport) = (res,post) at heval
                    rw [hpost,congrArg Prod.fst hop] at heval
                    rcases Prod.mk.inj heval with ⟨hr,hp⟩
                    subst res
                    subst post
                    refine ⟨?_,hlocal,hglobal,hglobals,?_,?_,?_⟩
                    · rw [compileProgExact,PanSemStateFiniteExact.evaluateHOLFiniteState_shMemStore_total]
                      dsimp only
                      rw [hdtarget,hstarget]
                      dsimp only
                      let targetOut := @shMemStoreHOLExact width σ _ (convertStateExact context source).toExact
                        (fun key => Classical.propDecidable ((convertStateExact context source).shMemaddrs key))
                        bytes address (nbOpHOL operator)
                      have htout : targetOut = (none,(convertStateExact context ({source with ffi := newFfi} : PanSemStateFiniteExact width σ)).toExact) := by
                        simp only [targetOut,shMemStoreHOLExact,convertStateExact,
                          PanSemStateFiniteExact.toExact,hn,ite_true]
                        rw [if_pos ha,hf]
                      let targetSupport : targetOut.2.FiniteSupport :=
                        @shMemStoreHOLExact_finiteSupport width σ _ (convertStateExact context source).toExact
                          (fun key => Classical.propDecidable ((convertStateExact context source).shMemaddrs key))
                          bytes address (nbOpHOL operator) (convertStateExact context source).toExact_finiteSupport
                      apply Prod.ext
                      · simpa only [convertResHOL] using
                          congrArg (fun pair : Option (PanSemResultExact width) × PanSemStateExact width σ => pair.1) htout
                      · exact repack targetOut.2 _ (congrArg Prod.snd htout) targetSupport
                    · intro _
                      exact hlocals
                    · simp [resVsHOL]
                    · simp [resVsHOL]
                · have hop : sourceOut = (some .error,source.toExact) := by
                    simp [sourceOut,shMemStoreHOLExact,hn,ha]
                  have hr : sourceOut.1 = res := (Prod.mk.inj heval).1
                  exact False.elim (herror (by rw [← hr]; exact congrArg Prod.fst hop))
              · by_cases ha : source.shMemaddrs (panByteAlignHOL address)
                · cases hf : callFFIHOL source.ffi (.sharedMem .mappedWrite)
                    [BitVec.ofNat 8 (nbOpHOL operator)] ((panWordToBytesHOL bytes false).take (nbOpHOL operator) ++ panWordToBytesHOL address false) with
                  | final event =>
                    have hop : sourceOut = (some (.finalFfi event),(source).toExact) := by
                      simp only [sourceOut,shMemStoreHOLExact]
                      simp [hn,ha,hf]
                    have hpost : PanSemStateFiniteExact.ofExact sourceOut.2 sourceSupport = source :=
                      repack sourceOut.2 source (congrArg Prod.snd hop) sourceSupport
                    change (sourceOut.1,PanSemStateFiniteExact.ofExact sourceOut.2 sourceSupport) = (res,post) at heval
                    rw [hpost,congrArg Prod.fst hop] at heval
                    rcases Prod.mk.inj heval with ⟨hr,hp⟩
                    subst res
                    subst post
                    refine ⟨?_,hlocal,hglobal,hglobals,?_,?_,?_⟩
                    · rw [compileProgExact,PanSemStateFiniteExact.evaluateHOLFiniteState_shMemStore_total]
                      dsimp only
                      rw [hdtarget,hstarget]
                      dsimp only
                      let targetOut := @shMemStoreHOLExact width σ _ (convertStateExact context source).toExact
                        (fun key => Classical.propDecidable ((convertStateExact context source).shMemaddrs key))
                        bytes address (nbOpHOL operator)
                      have htout : targetOut = (some (.finalFfi event),(convertStateExact context source).toExact) := by
                        simp only [targetOut,shMemStoreHOLExact]
                        simp [hn,ha,hf,convertStateExact,PanSemStateFiniteExact.toExact]
                      let targetSupport : targetOut.2.FiniteSupport :=
                        @shMemStoreHOLExact_finiteSupport width σ _ (convertStateExact context source).toExact
                          (fun key => Classical.propDecidable ((convertStateExact context source).shMemaddrs key))
                          bytes address (nbOpHOL operator) (convertStateExact context source).toExact_finiteSupport
                      apply Prod.ext
                      · simpa only [convertResHOL] using
                          congrArg (fun pair : Option (PanSemResultExact width) × PanSemStateExact width σ => pair.1) htout
                      · exact repack targetOut.2 _ (congrArg Prod.snd htout) targetSupport
                    · intro _
                      exact hlocals
                    · simp [resVsHOL]
                    · simp [resVsHOL]
                  | ret newFfi newBytes =>
                    have hop : sourceOut = (none,(({source with ffi := newFfi} : PanSemStateFiniteExact width σ)).toExact) := by
                      simp only [sourceOut,shMemStoreHOLExact]
                      simp [hn,ha,hf]
                    have hpost : PanSemStateFiniteExact.ofExact sourceOut.2 sourceSupport = ({source with ffi := newFfi} : PanSemStateFiniteExact width σ) :=
                      repack sourceOut.2 ({source with ffi := newFfi} : PanSemStateFiniteExact width σ) (congrArg Prod.snd hop) sourceSupport
                    change (sourceOut.1,PanSemStateFiniteExact.ofExact sourceOut.2 sourceSupport) = (res,post) at heval
                    rw [hpost,congrArg Prod.fst hop] at heval
                    rcases Prod.mk.inj heval with ⟨hr,hp⟩
                    subst res
                    subst post
                    refine ⟨?_,hlocal,hglobal,hglobals,?_,?_,?_⟩
                    · rw [compileProgExact,PanSemStateFiniteExact.evaluateHOLFiniteState_shMemStore_total]
                      dsimp only
                      rw [hdtarget,hstarget]
                      dsimp only
                      let targetOut := @shMemStoreHOLExact width σ _ (convertStateExact context source).toExact
                        (fun key => Classical.propDecidable ((convertStateExact context source).shMemaddrs key))
                        bytes address (nbOpHOL operator)
                      have htout : targetOut = (none,(convertStateExact context ({source with ffi := newFfi} : PanSemStateFiniteExact width σ)).toExact) := by
                        simp only [targetOut,shMemStoreHOLExact]
                        simp [hn,ha,hf,convertStateExact,PanSemStateFiniteExact.toExact]
                      let targetSupport : targetOut.2.FiniteSupport :=
                        @shMemStoreHOLExact_finiteSupport width σ _ (convertStateExact context source).toExact
                          (fun key => Classical.propDecidable ((convertStateExact context source).shMemaddrs key))
                          bytes address (nbOpHOL operator) (convertStateExact context source).toExact_finiteSupport
                      apply Prod.ext
                      · simpa only [convertResHOL] using
                          congrArg (fun pair : Option (PanSemResultExact width) × PanSemStateExact width σ => pair.1) htout
                      · exact repack targetOut.2 _ (congrArg Prod.snd htout) targetSupport
                    · intro _
                      exact hlocals
                    · simp [resVsHOL]
                    · simp [resVsHOL]
                · have hop : sourceOut = (some .error,source.toExact) := by
                    simp [sourceOut,shMemStoreHOLExact,hn,ha]
                  have hr : sourceOut.1 = res := (Prod.mk.inj heval).1
                  exact False.elim (herror (by rw [← hr]; exact congrArg Prod.fst hop))
end Flapjack.Pancake.Proofs.PanStructs.CompileCorrectShMemStore
