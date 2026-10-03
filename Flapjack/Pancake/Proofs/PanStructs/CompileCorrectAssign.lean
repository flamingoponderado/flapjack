import Flapjack.Pancake.Proofs.PanStructs.FupdateElim2
import Flapjack.Pancake.Proofs.PanStructs.CompileExpCorrectExact
import Flapjack.Pancake.Proofs.PanStructs.ValueShapeConversion
import Flapjack.Pancake.PanStructs.CompileProgExact
namespace Flapjack.Pancake.Proofs.PanStructs.CompileCorrectAssign
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


/-- Lookup extensionality for proof plumbing; no independent HOL original. -/
private theorem mapExt {α β : Type} (a b : HolFiniteMapExact α β)
    (h : ∀ k, a.lookup k = b.lookup k) : a = b := by
  cases a with | mk al af =>
    cases b with | mk bl bf =>
      have he : al = bl := funext h
      subst bl
      rfl

/-- Map/update commutation for proof plumbing; no independent HOL original. -/
private theorem mapUpdate {α β γ : Type} [BEq α] [LawfulBEq α]
    (fm : HolFiniteMapExact α β) (f : α × β → γ) (k : α) (v : β) :
    (fm.update (k,v)).map2 f = (fm.map2 f).update (k,f (k,v)) := by
  apply mapExt
  intro key
  simp only [HolFiniteMapExact.lookup_map2, HolFiniteMapExact.lookup_update, FUPDATE]
  by_cases hk : k == key
  · have he := beq_iff_eq.mp hk
    subst key
    simp
  · simp [hk]

/-- Existing-binding neutrality for the executed update; no independent HOL original. -/
private theorem updateNeutral {α β : Type} [BEq α] [LawfulBEq α]
    (fm : HolFiniteMapExact α β) (k : α) (v : β) (h : fm.lookup k = some v) :
    fm.update (k,v) = fm := by
  classical
  have he : fm.update (k,v) = fm.updateEq (k,v) := by
    apply mapExt
    intro key
    simp only [HolFiniteMapExact.lookup_update, HolFiniteMapExact.lookup_updateEq,
      FUPDATE_HOL_eq_FUPDATE]
  rw [he]
  exact FupdateElim2.fupdateElim2 fm k v h

/-- Updated-map validity for proof plumbing; no independent HOL original. -/
private theorem everyUpdate {α β : Type} [BEq α] [LawfulBEq α]
    (fm : HolFiniteMapExact α β) (P : α × β → Bool) (k : α) (v : β)
    (h : feveryHOL P fm) (hv : P (k,v) = true) : feveryHOL P (fm.update (k,v)) := by
  intro key value he
  simp only [HolFiniteMapExact.lookup_update, FUPDATE] at he
  split at he
  next hk =>
    have heq := beq_iff_eq.mp hk
    subst key
    cases he
    exact hv
  next => exact h key value he

/-- Genuine local/global Assign case of the full original program theorem. All ten
source premises and all seven conclusions are retained; there is no recursive IH.
Target validity follows internally from source lookup/shape equality and the full
value-shape conversion theorem. Canonical updates commute with conversion; the
shape map update is neutral because the new value has the existing shape. -/
@[hol "cakeml/pancake/proofs/pan_structsProofScript.sml" "compile_correct"
  (fmap_as_finite_support := [locals, globals, code, eshapes])
  (words_as_type_indexed_bitvec)]
theorem compileCorrectAssign {width : Nat} {σ : Type} [NeZero width]
    (source post : PanSemStateFiniteExact width σ) (context : ContextExact)
    (kind : VarKind) (name : MlS) (expression : ExpHOL width)
    (res : Option (PanSemResultExact width))
    (h : PanSemStateFiniteExact.evaluateHOLFiniteState source (.assign kind name expression : ProgHOL width) = (res, post) ∧
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
      (compileProgExact context (.assign kind name expression : ProgHOL width)) = (convertResHOL res, convertStateExact context post) ∧
    feveryHOL (fun entry => valueFldsOkHOLExact post.structs entry.2) post.locals ∧
    feveryHOL (fun entry => valueFldsOkHOLExact post.structs entry.2) post.globals ∧
    shapeMap context.globals = post.globals.map2 (fun entry => shapeOfHOLExact entry.2) ∧
    (isContResHOL res = true →
      shapeMap context.locals = post.locals.map2 (fun entry => shapeOfHOLExact entry.2)) ∧
    (∀ value ∈ resVsHOL res, valueFldsOkHOLExact post.structs value = true) ∧
    (∀ value ∈ resVsHOL res, isWfShapeValueHOLExact post.structs value = true) := by
  classical
  rcases h with ⟨heval, hstructs, hlocal, hglobal, hwlocal, hwglobal, hinfo, hlocals, hglobals, herror⟩
  rw [PanSemStateFiniteExact.evaluateHOLFiniteState_assign] at heval
  cases hv : @evalHOLExact width σ _ source.toExact
      (fun a => Classical.propDecidable (source.memaddrs a)) expression with
  | none =>
    simp only [hv, Prod.mk.injEq] at heval
    exact False.elim (herror heval.1.symm)
  | some value =>
    rw [hv] at heval
    dsimp only at heval
    split at heval
    next hvalid =>
      simp only [Prod.mk.injEq] at heval
      rcases heval with ⟨hr, hp⟩
      subst res
      subst post
      have hexp := CompileExpCorrectExact.compileExpCorrectExact source context expression value
        ⟨by simpa [PanSemStateFiniteExact.evalHOLFinite] using hv,
          hlocals, hglobals, hstructs, hlocal, hglobal, hinfo⟩
      have hwf := @evalHOLExact_isWfShapeValueHOLExact width σ _ source.toExact
        (fun a => Classical.propDecidable (source.memaddrs a)) hwlocal hwglobal expression value hv
      have hnewshape := ValueShapeConversion.shapeOfConvertVRev source.structs value
        ⟨hexp.2.1, hwf, hinfo⟩
      have htarget := hexp.2.2
      simp only [PanSemStateFiniteExact.evalHOLFinite] at htarget
      cases kind with
      | «local» =>
        simp only [PanSemStateFiniteExact.isValidValueHOLFinite,
          PanSemStateFiniteExact.lookupKvarHOLFinite] at hvalid
        cases ho : source.locals.lookup name with
        | none => simp [ho] at hvalid
        | some old =>
          simp only [ho] at hvalid
          have hs := (shapeEqHOL_eq_true _ _).mp hvalid
          have holdshape := ValueShapeConversion.shapeOfConvertVRev source.structs old
            ⟨hlocal name old ho, hwlocal name old ho, hinfo⟩
          have htargetValid : PanSemStateFiniteExact.isValidValueHOLFinite
              (convertStateExact context source) .local name (convertV value) = true := by
            simp only [PanSemStateFiniteExact.isValidValueHOLFinite,
              PanSemStateFiniteExact.lookupKvarHOLFinite, convertStateExact,
              HolFiniteMapExact.lookup_map2, ho, Option.map_some]
            apply (shapeEqHOL_eq_true _ _).mpr
            rw [hnewshape, holdshape, hs]
          have hmaps : (source.locals.update (name,value)).map2
              (fun entry => shapeOfHOLExact entry.2) =
              source.locals.map2 (fun entry => shapeOfHOLExact entry.2) := by
            rw [mapUpdate]
            apply updateNeutral
            simp only [HolFiniteMapExact.lookup_map2, ho, Option.map_some]
            exact congrArg some hs.symm
          have hfields := everyUpdate source.locals
            (fun entry => valueFldsOkHOLExact source.structs entry.2) name value hlocal hexp.2.1
          refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
          · simp only [compileProgExact, PanSemStateFiniteExact.evaluateHOLFiniteState_assign]
            rw [htarget]
            dsimp only
            rw [htargetValid]
            simp only [ite_true, convertResHOL]
            congr 1
            simp only [PanSemStateFiniteExact.setKvarHOLFinite,
              PanSemStateFiniteExact.setVarHOLFinite, convertStateExact]
            congr 1
            exact (mapUpdate source.locals (fun entry => convertV entry.2) name value).symm
          · exact hfields
          · exact hglobal
          · exact hglobals
          · intro _
            simpa only [PanSemStateFiniteExact.setKvarHOLFinite, PanSemStateFiniteExact.setVarHOLFinite, hmaps] using hlocals
          · simp [resVsHOL]
          · simp [resVsHOL]
      | global =>
        simp only [PanSemStateFiniteExact.isValidValueHOLFinite,
          PanSemStateFiniteExact.lookupKvarHOLFinite] at hvalid
        cases ho : source.globals.lookup name with
        | none => simp [ho] at hvalid
        | some old =>
          simp only [ho] at hvalid
          have hs := (shapeEqHOL_eq_true _ _).mp hvalid
          have holdshape := ValueShapeConversion.shapeOfConvertVRev source.structs old
            ⟨hglobal name old ho, hwglobal name old ho, hinfo⟩
          have htargetValid : PanSemStateFiniteExact.isValidValueHOLFinite
              (convertStateExact context source) .global name (convertV value) = true := by
            simp only [PanSemStateFiniteExact.isValidValueHOLFinite,
              PanSemStateFiniteExact.lookupKvarHOLFinite, convertStateExact,
              HolFiniteMapExact.lookup_map2, ho, Option.map_some]
            apply (shapeEqHOL_eq_true _ _).mpr
            rw [hnewshape, holdshape, hs]
          have hmaps : (source.globals.update (name,value)).map2
              (fun entry => shapeOfHOLExact entry.2) =
              source.globals.map2 (fun entry => shapeOfHOLExact entry.2) := by
            rw [mapUpdate]
            apply updateNeutral
            simp only [HolFiniteMapExact.lookup_map2, ho, Option.map_some]
            exact congrArg some hs.symm
          have hfields := everyUpdate source.globals
            (fun entry => valueFldsOkHOLExact source.structs entry.2) name value hglobal hexp.2.1
          refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
          · simp only [compileProgExact, PanSemStateFiniteExact.evaluateHOLFiniteState_assign]
            rw [htarget]
            dsimp only
            rw [htargetValid]
            simp only [ite_true, convertResHOL]
            congr 1
            simp only [PanSemStateFiniteExact.setKvarHOLFinite,
              PanSemStateFiniteExact.setGlobalHOLFinite, convertStateExact]
            congr 1
            exact (mapUpdate source.globals (fun entry => convertV entry.2) name value).symm
          · exact hlocal
          · exact hfields
          · simpa only [PanSemStateFiniteExact.setKvarHOLFinite, PanSemStateFiniteExact.setGlobalHOLFinite, hmaps] using hglobals
          · intro _
            exact hlocals
          · simp [resVsHOL]
          · simp [resVsHOL]
    next hinvalid =>
      simp only [Prod.mk.injEq] at heval
      exact False.elim (herror heval.1.symm)
end Flapjack.Pancake.Proofs.PanStructs.CompileCorrectAssign
