import Flapjack.Pancake.Proofs.PanStructs.MapRestoration
import Flapjack.Pancake.Proofs.PanStructs.EvaluateStructsCodeInvariant
import Flapjack.Pancake.Proofs.PanStructs.CompileExpCorrectExact
import Flapjack.Pancake.Proofs.PanStructs.ValueShapeConversion
import Flapjack.Pancake.PanStructs.CompileProgExact
namespace Flapjack.Pancake.Proofs.PanStructs.CompileCorrectDec
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

/-- Local context bindings are overwritten by every code entry's own params.
Flapjack proof plumbing; no independent HOL declaration. -/
private theorem convertStateLocalContext {width : Nat} {σ : Type} [NeZero width]
    (context : ContextExact) (locals : List (MlS × ShapeHOL))
    (state : PanSemStateFiniteExact width σ) :
    convertStateExact {context with locals := locals} state = convertStateExact context state := by
  rfl

/-- Equality decisions for the same key proposition are unique. Flapjack proof
plumbing; no extra comparison assumption and no independent HOL declaration. -/
private theorem resVarCanonical {α β : Type} (d : DecidableEq α)
    (fm : HolFiniteMapExact α β) (entry : α × Option β) :
    @HolFiniteMapExact.resVarEq α β d fm entry =
    @HolFiniteMapExact.resVarEq α β (Classical.typeDecidableEq α) fm entry := by
  have h : d = Classical.typeDecidableEq α := Subsingleton.elim _ _
  subst d
  rfl

/-- Genuine Dec case with all ten original premises/seven conclusions and
precisely the original initializer-SOME/declared-shape guarded body IH, at the
actual state whose local binding is updated. Body validity, well-formedness and
context shape maps are derived from source invariants and expression correctness.
The original body evaluator result restores the caller binding with res_var;
map restoration and literal singleton restriction prove conversion/FEVERY and
continuing shape-map preservation, including absent and shadowed old bindings.
No target run, target shape, body post-state invariant or update premise is added. -/
@[hol "cakeml/pancake/proofs/pan_structsProofScript.sml" "compile_correct"
  (fmap_as_finite_support := [locals, globals, code, eshapes])
  (words_as_type_indexed_bitvec)]
theorem compileCorrectDec {width : Nat} {σ : Type} [NeZero width]
    (source post : PanSemStateFiniteExact width σ) (context : ContextExact)
    (name : MlS) (shape : ShapeHOL) (initializer : ExpHOL width) (body : ProgHOL width)
    (res : Option (PanSemResultExact width))
    (ih : ∀ value : ValueHOL width,
      @evalHOLExact width σ _ source.toExact
        (fun a => Classical.propDecidable (source.memaddrs a)) initializer = some value ∧
        shape = shapeOfHOLExact value →
      ∀ (post : PanSemStateFiniteExact width σ) (context : ContextExact)
        (res : Option (PanSemResultExact width)),
      ( PanSemStateFiniteExact.evaluateHOLFiniteState ({ source with locals := source.locals.update (name,value) }) body = (res, post) ∧
      context.structs = source.structs.map (fun entry => (entry.1, entry.2.fields)) ∧
      feveryHOL (fun entry => valueFldsOkHOLExact source.structs entry.2) ({ source with locals := source.locals.update (name,value) } : PanSemStateFiniteExact width σ).locals ∧
      feveryHOL (fun entry => valueFldsOkHOLExact source.structs entry.2) source.globals ∧
      feveryHOL (fun entry => isWfShapeValueHOLExact source.structs entry.2) ({ source with locals := source.locals.update (name,value) } : PanSemStateFiniteExact width σ).locals ∧
      feveryHOL (fun entry => isWfShapeValueHOLExact source.structs entry.2) source.globals ∧
      structInfosOkHOLExact source.structs ∧
      shapeMap context.locals = ({ source with locals := source.locals.update (name,value) } : PanSemStateFiniteExact width σ).locals.map2 (fun entry => shapeOfHOLExact entry.2) ∧
      shapeMap context.globals = source.globals.map2 (fun entry => shapeOfHOLExact entry.2) ∧
      res ≠ some .error) →
    PanSemStateFiniteExact.evaluateHOLFiniteState (convertStateExact context { source with locals := source.locals.update (name,value) })
      (compileProgExact context body) = (convertResHOL res, convertStateExact context post) ∧
    feveryHOL (fun entry => valueFldsOkHOLExact post.structs entry.2) post.locals ∧
    feveryHOL (fun entry => valueFldsOkHOLExact post.structs entry.2) post.globals ∧
    shapeMap context.globals = post.globals.map2 (fun entry => shapeOfHOLExact entry.2) ∧
    (isContResHOL res = true →
      shapeMap context.locals = post.locals.map2 (fun entry => shapeOfHOLExact entry.2)) ∧
    (∀ value ∈ resVsHOL res, valueFldsOkHOLExact post.structs value = true) ∧
    (∀ value ∈ resVsHOL res, isWfShapeValueHOLExact post.structs value = true))
    (h : PanSemStateFiniteExact.evaluateHOLFiniteState source (.dec name shape initializer body : ProgHOL width) = (res, post) ∧
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
      (compileProgExact context (.dec name shape initializer body : ProgHOL width)) = (convertResHOL res, convertStateExact context post) ∧
    feveryHOL (fun entry => valueFldsOkHOLExact post.structs entry.2) post.locals ∧
    feveryHOL (fun entry => valueFldsOkHOLExact post.structs entry.2) post.globals ∧
    shapeMap context.globals = post.globals.map2 (fun entry => shapeOfHOLExact entry.2) ∧
    (isContResHOL res = true →
      shapeMap context.locals = post.locals.map2 (fun entry => shapeOfHOLExact entry.2)) ∧
    (∀ value ∈ resVsHOL res, valueFldsOkHOLExact post.structs value = true) ∧
    (∀ value ∈ resVsHOL res, isWfShapeValueHOLExact post.structs value = true) := by
  classical
  rcases h with ⟨heval,hstructs,hlocal,hglobal,hwlocal,hwglobal,hinfo,hlocals,hglobals,herror⟩
  rw [PanSemStateFiniteExact.evaluateHOLFiniteState_dec_total] at heval
  dsimp only at heval
  cases hv : @evalHOLExact width σ _ source.toExact
      (fun a => Classical.propDecidable (source.memaddrs a)) initializer with
  | none =>
    simp only [hv, Prod.mk.injEq] at heval
    exact False.elim (herror heval.1.symm)
  | some value =>
    rw [hv] at heval
    dsimp only at heval
    split at heval
    next hshape =>
      have hs := (shapeEqHOL_eq_true _ _).mp hshape
      cases hb : PanSemStateFiniteExact.evaluateHOLFiniteState
          (PanSemStateFiniteExact.setVarHOLFinite name value source) body with
      | mk bodyRes middle =>
        rw [hb] at heval
        dsimp only at heval
        simp only [Prod.mk.injEq] at heval
        rcases heval with ⟨hr,hp⟩
        subst res
        subst post
        have hexp := CompileExpCorrectExact.compileExpCorrectExact source context initializer value
          ⟨hv,hlocals,hglobals,hstructs,hlocal,hglobal,hinfo⟩
        have hwf := @evalHOLExact_isWfShapeValueHOLExact width σ _ source.toExact
          (fun a => Classical.propDecidable (source.memaddrs a)) hwlocal hwglobal initializer value hv
        let upd : ContextExact := {context with locals := (name,shape)::context.locals}
        have hbodylocal := everyUpdate source.locals
          (fun entry => valueFldsOkHOLExact source.structs entry.2) name value hlocal hexp.2.1
        have hbodywf := everyUpdate source.locals
          (fun entry => isWfShapeValueHOLExact source.structs entry.2) name value hwlocal hwf
        have hbodyshapes : shapeMap upd.locals = (source.locals.update (name,value)).map2
            (fun entry => shapeOfHOLExact entry.2) := by
          simp only [upd, shapeMap, List.foldr_cons]
          rw [mapUpdate, ← hlocals, ← hs]
          rfl
        have hbody := ih value ⟨hv,hs⟩ middle upd bodyRes
          ⟨hb,hstructs,hbodylocal,hglobal,hbodywf,hwglobal,hinfo,hbodyshapes,hglobals,herror⟩
        have hstruct := (EvaluateStructsCodeInvariant.evaluateStructsCodeInv body
          (PanSemStateFiniteExact.setVarHOLFinite name value source) middle bodyRes hb).1
        change middle.structs = source.structs at hstruct
        have hconverted := ValueShapeConversion.shapeOfConvertVRev source.structs value
          ⟨hexp.2.1,hwf,hinfo⟩
        have ht := hexp.2.2
        simp only [PanSemStateFiniteExact.evalHOLFinite] at ht
        refine ⟨?_,?_,hbody.2.2.1,hbody.2.2.2.1,?_,hbody.2.2.2.2.2.1,hbody.2.2.2.2.2.2⟩
        · simp only [compileProgExact, PanSemStateFiniteExact.evaluateHOLFiniteState_dec_total]
          rw [ht]
          dsimp only
          have htshape : shapeEqHOL (compileShapeExact context.structs shape)
              (shapeOfHOLExact (convertV value)) = true := by
            apply (shapeEqHOL_eq_true _ _).mpr
            rw [hconverted, ← hstructs, ← hs]
          rw [htshape]
          simp only [ite_true]
          have hstate : PanSemStateFiniteExact.setVarHOLFinite name (convertV value)
              (convertStateExact context source) =
              convertStateExact upd (PanSemStateFiniteExact.setVarHOLFinite name value source) := by
            rw [show upd = {context with locals := (name,shape)::context.locals} from rfl,
              convertStateLocalContext]
            simp only [PanSemStateFiniteExact.setVarHOLFinite, convertStateExact]
            congr 1
            exact (mapUpdate source.locals (fun entry => convertV entry.2) name value).symm
          have hrun : PanSemStateFiniteExact.evaluateHOLFiniteState
              (convertStateExact upd (PanSemStateFiniteExact.setVarHOLFinite name value source))
              (compileProgExact {context with locals := (name,shape)::context.locals} body) =
              (convertResHOL bodyRes,convertStateExact upd middle) := hbody.1
          rw [hstate,hrun]
          dsimp only
          simp only [show upd = {context with locals := (name,shape)::context.locals} from rfl,
            convertStateExact, HolFiniteMapExact.lookup_map2, resVarCanonical]
          congr 1
          congr 1
          exact (MapRestoration.resVarFmapMap2Rev middle.locals
            (fun entry => convertV entry.2) name (source.locals.lookup name)).symm
        · dsimp only
          simp only [resVarCanonical]
          apply (MapRestoration.feveryResVar middle.locals
            (fun entry => valueFldsOkHOLExact middle.structs entry.2) name
            (source.locals.lookup name)).mpr
          constructor
          · intro key val he
            rw [MapRestoration.restrictExceptLookup] at he
            by_cases hk : key=name
            · simp [hk] at he
            · apply hbody.2.1 key val
              simpa [hk] using he
          · intro val he
            simpa only [hstruct] using hlocal name val he
        · intro hc
          have hbodymap := hbody.2.2.2.2.1 hc
          dsimp only
          simp only [resVarCanonical]
          rw [MapRestoration.resVarFmapMap2Rev]
          apply mapExt
          intro key
          by_cases hk : key=name
          · subst key
            simp only [HolFiniteMapExact.resVarEq]
            cases ho : source.locals.lookup name with
            | none =>
              simp only [Option.map_none, HolFiniteMapExact.eraseEq, FDOMSUB_HOL, ite_true]
              simpa only [HolFiniteMapExact.lookup_map2, ho, Option.map_none] using
                congrArg (fun m => m.lookup name) hlocals
            | some old =>
              simp only [Option.map_some, HolFiniteMapExact.updateEq, FUPDATE_HOL, ite_true]
              simpa only [HolFiniteMapExact.lookup_map2, ho, Option.map_some] using
                congrArg (fun m => m.lookup name) hlocals
          · have hright :
                (@HolFiniteMapExact.resVarEq MlS ShapeHOL (Classical.typeDecidableEq MlS)
                  (middle.locals.map2 (fun entry => shapeOfHOLExact entry.2))
                  (name,(source.locals.lookup name).map (fun y => shapeOfHOLExact y))).lookup key =
                (middle.locals.map2 (fun entry => shapeOfHOLExact entry.2)).lookup key := by
              cases source.locals.lookup name <;>
                simp [HolFiniteMapExact.resVarEq, HolFiniteMapExact.eraseEq,
                  HolFiniteMapExact.updateEq, FDOMSUB_HOL, FUPDATE_HOL, hk]
            rw [hright, ← hbodymap]
            simp only [upd, shapeMap, List.foldr_cons, HolFiniteMapExact.lookup_update, FUPDATE]
            have hne : ¬(name == key) := by
              intro he
              exact hk (beq_iff_eq.mp he).symm
            simp [hne]

    next hbad =>
      simp only [Prod.mk.injEq] at heval
      exact False.elim (herror heval.1.symm)
end Flapjack.Pancake.Proofs.PanStructs.CompileCorrectDec
