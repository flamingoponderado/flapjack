import Flapjack.Pancake.Semantics.PanSem.TotalEvalAgree

/-!
# Production PanSem entry state from evaluated declarations

HOL `semantics_decls_def` (`cakeml/pancake/semantics/panSemScript.sml:861-869`)
runs `evaluate_decls (s with structs := st_ctxt) decls` and then
`semantics s' start`.  HOL `evaluate_decls_def` (`:814-837`) writes only
`globals` (`Decl`), `code` (`Function`) and `eshapes` (`ExnDecl`), leaving every
other field of `s` unchanged.

Production `evaluateDecls` works on `PanSemDeclarationState`, whose `runtime`
holds the expression-evaluation fields and whose `code`/`eshapes` are
`InfoMap`s.  This module defines the canonical production entry state
`panSemEntryStateOfDecls` fed to the total evaluator, and proves the production
frame: `evaluateDecls` changes only `runtime.globals`, `code` and `eshapes`,
matching HOL.  The memory-domain fields `memaddrs`/`sharedMemaddrs` and the
byte order `be` are not carried by the declaration state; they come from the
machine state.  Untagged Flapjack-specific bridge infrastructure
(`flapjack-pxn.18.4.3.77.2.17.1`).  `evaluateDecls_agree` relates production
`evaluateDecls` to the exact `evaluateDeclsHOLFinite` over whole declaration
lists (`flapjack-pxn.18.4.3.77.2.17.2`), and
`panSemEntryStateOfDecls_codeRanged_exnRanged` gives the entry state's code and
exception-shape rangedness (`flapjack-pxn.18.4.3.77.2.17.3`).
-/

namespace Flapjack

open Flapjack.Pancake.PanLang
open Flapjack.Basis.Pure.MlString
open PanSemStateFiniteExact

/-- The production PanSem entry state after declaration evaluation: structure
    context, globals, locals, memory, FFI, clock and base/top addresses from the
    evaluated declaration state's runtime, `code` from its function entries (the
    HOL code value `(params, body, return)`), `exceptionShapes` by lookup in its
    exception-shape map, and the memory domains and byte order from `machine`. -/
def panSemEntryStateOfDecls {σ : Type}
    (machine : PanSemState (RiscV.Word 64) (FfiState σ))
    (decl : PanSemDeclarationState (RiscV.Word 64) σ) :
    PanSemState (RiscV.Word 64) (FfiState σ) where
  locals := decl.runtime.locals
  globals := decl.runtime.globals
  structs := decl.runtime.structs
  code := decl.code.map fun entry =>
    (entry.1, (entry.2.params, entry.2.body, entry.2.returnShape))
  exceptionShapes := fun exception => lookupInfo exception decl.eshapes
  memory := decl.runtime.memory
  memaddrs := machine.memaddrs
  sharedMemaddrs := machine.sharedMemaddrs
  clock := decl.runtime.clock
  be := machine.be
  ffi := decl.runtime.ffi
  baseAddress := decl.runtime.baseAddress
  topAddress := decl.runtime.topAddress

/-- **Production `evaluate_decls` frame.**  A successful production
    `evaluateDecls` changes only `runtime.globals`, `code` and `eshapes`; the rest
    of the runtime (structure context, locals, memory, FFI, clock, addresses,
    byte width and memory hooks) and the memory access are unchanged, as in HOL
    `evaluate_decls_def`. -/
theorem evaluateDecls_frame {σ : Type} :
    ∀ (declarations : List (Decl (RiscV.Word 64)))
      (state out : PanSemDeclarationState (RiscV.Word 64) σ),
      evaluateDecls state declarations = some out →
      out.runtime = { state.runtime with globals := out.runtime.globals } ∧
        out.memoryAccess = state.memoryAccess := by
  intro declarations
  induction declarations with
  | nil =>
      intro state out h
      simp only [evaluateDecls, Option.some.injEq] at h
      subst h
      exact ⟨rfl, rfl⟩
  | cons declaration declarations ih =>
      intro state out h
      cases declaration with
      | name _ _ =>
          simp only [evaluateDecls] at h
          exact ih state out h
      | decl shape name expression =>
          simp only [evaluateDecls] at h
          split at h
          · cases h
          · split at h
            · obtain ⟨hr, hm⟩ := ih _ out h
              exact ⟨by rw [hr], hm⟩
            · cases h
      | function fd =>
          simp only [evaluateDecls] at h
          split at h
          · obtain ⟨hr, hm⟩ := ih _ out h
            exact ⟨hr, hm⟩
          · cases h
      | exnDecl exception shape =>
          simp only [evaluateDecls] at h
          split at h
          · cases h
          · split at h
            · obtain ⟨hr, hm⟩ := ih _ out h
              exact ⟨hr, hm⟩
            · cases h

/-- The fields of the entry state that `evaluate_decls` does not write are those
    of the initial declaration state's runtime. -/
theorem panSemEntryStateOfDecls_frame {σ : Type}
    (machine : PanSemState (RiscV.Word 64) (FfiState σ))
    (declarations : List (Decl (RiscV.Word 64)))
    (state out : PanSemDeclarationState (RiscV.Word 64) σ)
    (h : evaluateDecls state declarations = some out) :
    (panSemEntryStateOfDecls machine out).structs = state.runtime.structs ∧
      (panSemEntryStateOfDecls machine out).locals = state.runtime.locals ∧
      (panSemEntryStateOfDecls machine out).memory = state.runtime.memory ∧
      (panSemEntryStateOfDecls machine out).ffi = state.runtime.ffi ∧
      (panSemEntryStateOfDecls machine out).clock = state.runtime.clock ∧
      (panSemEntryStateOfDecls machine out).baseAddress = state.runtime.baseAddress ∧
      (panSemEntryStateOfDecls machine out).topAddress = state.runtime.topAddress := by
  obtain ⟨hr, _⟩ := evaluateDecls_frame declarations state out h
  simp only [panSemEntryStateOfDecls]
  rw [hr]
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Production `isWfShape` agrees with the exact HOL `is_wf_shape` on a
    byte-ranged shape under a byte-ranged structure context. -/
theorem isWfShape_eq_isWfShapeExactHOL (context : StructContext)
    (hcontext : StructContextByteRanged context.toHOL) (shape : Shape)
    (hshape : ShapeByteRanged shape) :
    isWfShape context shape = isWfShapeExactHOL (panStructContextToHOL context) (shapeToHOL shape) := by
  rw [← isWfShapeHOL_toHOL, panStructContextToHOL]
  exact isWfShapeHOL_eq_isWfShapeExactHOL context.toHOL (fun p hp => (hcontext p hp).1) shape hshape


/-- `List.all` congruence on the list members. -/
theorem list_all_congr_mem {β : Type} (l : List β) (f g : β → Bool)
    (h : ∀ x ∈ l, f x = g x) : l.all f = l.all g := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
      simp only [List.all_cons, h x (by simp), ih (fun y hy => h y (by simp [hy]))]

/-- `lookupInfo` commutes with mapping the values. -/
theorem lookupInfo_map_snd {β γ : Type} (key : String) (entries : List (String × β))
    (g : β → γ) :
    lookupInfo key (entries.map fun entry => (entry.1, g entry.2)) = (lookupInfo key entries).map g := by
  induction entries with
  | nil => rfl
  | cons entry entries ih =>
      simp only [List.map_cons, lookupInfo]
      split <;> simp [ih]

/-- Code lookup in the entry state is lookup in the declaration code map. -/
theorem panSemEntryStateOfDecls_codeLookup {σ : Type}
    (machine : PanSemState (RiscV.Word 64) (FfiState σ))
    (decl : PanSemDeclarationState (RiscV.Word 64) σ) (key : String) :
    panSemCodeLookup (panSemEntryStateOfDecls machine decl).code key =
      (lookupInfo key decl.code).map fun entry => (entry.params, entry.body, entry.returnShape) :=
  lookupInfo_map_snd key decl.code (fun entry => (entry.params, entry.body, entry.returnShape))

/-- The combined production/exact relation during declaration evaluation: the
    production entry state is related to the exact state and ranged, and the
    declaration state's memory access and byte width are the canonical ones. -/
def PanSemDeclEntryRel {σ : Type}
    (machine : PanSemState (RiscV.Word 64) (FfiState σ))
    (decl : PanSemDeclarationState (RiscV.Word 64) σ)
    (exact : PanSemStateFiniteExact 64 σ) : Prop :=
  PanSemStateRelExec (panSemEntryStateOfDecls machine decl) exact.toExact ∧
    PanSemStateRelExecRanged (panSemEntryStateOfDecls machine decl) ∧
    decl.memoryAccess = panSemBitVec64MemoryAccess machine ∧
    decl.runtime.bytesInWord = panSemBitVec64BytesInWord

/-- The production/exact declaration-evaluation outcome relation. -/
def PanSemDeclOutcomeRel {σ : Type}
    (machine : PanSemState (RiscV.Word 64) (FfiState σ)) :
    Option (PanSemDeclarationState (RiscV.Word 64) σ) →
      Option (PanSemStateFiniteExact 64 σ) → Prop
  | none, none => True
  | some decl, some exact => PanSemDeclEntryRel machine decl exact
  | _, _ => False

/-- **Production/exact `evaluate_decls` correspondence.**  For byte-ranged
    production declarations, production `evaluateDecls` and the tagged exact
    `evaluateDeclsHOLFinite` on `declarations.map declToHOL` (HOL
    `evaluate_decls_def`, `panSemScript.sml:814-837`) either both fail or both
    succeed, and success keeps the entry-state relation `PanSemDeclEntryRel`:
    the production entry state stays `PanSemStateRelExec`-related to the exact
    state and ranged.  Each clause is compared with its HOL counterpart:
    * `Name`: no-op on both sides;
    * `Decl`: the expression is evaluated with empty locals by both
      (`evalPanValueExp_agree`, under the canonical memory access and byte width),
      the shape tests agree (`panShapeMatches_eq_shapeEqHOL`), and the global
      update is `PanSemStateRelExec.updateGlobals`;
    * `Function`: the well-formed-shape tests agree
      (`isWfShape_eq_isWfShapeExactHOL`) and the code-map update corresponds
      pointwise on byte-ranged names;
    * `ExnDecl`: the absence test and shape test agree and the exception-shape
      update corresponds pointwise. -/
theorem evaluateDecls_agree {σ : Type}
    (machine : PanSemState (RiscV.Word 64) (FfiState σ)) :
    ∀ (declarations : List (Decl (RiscV.Word 64)))
      (decl : PanSemDeclarationState (RiscV.Word 64) σ) (exact : PanSemStateFiniteExact 64 σ),
      (∀ d ∈ declarations, DeclByteRanged d) →
      PanSemDeclEntryRel machine decl exact →
      PanSemDeclOutcomeRel machine (evaluateDecls decl declarations)
        (@evaluateDeclsHOLFinite 64 σ _ exact
          (fun a => Classical.propDecidable (exact.memaddrs a)) (declarations.map declToHOL)) := by
  intro declarations
  induction declarations with
  | nil =>
      intro decl exact _ h
      simp only [evaluateDecls, List.map_nil, evaluateDeclsHOLFinite]
      exact h
  | cons declaration declarations ih =>
      intro decl exact hranged h
      have htail : ∀ d ∈ declarations, DeclByteRanged d := fun d hd => hranged d (by simp [hd])
      have hhead := hranged declaration (by simp)
      cases declaration with
      | name s f =>
          simp only [evaluateDecls, List.map_cons, declToHOL, evaluateDeclsHOLFinite]
          exact ih decl exact htail h
      | decl shape name expression =>
          obtain ⟨hshape, hname, hexp⟩ : ShapeByteRanged shape ∧ NameRanged name ∧
            ExpByteRanged expression := hhead
          obtain ⟨hrel, hrg, hma, hbw⟩ := h
          letI : DecidablePred exact.memaddrs := fun a => Classical.propDecidable _
          have hrelE : PanSemStateRelExec (panEmptyLocals (panSemEntryStateOfDecls machine decl))
              (emptyLocalsHOLFinite exact).toExact := by
            simpa only [panEmptyLocals, toExact_emptyLocalsHOLFinite] using
              PanSemStateRelExec.emptyLocals hrel
          have hagree := @evalPanValueExp_agree σ (panEmptyLocals (panSemEntryStateOfDecls machine decl))
            (emptyLocalsHOLFinite exact) (fun a => Classical.propDecidable (exact.memaddrs a))
            hrelE hrg.panEmptyLocals expression hexp
          have hprodEq : evalPanValueExp decl.runtime.structs (fun _ => none) decl.runtime.globals
              decl.runtime.memory decl.runtime.baseAddress decl.runtime.topAddress
              decl.runtime.bytesInWord expression (memoryAccess := some decl.memoryAccess) =
              evalPanValueExp (panEmptyLocals (panSemEntryStateOfDecls machine decl)).structs
                (panEmptyLocals (panSemEntryStateOfDecls machine decl)).locals
                (panEmptyLocals (panSemEntryStateOfDecls machine decl)).globals
                (panEmptyLocals (panSemEntryStateOfDecls machine decl)).memory
                (panEmptyLocals (panSemEntryStateOfDecls machine decl)).baseAddress
                (panEmptyLocals (panSemEntryStateOfDecls machine decl)).topAddress
                panSemBitVec64BytesInWord expression
                (memoryAccess := some (panSemBitVec64MemoryAccess
                  (panEmptyLocals (panSemEntryStateOfDecls machine decl)))) := by
            rw [hbw, hma]
            rfl
          simp only [evaluateDecls, List.map_cons, declToHOL, evaluateDeclsHOLFinite]
          rw [hprodEq, ← hagree]
          cases hv : evalPanValueExp (panEmptyLocals (panSemEntryStateOfDecls machine decl)).structs
              (panEmptyLocals (panSemEntryStateOfDecls machine decl)).locals
              (panEmptyLocals (panSemEntryStateOfDecls machine decl)).globals
              (panEmptyLocals (panSemEntryStateOfDecls machine decl)).memory
              (panEmptyLocals (panSemEntryStateOfDecls machine decl)).baseAddress
              (panEmptyLocals (panSemEntryStateOfDecls machine decl)).topAddress
              panSemBitVec64BytesInWord expression
              (memoryAccess := some (panSemBitVec64MemoryAccess
                (panEmptyLocals (panSemEntryStateOfDecls machine decl)))) with
          | none => trivial
          | some value =>
              simp only [Option.map_some]
              have hvR := evalPanValueExp_byteRanged _ hrg.panEmptyLocals _ expression hexp value hv
              have hvShape := panValueShape_byteRanged decl.runtime.structs value hvR
              have hmatch : panShapeMatches (panValueShape decl.runtime.structs value) shape =
                  shapeEqHOL (shapeToHOL shape) (shapeOfHOLExact (panValueToHOL value)) := by
                rw [panShapeMatches_comm, shapeOfHOLExact_panValueToHOL decl.runtime.structs value]
                exact panShapeMatches_eq_shapeEqHOL shape _ hshape hvShape
              rw [← hmatch]
              by_cases hm : panShapeMatches (panValueShape decl.runtime.structs value) shape = true
              · rw [if_pos hm, if_pos hm]
                apply ih _ _ htail
                refine ⟨?_, ?_, hma, hbw⟩
                · exact PanSemStateRelExec.updateGlobals hrel name hname value
                · exact hrg.updateGlobals name value hvR
              · rw [if_neg hm, if_neg hm]
                trivial
      | function fd =>
          obtain ⟨hfname, hparams, _, hret⟩ : FunDeclByteRanged fd := hhead
          obtain ⟨hrel, hrg, hma, hbw⟩ := h
          have hsctx : StructContextByteRanged decl.runtime.structs.toHOL := hrg.2.2
          have hstructs : panStructContextToHOL decl.runtime.structs = exact.structs := hrel.2.2.1
          have hcheck : (fd.params.all (fun p => isWfShape decl.runtime.structs p.2) &&
              isWfShape decl.runtime.structs fd.returnShape) =
              ((fd.params.map paramToHOL).all (fun p => isWfShapeExactHOL exact.structs p.2) &&
                isWfShapeExactHOL exact.structs (shapeToHOL fd.returnShape)) := by
            rw [← hstructs, List.all_map,
              isWfShape_eq_isWfShapeExactHOL _ hsctx _ hret]
            congr 1
            apply list_all_congr_mem
            intro p hp
            exact isWfShape_eq_isWfShapeExactHOL _ hsctx _ (hparams p hp).2
          simp only [evaluateDecls, List.map_cons, declToHOL, evaluateDeclsHOLFinite, funDeclToHOL]
          rw [← hcheck]
          by_cases hc : (fd.params.all (fun p => isWfShape decl.runtime.structs p.2) &&
              isWfShape decl.runtime.structs fd.returnShape) = true
          · rw [if_pos hc, if_pos hc]
            apply ih _ _ htail
            refine ⟨?_, hrg.of_fields rfl rfl rfl, hma, hbw⟩
            obtain ⟨hl, hg, hs, hcode, he, hm, hmd, hsm, hck, hbe, hffi, hb, ht⟩ := hrel
            refine ⟨hl, hg, hs, ?_, he, hm, hmd, hsm, hck, hbe, hffi, hb, ht⟩
            intro q hq
            have hold := hcode q hq
            rw [panSemEntryStateOfDecls_codeLookup] at hold ⊢
            simp only [lookupInfo_panSemDeclUpdateInfo, FLOOKUP_update,
              HolFiniteMapExact.lookup_update_pointwise]
            by_cases hname : fd.name = q
            · subst hname
              simp [panLangEntryToHOL]
            · have hne : ofString q ≠ ofString fd.name :=
                fun h => hname (ofString_injective_of_ranged hfname hq h.symm)
              have hbeq : (fd.name == q) = false := beq_eq_false_iff_ne.mpr hname
              simp only [hbeq, hne, if_false, Bool.false_eq_true]
              exact hold
          · rw [if_neg hc, if_neg hc]
            trivial
      | exnDecl eid shape =>
          obtain ⟨heid, hshape⟩ : NameRanged eid ∧ ShapeByteRanged shape := hhead
          obtain ⟨hrel, hrg, hma, hbw⟩ := h
          have hsctx : StructContextByteRanged decl.runtime.structs.toHOL := hrg.2.2
          have hstructs : panStructContextToHOL decl.runtime.structs = exact.structs := hrel.2.2.1
          have hwf : isWfShape decl.runtime.structs shape =
              isWfShapeExactHOL exact.structs (shapeToHOL shape) := by
            rw [← hstructs]
            exact isWfShape_eq_isWfShapeExactHOL _ hsctx _ hshape
          have hlook : Option.map shapeToHOL (lookupInfo eid decl.eshapes) =
              exact.eshapes.lookup (ofString eid) := hrel.2.2.2.2.1 eid heid
          have hnone : (exact.eshapes.lookup (ofString eid)).isNone =
              !(lookupInfo eid decl.eshapes).isSome := by
            rw [← hlook]
            cases lookupInfo eid decl.eshapes <;> rfl
          simp only [evaluateDecls, List.map_cons, declToHOL, evaluateDeclsHOLFinite]
          rw [hnone, ← hwf]
          by_cases hs : (lookupInfo eid decl.eshapes).isSome = true
          · rw [if_pos hs]
            simp [hs, PanSemDeclOutcomeRel]
          · rw [if_neg hs]
            by_cases hw : isWfShape decl.runtime.structs shape = true
            · have hcond : (!(lookupInfo eid decl.eshapes).isSome &&
                  isWfShape decl.runtime.structs shape) = true := by
                simp [hs, hw]
              rw [if_pos hw, if_pos hcond]
              apply ih _ _ htail
              refine ⟨?_, hrg.of_fields rfl rfl rfl, hma, hbw⟩
              obtain ⟨hl, hg, hstr, hcode, he, hm, hmd, hsm, hck, hbe, hffi, hb, ht⟩ := hrel
              refine ⟨hl, hg, hstr, hcode, ?_, hm, hmd, hsm, hck, hbe, hffi, hb, ht⟩
              intro q hq
              have hold := he q hq
              simp only [panSemEntryStateOfDecls] at hold ⊢
              simp only [lookupInfo_panSemDeclUpdateInfo, FLOOKUP_update,
                HolFiniteMapExact.lookup_update_pointwise]
              by_cases hname : eid = q
              · subst hname
                simp
              · have hne : ofString q ≠ ofString eid :=
                  fun h => hname (ofString_injective_of_ranged heid hq h.symm)
                have hbeq : (eid == q) = false := beq_eq_false_iff_ne.mpr hname
                simp only [hbeq, hne, if_false, Bool.false_eq_true]
                exact hold
            · have hcond : ¬ (!(lookupInfo eid decl.eshapes).isSome &&
                  isWfShape decl.runtime.structs shape) = true := by
                simp [hw]
              rw [if_neg hw, if_neg hcond]
              trivial

/-- Membership in a declaration map update. -/
theorem mem_panSemDeclUpdateInfo {β : Type} {entries : InfoMap β} {name : String} {value : β}
    {x : String × β} (h : x ∈ panSemDeclUpdateInfo entries name value) :
    x = (name, value) ∨ x ∈ entries := by
  simp only [panSemDeclUpdateInfo, List.mem_cons, List.mem_filter] at h
  rcases h with h | ⟨h, _⟩
  · exact Or.inl h
  · exact Or.inr h

/-- A successful `lookupInfo` returns a stored value. -/
theorem lookupInfo_mem_of_some {β : Type} :
    ∀ (entries : List (String × β)) (key : String) (value : β),
      lookupInfo key entries = some value → ∃ k, (k, value) ∈ entries
  | [], _, _, h => by simp [lookupInfo] at h
  | (candidate, stored) :: rest, key, value, h => by
      simp only [lookupInfo] at h
      split at h
      · cases h
        exact ⟨candidate, by simp⟩
      · obtain ⟨k, hk⟩ := lookupInfo_mem_of_some rest key value h
        exact ⟨k, by simp [hk]⟩

/-- Successful production declaration evaluation keeps the stored code entries
    and exception shapes byte-ranged, for byte-ranged declarations. -/
theorem evaluateDecls_entries_ranged {σ : Type} :
    ∀ (declarations : List (Decl (RiscV.Word 64)))
      (decl out : PanSemDeclarationState (RiscV.Word 64) σ),
      (∀ d ∈ declarations, DeclByteRanged d) →
      evaluateDecls decl declarations = some out →
      (∀ entry ∈ decl.code,
        PanLangEntryByteRanged (entry.2.params, entry.2.body, entry.2.returnShape)) →
      (∀ entry ∈ decl.eshapes, ShapeByteRanged entry.2) →
      (∀ entry ∈ out.code,
        PanLangEntryByteRanged (entry.2.params, entry.2.body, entry.2.returnShape)) ∧
        (∀ entry ∈ out.eshapes, ShapeByteRanged entry.2) := by
  intro declarations
  induction declarations with
  | nil =>
      intro decl out _ h hc he
      simp only [evaluateDecls, Option.some.injEq] at h
      subst h
      exact ⟨hc, he⟩
  | cons declaration declarations ih =>
      intro decl out hranged h hc he
      have htail : ∀ d ∈ declarations, DeclByteRanged d := fun d hd => hranged d (by simp [hd])
      have hhead := hranged declaration (by simp)
      cases declaration with
      | name _ _ =>
          simp only [evaluateDecls] at h
          exact ih decl out htail h hc he
      | decl shape name expression =>
          simp only [evaluateDecls] at h
          split at h
          · cases h
          · split at h
            · exact ih _ out htail h hc he
            · cases h
      | function fd =>
          obtain ⟨_, hparams, hbody, hret⟩ : FunDeclByteRanged fd := hhead
          simp only [evaluateDecls] at h
          split at h
          · refine ih _ out htail h ?_ he
            intro entry hentry
            rcases mem_panSemDeclUpdateInfo hentry with rfl | hentry
            · exact ⟨hparams, hbody, hret⟩
            · exact hc entry hentry
          · cases h
      | exnDecl eid shape =>
          obtain ⟨_, hshape⟩ : NameRanged eid ∧ ShapeByteRanged shape := hhead
          simp only [evaluateDecls] at h
          split at h
          · cases h
          · split at h
            · refine ih _ out htail h hc ?_
              intro entry hentry
              rcases mem_panSemDeclUpdateInfo hentry with rfl | hentry
              · exact hshape
              · exact he entry hentry
            · cases h

/-- The entry state of a successful byte-ranged declaration evaluation has
    byte-ranged code and exception shapes. -/
theorem panSemEntryStateOfDecls_codeRanged_exnRanged {σ : Type}
    (machine : PanSemState (RiscV.Word 64) (FfiState σ))
    (declarations : List (Decl (RiscV.Word 64)))
    (decl out : PanSemDeclarationState (RiscV.Word 64) σ)
    (hranged : ∀ d ∈ declarations, DeclByteRanged d)
    (hc : ∀ entry ∈ decl.code,
      PanLangEntryByteRanged (entry.2.params, entry.2.body, entry.2.returnShape))
    (he : ∀ entry ∈ decl.eshapes, ShapeByteRanged entry.2)
    (h : evaluateDecls decl declarations = some out) :
    PanSemCodeRanged (panSemEntryStateOfDecls machine out) ∧
      PanSemExceptionShapesRanged (panSemEntryStateOfDecls machine out) := by
  obtain ⟨hcOut, heOut⟩ := evaluateDecls_entries_ranged declarations decl out hranged h hc he
  refine ⟨panSemCodeRanged_of_entries _ ?_, ?_⟩
  · intro entry hentry
    obtain ⟨e, he', rfl⟩ := List.mem_map.mp hentry
    exact hcOut e he'
  · intro eid shape hlookup
    obtain ⟨k, hk⟩ := lookupInfo_mem_of_some out.eshapes eid shape hlookup
    exact heOut (k, shape) hk

end Flapjack
