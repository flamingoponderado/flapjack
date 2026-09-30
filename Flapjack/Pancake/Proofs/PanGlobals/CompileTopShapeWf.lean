import Flapjack.Pancake.Proofs.PanGlobals.CompileDecsStructural
import Flapjack.Pancake.Semantics.PanProps

/-!
# pan_globals `compile_top` shape well-formedness (exact carriers)

Exact counterparts of `evaluate_decls_functions_wf`, `compile_top_shape_wf`
and `compile_top_shape_wf_nil` (`pan_globalsProofScript.sml:2367-2506`, bead
`flapjack-pxn.18.5.2.22.8`).  The declaration evaluator is the tagged
finite-support `evaluateDeclsHOLFinite` (`evaluate_decls_def`) on
`PanSemStateFiniteExact`, the same carrier used by the tagged `semantics_decls`
port; well-formedness is the tagged `isWfShapeExactHOL` (`is_wf_shape_def`)
and `isWfShapeNilHOL` (`is_wf_shape_nil`).  HOL `EVERY (is_wf_shape c ∘ SND)
ps` is `∀ p ∈ ps, isWfShapeExactHOL c p.2 = true`.  The evaluator's memory
domain decidability is not a binder: HOL membership in `s.memaddrs` is
classical, so every evaluator call (in hypotheses and conclusions) uses
`Classical.propDecidable`, as in the tagged `semantics_decls` port.
-/

namespace Flapjack

open Flapjack.Pancake.PanLang
open PanSemStateFiniteExact

namespace PanGlobalsCompileTopShapeWf

attribute [local simp] isFunctionHOL.eq_1 isFunctionHOL.eq_2 isNameHOL.eq_1
  isNameHOL.eq_2 isDeclHOL.eq_1 isDeclHOL.eq_2 isExnDeclHOL.eq_1 isExnDeclHOL.eq_2

/-- Same-module canonical witness for the `fmap_as_finite_support` qualifier
    on the four `PanSemStateFiniteExact` map fields. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} {σ : Type} [NeZero width] :
    (∀ (state : PanSemStateExact width σ) (h : state.FiniteSupport),
        (PanSemStateFiniteExact.ofExact state h).toExact = state) ∧
    (∀ state : PanSemStateFiniteExact width σ,
        PanSemStateFiniteExact.ofExact state.toExact state.toExact_finiteSupport = state) :=
  PanSemStateFiniteExact.holFmapAsFiniteSupportWitness

/-- Exact HOL `evaluate_decls_functions_wf` (`pan_globalsProofScript.sml:2367-2372`).
    HOL's free `s'` and `fi` are the outer parameters. -/
@[hol "cakeml/pancake/proofs/pan_globalsProofScript.sml" "evaluate_decls_functions_wf"
  (fmap_as_finite_support := [locals, globals, code, eshapes])
  (words_as_type_indexed_bitvec)]
theorem evaluate_decls_functions_wfHOL {width : Nat} {σ : Type} [NeZero width]
    (s' : PanSemStateFiniteExact width σ) (fi : FunDeclHOL width) :
    ∀ (s : PanSemStateFiniteExact width σ) (decs : List (DeclHOL width)),
      @evaluateDeclsHOLFinite width σ _ s (fun a => Classical.propDecidable (s.memaddrs a)) decs = some s' ∧ (.function fi : DeclHOL width) ∈ decs ∧
        (∀ d ∈ decs, isFunctionHOL d = true ∨ isDeclHOL d = true ∨ isExnDeclHOL d = true) →
      (∀ p ∈ fi.params, isWfShapeExactHOL s.structs p.2 = true) ∧
        isWfShapeExactHOL s.structs fi.returnShape = true := by
  intro s decs
  induction decs generalizing s with
  | nil => intro ⟨_, hmem, _⟩; simp at hmem
  | cons d ds ih =>
      intro ⟨hev, hmem, hall⟩
      have htail : ∀ e ∈ ds, isFunctionHOL e = true ∨ isDeclHOL e = true ∨
          isExnDeclHOL e = true := fun e he => hall e (by simp [he])
      cases d with
      | function fj =>
          simp only [evaluateDeclsHOLFinite] at hev
          split at hev
          next hwf =>
            simp only [Bool.and_eq_true, List.all_eq_true] at hwf
            rcases List.mem_cons.mp hmem with heq | hmem
            · cases heq
              exact ⟨fun p hp => hwf.1 p hp, hwf.2⟩
            · exact ih { s with code := s.code.update (fj.name, fj.params, fj.body, fj.returnShape) }
                ⟨hev, hmem, htail⟩
          next => simp at hev
      | decl shape name value =>
          have hmem' : (.function fi : DeclHOL width) ∈ ds := by simpa using hmem
          simp only [evaluateDeclsHOLFinite] at hev
          split at hev
          next value' _ =>
            split at hev
            next => exact ih (setGlobalHOLFinite name value' s) ⟨hev, hmem', htail⟩
            next => simp at hev
          next => simp at hev
      | exnDecl name shape =>
          have hmem' : (.function fi : DeclHOL width) ∈ ds := by simpa using hmem
          simp only [evaluateDeclsHOLFinite] at hev
          split at hev
          next => exact ih { s with eshapes := s.eshapes.update (name, shape) }
                    ⟨hev, hmem', htail⟩
          next => simp at hev
      | name name fields => simpa using hall (.name name fields) (by simp)

/-- Exact HOL `compile_top_shape_wf` (`pan_globalsProofScript.sml:2458-2464`). -/
@[hol "cakeml/pancake/proofs/pan_globalsProofScript.sml" "compile_top_shape_wf"
  (fmap_as_finite_support := [locals, globals, code, eshapes])
  (words_as_type_indexed_bitvec)]
theorem compile_top_shape_wfHOL {width : Nat} {σ : Type} [NeZero width]
    (s s' : PanSemStateFiniteExact width σ)
    (code : List (DeclHOL width)) (start : MlS) :
    @evaluateDeclsHOLFinite width σ _ s (fun a => Classical.propDecidable (s.memaddrs a)) code = some s' ∧
      (∀ d ∈ code, isFunctionHOL d = true ∨ isDeclHOL d = true ∨ isExnDeclHOL d = true) →
    ∀ d ∈ compileTopExactHOL code start, ∀ fi : FunDeclHOL width, d = .function fi →
      (∀ p ∈ fi.params, isWfShapeExactHOL s.structs p.2 = true) ∧
        isWfShapeExactHOL s.structs fi.returnShape = true := by
  intro ⟨hev, hall⟩
  have hwf : ∀ fj : FunDeclHOL width, (.function fj : DeclHOL width) ∈ code →
      (∀ p ∈ fj.params, isWfShapeExactHOL s.structs p.2 = true) ∧
        isWfShapeExactHOL s.structs fj.returnShape = true :=
    fun fj hfj => evaluate_decls_functions_wfHOL s' fj s code ⟨hev, hfj, hall⟩
  unfold compileTopExactHOL
  rw [compileTopFunctionLookup_eq_lookup]
  split
  · simp
  · next arguments body returnShape hlookup =>
    intro d hd fi hfi
    subst hfi
    simp only [List.mem_append, List.mem_cons] at hd
    rcases hd with hd | hd | hd
    · rw [PanGlobalsCompileDecsStructural.compile_decs_exns_are_exnsHOL _ _ _ _ _ _ rfl] at hd
      simp at hd
    · simp only [DeclHOL.function.injEq] at hd
      subst hd
      obtain ⟨l₁, l₂, hsplit, _⟩ := List.lookup_eq_some_iff.mp hlookup
      have hentry : (start, arguments, body, returnShape) ∈ functionsHOL code := by
        rw [hsplit]; simp
      obtain ⟨fj, hfj, heq⟩ := MEM_functionsHOL hentry
      simp only [Prod.mk.injEq] at heq
      obtain ⟨_, hparams, _, hret⟩ := heq
      obtain ⟨h1, h2⟩ := hwf fj hfj
      exact ⟨by simpa [hparams] using h1, by simpa [hret] using h2⟩
    · let P : DeclHOL width → Prop := fun d => ∀ fi : FunDeclHOL width, d = .function fi →
        (∀ p ∈ fi.params, isWfShapeExactHOL s.structs p.2 = true) ∧
          isWfShapeExactHOL s.structs fi.returnShape = true
      have hfunsP : ∀ (ctxt : PanGlobalsContextExact width) (code' : List (DeclHOL width)),
          (∀ e ∈ code', ∀ (fj : FunDeclHOL width) (ctxt : PanGlobalsContextExact width),
            e = .function fj →
              P (.function { fj with body := compileProgExactHOL ctxt fj.body })) →
          ∀ e ∈ (compileDecsExactHOL ctxt code').2.1, P e :=
        fun ctxt code' H =>
          PanGlobalsCompileDecsStructural.compile_decs_EVERYHOL P ctxt code' _ _ _ _ ⟨rfl, H⟩
      refine hfunsP _ _ ?_ _ hd fi rfl
      · apply EVERY_fperm_decsHOL
        · intro e _ hne fj ctxt hfj
          subst hfj
          simp at hne
        · intro e he fj hfj fk ctxt hfk
          subst hfj
          simp only [DeclHOL.function.injEq] at hfk
          intro fl hfl
          simp only [DeclHOL.function.injEq] at hfl
          subst hfk hfl
          have hmem : (.function fj : DeclHOL width) ∈ code := by
            simp only [resortDeclsHOL, List.mem_append, List.mem_filter] at he
            rcases he with ((h | h) | h) | h <;> exact h.1
          exact hwf fj hmem

/-- Exact HOL `compile_top_shape_wf_nil` (`pan_globalsProofScript.sml:2495-2502`). -/
@[hol "cakeml/pancake/proofs/pan_globalsProofScript.sml" "compile_top_shape_wf_nil"
  (fmap_as_finite_support := [locals, globals, code, eshapes])
  (words_as_type_indexed_bitvec)]
theorem compile_top_shape_wf_nilHOL {width : Nat} {σ : Type} [NeZero width]
    (s s' : PanSemStateFiniteExact width σ)
    (code : List (DeclHOL width)) (start : MlS) :
    @evaluateDeclsHOLFinite width σ _ s (fun a => Classical.propDecidable (s.memaddrs a)) code = some s' ∧ s.structs = [] ∧
      (∀ d ∈ code, isFunctionHOL d = true ∨ isDeclHOL d = true ∨ isExnDeclHOL d = true) →
    ∀ d ∈ compileTopExactHOL code start, ∀ fi : FunDeclHOL width, d = .function fi →
      (∀ p ∈ fi.params, isWfShapeNilHOL p.2 = true) ∧ isWfShapeNilHOL fi.returnShape = true := by
  intro ⟨hev, hstructs, hall⟩ d hd fi hfi
  have h := compile_top_shape_wfHOL s s' code start ⟨hev, hall⟩ d hd fi hfi
  rw [hstructs] at h
  exact h

end PanGlobalsCompileTopShapeWf

end Flapjack
