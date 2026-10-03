import Flapjack.Pancake.PanStructs.CompileDeclsExact
import Flapjack.Pancake.Semantics.PanSem.DeclContextExact
import Flapjack.Pancake.Proofs.PanStructs.StructInfosOkExact

/-! Original pan_structsProof `decs_stcnames_to_get_names` and
`decs_stcnames_infos_ok` (pan_structsProofScript.sml:1446-1471): the struct
names collected by `decs_stcnames` agree with `get_names`, and preserve
`struct_infos_ok`. -/

namespace Flapjack.Pancake.PanStructs.CompileShapeExact
open Flapjack.Pancake.PanLang

/-- An absent struct name is not a key of the context. Flapjack
infrastructure; no HOL original. -/
theorem structContextLookupHOL_none_not_mem (name : MlS) :
    ∀ (context : StructContextExact), structContextLookupHOL name context = none →
      name ∉ context.map Prod.fst
  | [], _ => by simp
  | (candidate, info) :: rest, h => by
      simp only [structContextLookupHOL] at h
      by_cases hc : name = candidate
      · simp [hc] at h
      · simp only [hc, if_false] at h
        have := structContextLookupHOL_none_not_mem name rest h
        simp only [List.map_cons, List.mem_cons, not_or]
        exact ⟨hc, this⟩

/-- The list well-formedness check is `EVERY` of the single-shape check.
Flapjack infrastructure; no HOL original. -/
theorem isWfShapesExactHOL_eq_all (context : StructContextExact) :
    ∀ shapes : List ShapeHOL,
      isWfShapesExactHOL context shapes = shapes.all (isWfShapeExactHOL context)
  | [] => rfl
  | shape :: shapes => by
      simp only [isWfShapesExactHOL, List.all_cons, isWfShapesExactHOL_eq_all context shapes]

/-- Exact HOL `decs_stcnames_to_get_names` (`pan_structsProofScript.sml:1446-1457`),
with the elaborated binders `acc code res ctxt` (captured by
`pan_structs_leaves_probe`). -/
@[hol "cakeml/pancake/proofs/pan_structsProofScript.sml" "decs_stcnames_to_get_names"
  (words_as_type_indexed_bitvec)]
theorem decsStcnamesToGetNames {width : Nat} [NeZero width] :
    ∀ (acc : StructContextExact) (code : List (DeclHOL width)) (res : StructContextExact)
      (ctxt : ContextExact),
      decsStcnamesHOLExact acc code = some res ∧
        ctxt.structs = acc.map (fun entry => (entry.1, entry.2.fields)) →
      getNamesExact ctxt code = { ctxt with structs := res.map (fun entry => (entry.1, entry.2.fields)) } := by
  intro acc code
  induction code generalizing acc with
  | nil =>
    rintro res ctxt ⟨h, hs⟩
    simp only [decsStcnamesHOLExact, Option.some.injEq] at h
    subst h
    simp only [getNamesExact, ← hs]
  | cons d ds ih =>
    rintro res ctxt ⟨h, hs⟩
    cases d with
    | name nm fields =>
      simp only [decsStcnamesHOLExact] at h
      split at h
      · exact absurd h (by simp)
      · split at h
        · split at h
          · simp only [getNamesExact]
            apply ih _ res _ ⟨h, _⟩
            simp [hs]
          · exact absurd h (by simp)
        · exact absurd h (by simp)
    | decl sh v e => exact ih acc res ctxt ⟨h, hs⟩
    | function f => exact ih acc res ctxt ⟨h, hs⟩
    | exnDecl n sh => exact ih acc res ctxt ⟨h, hs⟩

/-- Exact HOL `decs_stcnames_infos_ok` (`pan_structsProofScript.sml:1459-1471`).
The elaborated HOL theorem keeps a `ctxt` binder of its own type variable
that occurs nowhere in the formula (captured by `pan_structs_leaves_probe`);
it is retained. -/
@[hol "cakeml/pancake/proofs/pan_structsProofScript.sml" "decs_stcnames_infos_ok"
  (words_as_type_indexed_bitvec)]
theorem decsStcnamesInfosOk {width : Nat} [NeZero width] {β : Type} :
    ∀ (acc : StructContextExact) (code : List (DeclHOL width)) (res : StructContextExact)
      (_ctxt : β),
      decsStcnamesHOLExact acc code = some res ∧ Flapjack.Pancake.Proofs.PanStructs.StructInfosOkExact.structInfosOkHOLExact acc →
      Flapjack.Pancake.Proofs.PanStructs.StructInfosOkExact.structInfosOkHOLExact res := by
  intro acc code
  induction code generalizing acc with
  | nil =>
    rintro res _ ⟨h, hok⟩
    simp only [decsStcnamesHOLExact, Option.some.injEq] at h
    exact h ▸ hok
  | cons d ds ih =>
    rintro res c ⟨h, hok⟩
    cases d with
    | name nm fields =>
      simp only [decsStcnamesHOLExact] at h
      split at h
      · exact absurd h (by simp)
      · rename_i hnone
        split at h
        · rename_i hnd
          split at h
          · rename_i hwf
            refine ih _ res c ⟨h, ?_⟩
            exact Flapjack.Pancake.Proofs.PanStructs.StructInfosOkExact.structInfosOkHOLExact_cons acc nm _ hok hnd
              (structContextLookupHOL_none_not_mem nm acc hnone)
              (by rw [isWfShapesExactHOL_eq_all]; simpa using hwf) rfl
          · exact absurd h (by simp)
        · exact absurd h (by simp)
    | decl sh v e => exact ih acc res c ⟨h, hok⟩
    | function f => exact ih acc res c ⟨h, hok⟩
    | exnDecl n sh => exact ih acc res c ⟨h, hok⟩

/-- Exact HOL `compile_decs_no_names` (`pan_structsProofScript.sml:1570-1576`,
local in HOL); `EVERY` is membership quantification over the Boolean
classifiers. -/
@[hol "cakeml/pancake/proofs/pan_structsProofScript.sml" "compile_decs_no_names"
  (words_as_type_indexed_bitvec)]
theorem compileDecsNoNames {width : Nat} [NeZero width] :
    ∀ (ctxt : ContextExact) (decs : List (DeclHOL width)),
      ∀ d ∈ (compileDeclsExact ctxt decs).1,
        isFunctionHOL d = true ∨ isDeclHOL d = true ∨ isExnDeclHOL d = true := by
  intro ctxt decs
  induction decs generalizing ctxt with
  | nil => simp [compileDeclsExact]
  | cons d ds ih =>
    cases d <;> simp only [compileDeclsExact, List.mem_cons, forall_eq_or_imp]
    all_goals first
      | exact ih _
      | exact ⟨by simp [isFunctionHOL, isDeclHOL, isExnDeclHOL], ih _⟩

/-- Exact HOL `compile_top_no_names` (`pan_structsProofScript.sml:1578-1582`);
the free `pan_code` is bound explicitly. -/
@[hol "cakeml/pancake/proofs/pan_structsProofScript.sml" "compile_top_no_names"
  (words_as_type_indexed_bitvec)]
theorem compileTopNoNames {width : Nat} [NeZero width] (pan_code : List (DeclHOL width)) :
    ∀ d ∈ compileTopExact pan_code,
      isFunctionHOL d = true ∨ isDeclHOL d = true ∨ isExnDeclHOL d = true :=
  compileDecsNoNames _ pan_code

end Flapjack.Pancake.PanStructs.CompileShapeExact
