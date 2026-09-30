import Flapjack.Pancake.Proofs.PanGlobals
import Flapjack.Pancake.Semantics.PanProps

/-!
# pan_globals declaration-list lemmas over the exact `DeclHOL` carrier

Exact counterparts of the `pan_globalsProofScript.sml` list lemmas used by
`compile_top_semantics_decls` (bead `flapjack-pxn.18.5.2.22.7`).  The older
declarations of the same HOL names in `Flapjack.Pancake.Proofs.PanGlobals`
range over the production `Decl α`/`String` carriers and remain documented
mismatches; the theorems here use the reviewed word-indexed `DeclHOL width`
carrier with `MlS` names and `ShapeHOL` shapes, and the tagged exact
definitions `functionsHOL`, `exceptionsHOL`, `decShapesHOL`, `fpermDecsHOL`,
`resortDeclsHOL`, `newMainNameHOL`, `freshNameMlS` and the `is_*` predicates.

Renderings: HOL `FILTER` is `List.filter`, `MAP FST` is `List.map Prod.fst`,
`ALL_DISTINCT` is `List.Nodup`, `MEM` is `∈`, and `EVERY P xs` for a
Bool-valued `P` is `∀ d ∈ xs, P d = true`.  The `is_*` predicates are
Bool-valued as in HOL, so a HOL use as a proposition is `_ = true`.
-/

namespace Flapjack

open Flapjack.Pancake.PanLang

namespace PanGlobalsDeclListExact

/- Constructor-head evaluation of the `is_*` predicates.  The fallback
equations carry a constructor-disequality premise, so `simp` only rewrites
predicate applications at a concrete constructor and leaves the filter
lambdas (and hence the induction hypotheses) syntactically intact. -/
attribute [local simp] isFunctionHOL.eq_1 isFunctionHOL.eq_2 isNameHOL.eq_1
  isNameHOL.eq_2 isDeclHOL.eq_1 isDeclHOL.eq_2 isExnDeclHOL.eq_1 isExnDeclHOL.eq_2

/-- Exact HOL `fresh_name_correct` (`pan_globalsProofScript.sml:993-995`) over
    the exact `mlstring` carrier: `MEM (fresh_name name names) names ⇒ F`.
    The String-backed `freshNameHOL_not_mem_hol` is the `names_as_string`
    rendering of the same HOL theorem. -/
@[hol "cakeml/pancake/proofs/pan_globalsProofScript.sml" "fresh_name_correct"]
theorem freshNameMlS_correct :
    ∀ (name : MlS) (names : List MlS), freshNameMlS name names ∈ names → False := by
  intro name names
  fun_induction freshNameMlS name names with
  | case1 name _ ih => exact ih
  | case2 name hnot => exact hnot

/-- Exact native `mlstring` port of HOL's subset freshness corollary.
The subset is written pointwise as membership implication, preserving HOL's
`set names' ⊆ set names`; no String codec or byte-range premise is needed. -/
@[hol "cakeml/pancake/proofs/pan_globalsProofScript.sml" "fresh_name_correct'"]
theorem freshNameMlS_correctSubset :
    ∀ (name : MlS) (names names' : List MlS),
      freshNameMlS name names ∈ names' →
      (∀ candidate, candidate ∈ names' → candidate ∈ names) → False := by
  intro name names names' hmem hsubset
  exact freshNameMlS_correct name names (hsubset _ hmem)

/-- Exact HOL `ALL_DISTINCT_fperm_decs` (`pan_globalsProofScript.sml:1711-1714`). -/
@[hol "cakeml/pancake/proofs/pan_globalsProofScript.sml" "ALL_DISTINCT_fperm_decs"]
theorem ALL_DISTINCT_fperm_decsHOL {width : Nat} [NeZero width] :
    ∀ (x y : MlS) (code : List (DeclHOL width)),
      ((functionsHOL code).map Prod.fst).Nodup →
      ((functionsHOL (fpermDecsHOL x y code)).map Prod.fst).Nodup := by
  intro x y code hnodup
  rw [functionsFpermDecsHOL, List.map_map]
  have hcomp : (Prod.fst ∘ fun entry : MlS × List (MlS × ShapeHOL) × ProgHOL width × ShapeHOL =>
      (fpermName x y entry.1, entry.2.1, fpermHOL x y entry.2.2.1, entry.2.2.2)) =
      fpermName x y ∘ Prod.fst := rfl
  rw [hcomp, ← List.map_map]
  refine List.Pairwise.map (fpermName x y) ?_ hnodup
  intro a b hne heq
  apply hne
  have := congrArg (fpermName x y) heq
  rwa [fpermName_cancel, fpermName_cancel] at this

/-- Exact HOL `fperm_decs_decls` (`pan_globalsProofScript.sml:2023-2026`).
    HOL's binder `ys` is unused, so its type is an unconstrained type
    variable, rendered as the free type `δ`. -/
@[hol "cakeml/pancake/proofs/pan_globalsProofScript.sml" "fperm_decs_decls"]
theorem fperm_decs_declsHOL {width : Nat} [NeZero width] {δ : Type} :
    ∀ (f g : MlS) (xs : List (DeclHOL width)) (_ys : δ),
      (∀ d ∈ xs, (!isFunctionHOL d) = true) → fpermDecsHOL f g xs = xs := by
  intro f g xs _ys hxs
  induction xs with
  | nil => simp [fpermDecsHOL]
  | cons d ds ih =>
      have htail : ∀ e ∈ ds, (!isFunctionHOL e) = true := fun e he => hxs e (by simp [he])
      have hd := hxs d (by simp)
      cases d with
      | function fi => simp [isFunctionHOL] at hd
      | decl shape name value => simp [fpermDecsHOL, ih htail]
      | exnDecl name shape => simp [fpermDecsHOL, ih htail]
      | name name fields => simp [fpermDecsHOL, ih htail]

/-- Exact HOL `fperm_decs_FILTER_is_function`
    (`pan_globalsProofScript.sml:2032-2035`). -/
@[hol "cakeml/pancake/proofs/pan_globalsProofScript.sml" "fperm_decs_FILTER_is_function"]
theorem fperm_decs_FILTER_is_functionHOL {width : Nat} [NeZero width] :
    ∀ (f g : MlS) (decs : List (DeclHOL width)),
      fpermDecsHOL f g (decs.filter isFunctionHOL) =
        (fpermDecsHOL f g decs).filter isFunctionHOL := by
  intro f g decs
  induction decs with
  | nil => simp [fpermDecsHOL]
  | cons d ds ih =>
      cases d <;> simp [fpermDecsHOL, ih]

/-- Exact HOL `functions_FILTER_exn_decl` (`pan_globalsProofScript.sml:2042-2043`). -/
@[hol "cakeml/pancake/proofs/pan_globalsProofScript.sml" "functions_FILTER_exn_decl"]
theorem functions_FILTER_exn_declHOL {width : Nat} [NeZero width] :
    ∀ prog : List (DeclHOL width), functionsHOL (prog.filter isExnDeclHOL) = [] := by
  intro prog
  induction prog with
  | nil => rfl
  | cons d ds ih => cases d <;> simp [functionsHOL, ih]

/-- Exact HOL `functions_FILTER_is_name` (`pan_globalsProofScript.sml:2049-2050`). -/
@[hol "cakeml/pancake/proofs/pan_globalsProofScript.sml" "functions_FILTER_is_name"]
theorem functions_FILTER_is_nameHOL {width : Nat} [NeZero width] :
    ∀ prog : List (DeclHOL width), functionsHOL (prog.filter isNameHOL) = [] := by
  intro prog
  induction prog with
  | nil => rfl
  | cons d ds ih => cases d <;> simp [functionsHOL, ih]

/-- Exact HOL `resort_decls_preserve_functions`
    (`pan_globalsProofScript.sml:2055-2056`). -/
@[hol "cakeml/pancake/proofs/pan_globalsProofScript.sml" "resort_decls_preserve_functions"]
theorem resort_decls_preserve_functionsHOL {width : Nat} [NeZero width] :
    ∀ code : List (DeclHOL width), functionsHOL (resortDeclsHOL code) = functionsHOL code := by
  intro code
  have hdecl : functionsHOL (code.filter isDeclHOL) = [] := by
    induction code with
    | nil => rfl
    | cons d ds ih => cases d <;> simp [functionsHOL, ih]
  simp only [resortDeclsHOL, functionsHOL_append, functions_FILTER_is_nameHOL,
    functions_FILTER_exn_declHOL, hdecl, functionsHOL_filter_isFunction, List.nil_append]

/-- Exact HOL `new_main_name_correct` (`pan_globalsProofScript.sml:2073-2074`). -/
@[hol "cakeml/pancake/proofs/pan_globalsProofScript.sml" "new_main_name_correct"]
theorem new_main_name_correctHOL {width : Nat} [NeZero width]
    (code : List (DeclHOL width)) :
    newMainNameHOL code ∈ (functionsHOL code).map Prod.fst → False :=
  freshNameMlS_correct _ _

/-- Exact HOL `dec_shapes_append` (`pan_globalsProofScript.sml:2328-2329`). -/
@[hol "cakeml/pancake/proofs/pan_globalsProofScript.sml" "dec_shapes_append"]
theorem dec_shapes_appendHOL {width : Nat} [NeZero width] (xs ys : List (DeclHOL width)) :
    decShapesHOL (xs ++ ys) = decShapesHOL xs ++ decShapesHOL ys := by
  induction xs with
  | nil => rfl
  | cons d ds ih => cases d <;> simp [decShapesHOL, ih]

/-- Exact HOL `dec_shapes_functions` (`pan_globalsProofScript.sml:2335-2337`). -/
@[hol "cakeml/pancake/proofs/pan_globalsProofScript.sml" "dec_shapes_functions"]
theorem dec_shapes_functionsHOL {width : Nat} [NeZero width] (xs : List (DeclHOL width)) :
    (∀ d ∈ xs, isFunctionHOL d = true) → decShapesHOL xs = [] := by
  intro hxs
  induction xs with
  | nil => rfl
  | cons d ds ih =>
      have htail : ∀ e ∈ ds, isFunctionHOL e = true := fun e he => hxs e (by simp [he])
      have hd := hxs d (by simp)
      cases d <;> simp_all [decShapesHOL]

/-- Exact HOL `dec_shapes_FILTER` (`pan_globalsProofScript.sml:2343-2347`). -/
@[hol "cakeml/pancake/proofs/pan_globalsProofScript.sml" "dec_shapes_FILTER"]
theorem dec_shapes_FILTERHOL {width : Nat} [NeZero width] (xs : List (DeclHOL width)) :
    decShapesHOL (xs.filter (fun d => !isFunctionHOL d)) = decShapesHOL xs ∧
    decShapesHOL (xs.filter isNameHOL) = [] ∧
    decShapesHOL (xs.filter isDeclHOL) = decShapesHOL xs ∧
    decShapesHOL (xs.filter isExnDeclHOL) = [] := by
  induction xs with
  | nil => simp [decShapesHOL]
  | cons d ds ih =>
      obtain ⟨h1, h2, h3, h4⟩ := ih
      cases d <;> simp [decShapesHOL, h1, h2, h3, h4]

/-- Exact HOL `dec_shapes_fperm_decs` (`pan_globalsProofScript.sml:2354-2355`). -/
@[hol "cakeml/pancake/proofs/pan_globalsProofScript.sml" "dec_shapes_fperm_decs"]
theorem dec_shapes_fperm_decsHOL {width : Nat} [NeZero width] (f g : MlS)
    (xs : List (DeclHOL width)) :
    decShapesHOL (fpermDecsHOL f g xs) = decShapesHOL xs := by
  induction xs with
  | nil => simp [fpermDecsHOL]
  | cons d ds ih => cases d <;> simp [decShapesHOL, fpermDecsHOL, ih]

/-- Exact HOL `dec_shapes_resort_decls_def` (`pan_globalsProofScript.sml:2361-2362`). -/
@[hol "cakeml/pancake/proofs/pan_globalsProofScript.sml" "dec_shapes_resort_decls_def"]
theorem dec_shapes_resort_declsHOL {width : Nat} [NeZero width] (xs : List (DeclHOL width)) :
    decShapesHOL (resortDeclsHOL xs) = decShapesHOL xs := by
  obtain ⟨_, h2, h3, h4⟩ := dec_shapes_FILTERHOL xs
  have hfun : decShapesHOL (xs.filter isFunctionHOL) = [] :=
    dec_shapes_functionsHOL _ (fun d hd => (List.mem_filter.mp hd).2)
  simp only [resortDeclsHOL, dec_shapes_appendHOL, h2, h3, h4, hfun, List.nil_append,
    List.append_nil]

/-- Exact HOL `exceptions_append` (`pan_globalsProofScript.sml:2507-2509`). -/
@[hol "cakeml/pancake/proofs/pan_globalsProofScript.sml" "exceptions_append"]
theorem exceptions_appendHOL {width : Nat} [NeZero width] :
    ∀ ds ds' : List (DeclHOL width),
      exceptionsHOL (ds ++ ds') = exceptionsHOL ds ++ exceptionsHOL ds' := by
  intro ds ds'
  induction ds with
  | nil => rfl
  | cons d ds ih => cases d <;> simp [exceptionsHOL, ih]

/-- Exact HOL `exceptions_FILTER_is_function`
    (`pan_globalsProofScript.sml:2515-2520`). -/
@[hol "cakeml/pancake/proofs/pan_globalsProofScript.sml" "exceptions_FILTER_is_function"]
theorem exceptions_FILTER_is_functionHOL {width : Nat} [NeZero width]
    (decs : List (DeclHOL width)) :
    exceptionsHOL (decs.filter isFunctionHOL) = [] ∧
    exceptionsHOL (decs.filter (fun d => !isFunctionHOL d)) = exceptionsHOL decs ∧
    exceptionsHOL (decs.filter isExnDeclHOL) = exceptionsHOL decs ∧
    exceptionsHOL (decs.filter isNameHOL) = [] ∧
    exceptionsHOL (decs.filter isDeclHOL) = [] := by
  induction decs with
  | nil => simp [exceptionsHOL]
  | cons d ds ih =>
      obtain ⟨h1, h2, h3, h4, h5⟩ := ih
      cases d <;> simp [exceptionsHOL, h1, h2, h3, h4, h5]

/-- Exact HOL `not_is_function` (`pan_globalsProofScript.sml:2527-2530`). -/
@[hol "cakeml/pancake/proofs/pan_globalsProofScript.sml" "not_is_function"]
theorem not_is_functionHOL {width : Nat} [NeZero width] (x : DeclHOL width) :
    (isNameHOL x = true → ¬ isFunctionHOL x = true) ∧
    (isDeclHOL x = true → ¬ isFunctionHOL x = true) ∧
    (isExnDeclHOL x = true → ¬ isFunctionHOL x = true) := by
  cases x <;> simp [isNameHOL, isDeclHOL, isExnDeclHOL, isFunctionHOL]

/-- Exact HOL `decl_distinct` (`pan_globalsProofScript.sml:2535-2538`). -/
@[hol "cakeml/pancake/proofs/pan_globalsProofScript.sml" "decl_distinct"]
theorem decl_distinctHOL {width : Nat} [NeZero width] (x : DeclHOL width) :
    ((isDeclHOL x = true ∧ isNameHOL x = true) ↔ False) ∧
    ((isDeclHOL x = true ∧ isFunctionHOL x = true) ↔ False) ∧
    ((isDeclHOL x = true ∧ isExnDeclHOL x = true) ↔ False) := by
  cases x <;> simp [isNameHOL, isDeclHOL, isExnDeclHOL, isFunctionHOL]

/-- Exact HOL `functions_filter_nil` (`pan_globalsProofScript.sml:2967-2968`). -/
@[hol "cakeml/pancake/proofs/pan_globalsProofScript.sml" "functions_filter_nil"]
theorem functions_filter_nilHOL {width : Nat} [NeZero width] :
    ∀ decls : List (DeclHOL width),
      functionsHOL (decls.filter (fun d => !isFunctionHOL d)) = [] := by
  intro decls
  induction decls with
  | nil => rfl
  | cons d ds ih => cases d <;> simp [functionsHOL, ih]

end PanGlobalsDeclListExact

end Flapjack
