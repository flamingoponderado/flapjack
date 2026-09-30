import Flapjack.Pancake.Proofs.PanGlobals.DeclListLemmas
import Flapjack.Pancake.PanGlobals.CompileTopExact

/-!
# pan_globals `compile_decs`/`compile_top` structural lemmas (exact carriers)

Exact counterparts of the `pan_globalsProofScript.sml` structural lemmas about
`compile_decs` and `compile_top` used by `compile_top_semantics_decls`
(bead `flapjack-pxn.18.5.2.22.8`), over the tagged exact `compileDecsExactHOL`
(`compile_decs_def`), `compileProgExactHOL` (`compile_def`) and
`compileTopExactHOL` (`compile_top_def`) on the `DeclHOL`/`MlS` carriers and
the reviewed `PanGlobalsContextExact` context.  The older production-carrier
declarations of the same HOL names in `Flapjack.Pancake.Proofs.PanGlobals`
remain documented mismatches.

Renderings follow `DeclListLemmas`: `FILTER` is `List.filter`, `MAP FST` is
`List.map Prod.fst`, `EVERY P` is membership-quantified, Bool-valued `is_*`
predicates are used as `_ = true`, and HOL `ALOOKUP l k` is `l.lookup k`.
HOL `ARB` in `compile_decs_functions_thm` sits on a branch that the `EVERY
is_function` premise makes unreachable; it is rendered by the fixed
declaration `.name (ofString "") []`, following `functionsHOL_eq_FILTER`.
-/

namespace Flapjack

open Flapjack.Pancake.PanLang

namespace PanGlobalsCompileDecsStructural

attribute [local simp] isFunctionHOL.eq_1 isFunctionHOL.eq_2 isNameHOL.eq_1
  isNameHOL.eq_2 isDeclHOL.eq_1 isDeclHOL.eq_2 isExnDeclHOL.eq_1 isExnDeclHOL.eq_2

/-- Same-module canonical witness for the `fmap_as_finite_support` qualifier
    on `PanGlobalsContextExact.globals`. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} [NeZero width]
    (context : PanGlobalsContextExact width) :
    PanGlobalsContextExact.ofBroad (PanGlobalsContextExact.toBroad context) = context :=
  PanGlobalsContextExact.holFmapAsFiniteSupportWitness context

/-- Exact HOL `compile_decs_functions_thm` (`pan_globalsProofScript.sml:1951-1958`). -/
@[hol "cakeml/pancake/proofs/pan_globalsProofScript.sml" "compile_decs_functions_thm"
  (fmap_as_finite_support := [globals])
  (words_as_type_indexed_bitvec)]
theorem compile_decs_functions_thmHOL {width : Nat} [NeZero width] :
    ∀ (ctxt : PanGlobalsContextExact width) (fdecs : List (DeclHOL width))
      (decls : List (ProgHOL width)) (funs exns : List (DeclHOL width))
      (ctxt' : PanGlobalsContextExact width),
      compileDecsExactHOL ctxt fdecs = (decls, funs, exns, ctxt') ∧
        (∀ d ∈ fdecs, isFunctionHOL d = true) →
      decls = [] ∧ exns = [] ∧ ctxt' = ctxt ∧
        funs = fdecs.map (fun x => match x with
          | .function fi => .function { fi with body := compileProgExactHOL ctxt fi.body }
          | _ => .name (Flapjack.Basis.Pure.MlString.ofString "") []) := by
  intro ctxt fdecs
  induction fdecs with
  | nil =>
      intro decls funs exns ctxt' ⟨h, _⟩
      simp only [compileDecsExactHOL, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl, rfl⟩ := h
      simp
  | cons d ds ih =>
      intro decls funs exns ctxt' ⟨h, hall⟩
      have htail : ∀ e ∈ ds, isFunctionHOL e = true := fun e he => hall e (by simp [he])
      cases d with
      | function fi =>
          rcases hr : compileDecsExactHOL ctxt ds with ⟨a, b, c, e⟩
          simp only [compileDecsExactHOL, hr, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl, rfl, rfl⟩ := h
          obtain ⟨h1, h2, h3, h4⟩ := ih a b c e ⟨hr, htail⟩
          simp [h1, h2, h3, h4]
      | decl shape name value => simpa using hall (.decl shape name value) (by simp)
      | exnDecl name shape => simpa using hall (.exnDecl name shape) (by simp)
      | name name fields => simpa using hall (.name name fields) (by simp)

/-- Exact HOL `compile_decs_decls_thm` (`pan_globalsProofScript.sml:1967-1971`). -/
@[hol "cakeml/pancake/proofs/pan_globalsProofScript.sml" "compile_decs_decls_thm"
  (fmap_as_finite_support := [globals])
  (words_as_type_indexed_bitvec)]
theorem compile_decs_decls_thmHOL {width : Nat} [NeZero width] :
    ∀ (ctxt : PanGlobalsContextExact width) (fdecs : List (DeclHOL width))
      (decls : List (ProgHOL width)) (funs exns : List (DeclHOL width))
      (ctxt' : PanGlobalsContextExact width),
      compileDecsExactHOL ctxt fdecs = (decls, funs, exns, ctxt') ∧
        (∀ d ∈ fdecs, ¬ isFunctionHOL d = true) →
      funs = [] := by
  intro ctxt fdecs
  induction fdecs generalizing ctxt with
  | nil =>
      intro decls funs exns ctxt' ⟨h, _⟩
      simp only [compileDecsExactHOL, Prod.mk.injEq] at h
      exact h.2.1.symm
  | cons d ds ih =>
      intro decls funs exns ctxt' ⟨h, hall⟩
      have htail : ∀ e ∈ ds, ¬ isFunctionHOL e = true := fun e he => hall e (by simp [he])
      cases d with
      | function fi => exact absurd (by simp) (hall (.function fi) (by simp))
      | decl shape name value =>
          simp only [compileDecsExactHOL] at h
          generalize hr : compileDecsExactHOL (width := width) _ ds = r at h
          obtain ⟨a, b, c, e⟩ := r
          simp only [Prod.mk.injEq] at h
          obtain ⟨_, rfl, _, _⟩ := h
          exact ih _ a b c e ⟨hr, htail⟩
      | exnDecl name shape =>
          simp only [compileDecsExactHOL] at h
          generalize hr : compileDecsExactHOL (width := width) _ ds = r at h
          obtain ⟨a, b, c, e⟩ := r
          simp only [Prod.mk.injEq] at h
          obtain ⟨_, rfl, _, _⟩ := h
          exact ih _ a b c e ⟨hr, htail⟩
      | name name fields =>
          simp only [compileDecsExactHOL] at h
          exact ih _ _ _ _ _ ⟨h, htail⟩

/-- Exact HOL `compile_decs_EVERY_is_function` (`pan_globalsProofScript.sml:1977-1980`). -/
@[hol "cakeml/pancake/proofs/pan_globalsProofScript.sml" "compile_decs_EVERY_is_function"
  (fmap_as_finite_support := [globals])
  (words_as_type_indexed_bitvec)]
theorem compile_decs_EVERY_is_functionHOL {width : Nat} [NeZero width] :
    ∀ (ctxt : PanGlobalsContextExact width) (decs : List (DeclHOL width))
      (decls : List (ProgHOL width)) (funs exns : List (DeclHOL width))
      (ctxt' : PanGlobalsContextExact width),
      compileDecsExactHOL ctxt decs = (decls, funs, exns, ctxt') →
      ∀ d ∈ funs, isFunctionHOL d = true := by
  intro ctxt decs
  induction decs generalizing ctxt with
  | nil =>
      intro decls funs exns ctxt' h
      simp only [compileDecsExactHOL, Prod.mk.injEq] at h
      obtain ⟨_, rfl, _, _⟩ := h
      simp
  | cons d ds ih =>
      intro decls funs exns ctxt' h
      cases d with
      | function fi =>
          simp only [compileDecsExactHOL] at h
          generalize hr : compileDecsExactHOL (width := width) _ ds = r at h
          obtain ⟨a, b, c, e⟩ := r
          simp only [Prod.mk.injEq] at h
          obtain ⟨_, rfl, _, _⟩ := h
          intro x hx
          rcases List.mem_cons.mp hx with rfl | hx
          · simp
          · exact ih _ a b c e hr x hx
      | decl shape name value =>
          simp only [compileDecsExactHOL] at h
          generalize hr : compileDecsExactHOL (width := width) _ ds = r at h
          obtain ⟨a, b, c, e⟩ := r
          simp only [Prod.mk.injEq] at h
          obtain ⟨_, rfl, _, _⟩ := h
          exact ih _ a b c e hr
      | exnDecl name shape =>
          simp only [compileDecsExactHOL] at h
          generalize hr : compileDecsExactHOL (width := width) _ ds = r at h
          obtain ⟨a, b, c, e⟩ := r
          simp only [Prod.mk.injEq] at h
          obtain ⟨_, rfl, _, _⟩ := h
          exact ih _ a b c e hr
      | name name fields =>
          simp only [compileDecsExactHOL] at h
          exact ih _ _ _ _ _ h

/-- Exact HOL `compile_decs_EVERY` (`pan_globalsProofScript.sml:1986-1991`).
    HOL's free predicate `P : 'a decl -> bool` is a Prop-valued predicate,
    as in `EVERY_fperm_decsHOL`. -/
@[hol "cakeml/pancake/proofs/pan_globalsProofScript.sml" "compile_decs_EVERY"
  (fmap_as_finite_support := [globals])
  (words_as_type_indexed_bitvec)]
theorem compile_decs_EVERYHOL {width : Nat} [NeZero width] (P : DeclHOL width → Prop) :
    ∀ (ctxt : PanGlobalsContextExact width) (decs : List (DeclHOL width))
      (decls : List (ProgHOL width)) (funs exns : List (DeclHOL width))
      (ctxt' : PanGlobalsContextExact width),
      compileDecsExactHOL ctxt decs = (decls, funs, exns, ctxt') ∧
        (∀ d ∈ decs, ∀ (fi : FunDeclHOL width) (ctxt : PanGlobalsContextExact width),
          d = .function fi →
            P (.function { fi with body := compileProgExactHOL ctxt fi.body })) →
      ∀ d ∈ funs, P d := by
  intro ctxt decs
  induction decs generalizing ctxt with
  | nil =>
      intro decls funs exns ctxt' ⟨h, _⟩
      simp only [compileDecsExactHOL, Prod.mk.injEq] at h
      obtain ⟨_, rfl, _, _⟩ := h
      simp
  | cons d ds ih =>
      intro decls funs exns ctxt' ⟨h, hall⟩
      have htail : ∀ e ∈ ds, ∀ (fi : FunDeclHOL width) (ctxt : PanGlobalsContextExact width),
          e = .function fi →
            P (.function { fi with body := compileProgExactHOL ctxt fi.body }) :=
        fun e he => hall e (by simp [he])
      cases d with
      | function fi =>
          simp only [compileDecsExactHOL] at h
          generalize hr : compileDecsExactHOL (width := width) _ ds = r at h
          obtain ⟨a, b, c, e⟩ := r
          simp only [Prod.mk.injEq] at h
          obtain ⟨_, rfl, _, _⟩ := h
          intro x hx
          rcases List.mem_cons.mp hx with rfl | hx
          · exact hall _ (by simp) fi ctxt rfl
          · exact ih _ a b c e ⟨hr, htail⟩ x hx
      | decl shape name value =>
          simp only [compileDecsExactHOL] at h
          generalize hr : compileDecsExactHOL (width := width) _ ds = r at h
          obtain ⟨a, b, c, e⟩ := r
          simp only [Prod.mk.injEq] at h
          obtain ⟨_, rfl, _, _⟩ := h
          exact ih _ a b c e ⟨hr, htail⟩
      | exnDecl name shape =>
          simp only [compileDecsExactHOL] at h
          generalize hr : compileDecsExactHOL (width := width) _ ds = r at h
          obtain ⟨a, b, c, e⟩ := r
          simp only [Prod.mk.injEq] at h
          obtain ⟨_, rfl, _, _⟩ := h
          exact ih _ a b c e ⟨hr, htail⟩
      | name name fields =>
          simp only [compileDecsExactHOL] at h
          exact ih _ _ _ _ _ ⟨h, htail⟩

/-- Exact HOL `compile_decls_append` (`pan_globalsProofScript.sml:1997-2004`). -/
@[hol "cakeml/pancake/proofs/pan_globalsProofScript.sml" "compile_decls_append"
  (fmap_as_finite_support := [globals])
  (words_as_type_indexed_bitvec)]
theorem compile_decls_appendHOL {width : Nat} [NeZero width] :
    ∀ (decs' : List (DeclHOL width)) (ctxt : PanGlobalsContextExact width)
      (decs : List (DeclHOL width)),
      compileDecsExactHOL ctxt (decs ++ decs') =
        let (decls, funs, exns, ctxt') := compileDecsExactHOL ctxt decs
        let (decls', funs', exns', ctxt'') := compileDecsExactHOL ctxt' decs'
        (decls ++ decls', funs ++ funs', exns ++ exns', ctxt'') := by
  intro decs' ctxt decs
  induction decs generalizing ctxt with
  | nil => simp [compileDecsExactHOL]
  | cons d ds ih =>
      cases d with
      | function fi => simp only [List.cons_append, compileDecsExactHOL, ih]
      | decl shape name value => simp only [List.cons_append, compileDecsExactHOL, ih]
      | exnDecl name shape => simp only [List.cons_append, compileDecsExactHOL, ih]
      | name name fields => simp only [List.cons_append, compileDecsExactHOL, ih]

/-- Exact HOL `compile_decls_append_IMP` (`pan_globalsProofScript.sml:2012-2019`),
the tupling corollary of `compile_decls_append` used inside
`evaluate_decls_compile_top`. -/
@[hol "cakeml/pancake/proofs/pan_globalsProofScript.sml" "compile_decls_append_IMP"
  (fmap_as_finite_support := [globals])
  (words_as_type_indexed_bitvec)]
theorem compile_decls_appendIMPHOL {width : Nat} [NeZero width]
    (decs' : List (DeclHOL width)) (ctxt : PanGlobalsContextExact width)
    (decs : List (DeclHOL width))
    (X : List (ProgHOL width) × List (DeclHOL width) × List (DeclHOL width) ×
      PanGlobalsContextExact width) :
    compileDecsExactHOL ctxt (decs ++ decs') = X →
      (let (decls, funs, exns, ctxt') := compileDecsExactHOL ctxt decs
       let (decls', funs', exns', ctxt'') := compileDecsExactHOL ctxt' decs'
       (decls ++ decls', funs ++ funs', exns ++ exns', ctxt'')) = X := by
  intro h
  rw [compile_decls_appendHOL] at h
  exact h

/-- Exact HOL `compile_decs_preserve_functions` (`pan_globalsProofScript.sml:2062-2065`). -/
@[hol "cakeml/pancake/proofs/pan_globalsProofScript.sml" "compile_decs_preserve_functions"
  (fmap_as_finite_support := [globals])
  (words_as_type_indexed_bitvec)]
theorem compile_decs_preserve_functionsHOL {width : Nat} [NeZero width] :
    ∀ (code : List (DeclHOL width)) (ctxt : PanGlobalsContextExact width)
      (decs : List (ProgHOL width)) (funs exns : List (DeclHOL width))
      (ctxt' : PanGlobalsContextExact width),
      compileDecsExactHOL ctxt code = (decs, funs, exns, ctxt') →
      (functionsHOL funs).map Prod.fst = (functionsHOL code).map Prod.fst := by
  intro code
  induction code with
  | nil =>
      intro ctxt decs funs exns ctxt' h
      simp only [compileDecsExactHOL, Prod.mk.injEq] at h
      obtain ⟨_, rfl, _, _⟩ := h
      rfl
  | cons d ds ih =>
      intro ctxt decs funs exns ctxt' h
      cases d with
      | function fi =>
          simp only [compileDecsExactHOL] at h
          generalize hr : compileDecsExactHOL (width := width) _ ds = r at h
          obtain ⟨a, b, c, e⟩ := r
          simp only [Prod.mk.injEq] at h
          obtain ⟨_, rfl, _, _⟩ := h
          simp [functionsHOL, ih _ a b c e hr]
      | decl shape name value =>
          simp only [compileDecsExactHOL] at h
          generalize hr : compileDecsExactHOL (width := width) _ ds = r at h
          obtain ⟨a, b, c, e⟩ := r
          simp only [Prod.mk.injEq] at h
          obtain ⟨_, rfl, _, _⟩ := h
          simpa [functionsHOL] using ih _ a b c e hr
      | exnDecl name shape =>
          simp only [compileDecsExactHOL] at h
          generalize hr : compileDecsExactHOL (width := width) _ ds = r at h
          obtain ⟨a, b, c, e⟩ := r
          simp only [Prod.mk.injEq] at h
          obtain ⟨_, rfl, _, _⟩ := h
          simpa [functionsHOL] using ih _ a b c e hr
      | name name fields =>
          simp only [compileDecsExactHOL] at h
          simpa [functionsHOL] using ih _ _ _ _ _ h

/-- Exact HOL `compile_decs_exns_are_exns` (`pan_globalsProofScript.sml:2448-2451`). -/
@[hol "cakeml/pancake/proofs/pan_globalsProofScript.sml" "compile_decs_exns_are_exns"
  (fmap_as_finite_support := [globals])
  (words_as_type_indexed_bitvec)]
theorem compile_decs_exns_are_exnsHOL {width : Nat} [NeZero width] :
    ∀ (ctxt : PanGlobalsContextExact width) (code : List (DeclHOL width))
      (decls : List (ProgHOL width)) (funs exns : List (DeclHOL width))
      (ctxt' : PanGlobalsContextExact width),
      compileDecsExactHOL ctxt code = (decls, funs, exns, ctxt') →
      exns = code.filter isExnDeclHOL := by
  intro ctxt code
  induction code generalizing ctxt with
  | nil =>
      intro decls funs exns ctxt' h
      simp only [compileDecsExactHOL, Prod.mk.injEq] at h
      obtain ⟨_, _, rfl, _⟩ := h
      rfl
  | cons d ds ih =>
      intro decls funs exns ctxt' h
      cases d with
      | function fi =>
          simp only [compileDecsExactHOL] at h
          generalize hr : compileDecsExactHOL (width := width) _ ds = r at h
          obtain ⟨a, b, c, e⟩ := r
          simp only [Prod.mk.injEq] at h
          obtain ⟨_, _, rfl, _⟩ := h
          simpa using ih _ a b c e hr
      | decl shape name value =>
          simp only [compileDecsExactHOL] at h
          generalize hr : compileDecsExactHOL (width := width) _ ds = r at h
          obtain ⟨a, b, c, e⟩ := r
          simp only [Prod.mk.injEq] at h
          obtain ⟨_, _, rfl, _⟩ := h
          simpa using ih _ a b c e hr
      | exnDecl name shape =>
          simp only [compileDecsExactHOL] at h
          generalize hr : compileDecsExactHOL (width := width) _ ds = r at h
          obtain ⟨a, b, c, e⟩ := r
          simp only [Prod.mk.injEq] at h
          obtain ⟨_, _, rfl, _⟩ := h
          simpa using ih _ a b c e hr
      | name name fields =>
          simp only [compileDecsExactHOL] at h
          simpa using ih _ _ _ _ _ h

/-- Exact HOL `compile_decs_FILTER_decs` (`pan_globalsProofScript.sml:2822-2825`). -/
@[hol "cakeml/pancake/proofs/pan_globalsProofScript.sml" "compile_decs_FILTER_decs"
  (fmap_as_finite_support := [globals])
  (words_as_type_indexed_bitvec)]
theorem compile_decs_FILTER_declsHOL {width : Nat} [NeZero width] :
    ∀ (ctxt : PanGlobalsContextExact width) (code : List (DeclHOL width))
      (decls : List (ProgHOL width)) (funs exns : List (DeclHOL width))
      (ctxt' : PanGlobalsContextExact width),
      compileDecsExactHOL ctxt code = (decls, funs, exns, ctxt') →
      compileDecsExactHOL ctxt (code.filter isDeclHOL) = (decls, [], [], ctxt') := by
  intro ctxt code
  induction code generalizing ctxt with
  | nil =>
      intro decls funs exns ctxt' h
      simp only [compileDecsExactHOL, Prod.mk.injEq] at h
      obtain ⟨rfl, _, _, rfl⟩ := h
      simp [compileDecsExactHOL]
  | cons d ds ih =>
      intro decls funs exns ctxt' h
      cases d with
      | function fi =>
          simp only [compileDecsExactHOL] at h
          generalize hr : compileDecsExactHOL (width := width) _ ds = r at h
          obtain ⟨a, b, c, e⟩ := r
          simp only [Prod.mk.injEq] at h
          obtain ⟨rfl, _, _, rfl⟩ := h
          simpa using ih _ a b c e hr
      | decl shape name value =>
          simp only [compileDecsExactHOL] at h
          generalize hr : compileDecsExactHOL (width := width) _ ds = r at h
          obtain ⟨a, b, c, e⟩ := r
          simp only [Prod.mk.injEq] at h
          obtain ⟨rfl, _, _, rfl⟩ := h
          simp only [List.filter_cons, isDeclHOL.eq_1, if_true, compileDecsExactHOL,
            ih _ a b c e hr]
      | exnDecl name shape =>
          simp only [compileDecsExactHOL] at h
          generalize hr : compileDecsExactHOL (width := width) _ ds = r at h
          obtain ⟨a, b, c, e⟩ := r
          simp only [Prod.mk.injEq] at h
          obtain ⟨rfl, _, _, rfl⟩ := h
          simpa using ih _ a b c e hr
      | name name fields =>
          simp only [compileDecsExactHOL] at h
          simpa using ih _ _ _ _ _ h

/-- Projection forms of `compile_decs_exns_are_exns` and
    `compile_decs_EVERY_is_function`, used to rewrite inside the unfolded
    `compile_top`. Local support; no separate HOL declaration. -/
private theorem compileDecs_exns_proj {width : Nat} [NeZero width]
    (ctxt : PanGlobalsContextExact width) (code : List (DeclHOL width)) :
    (compileDecsExactHOL ctxt code).2.2.1 = code.filter isExnDeclHOL :=
  compile_decs_exns_are_exnsHOL ctxt code _ _ _ _ rfl

private theorem compileDecs_funs_proj {width : Nat} [NeZero width]
    (ctxt : PanGlobalsContextExact width) (code : List (DeclHOL width)) :
    ∀ d ∈ (compileDecsExactHOL ctxt code).2.1, isFunctionHOL d = true :=
  compile_decs_EVERY_is_functionHOL ctxt code _ _ _ _ rfl

/-- Exact HOL `compile_top_only_functions_or_exns`
    (`pan_globalsProofScript.sml:2611-2612`). -/
@[hol "cakeml/pancake/proofs/pan_globalsProofScript.sml" "compile_top_only_functions_or_exns"
  (words_as_type_indexed_bitvec)]
theorem compile_top_only_functions_or_exnsHOL {width : Nat} [NeZero width]
    (code : List (DeclHOL width)) (start : MlS) :
    ∀ d ∈ compileTopExactHOL code start, isFunctionHOL d = true ∨ isExnDeclHOL d = true := by
  unfold compileTopExactHOL
  rw [compileTopFunctionLookup_eq_lookup]
  split
  · simp
  · intro d hd
    simp only [List.mem_append, List.mem_cons] at hd
    rcases hd with hd | rfl | hd
    · rw [compileDecs_exns_proj] at hd
      exact Or.inr (List.mem_filter.mp hd).2
    · simp
    · exact Or.inl (compileDecs_funs_proj _ _ d hd)

/-- Renaming functions leaves the exception declarations unchanged. Local
    support for `exceptions_compile_top`, whose HOL proof uses
    `fperm_decs_append`/`fperm_decs_decls`; no separate HOL declaration. -/
private theorem exceptionsHOL_fpermDecsHOL {width : Nat} [NeZero width] (f g : MlS)
    (decs : List (DeclHOL width)) :
    exceptionsHOL (fpermDecsHOL f g decs) = exceptionsHOL decs := by
  induction decs with
  | nil => simp [fpermDecsHOL]
  | cons d ds ih => cases d <;> simp [fpermDecsHOL, exceptionsHOL, ih]

/-- A list of function declarations declares no exceptions. Local support;
    no separate HOL declaration. -/
private theorem exceptionsHOL_of_functions {width : Nat} [NeZero width] :
    ∀ decs : List (DeclHOL width), (∀ d ∈ decs, isFunctionHOL d = true) →
      exceptionsHOL decs = []
  | [], _ => rfl
  | d :: ds, h => by
      have hd := h d (by simp)
      have htail := exceptionsHOL_of_functions ds (fun e he => h e (by simp [he]))
      cases d <;> simp_all [exceptionsHOL]

/-- Exact HOL `exceptions_compile_top` (`pan_globalsProofScript.sml:2974-2976`). -/
@[hol "cakeml/pancake/proofs/pan_globalsProofScript.sml" "exceptions_compile_top"
  (words_as_type_indexed_bitvec)]
theorem exceptions_compile_topHOL {width : Nat} [NeZero width]
    (code : List (DeclHOL width)) (start : MlS)
    (x : List (MlS × ShapeHOL) × ProgHOL width × ShapeHOL) :
    (functionsHOL code).lookup start = some x →
    exceptionsHOL (compileTopExactHOL code start) = exceptionsHOL code := by
  intro hx
  unfold compileTopExactHOL
  rw [compileTopFunctionLookup_eq_lookup, hx]
  simp only
  rw [PanGlobalsDeclListExact.exceptions_appendHOL, compileDecs_exns_proj]
  simp only [exceptionsHOL]
  rw [exceptionsHOL_of_functions _ (compileDecs_funs_proj _ _), List.append_nil]
  obtain ⟨_, _, hexn, _, _⟩ :=
    PanGlobalsDeclListExact.exceptions_FILTER_is_functionHOL
      (fpermDecsHOL start (newMainNameHOL code) (resortDeclsHOL code))
  rw [hexn, exceptionsHOL_fpermDecsHOL]
  obtain ⟨hf, _, hexn', hname, hdecl⟩ :=
    PanGlobalsDeclListExact.exceptions_FILTER_is_functionHOL code
  simp only [resortDeclsHOL, PanGlobalsDeclListExact.exceptions_appendHOL, hf, hexn',
    hname, hdecl, List.nil_append, List.append_nil]

end PanGlobalsCompileDecsStructural

end Flapjack
