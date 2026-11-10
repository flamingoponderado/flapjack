module

public import Flapjack.Compiler.Backend.FlatPattern.Proofs.GlobalBounds

@[expose] public section

/-! Global-initialization safety for the pattern compilation traversal. -/
namespace Flapjack.Compiler.Backend.FlatPattern
open Flapjack.Compiler.Backend.BackendCommon FlatLang PatternCommon PatternSemantics
open Flapjack.Compiler.Backend.FlatProps

private theorem rowsSafe_iff (rows : List (FlatLang.Pat × FlatLang.Exp)) :
    esgcFreeRows rows ↔ ∀ p e, (p, e) ∈ rows → esgcFree e := by
  induction rows with
  | nil => simp [esgcFreeRows]
  | cons row rows ih =>
    obtain ⟨p, e⟩ := row
    simp only [esgcFreeRows, List.mem_cons, Prod.mk.injEq, ih]
    constructor
    · rintro ⟨he, hs⟩ p' e' (⟨_, rfl⟩ | member)
      · exact he
      · exact hs p' e' member
    · intro h
      exact ⟨h p e (by simp), fun p' e' member => h p' e' (Or.inr member)⟩

private theorem bagEmpty_of_bound (out input : GlobalBag)
    (bound : ∀ key, out key ≤ input key) (empty : input = emptyGlobalBag) :
    out = emptyGlobalBag := by
  funext key
  have h := bound key
  simp only [empty, emptyGlobalBag, Flapjack.emptyBag] at h ⊢
  omega

private theorem compileFuns_bagBounds (cfg : Config)
    (fs : List (Flapjack.AstHOL.VarN × Flapjack.AstHOL.VarN × FlatLang.Exp)) :
    ∀ key, funGlobals (compileFuns cfg fs).2.2 key ≤ funGlobals fs key := by
  induction fs with
  | nil => simp [compileFuns, funGlobals]
  | cons row fs ih =>
    obtain ⟨f, v, e⟩ := row
    cases he : compileExp cfg e with
    | mk i rest =>
      obtain ⟨sg, y⟩ := rest
      cases hfs : compileFuns cfg fs with
      | mk j rest =>
        obtain ⟨sgs, ys⟩ := rest
        intro key
        have h1 := compileExp_bagBounds cfg e key
        have h2 := ih key
        simp only [he] at h1
        simp only [hfs] at h2
        simp only [compileFuns, he, hfs, funGlobals, unionGlobalBag, Flapjack.bagUnion]
        omega

/-- The source expression, list, and row safety theorem. -/
@[hol "cakeml/compiler/backend/proofs/flat_patternProofScript.sml" "compile_exp_esgc_free"]
theorem compileExp_esgcFree :
    (∀ cfg exp n sg exp', compileExp cfg exp = (n, sg, exp') ∧ esgcFree exp → esgcFree exp') ∧
    (∀ cfg exps n sg exps', compileExps cfg exps = (n, sg, exps') ∧
      (∀ e ∈ exps, esgcFree e) → ∀ e ∈ exps', esgcFree e) ∧
    (∀ cfg rows n sg rows', compileMatch cfg rows = (n, sg, rows') ∧
      (∀ row ∈ rows, esgcFree row.2) → ∀ row ∈ rows', esgcFree row.2) := by
  have all (cfg : Config) :
      (∀ exp, esgcFree exp → esgcFree (compileExp cfg exp).2.2) ∧
      (∀ _fs : List (Flapjack.AstHOL.VarN × Flapjack.AstHOL.VarN × FlatLang.Exp), True) ∧
      (∀ es, esgcFreeList es → esgcFreeList (compileExps cfg es).2.2) ∧
      (∀ rows, esgcFreeRows rows → esgcFreeRows (compileMatch cfg rows).2.2) := by
    apply compileExp.mutual_induct cfg
    case case3 =>
      intro t x ps i sg y eq j sgp ps2 eqp ih ihp safe
      have h := safe
      simp only [esgcFree] at h
      have body : esgcFree y := by simpa [eq] using ih h.1
      have rows : esgcFreeRows ps2 := by simpa [eqp] using ihp h.2
      have branch := esgcFree_compilePats cfg sgp t (max i j + 2)
        (.varLocal t (encNumToName (max i j + 2)))
        (.raise t (.varLocal t (encNumToName (max i j + 2)))) ps2
        (by simp [esgcFree]) (by simp [esgcFree]) ((rowsSafe_iff ps2).mp rows)
      simpa [compileExp, eq, eqp, esgcFree, esgcFreeRows, body] using branch
    case case5 =>
      intro t v x i sg y eq ih safe
      simp only [esgcFree] at safe
      simp only [compileExp, eq, esgcFree]
      apply bagEmpty_of_bound _ _ _ safe
      simpa only [eq] using compileExp_bagBounds cfg x
    case case7 =>
      intro t x ps i sg y eq j sgp ps2 eqp ih ihp safe
      have h := safe
      simp only [esgcFree] at h
      have body : esgcFree y := by simpa [eq] using ih h.1
      have rows : esgcFreeRows ps2 := by simpa [eqp] using ihp h.2
      have branch := esgcFree_compilePats cfg sgp t (max i j + 2)
        (.varLocal t (encNumToName (max i j + 2)))
        (.raise t (.con t (some (0, none)) [])) ps2
        (by simp [esgcFree]) (by simp [esgcFree, esgcFreeList]) ((rowsSafe_iff ps2).mp rows)
      simpa [compileExp, eq, eqp, esgcFree, body] using branch
    case case9 =>
      intro t fs x j sgfs fs2 eqf i sg y eq ihf ih
      simp only [esgcFree, compileExp, eqf, eq]
      intro safe
      constructor
      · simpa [eq] using ih safe.1
      · apply bagEmpty_of_bound _ _ _ safe.2
        simpa only [eqf] using compileFuns_bagBounds cfg fs
    case case10 =>
      intro t x1 x2 x3 i sg1 y1 eq1 j sg2 y2 eq2 k sg3 y3 eq3 ih1 ih2 ih3
      simp only [esgcFree, compileExp, eq1, eq2, eq3]
      intro safe
      apply esgcFree_smartIf
      · simpa [eq1] using ih1 safe.1
      · simpa [eq2] using ih2 safe.2.1
      · simpa [eq3] using ih3 safe.2.2
    all_goals intros
    all_goals simp_all [compileExp, compileExps, compileMatch, esgcFree, esgcFreeRows, esgcFreeList]
  refine ⟨?_, ?_, ?_⟩
  · intro cfg exp n sg exp' h
    simpa only [h.1] using (all cfg).1 exp h.2
  · intro cfg exps n sg exps' h
    have out := (all cfg).2.2.1 exps ((FlatProps.esgcFreeList_iff exps).mpr h.2)
    rw [h.1] at out
    exact (FlatProps.esgcFreeList_iff exps').mp out
  · intro cfg rows n sg rows' h
    have input : esgcFreeRows rows := (rowsSafe_iff rows).mpr (by
      intro p e member
      exact h.2 (p, e) member)
    have out := (all cfg).2.2.2 rows input
    rw [h.1] at out
    intro row member
    exact (rowsSafe_iff rows').mp out row.1 row.2 (by cases row; exact member)

/-- Compiling a list of declarations preserves the original safety invariant. -/
@[hol "cakeml/compiler/backend/proofs/flat_patternProofScript.sml" "compile_decs_esgc_free"]
theorem compileDecs_esgcFree (cfg : Config) (ds : List FlatLang.Exp)
    (safe : ∀ d ∈ ds, esgcFree d) :
    ∀ d ∈ ds.map (compileDec cfg), esgcFree d := by
  intro d mem
  obtain ⟨source, sourceMem, rfl⟩ := List.mem_map.mp mem
  exact compileExp_esgcFree.1 cfg source (compileExp cfg source).1 (compileExp cfg source).2.1
    (compileExp cfg source).2.2 ⟨by cases h : compileExp cfg source with | mk a b => cases b; rfl,
      safe source sourceMem⟩

end Flapjack.Compiler.Backend.FlatPattern
