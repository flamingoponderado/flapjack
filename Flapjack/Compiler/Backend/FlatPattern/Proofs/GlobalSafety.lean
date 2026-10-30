import Flapjack.Compiler.Backend.FlatPattern.Proofs.GlobalBounds

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
  simp only [empty, emptyGlobalBag] at h ⊢
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
        simp only [compileFuns, he, hfs, funGlobals, unionGlobalBag]
        omega

private theorem safe_smartIf (t : Tra) (c x y : FlatLang.Exp)
    (hc : esgcFree c) (hx : esgcFree x) (hy : esgcFree y) : esgcFree (smartIf t c x y) := by
  cases c <;> simp_all [smartIf, esgcFree]
  case con t tag args =>
    cases tag <;> cases args <;> try simp_all [esgcFree]
    case some.nil pair =>
      obtain ⟨tag, typ⟩ := pair
      cases typ <;> try simp_all [esgcFree]
      all_goals split_ifs <;> simp_all [esgcFree]

/-- Expression safety is preserved by pattern compilation. -/
theorem compileExp_safe (cfg : Config) (exp : FlatLang.Exp) :
    esgcFree exp → esgcFree (compileExp cfg exp).2.2 := by
  induction exp using compileExp.induct cfg
      (motive_2 := fun _ => True)
      (motive_3 := fun es => esgcFreeList es → esgcFreeList (compileExps cfg es).2.2)
      (motive_4 := fun rows => esgcFreeRows rows → esgcFreeRows (compileMatch cfg rows).2.2) with
  | case1 => simp [compileExp, esgcFree]
  | case2 t x i sg y eq ih => simpa [compileExp, eq, esgcFree] using ih
  | case3 t x ps i sg y eq j sgp ps2 eqp ih ihp =>
    intro safe
    have h := safe
    simp only [esgcFree] at h
    have body : esgcFree y := by simpa [eq] using ih h.1
    have rows : esgcFreeRows ps2 := by simpa [eqp] using ihp h.2
    have branch := esgcFree_compilePats cfg sgp t (max i j + 2)
      (.varLocal t (encNumToName (max i j + 2)))
      (.raise t (.varLocal t (encNumToName (max i j + 2)))) ps2
      (by simp [esgcFree]) (by simp [esgcFree]) ((rowsSafe_iff ps2).mp rows)
    simpa [compileExp, eq, eqp, esgcFree, esgcFreeRows, body] using branch
  | case4 t tag xs i sg ys eq ih => simpa [compileExp, eq, esgcFree] using ih
  | case5 t v x i sg y eq ih =>
    intro safe
    simp only [esgcFree] at safe
    simp only [compileExp, eq, esgcFree]
    apply bagEmpty_of_bound _ _ _ safe
    simpa only [eq] using compileExp_bagBounds cfg x
  | case6 t op xs i sg ys eq ih => simpa [compileExp, eq, esgcFree] using ih
  | case7 t x ps i sg y eq j sgp ps2 eqp ih ihp =>
    intro safe
    have h := safe
    simp only [esgcFree] at h
    have body : esgcFree y := by simpa [eq] using ih h.1
    have rows : esgcFreeRows ps2 := by simpa [eqp] using ihp h.2
    have branch := esgcFree_compilePats cfg sgp t (max i j + 2)
      (.varLocal t (encNumToName (max i j + 2)))
      (.raise t (.con t (some (0, none)) [])) ps2
      (by simp [esgcFree]) (by simp [esgcFree, esgcFreeList]) ((rowsSafe_iff ps2).mp rows)
    simpa [compileExp, eq, eqp, esgcFree, body] using branch
  | case8 t vo x1 x2 i sg y eq j sg2 y2 eq2 ih1 ih2 =>
    simp only [esgcFree, compileExp, eq, eq2]
    intro safe
    exact ⟨by simpa [eq] using ih1 safe.1, by simpa [eq2] using ih2 safe.2⟩
  | case9 t fs x j sgfs fs2 eqf i sg y eq ihf ih =>
    simp only [esgcFree, compileExp, eqf, eq]
    intro safe
    constructor
    · simpa [eq] using ih safe.1
    · apply bagEmpty_of_bound _ _ _ safe.2
      simpa only [eqf] using compileFuns_bagBounds cfg fs
  | case10 t x1 x2 x3 i sg1 y1 eq1 j sg2 y2 eq2 k sg3 y3 eq3 ih1 ih2 ih3 =>
    simp only [esgcFree, compileExp, eq1, eq2, eq3]
    intro safe
    apply safe_smartIf
    · simpa [eq1] using ih1 safe.1
    · simpa [eq2] using ih2 safe.2.1
    · simpa [eq3] using ih3 safe.2.2
  | case11 e h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 =>
    cases e <;> simp_all [compileExp]
    all_goals first | exact False.elim (h8 _ _ _ _ rfl rfl rfl rfl) | exact False.elim (h10 _ _ _ _ rfl rfl rfl rfl)
  | case12 => simp [compileMatch, esgcFreeRows]
  | case13 p x ps i sg y eq j sgp ps2 eqp ih ihp =>
    rename_i safe
    simp only [esgcFreeRows] at safe
    simp only [compileMatch, eq, eqp, esgcFreeRows]
    exact ⟨by simpa [eq] using ih safe.1, by simpa [eqp] using ihp safe.2⟩
  | case14 => simp [compileExps, esgcFreeList]
  | case15 x xs i sg y eq j sg2 ys eqs ih ihs =>
    rename_i safe
    simp only [esgcFreeList] at safe
    simp only [compileExps, eq, eqs, esgcFreeList]
    exact ⟨by simpa [eq] using ih safe.1, by simpa [eqs] using ihs safe.2⟩
  | case16 => trivial
  | case17 => trivial

private theorem listSafe_iff (xs : List FlatLang.Exp) :
    esgcFreeList xs ↔ ∀ x ∈ xs, esgcFree x := by
  induction xs with
  | nil => simp [esgcFreeList]
  | cons x xs ih => simp [esgcFreeList, ih]

private theorem compileExps_safe (cfg : Config) (xs : List FlatLang.Exp) :
    esgcFreeList xs → esgcFreeList (compileExps cfg xs).2.2 := by
  induction xs with
  | nil => simp [compileExps, esgcFreeList]
  | cons x xs ih =>
    cases hx : compileExp cfg x with
    | mk i rest =>
      obtain ⟨sg, y⟩ := rest
      cases hxs : compileExps cfg xs with
      | mk j rest =>
        obtain ⟨sgs, ys⟩ := rest
        simp only [compileExps, hx, hxs, esgcFreeList]
        intro safe
        exact ⟨by simpa [hx] using compileExp_safe cfg x safe.1,
          by simpa [hxs] using ih safe.2⟩

private theorem compileMatch_safe (cfg : Config) (ps : List (FlatLang.Pat × FlatLang.Exp)) :
    esgcFreeRows ps → esgcFreeRows (compileMatch cfg ps).2.2 := by
  induction ps with
  | nil => simp [compileMatch, esgcFreeRows]
  | cons row ps ih =>
    obtain ⟨p, x⟩ := row
    cases hx : compileExp cfg x with
    | mk i rest =>
      obtain ⟨sg, y⟩ := rest
      cases hps : compileMatch cfg ps with
      | mk j rest =>
        obtain ⟨sgs, ys⟩ := rest
        simp only [compileMatch, hx, hps, esgcFreeRows]
        intro safe
        exact ⟨by simpa [hx] using compileExp_safe cfg x safe.1,
          by simpa [hps] using ih safe.2⟩

/-- The source expression, list, and row safety theorem. -/
@[hol "cakeml/compiler/backend/proofs/flat_patternProofScript.sml" "compile_exp_esgc_free"]
theorem compileExp_esgcFree :
    (∀ cfg exp n sg exp', compileExp cfg exp = (n, sg, exp') ∧ esgcFree exp → esgcFree exp') ∧
    (∀ cfg exps n sg exps', compileExps cfg exps = (n, sg, exps') ∧
      (∀ e ∈ exps, esgcFree e) → ∀ e ∈ exps', esgcFree e) ∧
    (∀ cfg rows n sg rows', compileMatch cfg rows = (n, sg, rows') ∧
      (∀ row ∈ rows, esgcFree row.2) → ∀ row ∈ rows', esgcFree row.2) := by
  refine ⟨?_, ?_, ?_⟩
  · intro cfg exp n sg exp' h
    simpa only [h.1] using compileExp_safe cfg exp h.2
  · intro cfg exps n sg exps' h
    have out := compileExps_safe cfg exps ((listSafe_iff exps).mpr h.2)
    rw [h.1] at out
    exact (listSafe_iff exps').mp out
  · intro cfg rows n sg rows' h
    have input : esgcFreeRows rows := (rowsSafe_iff rows).mpr (by
      intro p e member
      exact h.2 (p, e) member)
    have out := compileMatch_safe cfg rows input
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
  exact compileExp_safe cfg source (safe source sourceMem)

end Flapjack.Compiler.Backend.FlatPattern
