import Flapjack.Compiler.Backend.FlatPattern.Proofs.GlobalInvariants
import Flapjack.Compiler.Backend.FlatPattern.Proofs.GlobalFlag

/-! Global-write bounds for pattern compilation. -/
namespace Flapjack.Compiler.Backend.FlatPattern
open Flapjack.Compiler.Backend.BackendCommon FlatLang PatternCommon PatternSemantics
open Flapjack.Compiler.Backend.FlatProps

private theorem smartIf_bagBound (t : Tra) (c x y : FlatLang.Exp) (key : Nat) :
    setGlobals (smartIf t c x y) key ≤ setGlobals c key + setGlobals x key + setGlobals y key := by
  cases c <;> simp [smartIf, setGlobals, unionGlobalBag]
  case con t tag args =>
    cases tag <;> cases args <;> simp [setGlobals, elistGlobals, emptyGlobalBag, unionGlobalBag]
    case some.nil pair =>
      obtain ⟨tag, typ⟩ := pair
      cases typ <;> simp [setGlobals, elistGlobals, emptyGlobalBag, unionGlobalBag]
      all_goals split_ifs <;> simp [setGlobals, elistGlobals, emptyGlobalBag, unionGlobalBag]

private theorem compiledRows_empty (cfg : Config) (ps : List (FlatLang.Pat × FlatLang.Exp))
    (j : Nat) (sgp : Bool) (ps2 : List (FlatLang.Pat × FlatLang.Exp))
    (eqp : compileMatch cfg ps = (j, sgp, ps2))
    (bounds : ∀ key, rowGlobals ps2 key ≤ rowGlobals ps key)
    (flag : sgp = false) : rowGlobals ps2 = emptyGlobalBag := by
  have iff := compileMatch_globalFlag cfg ps
  simp only [eqp] at iff
  have srcEmpty : rowGlobals ps = emptyGlobalBag := by
    apply Classical.byContradiction
    intro nonempty
    have h := iff.mpr nonempty
    simp [flag] at h
  funext key
  have h := bounds key
  simp only [srcEmpty, emptyGlobalBag] at h ⊢
  omega

/-- Simultaneous global-write bounds for expressions, lists, rows, and function bodies. -/
theorem compileExp_bagBounds (cfg : Config) (exp : FlatLang.Exp) :
    ∀ key, setGlobals (compileExp cfg exp).2.2 key ≤ setGlobals exp key := by
  induction exp using compileExp.induct cfg
      (motive_2 := fun fs => ∀ key, funGlobals (compileFuns cfg fs).2.2 key ≤ funGlobals fs key)
      (motive_3 := fun es => ∀ key, elistGlobals (compileExps cfg es).2.2 key ≤ elistGlobals es key)
      (motive_4 := fun rows => ∀ key, rowGlobals (compileMatch cfg rows).2.2 key ≤ rowGlobals rows key) with
  | case1 => simp [compileExp]
  | case2 t x i sg y eq ih => simpa [compileExp, eq, setGlobals] using ih
  | case3 t x ps i sg y eq j sgp ps2 eqp ih ihp =>
    intro key
    let v := FlatLang.Exp.varLocal t (encNumToName (max i j + 2))
    let dflt := FlatLang.Exp.raise t v
    have hb : ∀ key, rowGlobals ps2 key ≤ rowGlobals ps key := by simpa only [eqp] using ihp
    have safe : (sgp = false → elistGlobals (dflt :: ps2.map Prod.snd) = emptyGlobalBag) ∧
        setGlobals v = emptyGlobalBag := by
      constructor
      · intro flag
        have e := compiledRows_empty cfg ps j sgp ps2 eqp hb flag
        simp only [dflt, v, setGlobals, elistGlobals, ← rowGlobals_eq_elistGlobals, e]
        funext k
        simp [unionGlobalBag, emptyGlobalBag]
      · simp [v, setGlobals]
    have hp := setGlobals_compilePats cfg sgp t (max i j + 2) v dflt ps2 safe key
    have hx := ih key
    have hr := hb key
    simp only [eq] at hx
    simp only [compileExp, eq, eqp, setGlobals, unionGlobalBag, rowGlobals_eq_elistGlobals,
      List.map_cons, List.map_nil, elistGlobals, emptyGlobalBag, Nat.add_zero]
    simp only [dflt, v, setGlobals, elistGlobals, emptyGlobalBag, unionGlobalBag,
      rowGlobals_eq_elistGlobals] at hp hr
    omega
  | case4 t tag xs i sg ys eq ih => simpa [compileExp, eq, setGlobals] using ih
  | case5 t v x i sg y eq ih => simpa [compileExp, eq, setGlobals] using ih
  | case6 t op xs i sg ys eq ih =>
    simp only [compileExp, eq, setGlobals, unionGlobalBag]
    intro key
    have h := ih key
    simp only [eq] at h
    omega
  | case7 t x ps i sg y eq j sgp ps2 eqp ih ihp =>
    intro key
    let v := FlatLang.Exp.varLocal t (encNumToName (max i j + 2))
    let dflt := FlatLang.Exp.raise t (.con t (some (0, none)) [])
    have hb : ∀ key, rowGlobals ps2 key ≤ rowGlobals ps key := by simpa only [eqp] using ihp
    have safe : (sgp = false → elistGlobals (dflt :: ps2.map Prod.snd) = emptyGlobalBag) ∧
        setGlobals v = emptyGlobalBag := by
      constructor
      · intro flag
        have e := compiledRows_empty cfg ps j sgp ps2 eqp hb flag
        simp only [dflt, setGlobals, elistGlobals, ← rowGlobals_eq_elistGlobals, e]
        funext k
        simp [unionGlobalBag, emptyGlobalBag]
      · simp [v, setGlobals]
    have hp := setGlobals_compilePats cfg sgp t (max i j + 2) v dflt ps2 safe key
    have hx := ih key
    have hr := hb key
    simp only [eq] at hx
    simp only [compileExp, eq, eqp, setGlobals, unionGlobalBag, rowGlobals_eq_elistGlobals]
    simp only [dflt, v, setGlobals, elistGlobals, emptyGlobalBag, unionGlobalBag,
      rowGlobals_eq_elistGlobals] at hp hr
    omega
  | case8 t vo x1 x2 i sg y eq j sg2 y2 eq2 ih1 ih2 =>
    simp only [compileExp, eq, eq2, setGlobals, unionGlobalBag]
    intro key
    have h1 := ih1 key; have h2 := ih2 key
    simp only [eq] at h1; simp only [eq2] at h2
    omega
  | case9 t fs x j sgfs fs2 eqf i sg y eq ihf ih =>
    simp only [compileExp, eqf, eq, setGlobals, unionGlobalBag]
    intro key
    have h1 := ih key; have h2 := ihf key
    simp only [eq] at h1; simp only [eqf] at h2
    omega
  | case10 t x1 x2 x3 i sg1 y1 eq1 j sg2 y2 eq2 k sg3 y3 eq3 ih1 ih2 ih3 =>
    intro key
    simp only [compileExp, eq1, eq2, eq3, setGlobals, unionGlobalBag]
    have bound := smartIf_bagBound t y1 y2 y3 key
    have h1 := ih1 key; have h2 := ih2 key; have h3 := ih3 key
    simp only [eq1] at h1; simp only [eq2] at h2; simp only [eq3] at h3
    omega
  | case11 e h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 =>
    cases e <;> simp_all [compileExp]
    all_goals first | exact False.elim (h8 _ _ _ _ rfl rfl rfl rfl) | exact False.elim (h10 _ _ _ _ rfl rfl rfl rfl)
  | case12 => simp [compileMatch, rowGlobals]
  | case13 p x ps i sg y eq j sgp ps2 eqp ih ihp =>
    rename_i key
    simp only [compileMatch, eq, eqp, rowGlobals, unionGlobalBag]
    have h1 := ih key; have h2 := ihp key
    simp only [eq] at h1; simp only [eqp] at h2
    omega
  | case14 => simp [compileExps, elistGlobals]
  | case15 x xs i sg y eq j sg2 ys eqs ih ihs =>
    rename_i key
    simp only [compileExps, eq, eqs, elistGlobals, unionGlobalBag]
    have h1 := ih key; have h2 := ihs key
    simp only [eq] at h1; simp only [eqs] at h2
    omega
  | case16 => simp [compileFuns, funGlobals]
  | case17 f v e fs i sg y eq j sgfs fs2 eqf ih ihf =>
    rename_i key
    simp only [compileFuns, eq, eqf, funGlobals, unionGlobalBag]
    have h1 := ih key; have h2 := ihf key
    simp only [eq] at h1; simp only [eqf] at h2
    omega

private theorem compileExps_bagBounds (cfg : Config) (xs : List FlatLang.Exp) :
    ∀ key, elistGlobals (compileExps cfg xs).2.2 key ≤ elistGlobals xs key := by
  induction xs with
  | nil => simp [compileExps, elistGlobals]
  | cons x xs ih =>
    cases hx : compileExp cfg x with
    | mk i rest =>
      obtain ⟨sg, y⟩ := rest
      cases hxs : compileExps cfg xs with
      | mk j rest =>
        obtain ⟨sgs, ys⟩ := rest
        intro key
        have h1 := compileExp_bagBounds cfg x key
        have h2 := ih key
        simp only [hx] at h1
        simp only [hxs] at h2
        simp only [compileExps, hx, hxs, elistGlobals, unionGlobalBag]
        omega

private theorem compileMatch_bagBounds (cfg : Config) (ps : List (FlatLang.Pat × FlatLang.Exp)) :
    ∀ key, rowGlobals (compileMatch cfg ps).2.2 key ≤ rowGlobals ps key := by
  induction ps with
  | nil => simp [compileMatch, rowGlobals]
  | cons row ps ih =>
    obtain ⟨p, x⟩ := row
    cases hx : compileExp cfg x with
    | mk i rest =>
      obtain ⟨sg, y⟩ := rest
      cases hps : compileMatch cfg ps with
      | mk j rest =>
        obtain ⟨sgs, ys⟩ := rest
        intro key
        have h1 := compileExp_bagBounds cfg x key
        have h2 := ih key
        simp only [hx] at h1
        simp only [hps] at h2
        simp only [compileMatch, hx, hps, rowGlobals, unionGlobalBag]
        omega

/-- Pattern compilation never increases any global-write multiplicity. -/
@[hol "cakeml/compiler/backend/proofs/flat_patternProofScript.sml" "compile_exp_set_globals"]
theorem compileExp_setGlobals :
    (∀ cfg exp n sg exp', compileExp cfg exp = (n, sg, exp') →
      ∀ key, setGlobals exp' key ≤ setGlobals exp key) ∧
    (∀ cfg exps n sg exps', compileExps cfg exps = (n, sg, exps') →
      ∀ key, elistGlobals exps' key ≤ elistGlobals exps key) ∧
    (∀ cfg rows n sg rows', compileMatch cfg rows = (n, sg, rows') →
      ∀ key, elistGlobals (rows'.map Prod.snd) key ≤ elistGlobals (rows.map Prod.snd) key) := by
  refine ⟨?_, ?_, ?_⟩
  · intro cfg exp n sg exp' compiled
    simpa only [compiled] using compileExp_bagBounds cfg exp
  · intro cfg exps n sg exps' compiled
    simpa only [compiled] using compileExps_bagBounds cfg exps
  · intro cfg rows n sg rows' compiled
    simpa only [compiled, rowGlobals_eq_elistGlobals] using compileMatch_bagBounds cfg rows

/-- Pattern compilation of declarations cannot increase their global-write bag. -/
@[hol "cakeml/compiler/backend/proofs/flat_patternProofScript.sml" "compile_decs_elist_globals"]
theorem compileDecs_elistGlobals (cfg : Config) (ds : List FlatLang.Exp) :
    ∀ key, elistGlobals (ds.map (compileDec cfg)) key ≤ elistGlobals ds key := by
  intro key
  induction ds with
  | nil => simp [elistGlobals]
  | cons d ds ih =>
    have head := compileExp_bagBounds cfg d key
    simp only [List.map_cons, compileDec, elistGlobals, unionGlobalBag]
    omega

end Flapjack.Compiler.Backend.FlatPattern
