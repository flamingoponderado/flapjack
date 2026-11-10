module

public import Flapjack.Compiler.Backend.FlatPattern.Proofs.GlobalInvariants
public import Flapjack.Compiler.Backend.FlatPattern.Proofs.GlobalFlag

@[expose] public section

/-! Global-write bounds for pattern compilation. -/
namespace Flapjack.Compiler.Backend.FlatPattern
open Flapjack.Compiler.Backend.BackendCommon FlatLang PatternCommon PatternSemantics
open Flapjack.Compiler.Backend.FlatProps

private theorem compiledRows_empty (cfg : Config) (ps : List (FlatLang.Pat × FlatLang.Exp))
    (j : Nat) (sgp : Bool) (ps2 : List (FlatLang.Pat × FlatLang.Exp))
    (eqp : compileMatch cfg ps = (j, sgp, ps2))
    (bounds : ∀ key, rowGlobals ps2 key ≤ rowGlobals ps key)
    (flag : sgp = false) : rowGlobals ps2 = emptyGlobalBag := by
  have iff : (compileMatch cfg ps).2.1 = true ↔ rowGlobals ps ≠ emptyGlobalBag := by
    simpa [rowGlobals_eq_elistGlobals] using compileExp_setGlobals_flag.2.2 cfg ps
  simp only [eqp] at iff
  have srcEmpty : rowGlobals ps = emptyGlobalBag := by
    apply Classical.byContradiction
    intro nonempty
    have h := iff.mpr nonempty
    simp [flag] at h
  funext key
  have h := bounds key
  simp only [srcEmpty, emptyGlobalBag, Flapjack.emptyBag] at h ⊢
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
  have all (cfg : Config) :
      (∀ exp key, setGlobals (compileExp cfg exp).2.2 key ≤ setGlobals exp key) ∧
      (∀ fs key, funGlobals (compileFuns cfg fs).2.2 key ≤ funGlobals fs key) ∧
      (∀ es key, elistGlobals (compileExps cfg es).2.2 key ≤ elistGlobals es key) ∧
      (∀ rows key, rowGlobals (compileMatch cfg rows).2.2 key ≤ rowGlobals rows key) := by
    apply compileExp.mutual_induct cfg
    case case3 =>
      intro t x ps i sg y eq j sgp ps2 eqp ih ihp key
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
          simp [unionGlobalBag, emptyGlobalBag, Flapjack.bagUnion, Flapjack.emptyBag]
        · simp [v, setGlobals]
      have hp := setGlobals_compilePats cfg sgp t (max i j + 2) v dflt ps2 safe key
      have hx := ih key
      have hr := hb key
      simp only [eq] at hx
      simp only [compileExp, eq, eqp, setGlobals, unionGlobalBag, rowGlobals_eq_elistGlobals,
        List.map_cons, List.map_nil, elistGlobals, emptyGlobalBag, Nat.add_zero, Flapjack.bagUnion, Flapjack.emptyBag]
      simp only [dflt, v, setGlobals, elistGlobals, emptyGlobalBag, unionGlobalBag,
        rowGlobals_eq_elistGlobals, Flapjack.bagUnion, Flapjack.emptyBag] at hp hr
      omega
    case case7 =>
      intro t x ps i sg y eq j sgp ps2 eqp ih ihp key
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
          simp [unionGlobalBag, emptyGlobalBag, Flapjack.bagUnion, Flapjack.emptyBag]
        · simp [v, setGlobals]
      have hp := setGlobals_compilePats cfg sgp t (max i j + 2) v dflt ps2 safe key
      have hx := ih key
      have hr := hb key
      simp only [eq] at hx
      simp only [compileExp, eq, eqp, setGlobals, unionGlobalBag, rowGlobals_eq_elistGlobals, Flapjack.bagUnion]
      simp only [dflt, v, setGlobals, elistGlobals, emptyGlobalBag, unionGlobalBag,
        rowGlobals_eq_elistGlobals, Flapjack.bagUnion, Flapjack.emptyBag] at hp hr
      omega
    case case10 =>
      intro t x1 x2 x3 i sg1 y1 eq1 j sg2 y2 eq2 k sg3 y3 eq3 ih1 ih2 ih3 key
      simp only [compileExp, eq1, eq2, eq3, setGlobals, unionGlobalBag, Flapjack.bagUnion]
      have bound := setGlobals_smartIf_le t y1 y2 y3 key
      have h1 := ih1 key; have h2 := ih2 key; have h3 := ih3 key
      simp only [eq1] at h1; simp only [eq2] at h2; simp only [eq3] at h3
      omega
    all_goals intros
    all_goals simp_all [compileExp, compileFuns, compileExps, compileMatch, setGlobals,
      elistGlobals, rowGlobals, funGlobals, unionGlobalBag, Flapjack.bagUnion]
    all_goals grind
  refine ⟨?_, ?_, ?_⟩
  · intro cfg exp n sg exp' compiled
    simpa only [compiled] using (all cfg).1 exp
  · intro cfg exps n sg exps' compiled
    simpa only [compiled] using (all cfg).2.2.1 exps
  · intro cfg rows n sg rows' compiled
    simpa only [compiled, rowGlobals_eq_elistGlobals] using (all cfg).2.2.2 rows

/-- Pattern compilation of declarations cannot increase their global-write bag. -/
@[hol "cakeml/compiler/backend/proofs/flat_patternProofScript.sml" "compile_decs_elist_globals"]
theorem compileDecs_elistGlobals (cfg : Config) (ds : List FlatLang.Exp) :
    ∀ key, elistGlobals (ds.map (compileDec cfg)) key ≤ elistGlobals ds key := by
  intro key
  induction ds with
  | nil => simp [elistGlobals]
  | cons d ds ih =>
    have head := compileExp_setGlobals.1 cfg d (compileExp cfg d).1 (compileExp cfg d).2.1
      (compileExp cfg d).2.2 (by cases h : compileExp cfg d with | mk a b => cases b; rfl) key
    simp only [List.map_cons, compileDec, elistGlobals, unionGlobalBag, Flapjack.bagUnion]
    omega

end Flapjack.Compiler.Backend.FlatPattern
