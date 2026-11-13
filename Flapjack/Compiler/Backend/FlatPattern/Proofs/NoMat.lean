module

public import Flapjack.Compiler.Backend.FlatPattern.Proofs.CompiledMatch
public import Flapjack.Compiler.Backend.FlatPattern.CompileTotal
public import Flapjack.Compiler.Backend.FlatProps.NoMat
public import Flapjack.Misc.Sptree.ToList
public import Mathlib.Tactic.SplitIfs

@[expose] public section

/-! Match-freedom facts for generated pattern tests. The compositional helper lemmas are Flapjack proof infrastructure. -/
namespace Flapjack.Compiler.Backend.FlatPattern
open Flapjack.Compiler.Backend.BackendCommon FlatLang PatternCommon PatternSemantics

/-- Boolean literals do not contain pattern matches. -/
theorem noMat_mkBool (trace : Tra) (value : Bool) : FlatProps.noMat (mkBool trace value) = true := by
  simp [mkBool, FlatProps.noMat, FlatProps.noMatList]

/-- Smart conditionals preserve match-freedom of all their inputs. -/
theorem noMat_smartIf (trace : Tra) (condition yes no : FlatLang.Exp)
    (conditionSafe : FlatProps.noMat condition = true)
    (yesSafe : FlatProps.noMat yes = true) (noSafe : FlatProps.noMat no = true) :
    FlatProps.noMat (smartIf trace condition yes no) = true := by
  rw [smartIf_thm]
  split_ifs <;> simp_all [FlatProps.noMat]

/-- Following a pattern position preserves a match-free value expression. -/
@[hol "cakeml/compiler/backend/proofs/flat_patternProofScript.sml" "decode_pos_no_Mat"]
theorem noMat_decodePos (trace : Tra) (pos : Position) (value : FlatLang.Exp)
    (safe : FlatProps.noMat value = true) : FlatProps.noMat (decodePos trace value pos) = true := by
  induction pos generalizing value with
  | emptyPos => exact safe
  | pos index rest ih =>
    apply ih
    simpa [FlatProps.noMat, FlatProps.noMatList] using safe

/-- Generated atomic tests preserve match-freedom. -/
@[hol "cakeml/compiler/backend/proofs/flat_patternProofScript.sml" "decode_test_no_Mat"]
theorem noMat_decodeTest (value : FlatLang.Exp) (trace : Tra) (test : DTest)
    (safe : FlatProps.noMat value = true) : FlatProps.noMat (decodeTest trace test value) = true := by
  cases test <;> simp [decodeTest, FlatProps.noMat, FlatProps.noMatList, safe]

/-- Generated decision guards preserve match-freedom. -/
@[hol "cakeml/compiler/backend/proofs/flat_patternProofScript.sml" "decode_guard_no_Mat"]
theorem noMat_decodeGuard (value : FlatLang.Exp) (trace : Tra) (guard : DGuard)
    (safe : FlatProps.noMat value = true) : FlatProps.noMat (decodeGuard trace value guard) = true := by
  induction guard with
  | true_ => exact noMat_mkBool trace true
  | posTest pos test => exact noMat_decodeTest _ trace test (noMat_decodePos trace pos value safe)
  | not guard ih => simp [decodeGuard, FlatProps.noMat, FlatProps.noMatList, ih, noMat_mkBool]
  | conj a b ihA ihB => exact noMat_smartIf trace _ _ _ ihA ihB (noMat_mkBool trace false)
  | disj a b ihA ihB => exact noMat_smartIf trace _ _ _ ihA (noMat_mkBool trace true) ihB

/-- Decoding a decision tree preserves match-freedom of its value, default,
and all expressions in its branch tree. -/
@[hol "cakeml/compiler/backend/proofs/flat_patternProofScript.sml" "decode_dtree_no_Mat"]
theorem noMat_decodeDtree (value default : FlatLang.Exp) (branches : Spt FlatLang.Exp) (trace : Tra) (tree : DTree)
    (premises : FlatProps.noMat value = true ∧ FlatProps.noMat default = true ∧
      ∀ branch ∈ sptToList branches, FlatProps.noMat branch = true) :
    FlatProps.noMat (decodeDtree trace branches value default tree) = true := by
  obtain ⟨valueSafe, defaultSafe, branchesSafe⟩ := premises
  induction tree with
  | fail => exact defaultSafe
  | typeFail => simp [decodeDtree, FlatProps.noMat]
  | leaf index =>
    cases found : sptLookup index branches with
    | none => simpa [decodeDtree, found] using defaultSafe
    | some branch =>
      simpa [decodeDtree, found] using branchesSafe branch ((sptMemToList branch branches).2 ⟨index, found⟩)
  | if_ guard yes no ihYes ihNo =>
    simp only [decodeDtree]
    split_ifs
    · exact ihYes
    · exact ihNo
    · exact noMat_smartIf trace _ _ _ (noMat_decodeGuard value trace _ valueSafe) ihYes ihNo

/-- Every generated child projection of a match-free expression is match-free. -/
theorem noMat_children (trace : Tra) (value : FlatLang.Exp) (patterns : List FlatLang.Pat)
    (safe : FlatProps.noMat value = true) :
    ∀ pattern expression, (pattern, expression) ∈
      patterns.mapIdx (fun i p => (p, .app trace (.el i) [value])) → FlatProps.noMat expression = true := by
  intro pattern expression member
  obtain ⟨i, _, eq⟩ := List.mem_mapIdx.mp member
  obtain ⟨_, rfl⟩ := Prod.mk.inj eq
  simpa [FlatProps.noMat, FlatProps.noMatList] using safe

/-- Naive matching generates a match-free guard when each worklist value is
match-free. -/
@[hol "cakeml/compiler/backend/proofs/flat_patternProofScript.sml" "naive_pattern_match_no_Mat"]
theorem noMat_naivePatternMatch (trace : Tra) (todo : List (FlatLang.Pat × FlatLang.Exp))
    (safe : ∀ item ∈ todo, FlatProps.noMat item.2 = true) :
    FlatProps.noMat (naivePatternMatch trace todo) = true := by
  have general (todo : List (FlatLang.Pat × FlatLang.Exp))
      (safe : ∀ pattern expression, (pattern, expression) ∈ todo → FlatProps.noMat expression = true) :
      FlatProps.noMat (naivePatternMatch trace todo) = true := by
    induction todo using naivePatternMatch.induct trace with
    | case1 => simp [naivePatternMatch, noMat_mkBool]
    | case2 value rest ih | case3 value rest _ ih =>
      simpa [naivePatternMatch] using ih fun p e m => safe p e (by simp [m])
    | case4 value rest literal ih =>
      simp [naivePatternMatch, FlatProps.noMat, FlatProps.noMatList, noMat_mkBool, noMat_smartIf,
        ih (fun p e m => safe p e (by simp [m])), safe (.plit literal) value (by simp)]
    | case5 value rest patterns ih =>
      simp [naivePatternMatch, ih (fun p e m => by
          rcases List.mem_append.mp m with m | m
          · exact noMat_children trace value patterns
              (safe (.pcon none patterns) value (by simp)) p e m
          · exact safe p e (by simp [m]))]
    | case6 value rest patterns tag typ ih =>
      simp only [naivePatternMatch]
      exact noMat_smartIf trace _ _ _
        (by simp [FlatProps.noMat, FlatProps.noMatList,
          safe (.pcon (some (tag, typ)) patterns) value (by simp)])
        (ih fun p e m => by
          rcases List.mem_append.mp m with m | m
          · exact noMat_children trace value patterns
              (safe (.pcon (some (tag, typ)) patterns) value (by simp)) p e m
          · exact safe p e (by simp [m])) (noMat_mkBool trace false)
    | case7 value rest pattern name ih =>
      simp [naivePatternMatch, ih (fun p e m => by
        simp only [List.mem_cons, Prod.mk.injEq] at m; rcases m with ⟨_, rfl⟩ | m
        · exact safe (.pas pattern name) e (by simp)
        · exact safe p e (by simp [m]))]
    | case8 value rest pattern ih =>
      simp [naivePatternMatch, ih (fun p e m => by
        simp only [List.mem_cons, Prod.mk.injEq] at m; rcases m with ⟨_, rfl⟩ | m
        · simpa [FlatProps.noMat, FlatProps.noMatList] using safe (.pref pattern) value (by simp)
        · exact safe p e (by simp [m]))]
  exact general todo (fun p e m => safe (p, e) m)

/-- Naive branch chains are match-free when their value, default, and
branch expressions are match-free. -/
@[hol "cakeml/compiler/backend/proofs/flat_patternProofScript.sml" "naive_pattern_matches_no_Mat"]
theorem noMat_naivePatternMatches (trace : Tra) (value : FlatLang.Exp)
    (rows : List (FlatLang.Pat × FlatLang.Exp)) (default : FlatLang.Exp)
    (safe : ∀ expression ∈ value :: default :: rows.map Prod.snd, FlatProps.noMat expression = true) :
    FlatProps.noMat (naivePatternMatches trace value rows default) = true := by
  fun_induction naivePatternMatches trace value rows default <;> simp_all
  case case2 =>
    rename_i ih
    apply noMat_smartIf
    · apply noMat_naivePatternMatch
      intro item member
      simp only [List.mem_singleton] at member
      subst item
      exact safe.1
    · exact safe.2.2.1
    · exact ih

/-- Generated binding work items refer only to fresh local variables. -/
theorem noMat_patternEntries (trace : Tra) (base start : Nat) (patterns : List FlatLang.Pat) :
    ∀ pattern index expression,
      (pattern, index, expression) ∈ (patternEntries trace base start patterns).map Prod.snd →
      FlatProps.noMat expression = true := by
  induction patterns generalizing start with
  | nil => simp [patternEntries]
  | cons first rest ih =>
    intro pattern index expression member
    simp only [patternEntries_cons, List.map_cons, List.mem_cons, Prod.mk.injEq] at member
    rcases member with ⟨_, _, rfl⟩ | member
    · simp [FlatProps.noMat]
    · exact ih (start + 1) pattern index expression member

/-- The generated projection bindings preserve a match-free continuation. -/
theorem noMat_projectionFold (trace : Tra) (value body : FlatLang.Exp)
    (entries : List ((Nat × Flapjack.Basis.Pure.MlString.MlString) × (FlatLang.Pat × Nat × FlatLang.Exp)))
    (valueSafe : FlatProps.noMat value = true) (bodySafe : FlatProps.noMat body = true) :
    FlatProps.noMat (entries.foldr (fun ((index, name), _) rest =>
      .let_ trace (some name) (.app trace (.el index) [value]) rest) body) = true := by
  induction entries with
  | nil => exact bodySafe
  | cons entry rest ih =>
    obtain ⟨⟨index, name⟩, work⟩ := entry
    simp [FlatProps.noMat, FlatProps.noMatList, valueSafe, ih]

/-- Pattern binding preserves match-freedom of its worklist and continuation. -/
@[hol "cakeml/compiler/backend/proofs/flat_patternProofScript.sml" "compile_pat_bindings_no_Mat"]
theorem noMat_compilePatBindings (trace : Tra) (base : Nat)
    (todo : List (FlatLang.Pat × Nat × FlatLang.Exp)) (body : FlatLang.Exp)
    (premises : FlatProps.noMat body = true ∧
      ∀ item ∈ todo, FlatProps.noMat item.2.2 = true) :
    FlatProps.noMat (compilePatBindings trace base todo body).2 = true := by
  obtain ⟨bodySafe, safe⟩ := premises
  fun_induction compilePatBindings trace base todo body
  all_goals simp_all [FlatProps.noMat, FlatProps.noMatList]
  case case5 i k x rest a ps entries used exp2 eq selected exp3 used2 ih =>
    refine noMat_projectionFold trace x exp2 selected safe.1 (ih ?_)
    intro a_1 a_2 b member
    rcases member with ⟨a_3, b_1, hmem⟩ | hmem
    · exact noMat_patternEntries trace i 0 ps a_1 a_2 b (by
        simp only [List.mem_map]; exact ⟨((a_3, b_1), a_1, a_2, b), hmem, rfl⟩)
    · exact safe.2 a_1 a_2 b hmem

/-- A compiled branch remains match-free when its value and body are. -/
theorem noMat_compilePatRhs (trace : Tra) (base : Nat) (value : FlatLang.Exp)
    (pattern : FlatLang.Pat) (body : FlatLang.Exp)
    (valueSafe : FlatProps.noMat value = true) (bodySafe : FlatProps.noMat body = true) :
    FlatProps.noMat (compilePatRhs trace base value (pattern, body)) = true := by
  apply noMat_compilePatBindings trace (base + 1) [(pattern, base, value)] body
  refine ⟨bodySafe, ?_⟩
  intro item member
  simp only [List.mem_singleton] at member
  subst item
  exact valueSafe


/-- Both implementations of branch compilation preserve match-freedom. -/
@[hol "cakeml/compiler/backend/proofs/flat_patternProofScript.sml" "compile_pats_no_Mat"]
theorem noMat_compilePats (default value : FlatLang.Exp) (rows : List (FlatLang.Pat × FlatLang.Exp))
    (cfg : Config) (naive : Bool) (trace : Tra) (base : Nat)
    (premises : FlatProps.noMat default = true ∧ FlatProps.noMat value = true ∧
      ∀ body ∈ rows.map Prod.snd, FlatProps.noMat body = true) :
    FlatProps.noMat (compilePats cfg naive trace base value default rows) = true := by
  obtain ⟨defaultSafe, valueSafe, rowsSafe⟩ := premises
  have branchesSafe : ∀ branch, branch ∈ rows.map (compilePatRhs trace base value) →
      FlatProps.noMat branch = true := by
    intro branch member
    obtain ⟨⟨pattern, body⟩, row, rfl⟩ := List.mem_map.mp member
    exact noMat_compilePatRhs trace base value pattern body valueSafe (rowsSafe body (List.mem_map.mpr ⟨(pattern, body), row, rfl⟩))
  cases naive with
  | false =>
    simp only [compilePats, Bool.false_eq_true, ↓reduceIte]
    apply noMat_decodeDtree value default _ trace _
    refine ⟨valueSafe, defaultSafe, ?_⟩
    intro branch member
    apply branchesSafe branch
    have eq := congrArg (fun (values : Set FlatLang.Exp) => branch ∈ values)
      (setToList_fromList (rows.map (compilePatRhs trace base value)))
    exact eq.mp member
  | true =>
    simp only [compilePats, ↓reduceIte]
    apply noMat_naivePatternMatches trace value _ default
    intro expression member
    simp only [List.mem_cons, List.mem_map] at member
    rcases member with rfl | rfl | ⟨⟨pattern, branch⟩, row, rfl⟩
    · exact valueSafe
    · exact defaultSafe
    · exact branchesSafe branch (List.of_mem_zip row).2


/-- All three expression-compiler outputs are match-free. -/
@[hol "cakeml/compiler/backend/proofs/flat_patternProofScript.sml" "compile_exp_no_Mat"]
theorem compileExp_noMat :
    (∀ cfg exp n sg exp', compileExp cfg exp = (n, sg, exp') → FlatProps.noMat exp' = true) ∧
    (∀ cfg exps n sg exps', compileExps cfg exps = (n, sg, exps') →
      ∀ e ∈ exps', FlatProps.noMat e = true) ∧
    (∀ cfg rows n sg rows', compileMatch cfg rows = (n, sg, rows') →
      ∀ row ∈ rows', FlatProps.noMat row.2 = true) := by
  have all (cfg : Config) :
      (∀ exp, FlatProps.noMat (compileExp cfg exp).2.2 = true) ∧
      (∀ fs, FlatProps.noMatFuns (compileFuns cfg fs).2.2 = true) ∧
      (∀ es, FlatProps.noMatList (compileExps cfg es).2.2 = true) ∧
      (∀ rows p e, (p, e) ∈ (compileMatch cfg rows).2.2 → FlatProps.noMat e = true) := by
    apply compileExp.mutual_induct cfg
    case case3 =>
      intro t x ps i sg y eq j sgp ps2 eqp ih ihp
      have branch := noMat_compilePats (.raise t (.varLocal t (encNumToName (max i j + 2))))
        (.varLocal t (encNumToName (max i j + 2))) ps2 cfg sgp t (max i j + 2)
        ⟨by simp [FlatProps.noMat], by simp [FlatProps.noMat], by
          intro body member
          obtain ⟨⟨pattern, expression⟩, row, rfl⟩ := List.mem_map.mp member
          apply ihp pattern expression
          simpa [eqp] using row⟩
      simpa [compileExp, eq, eqp, FlatProps.noMat] using And.intro ih branch
    case case7 =>
      intro t x ps i sg y eq j sgp ps2 eqp ih ihp
      have branch := noMat_compilePats (.raise t (.con t (some (0, none)) []))
        (.varLocal t (encNumToName (max i j + 2))) ps2 cfg sgp t (max i j + 2)
        ⟨by simp [FlatProps.noMat, FlatProps.noMatList], by simp [FlatProps.noMat], by
          intro body member
          obtain ⟨⟨pattern, expression⟩, row, rfl⟩ := List.mem_map.mp member
          apply ihp pattern expression
          simpa [eqp] using row⟩
      simpa [compileExp, eq, eqp, FlatProps.noMat] using And.intro ih branch
    case case10 =>
      intro t x1 x2 x3 i sg1 y1 eq1 j sg2 y2 eq2 k sg3 y3 eq3 ih1 ih2 ih3
      simp only [compileExp, eq1, eq2, eq3]
      apply noMat_smartIf
      · simpa [eq1] using ih1
      · simpa [eq2] using ih2
      · simpa [eq3] using ih3
    case case11 =>
      intro e h1 h2 h3 h4 h5 h6 h7 h8 h9 h10
      cases e <;> simp_all [compileExp, FlatProps.noMat]
      all_goals first | exact False.elim (h8 _ _ _ _ rfl rfl rfl rfl) | exact False.elim (h10 _ _ _ _ rfl rfl rfl rfl)
    case case13 =>
      intro p x ps i sg y eq j sgp ps2 eqp ih ihp p' e member
      simp only [compileMatch, eq, eqp, List.mem_cons, Prod.mk.injEq] at member
      rcases member with ⟨_, rfl⟩ | member
      · simpa [eq] using ih
      · exact ihp p' e (by simpa [eqp] using member)
    all_goals intros
    all_goals simp_all [compileExp, compileFuns, compileExps, compileMatch, FlatProps.noMat,
      FlatProps.noMatList, FlatProps.noMatFuns]
  refine ⟨?_, ?_, ?_⟩
  · intro cfg exp n sg exp' eq
    simpa only [eq] using (all cfg).1 exp
  · intro cfg exps n sg exps' eq
    have out := (all cfg).2.2.1 exps
    simpa only [eq, FlatProps.noMatList_eq_all, List.all_eq_true] using out
  · intro cfg rows n sg rows' eq row member
    have out := (all cfg).2.2.2 rows row.1 row.2
    apply out
    simpa [eq] using member

/-- Compiling every declaration produces the match-free input expected by
flat-to-closure compilation. -/
@[hol "cakeml/compiler/backend/proofs/flat_patternProofScript.sml" "compile_decs_no_Mat"]
theorem noMat_compileDecs (cfg : Config) (declarations : List FlatLang.Exp) :
    FlatProps.noMatDecs (declarations.map (compileDec cfg)) = true := by
  rw [FlatProps.noMatDecs_eq_noMatList, FlatProps.noMatList_eq_all, List.all_eq_true]
  intro e member
  obtain ⟨source, _, rfl⟩ := List.mem_map.mp member
  exact compileExp_noMat.1 cfg source (compileExp cfg source).1 (compileExp cfg source).2.1
    (compileExp cfg source).2.2 (by cases h : compileExp cfg source with | mk a b => cases b; rfl)



end Flapjack.Compiler.Backend.FlatPattern
