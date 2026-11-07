import Flapjack.Compiler.Backend.FlatPattern.Proofs.NoMat
import Flapjack.Compiler.Backend.FlatProps.GlobalBagProperties
import Flapjack.Misc.Sptree.ToList
import Mathlib.Tactic.SplitIfs

/-! Global-initialization safety of generated pattern decision expressions. -/
namespace Flapjack.Compiler.Backend.FlatPattern
open Flapjack.Compiler.Backend.BackendCommon FlatLang PatternCommon PatternSemantics
open Flapjack.Compiler.Backend.FlatProps

private theorem esgcFree_mkBool (t : Tra) (b : Bool) : esgcFree (mkBool t b) := by
  simp [mkBool, esgcFree, esgcFreeList]

/-- Flapjack helper: smart conditionals preserve branch global safety.
HOL uses the cases within its proofs. -/
theorem esgcFree_smartIf (t : Tra) (c x y : FlatLang.Exp)
    (hc : esgcFree c) (hx : esgcFree x) (hy : esgcFree y) :
    esgcFree (smartIf t c x y) := by
  cases c <;> simp_all [smartIf, esgcFree]
  case con t tag args =>
    cases tag <;> cases args <;> try simp_all [esgcFree]
    case some.nil pair =>
      obtain ⟨tag, typ⟩ := pair
      cases typ <;> try simp_all [esgcFree]
      all_goals split_ifs <;> simp_all [esgcFree]

@[hol "cakeml/compiler/backend/proofs/flat_patternProofScript.sml" "esgc_free_decode_pos"]
theorem esgcFree_decodePos (t : Tra) (p : Position) (exp : FlatLang.Exp)
    (safe : esgcFree exp) : esgcFree (decodePos t exp p) := by
  induction p generalizing exp with
  | emptyPos => exact safe
  | pos index rest ih =>
    apply ih
    simpa [esgcFree, esgcFreeList] using safe

@[hol "cakeml/compiler/backend/proofs/flat_patternProofScript.sml" "esgc_free_decode_test"]
theorem esgcFree_decodeTest (exp : FlatLang.Exp) (t : Tra) (d : DTest)
    (safe : esgcFree exp) : esgcFree (decodeTest t d exp) := by
  cases d <;> simp [decodeTest, esgcFree, esgcFreeList, safe]

@[hol "cakeml/compiler/backend/proofs/flat_patternProofScript.sml" "esgc_free_decode_guard"]
theorem esgcFree_decodeGuard (exp : FlatLang.Exp) (t : Tra) (gd : DGuard)
    (safe : esgcFree exp) : esgcFree (decodeGuard t exp gd) := by
  induction gd with
  | true_ => exact esgcFree_mkBool t true
  | posTest pos test => exact esgcFree_decodeTest _ t test (esgcFree_decodePos t pos exp safe)
  | not gd ih => simp [decodeGuard, esgcFree, esgcFreeList, ih, esgcFree_mkBool]
  | conj a b ihA ihB => exact esgcFree_smartIf t _ _ _ ihA ihB (esgcFree_mkBool t false)
  | disj a b ihA ihB => exact esgcFree_smartIf t _ _ _ ihA (esgcFree_mkBool t true) ihB

/-- Every generated child projection of a global-initialization-safe expression is global-initialization-safe. -/
theorem esgcFree_children (trace : Tra) (value : FlatLang.Exp) (patterns : List FlatLang.Pat)
    (safe : esgcFree value) :
    ∀ pattern expression, (pattern, expression) ∈
      patterns.mapIdx (fun i p => (p, .app trace (.el i) [value])) → esgcFree expression := by
  intro pattern expression member
  obtain ⟨i, _, eq⟩ := List.mem_mapIdx.mp member
  obtain ⟨_, rfl⟩ := Prod.mk.inj eq
  simpa [esgcFree, esgcFreeList] using safe

/-- Naive matching generates a global-initialization-safe guard when each worklist value is
global-initialization-safe. -/
theorem esgcFree_naivePatternMatch (trace : Tra) (todo : List (FlatLang.Pat × FlatLang.Exp))
    (safe : ∀ pattern expression, (pattern, expression) ∈ todo → esgcFree expression) :
    esgcFree (naivePatternMatch trace todo) := by
  induction todo using naivePatternMatch.induct trace with
  | case1 => simpa [naivePatternMatch] using esgcFree_mkBool trace true
  | case2 value rest ih | case3 value rest _ ih =>
    simp only [naivePatternMatch]
    apply ih
    intro pattern expression member
    exact safe pattern expression (by simp [member])
  | case4 value rest literal ih =>
    have valueSafe := safe (.plit literal) value (by simp)
    have restSafe : ∀ pattern expression, (pattern, expression) ∈ rest → esgcFree expression := by
      intro pattern expression member
      exact safe pattern expression (by simp [member])
    simp only [naivePatternMatch]
    apply esgcFree_smartIf
    · simp [esgcFree, esgcFreeList, valueSafe]
    · exact ih restSafe
    · exact esgcFree_mkBool trace false
  | case5 value rest patterns ih =>
    have valueSafe := safe (.pcon none patterns) value (by simp)
    simp only [naivePatternMatch]
    apply ih
    intro pattern expression member
    rcases List.mem_append.mp member with member | member
    · exact esgcFree_children trace value patterns valueSafe pattern expression member
    · exact safe pattern expression (by simp [member])
  | case6 value rest patterns tag typ ih =>
    have valueSafe := safe (.pcon (some (tag, typ)) patterns) value (by simp)
    simp only [naivePatternMatch]
    apply esgcFree_smartIf
    · simp [esgcFree, esgcFreeList, valueSafe]
    · apply ih
      intro pattern expression member
      rcases List.mem_append.mp member with member | member
      · exact esgcFree_children trace value patterns valueSafe pattern expression member
      · exact safe pattern expression (by simp [member])
    · exact esgcFree_mkBool trace false
  | case7 value rest pattern name ih =>
    simp only [naivePatternMatch]
    apply ih
    intro pattern' expression member
    simp only [List.mem_cons, Prod.mk.injEq] at member
    rcases member with ⟨_, rfl⟩ | member
    · exact safe (.pas pattern name) expression (by simp)
    · exact safe pattern' expression (by simp [member])
  | case8 value rest pattern ih =>
    have valueSafe := safe (.pref pattern) value (by simp)
    simp only [naivePatternMatch]
    apply ih
    intro pattern' expression member
    simp only [List.mem_cons, Prod.mk.injEq] at member
    rcases member with ⟨_, rfl⟩ | member
    · simpa [esgcFree, esgcFreeList] using valueSafe
    · exact safe pattern' expression (by simp [member])

/-- Naive branch chains are global-initialization-safe when their value, default, and
branch expressions are global-initialization-safe. -/
theorem esgcFree_naivePatternMatches (trace : Tra) (value default : FlatLang.Exp) (rows : List (FlatLang.Pat × FlatLang.Exp))
    (valueSafe : esgcFree value) (defaultSafe : esgcFree default)
    (branchesSafe : ∀ pattern body, (pattern, body) ∈ rows → esgcFree body) :
    esgcFree (naivePatternMatches trace value rows default) := by
  induction rows with
  | nil => exact defaultSafe
  | cons row rest ih =>
    obtain ⟨pattern, body⟩ := row
    simp only [naivePatternMatches]
    apply esgcFree_smartIf
    · apply esgcFree_naivePatternMatch
      intro pat expression member
      simp only [List.mem_singleton, Prod.mk.injEq] at member
      obtain ⟨_, rfl⟩ := member
      exact valueSafe
    · exact branchesSafe pattern body (by simp)
    · apply ih
      intro pat expression member
      exact branchesSafe pat expression (by simp [member])


/-- Generated binding work items refer only to fresh local variables. -/
theorem esgcFree_patternEntries (trace : Tra) (base start : Nat) (patterns : List FlatLang.Pat) :
    ∀ pattern index expression,
      (pattern, index, expression) ∈ (patternEntries trace base start patterns).map Prod.snd →
      esgcFree expression := by
  induction patterns generalizing start with
  | nil => simp [patternEntries]
  | cons first rest ih =>
    intro pattern index expression member
    simp only [patternEntries_cons, List.map_cons, List.mem_cons, Prod.mk.injEq] at member
    rcases member with ⟨_, _, rfl⟩ | member
    · simp [esgcFree]
    · exact ih (start + 1) pattern index expression member

/-- The generated projection bindings preserve a global-initialization-safe continuation. -/
theorem esgcFree_projectionFold (trace : Tra) (value body : FlatLang.Exp)
    (entries : List ((Nat × Flapjack.Basis.Pure.MlString.MlString) × (FlatLang.Pat × Nat × FlatLang.Exp)))
    (valueSafe : esgcFree value) (bodySafe : esgcFree body) :
    esgcFree (entries.foldr (fun ((index, name), _) rest =>
      .let_ trace (some name) (.app trace (.el index) [value]) rest) body) := by
  induction entries with
  | nil => exact bodySafe
  | cons entry rest ih =>
    obtain ⟨⟨index, name⟩, work⟩ := entry
    simp [esgcFree, esgcFreeList, valueSafe, ih]

/-- Pattern binding preserves global-initialization safety of its worklist and continuation. -/
theorem esgcFree_compilePatBindings (trace : Tra) (base : Nat)
    (todo : List (FlatLang.Pat × Nat × FlatLang.Exp)) (body : FlatLang.Exp)
    (bodySafe : esgcFree body)
    (todoSafe : ∀ pattern index expression, (pattern, index, expression) ∈ todo →
      esgcFree expression) :
    esgcFree (compilePatBindings trace base todo body).2 := by
  revert todoSafe
  induction base, todo using compilePatBindings.induct trace body with
  | case1 i =>
    intro _
    simpa [compilePatBindings] using bodySafe
  | case2 i key expression rest ih =>
    intro safe
    rw [compilePatBindings]
    apply ih
    intro p k e member
    exact safe p k e (by simp [member])
  | case3 i key expression rest lit ih =>
    intro safe
    rw [compilePatBindings]
    apply ih
    intro p k e member
    exact safe p k e (by simp [member])
  | case4 i key expression rest name used continuation compiled ih =>
    intro safe
    have valueSafe := safe (.pvar name) key expression (by simp)
    have restSafe : ∀ p k e, (p, k, e) ∈ rest → esgcFree e := by
      intro p k e member
      exact safe p k e (by simp [member])
    have next := ih restSafe
    rw [compiled] at next
    simp [compilePatBindings, compiled, esgcFree, valueSafe, next]
  | case5 i key expression rest stamp patterns entries used continuation compiled ih =>
    dsimp only [entries] at compiled
    intro safe
    have valueSafe := safe (.pcon stamp patterns) key expression (by simp)
    have restSafe : ∀ p k e, (p, k, e) ∈ rest → esgcFree e := by
      intro p k e member
      exact safe p k e (by simp [member])
    have allSafe : ∀ p k e, (p, k, e) ∈ (patternEntries trace i 0 patterns).map Prod.snd ++ rest →
        esgcFree e := by
      intro p k e member
      rcases List.mem_append.mp member with member | member
      · exact esgcFree_patternEntries trace i 0 patterns p k e member
      · exact restSafe p k e member
    have next := ih allSafe
    rw [compiled] at next
    simp only [compilePatBindings, compiled]
    exact esgcFree_projectionFold trace expression continuation _ valueSafe next
  | case6 i key expression rest pattern name generated used continuation compiled ih =>
    dsimp only [generated] at compiled
    intro safe
    have valueSafe := safe (.pas pattern name) key expression (by simp)
    have allSafe : ∀ p k e, (p, k, e) ∈
        (pattern, i + 1, .varLocal trace (encNumToName (i + 1))) :: rest →
        esgcFree e := by
      intro p k e member
      simp only [List.mem_cons, Prod.mk.injEq] at member
      rcases member with ⟨_, _, rfl⟩ | member
      · simp [esgcFree]
      · exact safe p k e (by simp [member])
    have next := ih allSafe
    rw [compiled] at next
    simp [compilePatBindings, compiled, esgcFree, valueSafe, next]
  | case7 i key expression rest pattern generated used continuation compiled ih =>
    dsimp only [generated] at compiled
    intro safe
    have valueSafe := safe (.pref pattern) key expression (by simp)
    have allSafe : ∀ p k e, (p, k, e) ∈
        (pattern, i + 1, .varLocal trace (encNumToName (i + 1))) :: rest →
        esgcFree e := by
      intro p k e member
      simp only [List.mem_cons, Prod.mk.injEq] at member
      rcases member with ⟨_, _, rfl⟩ | member
      · simp [esgcFree]
      · exact safe p k e (by simp [member])
    have next := ih allSafe
    rw [compiled] at next
    simp [compilePatBindings, compiled, esgcFree, esgcFreeList, valueSafe, next]

private theorem setGlobals_mkBool (t : Tra) (b : Bool) :
    setGlobals (mkBool t b) = emptyGlobalBag := by
  simp [mkBool, setGlobals, elistGlobals]

private theorem setGlobals_smartIf (t : Tra) (c x y : FlatLang.Exp)
    (hc : setGlobals c = emptyGlobalBag) (hx : setGlobals x = emptyGlobalBag)
    (hy : setGlobals y = emptyGlobalBag) :
    setGlobals (smartIf t c x y) = emptyGlobalBag := by
  cases c <;> simp_all [smartIf, setGlobals, FlatProps.unionGlobalBag_empty_right]
  case con t tag args =>
    cases tag <;> cases args <;> try simp_all [setGlobals, FlatProps.unionGlobalBag_empty_right]
    case some.nil pair =>
      obtain ⟨tag, typ⟩ := pair
      cases typ <;> try simp_all [setGlobals, FlatProps.unionGlobalBag_empty_right]
      all_goals split_ifs <;> simp_all [setGlobals, FlatProps.unionGlobalBag_empty_right]

@[hol "cakeml/compiler/backend/proofs/flat_patternProofScript.sml" "set_globals_decode_pos"]
theorem setGlobals_decodePos (t : Tra) (p : Position) (exp : FlatLang.Exp)
    (safe : setGlobals exp = emptyGlobalBag) : setGlobals (decodePos t exp p) = emptyGlobalBag := by
  induction p generalizing exp with
  | emptyPos => exact safe
  | pos index rest ih =>
    apply ih
    simp [setGlobals, elistGlobals, opGlobalBag, safe, FlatProps.unionGlobalBag_empty_right]

@[hol "cakeml/compiler/backend/proofs/flat_patternProofScript.sml" "set_globals_decode_test"]
theorem setGlobals_decodeTest (exp : FlatLang.Exp) (t : Tra) (d : DTest)
    (safe : setGlobals exp = emptyGlobalBag) : setGlobals (decodeTest t d exp) = emptyGlobalBag := by
  cases d <;> simp [decodeTest, setGlobals, elistGlobals, opGlobalBag, safe, FlatProps.unionGlobalBag_empty_right]

@[hol "cakeml/compiler/backend/proofs/flat_patternProofScript.sml" "set_globals_decode_guard"]
theorem setGlobals_decodeGuard (exp : FlatLang.Exp) (t : Tra) (gd : DGuard)
    (safe : setGlobals exp = emptyGlobalBag) : setGlobals (decodeGuard t exp gd) = emptyGlobalBag := by
  induction gd with
  | true_ => exact setGlobals_mkBool t true
  | posTest pos test => exact setGlobals_decodeTest _ t test (setGlobals_decodePos t pos exp safe)
  | not gd ih => simp [decodeGuard, setGlobals, elistGlobals, opGlobalBag, ih, setGlobals_mkBool, FlatProps.unionGlobalBag_empty_right]
  | conj a b ihA ihB => exact setGlobals_smartIf t _ _ _ ihA ihB (setGlobals_mkBool t false)
  | disj a b ihA ihB => exact setGlobals_smartIf t _ _ _ ihA (setGlobals_mkBool t true) ihB

/-- Every generated child projection of a global-initialization-safe expression is global-initialization-safe. -/
theorem setGlobals_children (trace : Tra) (value : FlatLang.Exp) (patterns : List FlatLang.Pat)
    (safe : setGlobals value = emptyGlobalBag) :
    ∀ pattern expression, (pattern, expression) ∈
      patterns.mapIdx (fun i p => (p, .app trace (.el i) [value])) → setGlobals expression = emptyGlobalBag := by
  intro pattern expression member
  obtain ⟨i, _, eq⟩ := List.mem_mapIdx.mp member
  obtain ⟨_, rfl⟩ := Prod.mk.inj eq
  simpa [setGlobals, elistGlobals, opGlobalBag, FlatProps.unionGlobalBag_empty_left, FlatProps.unionGlobalBag_empty_right] using safe

/-- Naive matching generates a global-initialization-safe guard when each worklist value is
global-initialization-safe. -/
theorem setGlobals_naivePatternMatch_aux (trace : Tra) (todo : List (FlatLang.Pat × FlatLang.Exp))
    (safe : ∀ pattern expression, (pattern, expression) ∈ todo → setGlobals expression = emptyGlobalBag) :
    setGlobals (naivePatternMatch trace todo) = emptyGlobalBag := by
  induction todo using naivePatternMatch.induct trace with
  | case1 => simpa [naivePatternMatch] using setGlobals_mkBool trace true
  | case2 value rest ih | case3 value rest _ ih =>
    simp only [naivePatternMatch]
    apply ih
    intro pattern expression member
    exact safe pattern expression (by simp [member])
  | case4 value rest literal ih =>
    have valueSafe := safe (.plit literal) value (by simp)
    have restSafe : ∀ pattern expression, (pattern, expression) ∈ rest → setGlobals expression = emptyGlobalBag := by
      intro pattern expression member
      exact safe pattern expression (by simp [member])
    simp only [naivePatternMatch]
    apply setGlobals_smartIf
    · simp [setGlobals, elistGlobals, opGlobalBag, valueSafe, FlatProps.unionGlobalBag_empty_right]
    · exact ih restSafe
    · exact setGlobals_mkBool trace false
  | case5 value rest patterns ih =>
    have valueSafe := safe (.pcon none patterns) value (by simp)
    simp only [naivePatternMatch]
    apply ih
    intro pattern expression member
    rcases List.mem_append.mp member with member | member
    · exact setGlobals_children trace value patterns valueSafe pattern expression member
    · exact safe pattern expression (by simp [member])
  | case6 value rest patterns tag typ ih =>
    have valueSafe := safe (.pcon (some (tag, typ)) patterns) value (by simp)
    simp only [naivePatternMatch]
    apply setGlobals_smartIf
    · simp [setGlobals, elistGlobals, opGlobalBag, valueSafe, FlatProps.unionGlobalBag_empty_right]
    · apply ih
      intro pattern expression member
      rcases List.mem_append.mp member with member | member
      · exact setGlobals_children trace value patterns valueSafe pattern expression member
      · exact safe pattern expression (by simp [member])
    · exact setGlobals_mkBool trace false
  | case7 value rest pattern name ih =>
    simp only [naivePatternMatch]
    apply ih
    intro pattern' expression member
    simp only [List.mem_cons, Prod.mk.injEq] at member
    rcases member with ⟨_, rfl⟩ | member
    · exact safe (.pas pattern name) expression (by simp)
    · exact safe pattern' expression (by simp [member])
  | case8 value rest pattern ih =>
    have valueSafe := safe (.pref pattern) value (by simp)
    simp only [naivePatternMatch]
    apply ih
    intro pattern' expression member
    simp only [List.mem_cons, Prod.mk.injEq] at member
    rcases member with ⟨_, rfl⟩ | member
    · simpa [setGlobals, elistGlobals, opGlobalBag, FlatProps.unionGlobalBag_empty_left, FlatProps.unionGlobalBag_empty_right] using valueSafe
    · exact safe pattern' expression (by simp [member])


/-- Naive pattern guards do not introduce global writes. -/
@[hol "cakeml/compiler/backend/proofs/flat_patternProofScript.sml" "set_globals_naive_pattern_match"]
theorem setGlobals_naivePatternMatch (t : Tra) (xs : List (FlatLang.Pat × FlatLang.Exp))
    (safe : ∀ pair ∈ xs, setGlobals pair.2 = emptyGlobalBag) :
    setGlobals (naivePatternMatch t xs) = emptyGlobalBag := by
  apply setGlobals_naivePatternMatch_aux
  intro p e member
  exact safe (p, e) member

/-- Flapjack helper: smart conditionals do not add global writes. HOL reasons by cases. -/
theorem setGlobals_smartIf_le (t : Tra) (c x y : FlatLang.Exp) (key : Nat) :
    setGlobals (smartIf t c x y) key ≤
      setGlobals c key + setGlobals x key + setGlobals y key := by
  cases c <;> simp [smartIf, setGlobals, unionGlobalBag]
  case con t tag args =>
    cases tag <;> cases args <;> simp [setGlobals, elistGlobals, emptyGlobalBag, unionGlobalBag]
    case some.nil pair =>
      obtain ⟨tag, typ⟩ := pair
      cases typ <;> simp [setGlobals, elistGlobals, emptyGlobalBag, unionGlobalBag]
      all_goals split_ifs <;> simp [setGlobals, elistGlobals, emptyGlobalBag, unionGlobalBag]

/-- The generated naive branch chain cannot add global writes. -/
@[hol "cakeml/compiler/backend/proofs/flat_patternProofScript.sml" "set_globals_naive_pattern_matches"]
theorem setGlobals_naivePatternMatches (t : Tra) (x : FlatLang.Exp)
    (ps : List (FlatLang.Pat × FlatLang.Exp)) (dflt : FlatLang.Exp)
    (safe : setGlobals x = emptyGlobalBag) :
    ∀ key, setGlobals (naivePatternMatches t x ps dflt) key ≤
      elistGlobals (dflt :: ps.map Prod.snd) key := by
  intro key
  induction ps with
  | nil => simp [naivePatternMatches, elistGlobals, unionGlobalBag, emptyGlobalBag]
  | cons row rest ih =>
    obtain ⟨p, body⟩ := row
    have guardSafe : setGlobals (naivePatternMatch t [(p, x)]) = emptyGlobalBag := by
      apply setGlobals_naivePatternMatch
      simp [safe]
    have bound := setGlobals_smartIf_le t (naivePatternMatch t [(p, x)]) body
      (naivePatternMatches t x rest dflt) key
    simp only [naivePatternMatches]
    simp only [guardSafe, emptyGlobalBag, Nat.zero_add] at bound
    simp only [List.map_cons, elistGlobals, unionGlobalBag] at ih ⊢
    omega

private theorem setGlobals_patternEntries (trace : Tra) (base start : Nat) (patterns : List FlatLang.Pat) :
    ∀ pattern index expression,
      (pattern, index, expression) ∈ (patternEntries trace base start patterns).map Prod.snd →
      setGlobals expression = emptyGlobalBag := by
  induction patterns generalizing start with
  | nil => simp [patternEntries]
  | cons first rest ih =>
    intro pattern index expression member
    simp only [patternEntries_cons, List.map_cons, List.mem_cons, Prod.mk.injEq] at member
    rcases member with ⟨_, _, rfl⟩ | member
    · simp [setGlobals]
    · exact ih (start + 1) pattern index expression member

private theorem setGlobals_projectionFold (trace : Tra) (value body : FlatLang.Exp)
    (entries : List ((Nat × Flapjack.Basis.Pure.MlString.MlString) × (FlatLang.Pat × Nat × FlatLang.Exp)))
    (valueSafe : setGlobals value = emptyGlobalBag) :
    setGlobals (entries.foldr (fun ((index, name), _) rest =>
      .let_ trace (some name) (.app trace (.el index) [value]) rest) body) = setGlobals body := by
  induction entries with
  | nil => rfl
  | cons entry rest ih =>
    obtain ⟨⟨index, name⟩, work⟩ := entry
    simp [setGlobals, elistGlobals, opGlobalBag, valueSafe, ih, FlatProps.unionGlobalBag_empty_left, FlatProps.unionGlobalBag_empty_right]

/-- Pattern binding preserves the global bag when worklist values have empty bags. -/
theorem setGlobals_compilePatBindings_aux (trace : Tra) (base : Nat)
    (todo : List (FlatLang.Pat × Nat × FlatLang.Exp)) (body : FlatLang.Exp)
    (todoSafe : ∀ pattern index expression, (pattern, index, expression) ∈ todo →
      setGlobals expression = emptyGlobalBag) :
    setGlobals (compilePatBindings trace base todo body).2 = setGlobals body := by
  revert todoSafe
  induction base, todo using compilePatBindings.induct trace body with
  | case1 i =>
    intro _
    simp [compilePatBindings]
  | case2 i key expression rest ih =>
    intro safe
    rw [compilePatBindings]
    apply ih
    intro p k e member
    exact safe p k e (by simp [member])
  | case3 i key expression rest lit ih =>
    intro safe
    rw [compilePatBindings]
    apply ih
    intro p k e member
    exact safe p k e (by simp [member])
  | case4 i key expression rest name used continuation compiled ih =>
    intro safe
    have valueSafe := safe (.pvar name) key expression (by simp)
    have restSafe : ∀ p k e, (p, k, e) ∈ rest → setGlobals e = emptyGlobalBag := by
      intro p k e member
      exact safe p k e (by simp [member])
    have next := ih restSafe
    rw [compiled] at next
    simp [compilePatBindings, compiled, setGlobals, valueSafe, next, FlatProps.unionGlobalBag_empty_left]
  | case5 i key expression rest stamp patterns entries used continuation compiled ih =>
    dsimp only [entries] at compiled
    intro safe
    have valueSafe := safe (.pcon stamp patterns) key expression (by simp)
    have restSafe : ∀ p k e, (p, k, e) ∈ rest → setGlobals e = emptyGlobalBag := by
      intro p k e member
      exact safe p k e (by simp [member])
    have allSafe : ∀ p k e, (p, k, e) ∈ (patternEntries trace i 0 patterns).map Prod.snd ++ rest →
        setGlobals e = emptyGlobalBag := by
      intro p k e member
      rcases List.mem_append.mp member with member | member
      · exact setGlobals_patternEntries trace i 0 patterns p k e member
      · exact restSafe p k e member
    have next := ih allSafe
    rw [compiled] at next
    simp only [compilePatBindings, compiled]
    exact (setGlobals_projectionFold trace expression continuation _ valueSafe).trans next
  | case6 i key expression rest pattern name generated used continuation compiled ih =>
    dsimp only [generated] at compiled
    intro safe
    have valueSafe := safe (.pas pattern name) key expression (by simp)
    have allSafe : ∀ p k e, (p, k, e) ∈
        (pattern, i + 1, .varLocal trace (encNumToName (i + 1))) :: rest →
        setGlobals e = emptyGlobalBag := by
      intro p k e member
      simp only [List.mem_cons, Prod.mk.injEq] at member
      rcases member with ⟨_, _, rfl⟩ | member
      · simp [setGlobals]
      · exact safe p k e (by simp [member])
    have next := ih allSafe
    rw [compiled] at next
    simp [compilePatBindings, compiled, setGlobals, valueSafe, next, FlatProps.unionGlobalBag_empty_left]
  | case7 i key expression rest pattern generated used continuation compiled ih =>
    dsimp only [generated] at compiled
    intro safe
    have valueSafe := safe (.pref pattern) key expression (by simp)
    have allSafe : ∀ p k e, (p, k, e) ∈
        (pattern, i + 1, .varLocal trace (encNumToName (i + 1))) :: rest →
        setGlobals e = emptyGlobalBag := by
      intro p k e member
      simp only [List.mem_cons, Prod.mk.injEq] at member
      rcases member with ⟨_, _, rfl⟩ | member
      · simp [setGlobals]
      · exact safe p k e (by simp [member])
    have next := ih allSafe
    rw [compiled] at next
    simp [compilePatBindings, compiled, setGlobals, elistGlobals, opGlobalBag, valueSafe, next,
      FlatProps.unionGlobalBag_empty_left, FlatProps.unionGlobalBag_empty_right]

/-- Pattern binding leaves the continuation's global bag unchanged. -/
@[hol "cakeml/compiler/backend/proofs/flat_patternProofScript.sml" "set_globals_compile_pat_bindings"]
theorem setGlobals_compilePatBindings (t : Tra) (i : Nat)
    (bindings : List (FlatLang.Pat × Nat × FlatLang.Exp)) (exp : FlatLang.Exp)
    (safe : ∀ binding ∈ bindings, setGlobals binding.2.2 = emptyGlobalBag) :
    setGlobals (compilePatBindings t i bindings exp).2 = setGlobals exp := by
  apply setGlobals_compilePatBindings_aux
  intro p k e mem
  exact safe (p, k, e) mem

/-- Decoding a decision tree preserves global-initialization safety. -/
@[hol "cakeml/compiler/backend/proofs/flat_patternProofScript.sml" "esgc_free_decode_dtree"]
theorem esgcFree_decodeDtree (value default : FlatLang.Exp) (branches : Spt FlatLang.Exp)
    (trace : Tra) (tree : DTree)
    (premises : esgcFree value ∧ esgcFree default ∧
      ∀ branch ∈ sptToList branches, esgcFree branch) :
    esgcFree (decodeDtree trace branches value default tree) := by
  obtain ⟨valueSafe, defaultSafe, branchesSafe⟩ := premises
  induction tree with
  | fail => exact defaultSafe
  | typeFail => simp [decodeDtree, esgcFree]
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
    · exact esgcFree_smartIf trace _ _ _ (esgcFree_decodeGuard value trace _ valueSafe) ihYes ihNo

/-- Decoding preserves empty global bags for a safe value, default, and
all expressions in the branch tree. -/
@[hol "cakeml/compiler/backend/proofs/flat_patternProofScript.sml" "set_globals_decode_dtree_empty"]
theorem setGlobals_decodeDtree (value default : FlatLang.Exp) (branches : Spt FlatLang.Exp)
    (trace : Tra) (tree : DTree)
    (premises : setGlobals value = emptyGlobalBag ∧ setGlobals default = emptyGlobalBag ∧
      ∀ branch ∈ sptToList branches, setGlobals branch = emptyGlobalBag) :
    setGlobals (decodeDtree trace branches value default tree) = emptyGlobalBag := by
  obtain ⟨valueSafe, defaultSafe, branchesSafe⟩ := premises
  induction tree with
  | fail => exact defaultSafe
  | typeFail => simp [decodeDtree, setGlobals]
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
    · exact setGlobals_smartIf trace _ _ _ (setGlobals_decodeGuard value trace _ valueSafe) ihYes ihNo


/-- A compiled branch remains global-initialization-safe when its value and body are. -/
theorem esgcFree_compilePatRhs (trace : Tra) (base : Nat) (value : FlatLang.Exp)
    (pattern : FlatLang.Pat) (body : FlatLang.Exp)
    (valueSafe : esgcFree value) (bodySafe : esgcFree body) :
    esgcFree (compilePatRhs trace base value (pattern, body)) := by
  apply esgcFree_compilePatBindings trace (base + 1) [(pattern, base, value)] body bodySafe
  intro p k e member
  simp only [List.mem_singleton, Prod.mk.injEq] at member
  obtain ⟨_, _, rfl⟩ := member
  exact valueSafe


private theorem setGlobals_compilePatRhs (trace : Tra) (base : Nat) (value : FlatLang.Exp)
    (pattern : FlatLang.Pat) (body : FlatLang.Exp)
    (safe : setGlobals value = emptyGlobalBag) :
    setGlobals (compilePatRhs trace base value (pattern, body)) = setGlobals body := by
  apply setGlobals_compilePatBindings trace (base + 1) [(pattern, base, value)] body
  simp [safe]

private theorem compiledRows_globals (t : Tra) (i : Nat) (x : FlatLang.Exp)
    (ps : List (FlatLang.Pat × FlatLang.Exp)) (safe : setGlobals x = emptyGlobalBag) :
    elistGlobals (List.zip (ps.map Prod.fst) (ps.map (compilePatRhs t i x)) |>.map Prod.snd) =
      elistGlobals (ps.map Prod.snd) := by
  induction ps with
  | nil => rfl
  | cons row rest ih =>
    obtain ⟨p, body⟩ := row
    simp only [List.map_cons, List.zip_cons_cons, elistGlobals]
    rw [setGlobals_compilePatRhs t i x p body safe, ih]

/-- Pattern compilation bounds global writes by its default and source branches. -/
@[hol "cakeml/compiler/backend/proofs/flat_patternProofScript.sml" "set_globals_compile_pats"]
theorem setGlobals_compilePats (cfg : Config) (naive : Bool) (t : Tra) (n : Nat)
    (x dflt : FlatLang.Exp) (ps : List (FlatLang.Pat × FlatLang.Exp))
    (safe : (naive = false → elistGlobals (dflt :: ps.map Prod.snd) = emptyGlobalBag) ∧
      setGlobals x = emptyGlobalBag) :
    ∀ key, setGlobals (compilePats cfg naive t n x dflt ps) key ≤
      elistGlobals (dflt :: ps.map Prod.snd) key := by
  intro key
  cases naive with
  | true =>
    have h := setGlobals_naivePatternMatches t x
      (List.zip (ps.map Prod.fst) (ps.map (compilePatRhs t n x))) dflt safe.2 key
    simp only [compilePats, ↓reduceIte]
    simpa only [elistGlobals, compiledRows_globals t n x ps safe.2] using h
  | false =>
    have allEmpty := safe.1 rfl
    have parts := (elistGlobals_eq_empty (dflt :: ps.map Prod.snd)).mp allEmpty
    have defaultSafe : setGlobals dflt = emptyGlobalBag := parts dflt (by simp)
    have branchesSafe : ∀ branch ∈ ps.map (compilePatRhs t n x), setGlobals branch = emptyGlobalBag := by
      intro branch mem
      obtain ⟨⟨p, body⟩, hmem, rfl⟩ := List.mem_map.mp mem
      rw [setGlobals_compilePatRhs t n x p body safe.2]
      apply parts body
      simp only [List.mem_cons, List.mem_map]
      exact Or.inr ⟨(p, body), hmem, rfl⟩
    have result := setGlobals_decodeDtree x dflt (branchTree (ps.map (compilePatRhs t n x))) t
      (PatternComp.comp (ps.zipIdx.map fun ((p, _), j) => (encodePat p, j)))
      ⟨safe.2, defaultSafe, by
        intro branch member
        apply branchesSafe branch
        have eq := congrArg (fun (values : Set FlatLang.Exp) => branch ∈ values)
          (setToList_fromList (ps.map (compilePatRhs t n x)))
        exact eq.mp member⟩
    simp only [compilePats, Bool.false_eq_true, ↓reduceIte]
    rw [result, allEmpty]

/-- Both implementations of branch compilation preserve global-initialization safety. -/
theorem esgcFree_compilePats (cfg : Config) (naive : Bool) (trace : Tra) (base : Nat)
    (value default : FlatLang.Exp) (rows : List (FlatLang.Pat × FlatLang.Exp))
    (valueSafe : esgcFree value) (defaultSafe : esgcFree default)
    (rowsSafe : ∀ pattern body, (pattern, body) ∈ rows → esgcFree body) :
    esgcFree (compilePats cfg naive trace base value default rows) := by
  have branchesSafe : ∀ branch, branch ∈ rows.map (compilePatRhs trace base value) →
      esgcFree branch := by
    intro branch member
    obtain ⟨⟨pattern, body⟩, row, rfl⟩ := List.mem_map.mp member
    exact esgcFree_compilePatRhs trace base value pattern body valueSafe (rowsSafe pattern body row)
  cases naive with
  | false =>
    simp only [compilePats, Bool.false_eq_true, ↓reduceIte]
    apply esgcFree_decodeDtree value default _ trace _
    refine ⟨valueSafe, defaultSafe, ?_⟩
    intro branch member
    apply branchesSafe branch
    have eq := congrArg (fun (values : Set FlatLang.Exp) => branch ∈ values)
      (setToList_fromList (rows.map (compilePatRhs trace base value)))
    exact eq.mp member
  | true =>
    simp only [compilePats, ↓reduceIte]
    apply esgcFree_naivePatternMatches trace value default _ valueSafe defaultSafe
    intro pattern branch member
    exact branchesSafe branch (List.of_mem_zip member).2



/-- The source worklist condition preserves the continuation invariant. -/
@[hol "cakeml/compiler/backend/proofs/flat_patternProofScript.sml" "esgc_free_compile_pat_bindings"]
theorem esgcFree_compilePatBindings_hol (t : Tra) (i : Nat)
    (bindings : List (FlatLang.Pat × Nat × FlatLang.Exp)) (exp : FlatLang.Exp)
    (safe : esgcFree exp ∧ ∀ binding ∈ bindings, esgcFree binding.2.2) :
    esgcFree (compilePatBindings t i bindings exp).2 := by
  apply esgcFree_compilePatBindings t i bindings exp safe.1
  intro pattern index value mem
  exact safe.2 (pattern, index, value) mem

@[hol "cakeml/compiler/backend/proofs/flat_patternProofScript.sml" "esgc_free_naive_pattern_match"]
theorem esgcFree_naivePatternMatch_hol (t : Tra) (xs : List (FlatLang.Pat × FlatLang.Exp))
    (safe : ∀ exp ∈ xs.map Prod.snd, esgcFree exp) :
    esgcFree (naivePatternMatch t xs) := by
  apply esgcFree_naivePatternMatch
  intro pat exp mem
  apply safe exp
  exact List.mem_map.mpr ⟨(pat, exp), mem, rfl⟩

@[hol "cakeml/compiler/backend/proofs/flat_patternProofScript.sml" "esgc_free_naive_pattern_matches"]
theorem esgcFree_naivePatternMatches_hol (t : Tra) (x : FlatLang.Exp)
    (xs : List (FlatLang.Pat × FlatLang.Exp)) (dflt : FlatLang.Exp)
    (safe : ∀ exp ∈ x :: dflt :: xs.map Prod.snd, esgcFree exp) :
    esgcFree (naivePatternMatches t x xs dflt) := by
  apply esgcFree_naivePatternMatches t x dflt xs
  · exact safe x (by simp)
  · exact safe dflt (by simp)
  · intro pat exp mem
    apply safe exp
    simp only [List.mem_cons, List.mem_map]
    exact Or.inr (Or.inr ⟨(pat, exp), mem, rfl⟩)

/-- Compiling match branches on a local scrutinee preserves the invariant. -/
@[hol "cakeml/compiler/backend/proofs/flat_patternProofScript.sml" "esgc_free_compile_pats"]
theorem esgcFree_compilePats_hol (cfg : Config) (naive : Bool) (t : Tra) (n : Nat)
    (t' : Tra) (name : Flapjack.Basis.Pure.MlString.MlString) (dflt : FlatLang.Exp)
    (ps : List (FlatLang.Pat × FlatLang.Exp))
    (safe : esgcFree dflt ∧ ∀ exp ∈ ps.map Prod.snd, esgcFree exp) :
    esgcFree (compilePats cfg naive t n (.varLocal t' name) dflt ps) := by
  apply esgcFree_compilePats cfg naive t n (.varLocal t' name) dflt ps
  · simp [esgcFree]
  · exact safe.1
  · intro pat exp mem
    exact safe.2 exp (List.mem_map.mpr ⟨(pat, exp), mem, rfl⟩)

end Flapjack.Compiler.Backend.FlatPattern
