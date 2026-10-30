import Flapjack.Compiler.Backend.FlatPattern.Proofs.NoMat
import Flapjack.Compiler.Backend.FlatProps.Globals
import Mathlib.Tactic.SplitIfs

/-! Global-initialization safety of generated pattern decision expressions. -/
namespace Flapjack.Compiler.Backend.FlatPattern
open Flapjack.Compiler.Backend.BackendCommon FlatLang PatternCommon PatternSemantics
open Flapjack.Compiler.Backend.FlatProps

private theorem esgcFree_mkBool (t : Tra) (b : Bool) : esgcFree (mkBool t b) := by
  simp [mkBool, esgcFree, esgcFreeList]

private theorem esgcFree_smartIf (t : Tra) (c x y : FlatLang.Exp)
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
theorem esgcFree_decodeTest (t : Tra) (d : DTest) (exp : FlatLang.Exp)
    (safe : esgcFree exp) : esgcFree (decodeTest t d exp) := by
  cases d <;> simp [decodeTest, esgcFree, esgcFreeList, safe]

@[hol "cakeml/compiler/backend/proofs/flat_patternProofScript.sml" "esgc_free_decode_guard"]
theorem esgcFree_decodeGuard (t : Tra) (exp : FlatLang.Exp) (gd : DGuard)
    (safe : esgcFree exp) : esgcFree (decodeGuard t exp gd) := by
  induction gd with
  | true_ => exact esgcFree_mkBool t true
  | posTest pos test => exact esgcFree_decodeTest t test _ (esgcFree_decodePos t pos exp safe)
  | not gd ih => simp [decodeGuard, esgcFree, esgcFreeList, ih, esgcFree_mkBool]
  | conj a b ihA ihB => exact esgcFree_smartIf t _ _ _ ihA ihB (esgcFree_mkBool t false)
  | disj a b ihA ihB => exact esgcFree_smartIf t _ _ _ ihA (esgcFree_mkBool t true) ihB

/-- Every generated child projection of a global-initialization-safe expression is global-initialization-safe. -/
theorem esgcFree_children (trace : Tra) (value : FlatLang.Exp) (start : Nat) (patterns : List FlatLang.Pat)
    (safe : esgcFree value) :
    ∀ pattern expression, (pattern, expression) ∈ children trace value start patterns →
      esgcFree expression := by
  induction patterns generalizing start with
  | nil => simp [children]
  | cons first rest ih =>
    intro pattern expression member
    simp only [children, List.mem_cons, Prod.mk.injEq] at member
    rcases member with ⟨_, rfl⟩ | member
    · simpa [esgcFree, esgcFreeList] using safe
    · exact ih (start + 1) pattern expression member

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
    · exact esgcFree_children trace value 0 patterns valueSafe pattern expression member
    · exact safe pattern expression (by simp [member])
  | case6 value rest patterns tag typ ih =>
    have valueSafe := safe (.pcon (some (tag, typ)) patterns) value (by simp)
    simp only [naivePatternMatch]
    apply esgcFree_smartIf
    · simp [esgcFree, esgcFreeList, valueSafe]
    · apply ih
      intro pattern expression member
      rcases List.mem_append.mp member with member | member
      · exact esgcFree_children trace value 0 patterns valueSafe pattern expression member
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
    simp only [patternEntries, List.map_cons, List.mem_cons, Prod.mk.injEq] at member
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

mutual
private def bindingWeight : FlatLang.Pat → Nat
  | .pcon _ ps => 1 + bindingWeights ps
  | .pas p _ | .pref p => 1 + bindingWeight p
  | _ => 1

private def bindingWeights : List FlatLang.Pat → Nat
  | [] => 0
  | p :: ps => bindingWeight p + bindingWeights ps
end

private def bindingTodoWeight : List (FlatLang.Pat × Nat × FlatLang.Exp) → Nat
  | [] => 0
  | (p, _, _) :: rest => bindingWeight p + bindingTodoWeight rest

private theorem bindingTodoWeight_append (xs ys : List (FlatLang.Pat × Nat × FlatLang.Exp)) :
    bindingTodoWeight (xs ++ ys) = bindingTodoWeight xs + bindingTodoWeight ys := by
  induction xs with
  | nil => simp [bindingTodoWeight]
  | cons x xs ih => cases x with | mk p pair => cases pair; simp [bindingTodoWeight, ih, Nat.add_assoc]

private theorem patternEntries_weight (trace : Tra) (base start : Nat) (patterns : List FlatLang.Pat) :
    bindingTodoWeight ((patternEntries trace base start patterns).map Prod.snd) = bindingWeights patterns := by
  induction patterns generalizing start with
  | nil => rfl
  | cons p ps ih => simp [patternEntries, bindingTodoWeight, bindingWeights, ih]

/-- Pattern binding preserves global-initialization safety of its worklist and continuation. -/
theorem esgcFree_compilePatBindings (trace : Tra) (base : Nat)
    (todo : List (FlatLang.Pat × Nat × FlatLang.Exp)) (body : FlatLang.Exp)
    (bodySafe : esgcFree body)
    (todoSafe : ∀ pattern index expression, (pattern, index, expression) ∈ todo →
      esgcFree expression) :
    esgcFree (compilePatBindings trace base todo body).2 := by
  suffices ∀ n todo, bindingTodoWeight todo = n → ∀ base,
      (∀ pattern index expression, (pattern, index, expression) ∈ todo →
        esgcFree expression) →
      esgcFree (compilePatBindings trace base todo body).2 by
    exact this _ todo rfl base todoSafe
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro todo hn base todoSafe
    cases todo with
    | nil => simpa [compilePatBindings] using bodySafe
    | cons item rest =>
      obtain ⟨pattern, index, value⟩ := item
      have valueSafe := todoSafe pattern index value (by simp)
      have restSafe : ∀ p k e, (p, k, e) ∈ rest → esgcFree e := by
        intro p k e member
        exact todoSafe p k e (by simp [member])
      cases pattern with
      | pany | plit _ =>
        rw [compilePatBindings]
        exact ih _ (by simp [bindingTodoWeight, bindingWeight] at hn ⊢; omega) rest rfl base restSafe
      | pvar name =>
        have ih := ih _ (by simp [bindingTodoWeight, bindingWeight] at hn ⊢; omega) rest rfl base restSafe
        cases run : compilePatBindings trace base rest body with
        | mk used result =>
          simp only [run] at ih
          simp [compilePatBindings, run, esgcFree, valueSafe, ih]
      | pcon tag patterns =>
        have allSafe : ∀ p k e, (p, k, e) ∈ (patternEntries trace base 0 patterns).map Prod.snd ++ rest →
            esgcFree e := by
          intro p k e member
          rcases List.mem_append.mp member with member | member
          · exact esgcFree_patternEntries trace base 0 patterns p k e member
          · exact restSafe p k e member
        have ih := ih _ (by simp [bindingTodoWeight, bindingWeight, bindingTodoWeight_append, patternEntries_weight] at hn ⊢; omega)
          ((patternEntries trace base 0 patterns).map Prod.snd ++ rest) rfl (base + 2 + patterns.length) allSafe
        cases run : compilePatBindings trace (base + 2 + patterns.length)
            ((patternEntries trace base 0 patterns).map Prod.snd ++ rest) body with
        | mk used result =>
          simp only [run] at ih
          simp only [compilePatBindings, run]
          exact esgcFree_projectionFold trace value result _ valueSafe ih
      | pas pattern name =>
        have allSafe : ∀ p k e, (p, k, e) ∈
            (pattern, base + 1, .varLocal trace (encNumToName (base + 1))) :: rest →
            esgcFree e := by
          intro p k e member
          simp only [List.mem_cons, Prod.mk.injEq] at member
          rcases member with ⟨_, _, rfl⟩ | member
          · simp [esgcFree]
          · exact restSafe p k e member
        have ih := ih _ (by simp [bindingTodoWeight, bindingWeight] at hn ⊢; omega)
          ((pattern, base + 1, .varLocal trace (encNumToName (base + 1))) :: rest) rfl (base + 2) allSafe
        cases run : compilePatBindings trace (base + 2)
            ((pattern, base + 1, .varLocal trace (encNumToName (base + 1))) :: rest) body with
        | mk used result =>
          simp only [run] at ih
          simp [compilePatBindings, run, esgcFree, valueSafe, ih]
      | pref pattern =>
        have allSafe : ∀ p k e, (p, k, e) ∈
            (pattern, base + 1, .varLocal trace (encNumToName (base + 1))) :: rest →
            esgcFree e := by
          intro p k e member
          simp only [List.mem_cons, Prod.mk.injEq] at member
          rcases member with ⟨_, _, rfl⟩ | member
          · simp [esgcFree]
          · exact restSafe p k e member
        have ih := ih _ (by simp [bindingTodoWeight, bindingWeight] at hn ⊢; omega)
          ((pattern, base + 1, .varLocal trace (encNumToName (base + 1))) :: rest) rfl (base + 2) allSafe
        cases run : compilePatBindings trace (base + 2)
            ((pattern, base + 1, .varLocal trace (encNumToName (base + 1))) :: rest) body with
        | mk used result =>
          simp only [run] at ih
          simp [compilePatBindings, run, esgcFree, esgcFreeList, valueSafe, ih]

/-- Decoding a decision tree preserves global-initialization safety when every reachable
branch and the default are global-initialization-safe. -/
theorem esgcFree_decodeDtree (trace : Tra) (branches : Spt FlatLang.Exp) (value default : FlatLang.Exp) (tree : DTree)
    (valueSafe : esgcFree value) (defaultSafe : esgcFree default)
    (branchesSafe : ∀ index branch, sptLookup index branches = some branch → esgcFree branch) :
    esgcFree (decodeDtree trace branches value default tree) := by
  induction tree with
  | fail => exact defaultSafe
  | typeFail => simp [decodeDtree, esgcFree]
  | leaf index =>
    cases found : sptLookup index branches with
    | none => simpa [decodeDtree, found] using defaultSafe
    | some branch => simpa [decodeDtree, found] using branchesSafe index branch found
  | if_ guard yes no ihYes ihNo =>
    simp only [decodeDtree]
    split_ifs
    · exact ihYes
    · exact ihNo
    · exact esgcFree_smartIf trace _ _ _ (esgcFree_decodeGuard trace value _ valueSafe) ihYes ihNo

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


/-- Every lookup in a branch-table fold is safe if the input tree and all
inserted expressions are safe. -/
theorem esgcFree_branchFold (branches : List FlatLang.Exp) (start : Nat) (tree : Spt FlatLang.Exp)
    (treeSafe : ∀ index branch, sptLookup index tree = some branch → esgcFree branch)
    (branchesSafe : ∀ branch, branch ∈ branches → esgcFree branch) :
    ∀ index branch, sptLookup index (branches.foldl (fun (state : Nat × Spt FlatLang.Exp) item =>
      (state.1 + 1, sptInsert state.1 item state.2)) (start, tree)).2 = some branch →
      esgcFree branch := by
  induction branches generalizing start tree with
  | nil => exact treeSafe
  | cons first rest ih =>
    simp only [List.foldl_cons]
    apply ih (start + 1) (sptInsert start first tree)
    · intro index branch found
      by_cases equal : index = start
      · subst index
        rw [sptLookup_sptInsert_same] at found
        cases found
        exact branchesSafe first (by simp)
      · rw [sptLookup_sptInsert_ne start index first tree equal] at found
        exact treeSafe index branch found
    · intro branch member
      exact branchesSafe branch (by simp [member])

/-- The branch table generated by pattern compilation contains only safe
expressions when all its inputs are safe. -/
theorem esgcFree_branchTree (branches : List FlatLang.Exp)
    (branchesSafe : ∀ branch, branch ∈ branches → esgcFree branch) :
    ∀ index branch, sptLookup index (branchTree branches) = some branch → esgcFree branch := by
  apply esgcFree_branchFold branches 0 .ln
  · intro index branch found
    simp [sptLookup] at found
  · exact branchesSafe

private theorem esgcFree_zip_right_mem {α β : Type} (xs : List α) (ys : List β) (a : α) (b : β)
    (member : (a, b) ∈ xs.zip ys) : b ∈ ys := by
  induction xs generalizing ys with
  | nil => simp at member
  | cons x xs ih =>
    cases ys with
    | nil => simp at member
    | cons y ys =>
      simp only [List.zip_cons_cons, List.mem_cons, Prod.mk.injEq] at member
      rcases member with ⟨_, rfl⟩ | member
      · simp
      · exact List.mem_cons_of_mem _ (ih ys member)

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
    exact esgcFree_decodeDtree trace _ value default _ valueSafe defaultSafe (esgcFree_branchTree _ branchesSafe)
  | true =>
    simp only [compilePats, ↓reduceIte]
    apply esgcFree_naivePatternMatches trace value default _ valueSafe defaultSafe
    intro pattern branch member
    exact branchesSafe branch (esgcFree_zip_right_mem _ _ pattern branch member)



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
