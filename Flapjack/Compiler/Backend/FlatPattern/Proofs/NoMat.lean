import Flapjack.Compiler.Backend.FlatPattern.Proofs.CompiledMatch
import Flapjack.Compiler.Backend.FlatPattern.CompileTotal
import Flapjack.Compiler.Backend.FlatProps.NoMat
import Mathlib.Tactic.SplitIfs

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
  cases condition <;> simp_all [smartIf, FlatProps.noMat]
  case con t tag args =>
    cases tag <;> cases args <;> try simp_all [FlatProps.noMat]
    case some.nil pair =>
      obtain ⟨tag, typ⟩ := pair
      cases typ <;> try simp_all [FlatProps.noMat]
      all_goals split_ifs <;> simp_all [FlatProps.noMat]

/-- Following a pattern position preserves a match-free value expression. -/
theorem noMat_decodePos (trace : Tra) (value : FlatLang.Exp) (pos : Position)
    (safe : FlatProps.noMat value = true) : FlatProps.noMat (decodePos trace value pos) = true := by
  induction pos generalizing value with
  | emptyPos => exact safe
  | pos index rest ih =>
    apply ih
    simpa [FlatProps.noMat, FlatProps.noMatList] using safe

/-- Generated atomic tests preserve match-freedom. -/
theorem noMat_decodeTest (trace : Tra) (test : DTest) (value : FlatLang.Exp)
    (safe : FlatProps.noMat value = true) : FlatProps.noMat (decodeTest trace test value) = true := by
  cases test <;> simp [decodeTest, FlatProps.noMat, FlatProps.noMatList, safe]

/-- Generated decision guards preserve match-freedom. -/
theorem noMat_decodeGuard (trace : Tra) (value : FlatLang.Exp) (guard : DGuard)
    (safe : FlatProps.noMat value = true) : FlatProps.noMat (decodeGuard trace value guard) = true := by
  induction guard with
  | true_ => exact noMat_mkBool trace true
  | posTest pos test => exact noMat_decodeTest trace test _ (noMat_decodePos trace value pos safe)
  | not guard ih => simp [decodeGuard, FlatProps.noMat, FlatProps.noMatList, ih, noMat_mkBool]
  | conj a b ihA ihB => exact noMat_smartIf trace _ _ _ ihA ihB (noMat_mkBool trace false)
  | disj a b ihA ihB => exact noMat_smartIf trace _ _ _ ihA (noMat_mkBool trace true) ihB

/-- Decoding a decision tree preserves match-freedom when every reachable
branch and the default are match-free. -/
theorem noMat_decodeDtree (trace : Tra) (branches : Spt FlatLang.Exp) (value default : FlatLang.Exp) (tree : DTree)
    (valueSafe : FlatProps.noMat value = true) (defaultSafe : FlatProps.noMat default = true)
    (branchesSafe : ∀ index branch, sptLookup index branches = some branch → FlatProps.noMat branch = true) :
    FlatProps.noMat (decodeDtree trace branches value default tree) = true := by
  induction tree with
  | fail => exact defaultSafe
  | typeFail => simp [decodeDtree, FlatProps.noMat]
  | leaf index =>
    cases found : sptLookup index branches with
    | none => simpa [decodeDtree, found] using defaultSafe
    | some branch => simpa [decodeDtree, found] using branchesSafe index branch found
  | if_ guard yes no ihYes ihNo =>
    simp only [decodeDtree]
    split_ifs
    · exact ihYes
    · exact ihNo
    · exact noMat_smartIf trace _ _ _ (noMat_decodeGuard trace value _ valueSafe) ihYes ihNo

/-- Every generated child projection of a match-free expression is match-free. -/
theorem noMat_children (trace : Tra) (value : FlatLang.Exp) (start : Nat) (patterns : List FlatLang.Pat)
    (safe : FlatProps.noMat value = true) :
    ∀ pattern expression, (pattern, expression) ∈ children trace value start patterns →
      FlatProps.noMat expression = true := by
  induction patterns generalizing start with
  | nil => simp [children]
  | cons first rest ih =>
    intro pattern expression member
    simp only [children, List.mem_cons, Prod.mk.injEq] at member
    rcases member with ⟨_, rfl⟩ | member
    · simpa [FlatProps.noMat, FlatProps.noMatList] using safe
    · exact ih (start + 1) pattern expression member

/-- Naive matching generates a match-free guard when each worklist value is
match-free. -/
theorem noMat_naivePatternMatch (trace : Tra) (todo : List (FlatLang.Pat × FlatLang.Exp))
    (safe : ∀ pattern expression, (pattern, expression) ∈ todo → FlatProps.noMat expression = true) :
    FlatProps.noMat (naivePatternMatch trace todo) = true := by
  induction todo using naivePatternMatch.induct trace with
  | case1 => simpa [naivePatternMatch] using noMat_mkBool trace true
  | case2 value rest ih | case3 value rest _ ih =>
    simp only [naivePatternMatch]
    apply ih
    intro pattern expression member
    exact safe pattern expression (by simp [member])
  | case4 value rest literal ih =>
    have valueSafe := safe (.plit literal) value (by simp)
    have restSafe : ∀ pattern expression, (pattern, expression) ∈ rest → FlatProps.noMat expression = true := by
      intro pattern expression member
      exact safe pattern expression (by simp [member])
    simp only [naivePatternMatch]
    apply noMat_smartIf
    · simp [FlatProps.noMat, FlatProps.noMatList, valueSafe]
    · exact ih restSafe
    · exact noMat_mkBool trace false
  | case5 value rest patterns ih =>
    have valueSafe := safe (.pcon none patterns) value (by simp)
    simp only [naivePatternMatch]
    apply ih
    intro pattern expression member
    rcases List.mem_append.mp member with member | member
    · exact noMat_children trace value 0 patterns valueSafe pattern expression member
    · exact safe pattern expression (by simp [member])
  | case6 value rest patterns tag typ ih =>
    have valueSafe := safe (.pcon (some (tag, typ)) patterns) value (by simp)
    simp only [naivePatternMatch]
    apply noMat_smartIf
    · simp [FlatProps.noMat, FlatProps.noMatList, valueSafe]
    · apply ih
      intro pattern expression member
      rcases List.mem_append.mp member with member | member
      · exact noMat_children trace value 0 patterns valueSafe pattern expression member
      · exact safe pattern expression (by simp [member])
    · exact noMat_mkBool trace false
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
    · simpa [FlatProps.noMat, FlatProps.noMatList] using valueSafe
    · exact safe pattern' expression (by simp [member])

/-- Naive branch chains are match-free when their value, default, and
branch expressions are match-free. -/
theorem noMat_naivePatternMatches (trace : Tra) (value default : FlatLang.Exp) (rows : List (FlatLang.Pat × FlatLang.Exp))
    (valueSafe : FlatProps.noMat value = true) (defaultSafe : FlatProps.noMat default = true)
    (branchesSafe : ∀ pattern body, (pattern, body) ∈ rows → FlatProps.noMat body = true) :
    FlatProps.noMat (naivePatternMatches trace value rows default) = true := by
  induction rows with
  | nil => exact defaultSafe
  | cons row rest ih =>
    obtain ⟨pattern, body⟩ := row
    simp only [naivePatternMatches]
    apply noMat_smartIf
    · apply noMat_naivePatternMatch
      intro pat expression member
      simp only [List.mem_singleton, Prod.mk.injEq] at member
      obtain ⟨_, rfl⟩ := member
      exact valueSafe
    · exact branchesSafe pattern body (by simp)
    · apply ih
      intro pat expression member
      exact branchesSafe pat expression (by simp [member])

/-- Generated binding work items refer only to fresh local variables. -/
theorem noMat_patternEntries (trace : Tra) (base start : Nat) (patterns : List FlatLang.Pat) :
    ∀ pattern index expression,
      (pattern, index, expression) ∈ (patternEntries trace base start patterns).map Prod.snd →
      FlatProps.noMat expression = true := by
  induction patterns generalizing start with
  | nil => simp [patternEntries]
  | cons first rest ih =>
    intro pattern index expression member
    simp only [patternEntries, List.map_cons, List.mem_cons, Prod.mk.injEq] at member
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

/-- Pattern binding preserves match-freedom of its worklist and continuation. -/
theorem noMat_compilePatBindings (trace : Tra) (base : Nat)
    (todo : List (FlatLang.Pat × Nat × FlatLang.Exp)) (body : FlatLang.Exp)
    (bodySafe : FlatProps.noMat body = true)
    (todoSafe : ∀ pattern index expression, (pattern, index, expression) ∈ todo →
      FlatProps.noMat expression = true) :
    FlatProps.noMat (compilePatBindings trace base todo body).2 = true := by
  suffices ∀ n todo, bindingTodoWeight todo = n → ∀ base,
      (∀ pattern index expression, (pattern, index, expression) ∈ todo →
        FlatProps.noMat expression = true) →
      FlatProps.noMat (compilePatBindings trace base todo body).2 = true by
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
      have restSafe : ∀ p k e, (p, k, e) ∈ rest → FlatProps.noMat e = true := by
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
          simp [compilePatBindings, run, FlatProps.noMat, valueSafe, ih]
      | pcon tag patterns =>
        have allSafe : ∀ p k e, (p, k, e) ∈ (patternEntries trace base 0 patterns).map Prod.snd ++ rest →
            FlatProps.noMat e = true := by
          intro p k e member
          rcases List.mem_append.mp member with member | member
          · exact noMat_patternEntries trace base 0 patterns p k e member
          · exact restSafe p k e member
        have ih := ih _ (by simp [bindingTodoWeight, bindingWeight, bindingTodoWeight_append, patternEntries_weight] at hn ⊢; omega)
          ((patternEntries trace base 0 patterns).map Prod.snd ++ rest) rfl (base + 2 + patterns.length) allSafe
        cases run : compilePatBindings trace (base + 2 + patterns.length)
            ((patternEntries trace base 0 patterns).map Prod.snd ++ rest) body with
        | mk used result =>
          simp only [run] at ih
          simp only [compilePatBindings, run]
          exact noMat_projectionFold trace value result _ valueSafe ih
      | pas pattern name =>
        have allSafe : ∀ p k e, (p, k, e) ∈
            (pattern, base + 1, .varLocal trace (encNumToName (base + 1))) :: rest →
            FlatProps.noMat e = true := by
          intro p k e member
          simp only [List.mem_cons, Prod.mk.injEq] at member
          rcases member with ⟨_, _, rfl⟩ | member
          · simp [FlatProps.noMat]
          · exact restSafe p k e member
        have ih := ih _ (by simp [bindingTodoWeight, bindingWeight] at hn ⊢; omega)
          ((pattern, base + 1, .varLocal trace (encNumToName (base + 1))) :: rest) rfl (base + 2) allSafe
        cases run : compilePatBindings trace (base + 2)
            ((pattern, base + 1, .varLocal trace (encNumToName (base + 1))) :: rest) body with
        | mk used result =>
          simp only [run] at ih
          simp [compilePatBindings, run, FlatProps.noMat, valueSafe, ih]
      | pref pattern =>
        have allSafe : ∀ p k e, (p, k, e) ∈
            (pattern, base + 1, .varLocal trace (encNumToName (base + 1))) :: rest →
            FlatProps.noMat e = true := by
          intro p k e member
          simp only [List.mem_cons, Prod.mk.injEq] at member
          rcases member with ⟨_, _, rfl⟩ | member
          · simp [FlatProps.noMat]
          · exact restSafe p k e member
        have ih := ih _ (by simp [bindingTodoWeight, bindingWeight] at hn ⊢; omega)
          ((pattern, base + 1, .varLocal trace (encNumToName (base + 1))) :: rest) rfl (base + 2) allSafe
        cases run : compilePatBindings trace (base + 2)
            ((pattern, base + 1, .varLocal trace (encNumToName (base + 1))) :: rest) body with
        | mk used result =>
          simp only [run] at ih
          simp [compilePatBindings, run, FlatProps.noMat, FlatProps.noMatList, valueSafe, ih]

/-- A compiled branch remains match-free when its value and body are. -/
theorem noMat_compilePatRhs (trace : Tra) (base : Nat) (value : FlatLang.Exp)
    (pattern : FlatLang.Pat) (body : FlatLang.Exp)
    (valueSafe : FlatProps.noMat value = true) (bodySafe : FlatProps.noMat body = true) :
    FlatProps.noMat (compilePatRhs trace base value (pattern, body)) = true := by
  apply noMat_compilePatBindings trace (base + 1) [(pattern, base, value)] body bodySafe
  intro p k e member
  simp only [List.mem_singleton, Prod.mk.injEq] at member
  obtain ⟨_, _, rfl⟩ := member
  exact valueSafe


/-- Every lookup in a branch-table fold is safe if the input tree and all
inserted expressions are safe. -/
theorem noMat_branchFold (branches : List FlatLang.Exp) (start : Nat) (tree : Spt FlatLang.Exp)
    (treeSafe : ∀ index branch, sptLookup index tree = some branch → FlatProps.noMat branch = true)
    (branchesSafe : ∀ branch, branch ∈ branches → FlatProps.noMat branch = true) :
    ∀ index branch, sptLookup index (branches.foldl (fun (state : Nat × Spt FlatLang.Exp) item =>
      (state.1 + 1, sptInsert state.1 item state.2)) (start, tree)).2 = some branch →
      FlatProps.noMat branch = true := by
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
theorem noMat_branchTree (branches : List FlatLang.Exp)
    (branchesSafe : ∀ branch, branch ∈ branches → FlatProps.noMat branch = true) :
    ∀ index branch, sptLookup index (branchTree branches) = some branch → FlatProps.noMat branch = true := by
  apply noMat_branchFold branches 0 .ln
  · intro index branch found
    simp [sptLookup] at found
  · exact branchesSafe

private theorem zip_right_mem {α β : Type} (xs : List α) (ys : List β) (a : α) (b : β)
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

/-- Both implementations of branch compilation preserve match-freedom. -/
theorem noMat_compilePats (cfg : Config) (naive : Bool) (trace : Tra) (base : Nat)
    (value default : FlatLang.Exp) (rows : List (FlatLang.Pat × FlatLang.Exp))
    (valueSafe : FlatProps.noMat value = true) (defaultSafe : FlatProps.noMat default = true)
    (rowsSafe : ∀ pattern body, (pattern, body) ∈ rows → FlatProps.noMat body = true) :
    FlatProps.noMat (compilePats cfg naive trace base value default rows) = true := by
  have branchesSafe : ∀ branch, branch ∈ rows.map (compilePatRhs trace base value) →
      FlatProps.noMat branch = true := by
    intro branch member
    obtain ⟨⟨pattern, body⟩, row, rfl⟩ := List.mem_map.mp member
    exact noMat_compilePatRhs trace base value pattern body valueSafe (rowsSafe pattern body row)
  cases naive with
  | false =>
    simp only [compilePats, Bool.false_eq_true, ↓reduceIte]
    exact noMat_decodeDtree trace _ value default _ valueSafe defaultSafe (noMat_branchTree _ branchesSafe)
  | true =>
    simp only [compilePats, ↓reduceIte]
    apply noMat_naivePatternMatches trace value default _ valueSafe defaultSafe
    intro pattern branch member
    exact branchesSafe branch (zip_right_mem _ _ pattern branch member)


/-- Compiling an expression eliminates every source match. -/
theorem noMat_compileExp (cfg : Config) (exp : FlatLang.Exp) :
    FlatProps.noMat (compileExp cfg exp).2.2 = true := by
  induction exp using compileExp.induct cfg
      (motive_2 := fun fs => FlatProps.noMatFuns (compileFuns cfg fs).2.2 = true)
      (motive_3 := fun es => FlatProps.noMatList (compileExps cfg es).2.2 = true)
      (motive_4 := fun rows => ∀ p e, (p, e) ∈ (compileMatch cfg rows).2.2 → FlatProps.noMat e = true) with
  | case1 => simp [compileExp, FlatProps.noMat]
  | case2 t x i sg y eq ih => simpa [compileExp, eq, FlatProps.noMat] using ih
  | case3 t x ps i sg y eq j sgp ps2 eqp ih ihp =>
    have branch := noMat_compilePats cfg sgp t (max i j + 2) (.varLocal t (encNumToName (max i j + 2))) (.raise t (.varLocal t (encNumToName (max i j + 2)))) ps2
      (by simp [FlatProps.noMat]) (by simp [FlatProps.noMat]) (by simpa [eqp] using ihp)
    simpa [compileExp, eq, eqp, FlatProps.noMat] using And.intro ih branch
  | case4 t tag xs i sg ys eq ih => simpa [compileExp, eq, FlatProps.noMat] using ih
  | case5 t v x i sg y eq ih => simpa [compileExp, eq, FlatProps.noMat] using ih
  | case6 t op xs i sg ys eq ih => simpa [compileExp, eq, FlatProps.noMat] using ih
  | case7 t x ps i sg y eq j sgp ps2 eqp ih ihp =>
    have branch := noMat_compilePats cfg sgp t (max i j + 2) (.varLocal t (encNumToName (max i j + 2)))
      (.raise t (.con t (some (0, none)) [])) ps2
      (by simp [FlatProps.noMat]) (by simp [FlatProps.noMat, FlatProps.noMatList]) (by simpa [eqp] using ihp)
    simpa [compileExp, eq, eqp, FlatProps.noMat] using And.intro ih branch
  | case8 t vo x1 x2 i sg y eq j sg2 y2 eq2 ih1 ih2 =>
    simpa [compileExp, eq, eq2, FlatProps.noMat] using And.intro ih1 ih2
  | case9 t fs x j sgfs fs2 eqf i sg y eq ihf ih =>
    simpa [compileExp, eqf, eq, FlatProps.noMat] using And.intro ihf ih
  | case10 t x1 x2 x3 i sg1 y1 eq1 j sg2 y2 eq2 k sg3 y3 eq3 ih1 ih2 ih3 =>
    simp only [compileExp, eq1, eq2, eq3]
    apply noMat_smartIf
    · simpa [eq1] using ih1
    · simpa [eq2] using ih2
    · simpa [eq3] using ih3
  | case11 e h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 =>
    cases e <;> simp_all [compileExp, FlatProps.noMat]
    all_goals first | exact False.elim (h8 _ _ _ _ rfl rfl rfl rfl) | exact False.elim (h10 _ _ _ _ rfl rfl rfl rfl)
  | case12 p e member => simp [compileMatch] at member
  | case13 p x ps i sg y eq j sgp ps2 eqp ih ihp p' e member =>
    simp only [compileMatch, eq, eqp, List.mem_cons, Prod.mk.injEq] at member
    rcases member with ⟨_, rfl⟩ | member
    · simpa [eq] using ih
    · exact ihp p' e (by simpa [eqp] using member)
  | case14 => simp [compileExps, FlatProps.noMatList]
  | case15 x xs i sg y eq j sg2 ys eqs ih ihs =>
    simpa [compileExps, eq, eqs, FlatProps.noMatList] using And.intro ih ihs
  | case16 => simp [compileFuns, FlatProps.noMatFuns]
  | case17 f v e fs i sg y eq j sgfs fs2 eqf ih ihf =>
    simpa [compileFuns, eq, eqf, FlatProps.noMatFuns] using And.intro ih ihf


private theorem noMat_compileExps (cfg : Config) (exps : List FlatLang.Exp) :
    ∀ e ∈ (compileExps cfg exps).2.2, FlatProps.noMat e = true := by
  induction exps with
  | nil => simp [compileExps]
  | cons x xs ih =>
    cases hx : compileExp cfg x with
    | mk i pair =>
      obtain ⟨sg, y⟩ := pair
      cases hxs : compileExps cfg xs with
      | mk j pair =>
        obtain ⟨sgs, ys⟩ := pair
        intro e mem
        simp only [compileExps, hx, hxs, List.mem_cons] at mem
        rcases mem with rfl | mem
        · simpa [hx] using noMat_compileExp cfg x
        · exact ih e (by simpa [hxs] using mem)

private theorem noMat_compileMatch (cfg : Config) (rows : List (FlatLang.Pat × FlatLang.Exp)) :
    ∀ row ∈ (compileMatch cfg rows).2.2, FlatProps.noMat row.2 = true := by
  induction rows with
  | nil => simp [compileMatch]
  | cons row rows ih =>
    obtain ⟨p, x⟩ := row
    cases hx : compileExp cfg x with
    | mk i pair =>
      obtain ⟨sg, y⟩ := pair
      cases hrs : compileMatch cfg rows with
      | mk j pair =>
        obtain ⟨sgs, ys⟩ := pair
        intro row mem
        simp only [compileMatch, hx, hrs, List.mem_cons] at mem
        rcases mem with rfl | mem
        · simpa [hx] using noMat_compileExp cfg x
        · exact ih row (by simpa [hrs] using mem)

/-- All three expression-compiler outputs are match-free. -/
@[hol "cakeml/compiler/backend/proofs/flat_patternProofScript.sml" "compile_exp_no_Mat"]
theorem compileExp_noMat :
    (∀ cfg exp n sg exp', compileExp cfg exp = (n, sg, exp') → FlatProps.noMat exp' = true) ∧
    (∀ cfg exps n sg exps', compileExps cfg exps = (n, sg, exps') →
      ∀ e ∈ exps', FlatProps.noMat e = true) ∧
    (∀ cfg rows n sg rows', compileMatch cfg rows = (n, sg, rows') →
      ∀ row ∈ rows', FlatProps.noMat row.2 = true) := by
  refine ⟨?_, ?_, ?_⟩
  · intro cfg exp n sg exp' eq
    simpa only [eq] using noMat_compileExp cfg exp
  · intro cfg exps n sg exps' eq
    simpa only [eq] using noMat_compileExps cfg exps
  · intro cfg rows n sg rows' eq
    simpa only [eq] using noMat_compileMatch cfg rows

/-- Compiling every declaration produces the match-free input expected by
flat-to-closure compilation. -/
@[hol "cakeml/compiler/backend/proofs/flat_patternProofScript.sml" "compile_decs_no_Mat"]
theorem noMat_compileDecs (cfg : Config) (declarations : List FlatLang.Exp) :
    FlatProps.noMatDecs (declarations.map (compileDec cfg)) = true := by
  induction declarations with
  | nil => rfl
  | cons declaration rest ih =>
    simp [FlatProps.noMatDecs, compileDec, noMat_compileExp, ih]



end Flapjack.Compiler.Backend.FlatPattern
