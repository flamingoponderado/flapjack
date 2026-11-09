module

public import Flapjack.Compiler.Backend.ClosKnown.Proofs.TraversalSyntax
public import Flapjack.Compiler.Backend.ClosKnown.Proofs.SyntaxOracle

-- Proofs below unfold private helpers of these modules.
import all Flapjack.Compiler.Backend.Semantics.ClosSem.EvaluateExact
import all Flapjack.Compiler.Backend.Semantics.ClosSem.EvaluateFuel
@[expose] public section


/-! Assembling optimizer annotation preservation over the complete traversal. -/
namespace Flapjack.Compiler.Backend.ClosKnown.TraversalSyntax

/-- The safety invariant for every traversal input, used to assemble the source theorem. -/
theorem knownVarsAll (c : Config) (xs : List ClosLang.Exp) (env : List ValApprox)
    (globals : Spt ValApprox) : KnownVarsInvariant c xs env globals := by
  induction c, xs, env, globals using knownListTotal.induct
    (motive1 := fun c e env g => KnownVarsInvariant c [e] env g)
    (motive2 := fun c fns clos env g => ∀ n e, (n, e) ∈ fns →
      KnownVarsInvariant c [e] (List.replicate n .other ++ clos ++ env) g)
  case case1 c env g t v =>
    intro eas next h
    exact knownVarsVar c t v env g eas next h
  case case2 =>
    rename_i c env g t x y z xe xa g1 hx ye ya g2 hy ze za g3 hz ix iy iz
    intro eas next h
    apply knownVarsIf c t x y z env g ?_ ?_ ix eas next h
    · intro ea1 next1 ea2 next2 ⟨eq1, eq2⟩
      simp [knownListTotal_single, hx] at eq1
      rcases eq1 with ⟨rfl, rfl⟩
      simp [knownListTotal_single, hy] at eq2
      rcases eq2 with ⟨rfl, rfl⟩
      exact iz
    · intro ea1 next1 eq1
      simp [knownListTotal_single, hx] at eq1
      rcases eq1 with ⟨rfl, rfl⟩
      exact iy
  case case3 =>
    rename_i c env g t xs body ea g1 h1 e a g2 h2 ib indBody
    intro eas next h
    apply knownVarsLet c t xs body env g ?_ ib eas next h
    intro ea1 next1 eq1
    rw [h1] at eq1
    cases eq1
    exact indBody
  case case6 =>
    rename_i c env g t body handler e1 a1 g1 h1 e2 a2 g2 h2 ib ih
    intro eas next h
    apply knownVarsHandle c t body handler env g ?_ ib eas next h
    intro ea1 next1 eq1
    simp [knownListTotal_single, h1] at eq1
    rcases eq1 with ⟨rfl, rfl⟩
    exact ih
  case case4 c env g t x xe xa g1 hx ih =>
    intro eas next h
    exact knownVarsRaise c t x env g ih eas next h
  case case5 c env g t x xe xa g1 hx ih =>
    intro eas next h
    exact knownVarsTick c t x env g ih eas next h
  case case7 c env g t ticks dest args ea g1 hargs ih =>
    intro eas next h
    exact knownVarsCall c t ticks dest args env g ih eas next h
  case case8 c env g t op args ea g1 hargs a g2 hop ih =>
    intro eas next h
    exact knownVarsOp c t op args env g ih eas next h
  case case9 =>
    rename_i c env g t loc x xs ea g1 ha e a g2 hx hd iargs ifun
    have len := knownListTotal_length c xs env g
    rw [ha] at len
    simp only at len
    intro eas next h
    apply knownVarsApp c t loc x xs env g ?_ ?_ iargs eas next h
    · intro ea2 next1 ea1 next2 e1 a1 body ⟨eq1, eq2, head, decision⟩
      rw [ha] at eq1
      cases eq1
      simp [knownListTotal_single, hx] at eq2
      rcases eq2 with ⟨rfl, rfl⟩
      simp [knownSourceHead] at head
      rcases head with ⟨rfl, rfl⟩
      simp [← len, hd] at decision
    · intro ea2 next1 eq1
      rw [ha] at eq1
      cases eq1
      exact ifun
  case case10 =>
    rename_i c env g t loc x xs ea g1 ha e a g2 hx target hd iargs ifun
    have len := knownListTotal_length c xs env g
    rw [ha] at len
    simp only at len
    intro eas next h
    apply knownVarsApp c t loc x xs env g ?_ ?_ iargs eas next h
    · intro ea2 next1 ea1 next2 e1 a1 body ⟨eq1, eq2, head, decision⟩
      rw [ha] at eq1
      cases eq1
      simp [knownListTotal_single, hx] at eq2
      rcases eq2 with ⟨rfl, rfl⟩
      simp [knownSourceHead] at head
      rcases head with ⟨rfl, rfl⟩
      simp [← len, hd] at decision
    · intro ea2 next1 eq1
      rw [ha] at eq1
      cases eq1
      exact ifun
  case case11 =>
    rename_i c env g t loc x xs ea g1 ha e a g2 hx body0 hd ae aa g3 hb iargs ifun ibody
    have len := knownListTotal_length c xs env g
    rw [ha] at len
    simp only at len
    intro eas next h
    apply knownVarsApp c t loc x xs env g ?_ ?_ iargs eas next h
    · intro ea2 next1 ea1 next2 e1 a1 body ⟨eq1, eq2, head, decision⟩
      rw [ha] at eq1
      cases eq1
      simp [knownListTotal_single, hx] at eq2
      rcases eq2 with ⟨rfl, rfl⟩
      simp [knownSourceHead] at head
      rcases head with ⟨rfl, rfl⟩
      simp [← len, hd] at decision
      subst body
      exact ibody
    · intro ea2 next1 eq1
      rw [ha] at eq1
      cases eq1
      exact ifun
  case case12 c env g name loc vs arity body e a g1 hb ih =>
    intro eas next h
    exact knownVarsFn c name loc vs arity body env g ih eas next h
  case case13 =>
    rename_i c env g names loc vs fns body clos e a g1 hb ifuns ibody
    intro eas next h
    apply knownVarsLetrec c names loc vs fns body env g ?_ ?_ eas next h
    · intro clos' newFns ⟨same, _⟩
      subst clos'
      cases loc <;> simpa [clos, noInline] using ibody
    · intro clos' arity e newEnv ⟨same, mem, sameEnv⟩
      subst newEnv
      cases loc <;> simp only at same <;> subst clos' <;>
        simpa [clos, noInline, List.append_assoc] using ifuns arity e mem
  case case14 => contradiction
  case case15 =>
    rename_i c clos env g arity body fns e a g1 hb ihBody ihRest n x member
    rcases List.mem_cons.mp member with same | tail
    · cases Prod.mk.inj same with
      | intro hn hx => subst n; subst x; exact ihBody
    · exact ihRest n x tail
  case case16 c env g =>
    intro eas next h
    exact knownVarsNil c env g eas next h
  case case17 =>
    rename_i c env g x xs xe xa g1 hx tailEa g2 ht ix it
    cases xs with
    | nil => exact ix
    | cons y ys =>
      intro eas next h
      apply knownVarsCons c x y ys env g ?_ ix eas next h
      intro ea1 next1 eq1
      simp [knownListTotal_single, hx] at eq1
      rcases eq1 with ⟨rfl, rfl⟩
      exact it



/-- The optimizer preserves the absence of function variable annotations. -/
@[hol "cakeml/compiler/backend/proofs/clos_knownProofScript.sml" "known_every_Fn_vs_NONE"]
theorem knownEveryFnVarsNone (c : Config) (xs : List ClosLang.Exp)
    (env : List ValApprox) (globals : Spt ValApprox)
    (h : ClosProps.everyFnVarsNone xs ∧ (∀ a ∈ env, valApproxVarsNone a) ∧
      globalsApproxVarsNone globals) :
    ClosProps.everyFnVarsNone ((knownListTotal c xs env globals).1.map Prod.fst) ∧
    (∀ a ∈ (knownListTotal c xs env globals).1.map Prod.snd, valApproxVarsNone a) ∧
    globalsApproxVarsNone (knownListTotal c xs env globals).2 := by
  cases run : knownListTotal c xs env globals with
  | mk eas next =>
    have result := knownVarsAll c xs env globals eas next ⟨run, h.1, h.2.1, h.2.2⟩
    simpa [run] using result

open ClosProps BackendProps Relations.StateRelation.Oracle

/-- The source syntax oracle and the initial optimizer run establish that
both the optimized program and every incremental output lack annotations. -/
theorem syntaxOracleOk_outputVarsNone {C : Type} (c : Config) (xs : List ClosLang.Exp)
    (co : Nat → (Spt ValApprox × C) × (List ClosLang.Exp × List (Nat × Nat × ClosLang.Exp)))
    (g : Spt ValApprox) (ys : List (ClosLang.Exp × ValApprox))
    (oracle : syntaxOracleOk c xs co g)
    (known : knownListTotal c (ClosFvs.compile xs) [] .ln = (ys, g)) :
    everyFnVarsNone (ys.map Prod.fst) ∧
      ∀ n, everyFnVarsNone (stateCo (compileInc c)
        (pureCo (ClosFvs.compileInc (β := Nat × Nat × ClosLang.Exp)) ∘ co) n).2.1 := by
  obtain ⟨initial, recurrence, first, _, programs⟩ := oracle
  have initialSafe : everyFnVarsNone (ClosFvs.compile xs) := by
    simpa [ClosFvs.compile] using (ClosFvs.removeList_varsNone xs 0).mpr initial.1
  have firstRun := knownVarsAll c (ClosFvs.compile xs) [] .ln ys g
    ⟨known, initialSafe, by simp, by simp [globalsApproxVarsNone, sptLookup]⟩
  have globalsSafe : ∀ n, globalsApproxVarsNone (co n).1.1 := by
    intro n
    induction n with
    | zero => simpa [first] using firstRun.2.2
    | succ n ih =>
      have input : everyFnVarsNone (ClosFvs.compile (co n).2.1) := by
        simpa [ClosFvs.compile] using
          (ClosFvs.removeList_varsNone (co n).2.1 0).mpr (programs n).1.1
      cases hk : knownListTotal (resetInlineFactor c) (ClosFvs.compile (co n).2.1) []
          (co n).1.1 with
      | mk eas next =>
        have safe := knownVarsAll (resetInlineFactor c) (ClosFvs.compile (co n).2.1)
          [] (co n).1.1 eas next ⟨hk, input, by simp, ih⟩
        have eq := recurrence n
        simp [pureCo, ClosFvs.compileInc, compileInc, hk] at eq
        simpa [eq] using safe.2.2
  refine ⟨firstRun.1, ?_⟩
  intro n
  have input : everyFnVarsNone (ClosFvs.compile (co n).2.1) := by
    simpa [ClosFvs.compile] using
      (ClosFvs.removeList_varsNone (co n).2.1 0).mpr (programs n).1.1
  have safe := knownEveryFnVarsNone (resetInlineFactor c) (ClosFvs.compile (co n).2.1)
    [] (co n).1.1 ⟨input, by simp, globalsSafe n⟩
  simpa [stateCo, pureCo, ClosFvs.compileInc, compileInc] using safe.1

end Flapjack.Compiler.Backend.ClosKnown.TraversalSyntax
