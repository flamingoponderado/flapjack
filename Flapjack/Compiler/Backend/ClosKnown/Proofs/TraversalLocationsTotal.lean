module

public import Flapjack.Compiler.Backend.ClosKnown.Proofs.TraversalLocations

@[expose] public section


/-! Assembling optimizer annotation preservation over the complete traversal. -/
namespace Flapjack.Compiler.Backend.ClosKnown.TraversalLocations

/-- The safety invariant for every traversal input, used to assemble the source theorem. -/
theorem knownLocationsAll (c : Config) (xs : List ClosLang.Exp) (env : List ValApprox)
    (globals : Spt ValApprox) : KnownLocationsInvariant c xs env globals := by
  induction c, xs, env, globals using knownListTotal.induct
    (motive1 := fun c e env g => KnownLocationsInvariant c [e] env g)
    (motive2 := fun c fns clos env g => ∀ n e, (n, e) ∈ fns →
      KnownLocationsInvariant c [e] (List.replicate n .other ++ clos ++ env) g)
  case case1 c env g t v =>
    intro eas next h
    exact knownLocationsVar c t v env g eas next h
  case case2 =>
    rename_i c env g t x y z xe xa g1 hx ye ya g2 hy ze za g3 hz ix iy iz
    intro eas next ⟨run, annotations, safe, globalSafe⟩
    have parts : ClosProps.everyFnLocationSome [x] ∧ ClosProps.everyFnLocationSome [y] ∧ ClosProps.everyFnLocationSome [z] := by
      simpa [ClosProps.everyFnLocationSome, ClosProps.fnLocationSomeExp] using annotations
    have h1 : knownListTotal c [x] env g = ([(xe, xa)], g1) := by
      simp [knownListTotal_single, hx]
    have h2 : knownListTotal c [y] env g1 = ([(ye, ya)], g2) := by
      simp [knownListTotal_single, hy]
    have h3 : knownListTotal c [z] env g2 = ([(ze, za)], g3) := by
      simp [knownListTotal_single, hz]
    have r1 := ix _ _ ⟨h1, parts.1, safe, globalSafe⟩
    have r2 := iy _ _ ⟨h2, parts.2.1, safe, r1.2.2⟩
    have r3 := iz _ _ ⟨h3, parts.2.2, safe, r2.2.2⟩
    rw [knownListTotal_if, h1] at run
    dsimp only at run
    rw [h2] at run
    dsimp only at run
    rw [h3] at run
    simp [knownSourceHead] at run
    rcases run with ⟨rfl, rfl⟩
    have merged : valApproxLocations (mergeHOL ya za) := valApproxLocationsMerge ya za
      ⟨by simpa using r2.2.1, by simpa using r3.2.1⟩
    simp [ClosProps.everyFnLocationSome, ClosProps.fnLocationSomeExp] at r1 r2 r3 ⊢
    exact ⟨⟨r1.1, r2.1, r3.1⟩, merged, r3.2.2⟩
  case case3 =>
    rename_i c env g t xs body ea g1 h1 e a g2 h2 ib indBody
    intro eas next h
    apply knownLocationsLet c t xs body env g ?_ ib eas next h
    intro ea1 next1 eq1
    rw [h1] at eq1
    cases eq1
    exact indBody
  case case6 =>
    rename_i c env g t body handler e1 a1 g1 h1 e2 a2 g2 h2 ib ih
    intro eas next h
    apply knownLocationsHandle c t body handler env g ?_ ib eas next h
    intro ea1 next1 eq1
    simp [knownListTotal_single, h1] at eq1
    rcases eq1 with ⟨rfl, rfl⟩
    exact ih
  case case4 c env g t x xe xa g1 hx ih =>
    intro eas next h
    exact knownLocationsRaise c t x env g ih eas next h
  case case5 c env g t x xe xa g1 hx ih =>
    intro eas next h
    exact knownLocationsTick c t x env g ih eas next h
  case case7 c env g t ticks dest args ea g1 hargs ih =>
    intro eas next h
    exact knownLocationsCall c t ticks dest args env g ih eas next h
  case case8 c env g t op args ea g1 hargs a g2 hop ih =>
    intro eas next h
    exact knownLocationsOp c t op args env g ih eas next h
  case case9 =>
    rename_i c env g t loc x xs ea g1 ha e a g2 hx hd iargs ifun
    have len := knownListTotal_length c xs env g
    rw [ha] at len
    simp only at len
    intro eas next h
    apply knownLocationsApp c t loc x xs env g ?_ ?_ iargs eas next h
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
    apply knownLocationsApp c t loc x xs env g ?_ ?_ iargs eas next h
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
    apply knownLocationsApp c t loc x xs env g ?_ ?_ iargs eas next h
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
    exact knownLocationsFn c name loc vs arity body env g ih eas next h
  case case13 =>
    rename_i c env g names loc vs fns body clos e a g1 hb ifuns ibody
    intro eas next h
    apply knownLocationsLetrec c names loc vs fns body env g ?_ ?_ eas next h
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
    exact knownLocationsNil c env g eas next h
  case case17 =>
    rename_i c env g x xs xe xa g1 hx tailEa g2 ht ix it
    cases xs with
    | nil => exact ix
    | cons y ys =>
      intro eas next h
      apply knownLocationsCons c x y ys env g ?_ ix eas next h
      intro ea1 next1 eq1
      simp [knownListTotal_single, hx] at eq1
      rcases eq1 with ⟨rfl, rfl⟩
      exact it



/-- The optimizer preserves the presence of function locations. -/
@[hol "cakeml/compiler/backend/proofs/clos_knownProofScript.sml" "known_every_Fn_SOME"]
theorem knownEveryFnLocations (c : Config) (xs : List ClosLang.Exp)
    (env : List ValApprox) (globals : Spt ValApprox)
    (h : ClosProps.everyFnLocationSome xs ∧ (∀ a ∈ env, valApproxLocations a) ∧
      globalsApproxLocations globals) :
    ClosProps.everyFnLocationSome ((knownListTotal c xs env globals).1.map Prod.fst) ∧
    (∀ a ∈ (knownListTotal c xs env globals).1.map Prod.snd, valApproxLocations a) ∧
    globalsApproxLocations (knownListTotal c xs env globals).2 := by
  cases run : knownListTotal c xs env globals with
  | mk eas next =>
    have result := knownLocationsAll c xs env globals eas next ⟨run, h.1, h.2.1, h.2.2⟩
    simpa [run] using result



end Flapjack.Compiler.Backend.ClosKnown.TraversalLocations
