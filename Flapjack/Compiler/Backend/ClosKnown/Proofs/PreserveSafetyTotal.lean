import Flapjack.Compiler.Backend.ClosKnown.Proofs.PreserveSafety

/-! Assembling optimizer safety over the complete traversal. -/
namespace Flapjack.Compiler.Backend.ClosKnown.PreserveSafety

/-- The safety invariant for every traversal input, used to assemble the source theorem. -/
theorem knownSafetyAll (c : Config) (xs : List ClosLang.Exp) (env : List ValApprox)
    (globals : Spt ValApprox) : KnownSafetyInvariant c xs env globals := by
  induction c, xs, env, globals using knownListTotal.induct
    (motive1 := fun c e env g => KnownSafetyInvariant c [e] env g)
    (motive2 := fun c fns clos env g => ∀ n e, (n, e) ∈ fns →
      KnownSafetyInvariant c [e] (List.replicate n .other ++ clos ++ env) g)
  case case1 c env g t v =>
    intro eas next h
    exact knownPreservesSafetyVar c t v env g eas next h
  case case2 =>
    rename_i c env g t x y z xe xa g1 hx ye ya g2 hy ze za g3 hz ix iy iz
    intro eas next h
    apply knownPreservesSafetyIf c t x y z env g ?_ ?_ ix eas next h
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
    apply knownPreservesSafetyLet c t xs body env g ?_ ib eas next h
    intro ea1 next1 eq1
    rw [h1] at eq1
    cases eq1
    exact indBody
  case case6 =>
    rename_i c env g t body handler e1 a1 g1 h1 e2 a2 g2 h2 ib ih
    intro eas next h
    apply knownPreservesSafetyHandle c t body handler env g ?_ ib eas next h
    intro ea1 next1 eq1
    simp [knownListTotal_single, h1] at eq1
    rcases eq1 with ⟨rfl, rfl⟩
    exact ih
  case case4 c env g t x xe xa g1 hx ih =>
    intro eas next h
    exact knownPreservesSafetyRaise c t x env g ih eas next h
  case case5 c env g t x xe xa g1 hx ih =>
    intro eas next h
    exact knownPreservesSafetyTick c t x env g ih eas next h
  case case7 c env g t ticks dest args ea g1 hargs ih =>
    intro eas next h
    exact knownPreservesSafetyCall c t ticks dest args env g ih eas next h
  case case8 c env g t op args ea g1 hargs a g2 hop ih =>
    intro eas next h
    exact knownPreservesSafetyOp c t op args env g ih eas next h
  case case9 =>
    rename_i c env g t loc x xs ea g1 ha e a g2 hx hd iargs ifun
    have len := knownListTotal_length c xs env g
    rw [ha] at len
    simp only at len
    intro eas next h
    apply knownPreservesSafetyApp c t loc x xs env g ?_ ?_ iargs eas next h
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
    apply knownPreservesSafetyApp c t loc x xs env g ?_ ?_ iargs eas next h
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
    apply knownPreservesSafetyApp c t loc x xs env g ?_ ?_ iargs eas next h
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
    exact knownPreservesSafetyFn c name loc vs arity body env g ih eas next h
  case case13 =>
    rename_i c env g names loc vs fns body clos e a g1 hb ifuns ibody
    intro eas next h
    apply knownPreservesSafetyLetrec c names loc vs fns body env g ?_ ?_ eas next h
    · intro clos' newFns ⟨same, _⟩
      subst clos'
      cases loc <;> simpa [clos, noInline] using ibody
    · intro clos' arity e newEnv ⟨same, mem, sameEnv⟩
      subst clos'
      subst newEnv
      cases loc <;> simpa [clos, noInline] using ifuns arity e mem
  case case14 => contradiction
  case case15 =>
    rename_i c clos env g arity body fns e a g1 hb ihBody ihRest n x member
    rcases List.mem_cons.mp member with same | tail
    · cases Prod.mk.inj same with
      | intro hn hx => subst n; subst x; exact ihBody
    · exact ihRest n x tail
  case case16 c env g =>
    intro eas next h
    exact knownPreservesSafetyNil c env g eas next h
  case case17 =>
    rename_i c env g x xs xe xa g1 hx tailEa g2 ht ix it
    cases xs with
    | nil => exact ix
    | cons y ys =>
      intro eas next h
      apply knownPreservesSafetyCons c x y ys env g ?_ ix eas next h
      intro ea1 next1 eq1
      simp [knownListTotal_single, hx] at eq1
      rcases eq1 with ⟨rfl, rfl⟩
      exact it


/-- Known-function optimization does not increase global writes and preserves
expression, approximation, and global-approximation safety. -/
@[hol "cakeml/compiler/backend/proofs/clos_knownProofScript.sml" "known_preserves_esgc_free_0"]
theorem knownPreservesSafety (c : Config) (es : List ClosLang.Exp) (aenv : List ValApprox)
    (g0 : Spt ValApprox) (eas : List (ClosLang.Exp × ValApprox)) (g : Spt ValApprox)
    (h : knownListTotal c es aenv g0 = (eas, g) ∧ (∀ e ∈ es, ClosProps.esgcFree e) ∧
      (∀ a ∈ aenv, valApproxSgcFree a) ∧ globalsApproxSgcFree g0) :
    (∀ i, ClosProps.elistGlobals (eas.map Prod.fst) i ≤ ClosProps.elistGlobals es i) ∧
      (∀ e ∈ eas.map Prod.fst, ClosProps.esgcFree e) ∧
      (∀ a ∈ eas.map Prod.snd, valApproxSgcFree a) ∧ globalsApproxSgcFree g :=
  knownSafetyAll c es aenv g0 eas g h

/-- Known-function optimization preserves expression and approximation safety. -/
@[hol "cakeml/compiler/backend/proofs/clos_knownProofScript.sml" "known_preserves_esgc_free"]
theorem knownPreservesEsgcFree (c : Config) (es : List ClosLang.Exp) (aenv : List ValApprox)
    (g0 : Spt ValApprox) (eas : List (ClosLang.Exp × ValApprox)) (g : Spt ValApprox)
    (h : knownListTotal c es aenv g0 = (eas, g) ∧ (∀ e ∈ es, ClosProps.esgcFree e) ∧
      (∀ a ∈ aenv, valApproxSgcFree a) ∧ globalsApproxSgcFree g0) :
    (∀ e ∈ eas.map Prod.fst, ClosProps.esgcFree e) ∧
      (∀ a ∈ eas.map Prod.snd, valApproxSgcFree a) ∧ globalsApproxSgcFree g :=
  (knownPreservesSafety c es aenv g0 eas g h).2

/-- Known-function optimization does not increase the global-write bag. -/
@[hol "cakeml/compiler/backend/proofs/clos_knownProofScript.sml" "known_elglobals_dont_grow"]
theorem knownElglobalsDontGrow (c : Config) (es : List ClosLang.Exp) (aenv : List ValApprox)
    (g0 : Spt ValApprox) (eas : List (ClosLang.Exp × ValApprox)) (g : Spt ValApprox)
    (h : knownListTotal c es aenv g0 = (eas, g) ∧ (∀ e ∈ es, ClosProps.esgcFree e) ∧
      (∀ a ∈ aenv, valApproxSgcFree a) ∧ globalsApproxSgcFree g0) :
    ∀ i, ClosProps.elistGlobals (eas.map Prod.fst) i ≤ ClosProps.elistGlobals es i :=
  (knownPreservesSafety c es aenv g0 eas g h).1

end Flapjack.Compiler.Backend.ClosKnown.PreserveSafety
