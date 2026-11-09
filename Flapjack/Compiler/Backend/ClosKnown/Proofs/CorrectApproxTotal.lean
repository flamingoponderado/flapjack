module

public import Flapjack.Compiler.Backend.ClosKnown.Proofs.CorrectApproxApp
public import Flapjack.Compiler.Backend.ClosKnown.Proofs.CorrectApproxLetrec
public import Flapjack.Compiler.Backend.ClosKnown.Proofs.CorrectApproxIf
public import Flapjack.Compiler.Backend.ClosKnown.Proofs.CorrectApproxLet
public import Flapjack.Compiler.Backend.ClosKnown.Proofs.CorrectApproxOpTotal

-- Proofs below unfold private helpers of these modules.
import all Flapjack.Compiler.Backend.Semantics.ClosSem.EvaluateExact
import all Flapjack.Compiler.Backend.Semantics.ClosSem.EvaluateFuel
@[expose] public section


/-! Complete known-function approximation preservation. -/
namespace Flapjack.Compiler.Backend.ClosKnown.CorrectApprox
open ClosSem ClosProps ClosProps.StateGlobalSafety UniqueGlobalsPort OracleGlobals
open Flapjack.SemanticPrimitivesHOL

/-- The quantified source induction predicate for all optimizer inputs.
This is Flapjack induction infrastructure. -/
theorem knownApproxAll {C F : Type} (c : Config) (xs : List ClosLang.Exp)
    (env : List ValApprox) (globals : Spt ValApprox) : KnownApproxInvariant C F c xs env globals := by
  induction c, xs, env, globals using knownListTotal.induct
    (motive1 := fun c e env g => KnownApproxInvariant C F c [e] env g)
    (motive2 := fun c fns clos env g => ∀ n e, (n, e) ∈ fns →
      KnownApproxInvariant C F c [e] (List.replicate n .other ++ clos ++ env) g)
  case case1 c env g t v =>
    intro eas next vEnv extra s0 res s h
    exact knownCorrectApproxVar c t v env g eas next vEnv extra s0 res s h
  case case2 =>
    rename_i c env g t x y z xe xa g1 hx ye ya g2 hy ze za g3 hz ix iy iz
    intro eas next vEnv extra s0 res s h
    apply If.knownCorrectApproxIf c t x y z env g ?_ ?_ ix eas next vEnv extra s0 res s h
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
    intro eas next vEnv extra s0 res s h
    apply Let.knownCorrectApproxLet c t xs body env g ?_ ib eas next vEnv extra s0 res s h
    intro ea1 next1 eq1
    rw [h1] at eq1
    cases eq1
    exact indBody
  case case6 =>
    rename_i c env g t body handler e1 a1 g1 h1 e2 a2 g2 h2 ib ih
    intro eas next vEnv extra s0 res s h
    apply Handle.knownCorrectApproxHandle c t body handler env g ?_ ib eas next vEnv extra s0 res s h
    intro ea1 next1 eq1
    simp [knownListTotal_single, h1] at eq1
    rcases eq1 with ⟨rfl, rfl⟩
    exact ih
  case case4 c env g t x xe xa g1 hx ih =>
    intro eas next vEnv extra s0 res s h
    exact knownCorrectApproxRaise c t x env g ih eas next vEnv extra s0 res s h
  case case5 c env g t x xe xa g1 hx ih =>
    intro eas next vEnv extra s0 res s h
    exact knownCorrectApproxTick c t x env g ih eas next vEnv extra s0 res s h
  case case7 c env g t ticks dest args ea g1 hargs ih =>
    intro eas next vEnv extra s0 res s h
    exact Call.knownCorrectApproxCall c t ticks dest args env g ih eas next vEnv extra s0 res s h
  case case8 c env g t op args ea g1 hargs a g2 hop ih =>
    intro eas next vEnv extra s0 res s h
    exact OpTotal.knownCorrectApproxOp c t op args env g ih eas next vEnv extra s0 res s h
  case case9 =>
    rename_i c env g t loc x xs ea g1 ha e a g2 hx hd iargs ifun
    have len := knownListTotal_length c xs env g
    rw [ha] at len
    simp only at len
    intro eas next vEnv extra s0 res s h
    apply App.knownCorrectApproxApp c t loc x xs env g ?_ ?_ iargs eas next vEnv extra s0 res s h
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
    intro eas next vEnv extra s0 res s h
    apply App.knownCorrectApproxApp c t loc x xs env g ?_ ?_ iargs eas next vEnv extra s0 res s h
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
    intro eas next vEnv extra s0 res s h
    apply App.knownCorrectApproxApp c t loc x xs env g ?_ ?_ iargs eas next vEnv extra s0 res s h
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
    intro eas next vEnv extra s0 res s h
    exact Fn.knownCorrectApproxFn c name loc vs arity body env g ih eas next vEnv extra s0 res s h
  case case13 =>
    rename_i c env g names loc vs fns body clos e a g1 hb ifuns ibody
    intro eas next vEnv extra s0 res s h
    apply Letrec.knownCorrectApproxLetrec c names loc vs fns body env g ?_ ?_ eas next vEnv extra s0 res s h
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
    intro eas next vEnv extra s0 res s h
    exact knownCorrectApproxNil c env g eas next vEnv extra s0 res s h
  case case17 =>
    rename_i c env g x xs xe xa g1 hx tailEa g2 ht ix it
    cases xs with
    | nil => exact ix
    | cons y ys =>
      intro eas next vEnv extra s0 res s h
      apply Cons.knownCorrectApproxCons c x y ys env g ?_ ix eas next vEnv extra s0 res s h
      intro ea1 next1 eq1
      simp [knownListTotal_single, hx] at eq1
      rcases eq1 with ⟨rfl, rfl⟩
      exact it


namespace Total

/-- The closure state uses canonical finite-map fields. -/
theorem holFmapAsFiniteSupportWitness {C F : Type} :
    (∀ s : ClosSem.StateBroad C F, (ClosSem.State.ofBroad s).toBroad = s) ∧
      (∀ s : ClosSem.State C F, ClosSem.State.ofBroad s.toBroad = s) :=
  ClosSem.holFmapAsFiniteSupportWitness

/-- Known-function optimization preserves global and returned-value
approximations under the original evaluator safety and uniqueness conditions. -/
@[hol "cakeml/compiler/backend/proofs/clos_knownProofScript.sml" "known_correct_approx"
  (fmap_as_finite_support := [refs, code])]
theorem knownCorrectApprox {C F : Type} (c : Config) (xs : List ClosLang.Exp)
    (aenv : List ValApprox) (g0 : Spt ValApprox)
    (eas : List (ClosLang.Exp × ValApprox)) (g : Spt ValApprox) (env extra : List ClosSem.Value)
    (s0 : State (Spt ValApprox × C) F) (res : Result (List ClosSem.Value) ClosSem.Value)
    (s : State (Spt ValApprox × C) F)
    (h : knownListTotal c xs aenv g0 = (eas, g) ∧
      evaluate xs (env ++ extra) s0 = (res, s) ∧
      uniqueSetGlobals xs s0.compileOracle ∧ List.Forall₂ ValApproxVal aenv env ∧
      stateGlobalsApprox s0 g0 ∧ mglobalsDisjoint s0.globals xs ∧
      oracleGapproxDisjoint g0 s0.compileOracle ∧ ssgcFree s0 ∧
      (∀ v ∈ env ++ extra, vsgcFree v) ∧ (∀ e ∈ xs, esgcFree e) ∧
      (∀ a ∈ aenv, valApproxSgcFree a) ∧ globalsApproxSgcFree g0) :
    stateGlobalsApprox s g ∧ ∀ vs, res = .val vs → List.Forall₂ ValApproxVal (eas.map Prod.snd) vs :=
  knownApproxAll c xs aenv g0 eas g env extra s0 res s h

end Total

end Flapjack.Compiler.Backend.ClosKnown.CorrectApprox
