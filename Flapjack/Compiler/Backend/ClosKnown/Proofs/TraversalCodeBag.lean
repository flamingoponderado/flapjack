import Flapjack.Compiler.Backend.ClosKnown.Proofs.SourceEquations
import Flapjack.Compiler.Backend.ClosKnown.Proofs.InlineCodeLocations
import Flapjack.Compiler.Backend.ClosOp.Proofs.SmartFixed

/-! Cases of the source optimizer's closure-label multiset bound. -/
namespace Flapjack.Compiler.Backend.ClosKnown.TraversalCodeBag
open ClosLang ClosProps

/-- Pointwise form of HOL's multiset bound, with the traversal result equation
made explicit so recursive cases can use the original induction hypotheses. -/
def KnownCodeBagInvariant (c : Config) (xs : List Exp) (env : List ValApprox) (g : Spt ValApprox) : Prop :=
  ∀ eas next, knownListTotal c xs env g = (eas, next) →
    ∀ label, (codeLocations (eas.map Prod.fst)).count label ≤ (codeLocations xs).count label

/-- Empty-list case of the optimizer code-location multiset theorem. -/
@[hol "cakeml/compiler/backend/proofs/clos_knownProofScript.sml" "known_code_locs_bag"]
theorem knownCodeBagNil (c : Config) (env : List ValApprox) (g : Spt ValApprox) :
    KnownCodeBagInvariant c [] env g := by
  intro eas next run label
  simp [knownListTotal] at run
  rcases run with ⟨rfl, rfl⟩
  simp [codeLocations]

/-- Variable case of the optimizer code-location multiset theorem. -/
@[hol "cakeml/compiler/backend/proofs/clos_knownProofScript.sml" "known_code_locs_bag"]
theorem knownCodeBagVar (c : Config) (trace : BackendCommon.Tra) (index : Nat)
    (env : List ValApprox) (g : Spt ValApprox) :
    KnownCodeBagInvariant c [.var trace index] env g := by
  intro eas next run label
  simp only [knownListTotal_var, Prod.mk.injEq] at run
  rcases run with ⟨rfl, rfl⟩
  simp [codeLocations, codeLocationsExp]

/-- Sequential-list case of the optimizer code-location multiset theorem. -/
@[hol "cakeml/compiler/backend/proofs/clos_knownProofScript.sml" "known_code_locs_bag"]
theorem knownCodeBagCons (c : Config) (x y : Exp) (xs : List Exp) (env : List ValApprox) (g : Spt ValApprox)
    (tailIH : ∀ ea1 g1, (ea1, g1) = knownListTotal c [x] env g → KnownCodeBagInvariant c (y :: xs) env g1)
    (headIH : KnownCodeBagInvariant c [x] env g) : KnownCodeBagInvariant c (x :: y :: xs) env g := by
  intro eas next run label
  cases headRun : knownListTotal c [x] env g with
  | mk headEas g1 =>
    cases tailRun : knownListTotal c (y :: xs) env g1 with
    | mk tailEas g2 =>
      rw [knownListTotal_cons_cons, headRun] at run
      dsimp only at run
      rw [tailRun] at run
      simp only [Prod.mk.injEq] at run
      rcases run with ⟨rfl, rfl⟩
      have first := headIH headEas g1 headRun label
      have rest := tailIH headEas g1 headRun.symm tailEas g2 tailRun label
      simp [List.map_append, codeLocations_append, List.count_append, codeLocations] at first rest ⊢
      omega

/-- Raise case of the optimizer code-location multiset theorem. -/
@[hol "cakeml/compiler/backend/proofs/clos_knownProofScript.sml" "known_code_locs_bag"]
theorem knownCodeBagRaise (c : Config) (trace : BackendCommon.Tra) (body : Exp)
    (env : List ValApprox) (g : Spt ValApprox) (ih : KnownCodeBagInvariant c [body] env g) :
    KnownCodeBagInvariant c [.raise trace body] env g := by
  intro eas next run label
  cases hk : knownListTotal c [body] env g with
  | mk bodyEas bodyG =>
    obtain ⟨bodyExpr, bodyApprox, bodyEq⟩ := knownListTotal_single_result c body env g bodyG bodyEas hk
    subst bodyEas
    have result := ih [(bodyExpr, bodyApprox)] bodyG hk label
    rw [knownListTotal_raise, hk] at run
    simp [knownSourceHead] at run
    rcases run with ⟨rfl, rfl⟩
    simpa [codeLocations, codeLocationsExp] using result

/-- Tick case of the optimizer code-location multiset theorem. -/
@[hol "cakeml/compiler/backend/proofs/clos_knownProofScript.sml" "known_code_locs_bag"]
theorem knownCodeBagTick (c : Config) (trace : BackendCommon.Tra) (body : Exp)
    (env : List ValApprox) (g : Spt ValApprox) (ih : KnownCodeBagInvariant c [body] env g) :
    KnownCodeBagInvariant c [.tick trace body] env g := by
  intro eas next run label
  cases hk : knownListTotal c [body] env g with
  | mk bodyEas bodyG =>
    obtain ⟨bodyExpr, bodyApprox, bodyEq⟩ := knownListTotal_single_result c body env g bodyG bodyEas hk
    subst bodyEas
    have result := ih [(bodyExpr, bodyApprox)] bodyG hk label
    rw [knownListTotal_tickSource, hk] at run
    simp [knownSourceHead] at run
    rcases run with ⟨rfl, rfl⟩
    simpa [codeLocations, codeLocationsExp] using result

/-- Direct-call case of the optimizer code-location multiset theorem. -/
@[hol "cakeml/compiler/backend/proofs/clos_knownProofScript.sml" "known_code_locs_bag"]
theorem knownCodeBagCall (c : Config) (trace : BackendCommon.Tra) (ticks dest : Nat)
    (xs : List Exp) (env : List ValApprox) (g : Spt ValApprox) (ih : KnownCodeBagInvariant c xs env g) :
    KnownCodeBagInvariant c [.call trace ticks dest xs] env g := by
  intro eas next run label
  cases hk : knownListTotal c xs env g with
  | mk ea g1 =>
    have result := ih ea g1 hk label
    rw [knownListTotal_call, hk] at run
    simp at run
    rcases run with ⟨rfl, rfl⟩
    simpa [codeLocations, codeLocationsExp] using result

/-- Primitive-operation case of the optimizer code-location multiset theorem. -/
@[hol "cakeml/compiler/backend/proofs/clos_knownProofScript.sml" "known_code_locs_bag"]
theorem knownCodeBagOp (c : Config) (trace : BackendCommon.Tra) (op : Op)
    (xs : List Exp) (env : List ValApprox) (g : Spt ValApprox) (ih : KnownCodeBagInvariant c xs env g) :
    KnownCodeBagInvariant c [.op trace op xs] env g := by
  intro eas next run label
  cases hk : knownListTotal c xs env g with
  | mk ea g1 =>
    have result := ih ea g1 hk label
    cases hop : knownOpHOL op (ea.map Prod.snd).reverse g1 with
    | mk approx g2 =>
      rw [knownListTotal_op, hk] at run
      dsimp only at run
      rw [hop] at run
      dsimp only at run
      let out := match op, approx with
        | .globOp (.global _), .int i => Exp.op trace (.intOp (.const i)) (ea.map Prod.fst)
        | .globOp (.global _), .tuple tag [] => Exp.op trace (.blockOp (.cons tag)) (ea.map Prod.fst)
        | _, _ => ClosOp.smartOp trace op (ea.map Prod.fst)
      have outEq : codeLocations [out] = codeLocations (ea.map Prod.fst) := by
        dsimp only [out]
        split
        · simp [codeLocations, codeLocationsExp]
        · simp [codeLocations, codeLocationsExp]
        · simpa [codeLocations, codeLocationsExp] using ClosOp.smartCodeLocations trace op (ea.map Prod.fst)
      change ([(out, approx)], g2) = (eas, next) at run
      cases run
      simp [codeLocations] at outEq
      simpa [codeLocations, codeLocationsExp, outEq] using result

/-- Conditional case of the optimizer code-location multiset theorem. -/
@[hol "cakeml/compiler/backend/proofs/clos_knownProofScript.sml" "known_code_locs_bag"]
theorem knownCodeBagIf (c : Config) (trace : BackendCommon.Tra) (x y z : Exp)
    (env : List ValApprox) (g : Spt ValApprox)
    (thirdIH : ∀ ea1 g1 ea2 g2, (ea1, g1) = knownListTotal c [x] env g ∧
      (ea2, g2) = knownListTotal c [y] env g1 → KnownCodeBagInvariant c [z] env g2)
    (secondIH : ∀ ea1 g1, (ea1, g1) = knownListTotal c [x] env g → KnownCodeBagInvariant c [y] env g1)
    (firstIH : KnownCodeBagInvariant c [x] env g) :
    KnownCodeBagInvariant c [.ifThenElse trace x y z] env g := by
  intro eas next run label
  cases h1 : knownListTotal c [x] env g with
  | mk ea1 g1 =>
    obtain ⟨x', a1, eq1⟩ := knownListTotal_single_result c x env g g1 ea1 h1
    subst ea1
    have r1 := firstIH [(x', a1)] g1 h1 label
    cases h2 : knownListTotal c [y] env g1 with
    | mk ea2 g2 =>
      obtain ⟨y', a2, eq2⟩ := knownListTotal_single_result c y env g1 g2 ea2 h2
      subst ea2
      have r2 := secondIH [(x', a1)] g1 h1.symm [(y', a2)] g2 h2 label
      cases h3 : knownListTotal c [z] env g2 with
      | mk ea3 g3 =>
        obtain ⟨z', a3, eq3⟩ := knownListTotal_single_result c z env g2 g3 ea3 h3
        subst ea3
        have r3 := thirdIH [(x', a1)] g1 [(y', a2)] g2 ⟨h1.symm, h2.symm⟩ [(z', a3)] g3 h3 label
        rw [knownListTotal_if, h1] at run
        dsimp only at run
        rw [h2] at run
        dsimp only at run
        rw [h3] at run
        simp [knownSourceHead] at run
        rcases run with ⟨rfl, rfl⟩
        simp [codeLocations, codeLocationsExp, List.count_append] at r1 r2 r3 ⊢
        omega

/-- Let-binding case of the optimizer code-location multiset theorem. -/
@[hol "cakeml/compiler/backend/proofs/clos_knownProofScript.sml" "known_code_locs_bag"]
theorem knownCodeBagLet (c : Config) (trace : BackendCommon.Tra) (xs : List Exp)
    (body : Exp) (env : List ValApprox) (g : Spt ValApprox)
    (bodyIH : ∀ ea g1, (ea, g1) = knownListTotal c xs env g →
      KnownCodeBagInvariant c [body] (ea.map Prod.snd ++ env) g1)
    (bindingsIH : KnownCodeBagInvariant c xs env g) :
    KnownCodeBagInvariant c [.let trace xs body] env g := by
  intro eas next run label
  cases h1 : knownListTotal c xs env g with
  | mk ea1 g1 =>
    have r1 := bindingsIH ea1 g1 h1 label
    cases h2 : knownListTotal c [body] (ea1.map Prod.snd ++ env) g1 with
    | mk ea2 g2 =>
      obtain ⟨bodyExpr, bodyApprox, eq2⟩ :=
        knownListTotal_single_result c body (ea1.map Prod.snd ++ env) g1 g2 ea2 h2
      subst ea2
      have r2 := bodyIH ea1 g1 h1.symm [(bodyExpr, bodyApprox)] g2 h2 label
      rw [knownListTotal_let, h1] at run
      dsimp only at run
      rw [h2] at run
      simp [knownSourceHead] at run
      rcases run with ⟨rfl, rfl⟩
      simp [codeLocations, codeLocationsExp, List.count_append] at r2 ⊢
      omega

/-- Handler case of the optimizer code-location multiset theorem. -/
@[hol "cakeml/compiler/backend/proofs/clos_knownProofScript.sml" "known_code_locs_bag"]
theorem knownCodeBagHandle (c : Config) (trace : BackendCommon.Tra) (body handler : Exp)
    (env : List ValApprox) (g : Spt ValApprox)
    (handlerIH : ∀ ea g1, (ea, g1) = knownListTotal c [body] env g →
      KnownCodeBagInvariant c [handler] (.other :: env) g1)
    (bodyIH : KnownCodeBagInvariant c [body] env g) :
    KnownCodeBagInvariant c [.handle trace body handler] env g := by
  intro eas next run label
  cases h1 : knownListTotal c [body] env g with
  | mk ea1 g1 =>
    obtain ⟨e1, a1, eq1⟩ := knownListTotal_single_result c body env g g1 ea1 h1
    subst ea1
    have r1 := bodyIH [(e1, a1)] g1 h1 label
    cases h2 : knownListTotal c [handler] (.other :: env) g1 with
    | mk ea2 g2 =>
      obtain ⟨e2, a2, eq2⟩ := knownListTotal_single_result c handler (.other :: env) g1 g2 ea2 h2
      subst ea2
      have r2 := handlerIH [(e1, a1)] g1 h1.symm [(e2, a2)] g2 h2 label
      rw [knownListTotal_handle, h1] at run
      dsimp only at run
      rw [h2] at run
      simp [knownSourceHead] at run
      rcases run with ⟨rfl, rfl⟩
      simp [codeLocations, codeLocationsExp, List.count_append] at r1 r2 ⊢
      omega

/-- Closure-construction case of the optimizer code-location multiset theorem. -/
@[hol "cakeml/compiler/backend/proofs/clos_knownProofScript.sml" "known_code_locs_bag"]
theorem knownCodeBagFn (c : Config) (name : Basis.Pure.MlString.MlString)
    (loc : Option Nat) (vs : Option (List Nat)) (arity : Nat) (body : Exp)
    (env : List ValApprox) (g : Spt ValApprox)
    (ih : KnownCodeBagInvariant c [body] (List.replicate arity .other ++ env) g) :
    KnownCodeBagInvariant c [.fn name loc vs arity body] env g := by
  intro eas next run label
  cases hk : knownListTotal c [body] (List.replicate arity .other ++ env) g with
  | mk ea g1 =>
    obtain ⟨bodyExpr, bodyApprox, bodyEq⟩ :=
      knownListTotal_single_result c body (List.replicate arity .other ++ env) g g1 ea hk
    subst ea
    have result := ih [(bodyExpr, bodyApprox)] g1 hk label
    rw [knownListTotal_fn, hk] at run
    simp [knownSourceHead] at run
    rcases run with ⟨rfl, rfl⟩
    simp [codeLocations, codeLocationsExp, List.count_append] at result ⊢
    omega

/-- Application case of the optimizer code-location multiset theorem, including inlining. -/
@[hol "cakeml/compiler/backend/proofs/clos_knownProofScript.sml" "known_code_locs_bag"]
theorem knownCodeBagApp (c : Config) (trace : BackendCommon.Tra) (loc : Option Nat)
    (x : Exp) (xs : List Exp) (env : List ValApprox) (g : Spt ValApprox)
    (inlineIH : ∀ ea2 g1 ea1 g2 e1 a1 body,
      (ea2, g1) = knownListTotal c xs env g ∧ (ea1, g2) = knownListTotal c [x] env g1 ∧
      (e1, a1) = knownSourceHead ea1 ∧ decideInlineHOL c a1 loc xs.length = .letInline body →
      KnownCodeBagInvariant (decInlineFactor c) [body] (ea2.map Prod.snd) g2)
    (functionIH : ∀ ea2 g1, (ea2, g1) = knownListTotal c xs env g → KnownCodeBagInvariant c [x] env g1)
    (argsIH : KnownCodeBagInvariant c xs env g) :
    KnownCodeBagInvariant c [.app trace loc x xs] env g := by
  intro eas next run label
  cases ha : knownListTotal c xs env g with
  | mk ea2 g1 =>
    have rArgs := argsIH ea2 g1 ha label
    cases hf : knownListTotal c [x] env g1 with
    | mk ea1 g2 =>
      obtain ⟨e1, a1, eq1⟩ := knownListTotal_single_result c x env g1 g2 ea1 hf
      subst ea1
      have rFun := functionIH ea2 g1 ha.symm [(e1, a1)] g2 hf label
      rw [knownListTotal_app, ha] at run
      dsimp only at run
      rw [hf] at run
      simp only [knownSourceHead, List.headD_cons] at run
      cases decision : decideInlineHOL c a1 loc xs.length with
      | nothing =>
        simp only [decision, Prod.mk.injEq] at run
        rcases run with ⟨rfl, rfl⟩
        simp [codeLocations, codeLocationsExp, List.count_append] at rFun ⊢
        omega
      | annotate target =>
        simp only [decision, Prod.mk.injEq] at run
        rcases run with ⟨rfl, rfl⟩
        simp [codeLocations, codeLocationsExp, List.count_append] at rFun ⊢
        omega
      | letInline body =>
        have bodyEmpty := decideInline_codeLocations c a1 loc xs.length body decision
        have bodyInvariant := inlineIH ea2 g1 [(e1, a1)] g2 e1 a1 body
          ⟨ha.symm, hf.symm, by simp [knownSourceHead], decision⟩
        cases hb : knownListTotal (decInlineFactor c) [body] (ea2.map Prod.snd) g2 with
        | mk inlineEa inlineG =>
          obtain ⟨inlineExpr, inlineApprox, eqBody⟩ :=
            knownListTotal_single_result (decInlineFactor c) body (ea2.map Prod.snd) g2 inlineG inlineEa hb
          subst inlineEa
          have rBody := bodyInvariant [(inlineExpr, inlineApprox)] inlineG hb label
          have ticksEq := ticks_codeLocations trace 1 xs.length inlineExpr
          simp only [decision] at run
          rw [hb] at run
          simp at run
          rcases run with ⟨rfl, rfl⟩
          simp [codeLocations] at bodyEmpty ticksEq rBody
          simp [codeLocations, codeLocationsExp, List.count_append, ticksEq] at rFun ⊢
          split <;> simp_all [codeLocations_append, codeLocations, List.count_append] <;> omega

/-- Recursive-closure case of the optimizer code-location multiset theorem. -/
@[hol "cakeml/compiler/backend/proofs/clos_knownProofScript.sml" "known_code_locs_bag"]
theorem knownCodeBagLetrec (c : Config) (names : List Basis.Pure.MlString.MlString)
    (loc : Option Nat) (vs : Option (List Nat)) (fns : List (Nat × Exp))
    (body : Exp) (env : List ValApprox) (g : Spt ValApprox)
    (bodyIH : ∀ clos newFns,
      clos = (match loc with | none => List.replicate fns.length .other | some n => closGenNoInline n 0 fns) ∧
      newFns = fns.map (fun (n, e) =>
        (n, (knownSourceHead (knownListTotal c [e] (List.replicate n ValApprox.other ++ clos ++ env) g).1).1)) →
      KnownCodeBagInvariant c [body] (clos ++ env) g)
    (funsIH : ∀ clos arity e newEnv,
      clos = (match loc with | none => List.replicate fns.length .other | some n => closGenNoInline n 0 fns) ∧
      (arity, e) ∈ fns ∧ newEnv = List.replicate arity .other ++ clos ++ env →
      KnownCodeBagInvariant c [e] newEnv g) :
    KnownCodeBagInvariant c [.letrec names loc vs fns body] env g := by
  intro eas next run label
  let clos := match loc with
    | none => List.replicate fns.length ValApprox.other
    | some n => closGenNoInline n 0 fns
  let transform := fun (entry : Nat × Exp) =>
    (entry.1, (knownSourceHead (knownListTotal c [entry.2]
      (List.replicate entry.1 ValApprox.other ++ clos ++ env) g).1).1)
  let newFns := fns.map transform
  have groups : ∀ fs : List (Nat × Exp), (∀ entry ∈ fs, entry ∈ fns) →
      (codeLocationsFuns (fs.map transform)).count label ≤ (codeLocationsFuns fs).count label := by
    intro fs
    induction fs with
    | nil => simp [codeLocationsFuns]
    | cons entry rest ih =>
      intro members
      obtain ⟨n, e⟩ := entry
      have member : (n, e) ∈ fns := members _ (by simp)
      have restBound := ih (fun v hv => members v (by simp [hv]))
      have one := funsIH clos n e (List.replicate n ValApprox.other ++ clos ++ env)
        ⟨by cases loc <;> rfl, member, rfl⟩
      cases he : knownListTotal c [e] (List.replicate n ValApprox.other ++ clos ++ env) g with
      | mk ea ge =>
        obtain ⟨e', a', eaEq⟩ := knownListTotal_single_result c e _ g ge ea he
        subst ea
        have bound := one [(e', a')] ge he label
        have transformed : (transform (n, e)).2 = e' := by
          change (knownSourceHead (knownListTotal c [e]
            (List.replicate n ValApprox.other ++ clos ++ env) g).1).1 = e'
          rw [he]
          rfl
        change (codeLocationsExp (transform (n, e)).2 ++ codeLocationsFuns (rest.map transform)).count label ≤
          (codeLocationsExp e ++ codeLocationsFuns rest).count label
        rw [transformed]
        simp [codeLocations, List.count_append] at bound ⊢
        omega
  have fnBound := groups fns (by intro entry member; exact member)
  cases hb : knownListTotal c [body] (clos ++ env) g with
  | mk ea gb =>
    obtain ⟨bodyExpr, bodyApprox, bodyEq⟩ := knownListTotal_single_result c body (clos ++ env) g gb ea hb
    subst ea
    have rBody := bodyIH clos newFns ⟨by cases loc <;> rfl, rfl⟩ [(bodyExpr, bodyApprox)] gb hb label
    rw [knownListTotal_letrec] at run
    change (let (ea, g1) := knownListTotal c [body] (clos ++ env) g
      let (e, a) := knownSourceHead ea
      ([(.letrec names loc none newFns e, a)], g1)) = (eas, next) at run
    rw [hb] at run
    simp [knownSourceHead] at run
    rcases run with ⟨rfl, rfl⟩
    simp [codeLocations, codeLocationsExp, List.count_append, newFns] at rBody fnBound ⊢
    omega

end Flapjack.Compiler.Backend.ClosKnown.TraversalCodeBag
