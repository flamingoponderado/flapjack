module

public import Flapjack.Compiler.Backend.ClosKnown.Proofs.CorrectApproxFn
public import Flapjack.Compiler.Backend.ClosKnown.Proofs.KnownUnchanged

-- Proofs below unfold private helpers of these modules.
import all Flapjack.Compiler.Backend.Semantics.ClosSem.EvaluateExact
import all Flapjack.Compiler.Backend.Semantics.ClosSem.EvaluateFuel
@[expose] public section

namespace Flapjack.Compiler.Backend.ClosKnown.CorrectApprox.Letrec
open ClosSem ClosProps ClosProps.StateGlobalSafety UniqueGlobalsPort OracleGlobals
open Flapjack.SemanticPrimitivesHOL

/-- Recursive closures are described by the generated approximation list.
This is Flapjack proof infrastructure. -/
theorem recClosuresApprox (loc : Option Nat) (captures : List ClosSem.Value)
    (fns : List (Nat × ClosLang.Exp)) :
    List.Forall₂ ValApproxVal
      (match loc with | none => List.replicate fns.length .other | some n => closGenNoInline n 0 fns)
      ((List.range fns.length).map (fun i => ClosSem.Value.recclosure loc [] captures fns i)) := by
  cases loc with
  | none =>
    rw [List.forall₂_iff_get]
    constructor
    · simp
    · intro i h1 h2
      simp [ValApproxVal.other]
  | some loc =>
    change List.Forall₂ ValApproxVal (noInline loc fns) _
    rw [noInline_eq_zip, List.forall₂_iff_get]
    constructor
    · simp
    · intro i h1 h2
      have hi : i < fns.length := by simpa using h1
      simp only [List.get_eq_getElem, List.getElem_map, List.getElem_zip, List.getElem_range]
      let _ : Nonempty (Nat × ClosLang.Exp) := ⟨(0, .var .none 0)⟩
      exact ValApproxVal.recNoInline _ _ _ _ _ _ ⟨rfl, hi, by rw [Flapjack.holEl_eq_getElem i fns hi]⟩


/-- The closure state uses canonical finite-map fields. -/
theorem holFmapAsFiniteSupportWitness {C F : Type} :
    (∀ s : ClosSem.StateBroad C F, (ClosSem.State.ofBroad s).toBroad = s) ∧
      (∀ s : ClosSem.State C F, ClosSem.State.ofBroad s.toBroad = s) :=
  ClosSem.holFmapAsFiniteSupportWitness

/-- Selection of safe captured values preserves safety. This is Flapjack
proof infrastructure. -/
private theorem lookupVarsSafe (indices : List Nat) (env selected : List ClosSem.Value)
    (safe : ∀ v ∈ env, vsgcFree v) (run : lookupVars indices env = some selected) :
    ∀ v ∈ selected, vsgcFree v := by
  induction indices generalizing selected with
  | nil => simp [lookupVars] at run; subst selected; simp
  | cons index rest ih =>
    simp only [lookupVars] at run
    cases found : env[index]? with
    | none => simp [found] at run
    | some value =>
      simp only [found] at run
      cases remaining : lookupVars rest env with
      | none => simp [remaining] at run
      | some values =>
        simp [remaining] at run
        subst selected
        exact by simpa using And.intro (safe value (List.mem_of_getElem? found)) (ih values remaining)

/-- Recursive-closure case of the original approximation theorem. -/
@[hol "cakeml/compiler/backend/proofs/clos_knownProofScript.sml" "known_correct_approx"
  (fmap_as_finite_support := [refs, code])]
theorem knownCorrectApproxLetrec {C F : Type} (c : Config) (names : List Basis.Pure.MlString.MlString)
    (loc : Option Nat) (selected : Option (List Nat)) (fns : List (Nat × ClosLang.Exp))
    (body : ClosLang.Exp) (aenv : List ValApprox) (g0 : Spt ValApprox)
    (bodyIH : ∀ (clos : List ValApprox) (newFns : List (Nat × ClosLang.Exp)),
      clos = (match loc with | none => List.replicate fns.length .other | some n => closGenNoInline n 0 fns) ∧
      newFns = fns.map (fun (n, e) =>
        (n, (knownSourceHead (knownListTotal c [e] (List.replicate n ValApprox.other ++ clos ++ aenv) g0).1).1)) →
      KnownApproxInvariant C F c [body] (clos ++ aenv) g0)
    (_funsIH : ∀ (clos : List ValApprox) (arity : Nat) (e : ClosLang.Exp) (newEnv : List ValApprox),
      clos = (match loc with | none => List.replicate fns.length .other | some n => closGenNoInline n 0 fns) ∧
      (arity, e) ∈ fns ∧ newEnv = List.replicate arity .other ++ clos ++ aenv →
      KnownApproxInvariant C F c [e] newEnv g0)
    (eas : List (ClosLang.Exp × ValApprox)) (g : Spt ValApprox) (env extra : List ClosSem.Value)
    (s0 : State (Spt ValApprox × C) F) (res : Result (List ClosSem.Value) ClosSem.Value)
    (s : State (Spt ValApprox × C) F)
    (h : knownListTotal c [.letrec names loc selected fns body] aenv g0 = (eas, g) ∧
      evaluate [.letrec names loc selected fns body] (env ++ extra) s0 = (res, s) ∧
      uniqueSetGlobals [.letrec names loc selected fns body] s0.compileOracle ∧ List.Forall₂ ValApproxVal aenv env ∧
      stateGlobalsApprox s0 g0 ∧ mglobalsDisjoint s0.globals [.letrec names loc selected fns body] ∧
      oracleGapproxDisjoint g0 s0.compileOracle ∧ ssgcFree s0 ∧
      (∀ v ∈ env ++ extra, vsgcFree v) ∧ (∀ e ∈ [ClosLang.Exp.letrec names loc selected fns body], esgcFree e) ∧
      (∀ a ∈ aenv, valApproxSgcFree a) ∧ globalsApproxSgcFree g0) :
    stateGlobalsApprox s g ∧ ∀ vs, res = .val vs → List.Forall₂ ValApproxVal (eas.map Prod.snd) vs := by
  rcases h with ⟨known, run, unique, related, approx, disjoint, oracle, safe, envSafe, exprSafe, approxSafe, globalsSafe⟩
  have safeParts : funGlobals fns = FlatProps.emptyGlobalBag ∧ esgcFree body := by
    simpa [esgcFree] using exprSafe (.letrec names loc selected fns body) (by simp)
  let clos := match loc with | none => List.replicate fns.length ValApprox.other | some n => closGenNoInline n 0 fns
  let newFns := fns.map (fun (n, e) =>
    (n, (knownSourceHead (knownListTotal c [e] (List.replicate n ValApprox.other ++ clos ++ aenv) g0).1).1))
  have closSafe : ∀ a ∈ clos, valApproxSgcFree a := by
    cases loc with
    | none => simp [clos, valApproxSgcFree]
    | some n => exact closGenNoInlineSafe n 0 fns
  have bodyUnique : uniqueSetGlobals [body] s0.compileOracle := by
    simpa [uniqueSetGlobals, elistGlobals, setGlobals, safeParts.1,
      FlatProps.unionGlobalBag, FlatProps.emptyGlobalBag, Flapjack.bagUnion, Flapjack.emptyBag] using unique
  have bodyDisjoint : mglobalsDisjoint s0.globals [body] := by
    simpa [mglobalsDisjoint, elistGlobals, setGlobals, safeParts.1,
      FlatProps.unionGlobalBag, FlatProps.emptyGlobalBag, Flapjack.bagUnion, Flapjack.emptyBag] using disjoint
  have bodySafe : ∀ e ∈ [body], esgcFree e := by simpa using safeParts.2
  cases hk : knownListTotal c [body] (clos ++ aenv) g0 with
  | mk bodyEas bodyG =>
    obtain ⟨bodyExpr, bodyApprox, bodyEq⟩ :=
      knownListTotal_single_result c body (clos ++ aenv) g0 bodyG bodyEas hk
    subst bodyEas
    have preserved := ApproxEvaluate.stateGlobalsApproxKnownDisjoint c [body]
      (clos ++ aenv) g0 [(bodyExpr, bodyApprox)] bodyG s0 ⟨hk, bodyDisjoint, approx⟩
    have ih := bodyIH clos newFns ⟨rfl, rfl⟩
    rw [knownListTotal_letrec] at known
    change (let clos' := clos; let fs := newFns; let (ea, gg) := knownListTotal c [body] (clos' ++ aenv) g0
      ([(.letrec names loc none fs (knownSourceHead ea).1, (knownSourceHead ea).2)], gg)) = (eas, g) at known
    dsimp only at known
    rw [hk] at known
    simp [knownSourceHead] at known
    rcases known with ⟨rfl, rfl⟩
    by_cases valid : (fns.all (fun (arity, _) => arity ≤ s0.maxApp && arity != 0)) = true
    · cases captured : (match selected with | none => some (env ++ extra) | some indices => lookupVars indices (env ++ extra)) with
      | none =>
        cases selected with
        | none => simp at captured
        | some indices =>
          simp [evaluate, valid, captured] at run
          rcases run with ⟨rfl, rfl⟩
          exact ⟨preserved, by intro vs eq; cases eq⟩
      | some captures =>
        have capturesSafe : ∀ v ∈ captures, vsgcFree v := by
          cases selected with
          | none => simp at captured; simpa [← captured] using envSafe
          | some indices => exact lookupVarsSafe indices (env ++ extra) captures envSafe captured
        let recs := (List.range fns.length).map (fun i => ClosSem.Value.recclosure loc [] captures fns i)
        have recSafe : ∀ v ∈ recs, vsgcFree v := by
          intro v member
          obtain ⟨i, _, rfl⟩ := List.mem_map.mp member
          simpa [recs, vsgcFree, ← funGlobals_eq_elist] using And.intro safeParts.1 capturesSafe
        have recRel : List.Forall₂ ValApproxVal clos recs := by
          simpa [clos, recs] using recClosuresApprox loc captures fns
        have extendedSafe : ∀ v ∈ (recs ++ env) ++ extra, vsgcFree v := by
          simpa [List.mem_append, or_imp, forall_and] using And.intro recSafe envSafe
        have extendedApproxSafe : ∀ a ∈ clos ++ aenv, valApproxSgcFree a := by
          simpa [List.mem_append, or_imp, forall_and] using And.intro closSafe approxSafe
        have bodyRun : evaluate [body] ((recs ++ env) ++ extra) s0 = (res, s) := by
          cases selected with
          | none =>
            simp only [Option.some.injEq] at captured
            subst captures
            simpa [evaluate, valid, recs, List.append_assoc] using run
          | some indices =>
            simpa [evaluate, valid, captured, recs, List.append_assoc] using run
        have result := ih [(bodyExpr, bodyApprox)] bodyG (recs ++ env) extra s0 res s
          ⟨hk, bodyRun, bodyUnique, List.rel_append recRel related, approx, bodyDisjoint, oracle,
            safe, extendedSafe, bodySafe, extendedApproxSafe, globalsSafe⟩
        simpa using result
    · cases selected <;> simp [evaluate, valid] at run <;>
        rcases run with ⟨rfl, rfl⟩ <;>
        exact ⟨preserved, by intro vs eq; cases eq⟩

end Flapjack.Compiler.Backend.ClosKnown.CorrectApprox.Letrec
