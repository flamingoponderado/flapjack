import Flapjack.Compiler.Backend.FlatElim.Proofs.PureFull
import Flapjack.Compiler.Backend.Semantics.FlatSem.Semantics
import Flapjack.Compiler.Backend.Semantics.FlatSem.SemanticsCongruence
import Flapjack.Compiler.Backend.FlatProps.EvalSim

/-! Declaration-removal simulation for flat elimination. -/
namespace Flapjack.Compiler.Backend.FlatElim
open Flapjack.SemanticPrimitivesHOL

/-- A discarded singleton expression preserves the relation to the unchanged
target and returns one value. The evaluator and carriers remain pending HOL
correspondence review. -/
@[hol "cakeml/compiler/backend/proofs/flat_elimProofScript.sml" "evaluate_sing_notKeep_flat_state_rel"]
theorem evaluate_sing_notKeep_flatStateRel {C F α : Type} (env : FlatSem.Environment α)
    (state : FlatSem.State C F) (expressions : List FlatLang.Exp) (next : FlatSem.State C F)
    (result : Result (List FlatSem.Value) FlatSem.Value) (expression : FlatLang.Exp)
    (reachable : NumSet) (target : FlatSem.State C F)
    (run : FlatSem.evaluate (emptyEnvironment env) state expressions = (next, result))
    (singleton : expressions = [expression]) (safe : hasEval expression = false)
    (notKept : keep reachable expression = false) (related : flatStateRel reachable state target)
    (notTypeError : result ≠ .err (.abort .typeError)) :
    flatStateRel reachable next target ∧ ∃ value : FlatSem.Value, result = .val [value] := by
  subst expressions
  have pure : isPure expression = true := by
    cases purity : isPure expression <;> simp [keep, purity] at notKept ⊢
  have empty : sptIsEmpty (sptInter (findLoc expression) reachable) = true := by
    cases emptiness : sptIsEmpty (sptInter (findLoc expression) reachable) <;> simp [keep, emptiness] at notKept ⊢
  have envSafe : bindingsNoEval (emptyEnvironment env : FlatSem.Environment FlatSem.Value).v := by
    simp [emptyEnvironment, bindingsNoEval]
  obtain ⟨values, nextRelated, resultEq, _⟩ :=
    evaluate_pure_flatStateRel (emptyEnvironment env) state [expression] next result reachable target run
      (singletonPure expression pure) envSafe (singletonExpression_noEval expression safe)
      (singletonLocations expression reachable empty) related notTypeError
  subst result
  obtain ⟨value, rfl⟩ := Flapjack.Compiler.Backend.FlatProps.evaluate_sing (emptyEnvironment env) state next expression values run
  exact ⟨nextRelated, value, rfl⟩

/-- Evaluating a discarded declaration either yields unit or a type error;
when the latter is excluded, its state remains related to the unchanged target.
This is a Flapjack helper for the declaration-list induction. -/
theorem evaluateDec_notKept {C F : Type} (state next target : FlatSem.State C F)
    (declaration : FlatLang.Exp) (result : Option (ErrorResult FlatSem.Value)) (reachable : NumSet)
    (run : FlatSem.evaluateDec state declaration = (next, result))
    (notKept : keep reachable declaration = false) (safe : hasEvalDec declaration = false)
    (related : flatStateRel reachable state target) (notTypeError : result ≠ some (.abort .typeError)) :
    result = none ∧ flatStateRel reachable next target := by
  cases evaluated : FlatSem.evaluate ⟨[]⟩ state [declaration] with
  | mk bodyState bodyResult =>
    have bodyNotTypeError : bodyResult ≠ .err (.abort .typeError) := by
      intro bad
      subst bodyResult
      simp [FlatSem.evaluateDec, evaluated] at run
      rcases run with ⟨_, rfl⟩
      exact notTypeError rfl
    obtain ⟨bodyRelated, value, valueEq⟩ :=
      evaluate_sing_notKeep_flatStateRel (⟨[]⟩ : FlatSem.Environment FlatSem.Value)
        state [declaration] bodyState bodyResult declaration reachable target evaluated rfl
        (by simpa [hasEvalDec] using safe) notKept related bodyNotTypeError
    subst bodyResult
    simp only [FlatSem.evaluateDec, evaluated] at run
    split at run <;> simp_all

/-- Declaration-list evaluation factors through the single-declaration
evaluator and the same clock clamp. This is a Flapjack evaluator helper. -/
theorem evaluateDecs_cons {C F : Type} (state : FlatSem.State C F)
    (declaration : FlatLang.Exp) (rest : List FlatLang.Exp) :
    FlatSem.evaluateDecs state (declaration :: rest) =
      (let next := FlatSem.fixClock state (FlatSem.evaluateDec state declaration)
       match next.2 with
       | some error => (next.1, some error)
       | none => FlatSem.evaluateDecs next.1 rest) := by
  rw [FlatSem.evaluateDecs, FlatSem.evaluateDec]
  cases evaluated : FlatSem.evaluate ⟨[]⟩ state [declaration] with
  | mk next result =>
    cases result with
    | err error => simp [FlatSem.fixClock]
    | val values =>
      simp only [FlatSem.fixClock]
      split <;> rfl

/-- Filtering closed, Eval-free declarations preserves evaluation and the
flat state relation when the original result is not a type error. This
Flapjack helper strengthens the original theorem with the final relation. -/
theorem evaluateDecs_removal_related {C F : Type} (declarations : List FlatLang.Exp)
    (state next : FlatSem.State C F) (result : Option (ErrorResult FlatSem.Value))
    (reachable : NumSet) (target : FlatSem.State C F)
    (run : FlatSem.evaluateDecs state declarations = (next, result))
    (notTypeError : result ≠ some (.abort .typeError))
    (related : flatStateRel reachable state target)
    (safe : ∀ declaration ∈ declarations, hasEvalDec declaration = false)
    (closed : decsClosed reachable declarations) :
    ∃ targetNext, FlatSem.evaluateDecs target (removeUnreachable reachable declarations) = (targetNext, result) ∧
      flatStateRel reachable next targetNext := by
  induction declarations generalizing state next result target with
  | nil =>
    simp [FlatSem.evaluateDecs] at run
    rcases run with ⟨rfl, rfl⟩
    exact ⟨target, by simp [removeUnreachable, FlatSem.evaluateDecs], related⟩
  | cons declaration rest ih =>
    have headSafe := safe declaration (by simp)
    have tailSafe : ∀ item ∈ rest, hasEvalDec item = false := by
      intro item member
      exact safe item (by simp [member])
    have headClosed := decsClosed_head reachable declaration rest closed
    have tailClosed := decsClosed_tail reachable declaration rest closed
    cases headEval : FlatSem.evaluateDec state declaration with
    | mk headState headResult =>
      rw [evaluateDecs_cons] at run
      simp only [headEval, FlatSem.fixClock] at run
      have headNotTypeError : headResult ≠ some (.abort .typeError) := by
        intro bad
        subst headResult
        simp at run
        rcases run with ⟨_, rfl⟩
        exact notTypeError rfl
      cases kept : keep reachable declaration with
      | true =>
        obtain ⟨targetHeadState, targetHeadEval, headRelated⟩ :=
          evaluate_dec_flatStateRel state declaration headState headResult reachable target headEval headClosed related kept headSafe headNotTypeError
        have clampedRelated : flatStateRel reachable
            { headState with clock := min state.clock headState.clock }
            { targetHeadState with clock := min target.clock targetHeadState.clock } := by
          obtain ⟨clock, refs, ffi, globals, refsClosed, refsSafe⟩ := headRelated
          exact ⟨by simp [related.1, clock], refs, ffi, globals, refsClosed, refsSafe⟩
        cases headResult with
        | some error =>
          simp only at run
          rcases run with ⟨rfl, rfl⟩
          refine ⟨{ targetHeadState with clock := min target.clock targetHeadState.clock }, ?_, clampedRelated⟩
          simp [removeUnreachable, kept, evaluateDecs_cons, targetHeadEval, FlatSem.fixClock]
        | none =>
          simp only at run
          obtain ⟨targetNext, evaluated, nextRelated⟩ :=
            ih _ next result _ run notTypeError clampedRelated tailSafe tailClosed
          refine ⟨targetNext, ?_, nextRelated⟩
          simpa [removeUnreachable, kept, evaluateDecs_cons, targetHeadEval, FlatSem.fixClock] using evaluated
      | false =>
        obtain ⟨headNone, headRelated⟩ :=
          evaluateDec_notKept state headState target declaration headResult reachable headEval kept headSafe related headNotTypeError
        subst headResult
        have clocks : state.clock = headState.clock := related.1.trans headRelated.1.symm
        simp only [clocks, Nat.min_self] at run
        obtain ⟨targetNext, evaluated, nextRelated⟩ :=
          ih headState next result target run notTypeError headRelated tailSafe tailClosed
        exact ⟨targetNext, by simpa [removeUnreachable, kept] using evaluated, nextRelated⟩

/-- Removing unreachable declarations preserves the evaluation result and
final FFI state. The evaluator and carriers remain pending HOL correspondence
review. -/
@[hol "cakeml/compiler/backend/proofs/flat_elimProofScript.sml" "flat_decs_removal_lemma"]
theorem flat_decs_removal {C F : Type} (state : FlatSem.State C F) (declarations : List FlatLang.Exp)
    (next : FlatSem.State C F) (result : Option (ErrorResult FlatSem.Value)) (reachable : NumSet)
    (removed : List FlatLang.Exp) (target : FlatSem.State C F)
    (run : FlatSem.evaluateDecs state declarations = (next, result))
    (notTypeError : result ≠ some (.abort .typeError)) (filtered : removeUnreachable reachable declarations = removed)
    (related : flatStateRel reachable state target)
    (safe : ∀ declaration ∈ declarations, hasEvalDec declaration = false)
    (closed : decsClosed reachable declarations) :
    ∃ targetNext, targetNext.ffi = next.ffi ∧ FlatSem.evaluateDecs target removed = (targetNext, result) := by
  subst removed
  obtain ⟨targetNext, evaluated, nextRelated⟩ :=
    evaluateDecs_removal_related declarations state next result reachable target run notTypeError related safe closed
  exact ⟨targetNext, nextRelated.2.2.1.symm, evaluated⟩

/-- Starting from the flat initial state, reachability-based removal preserves
evaluation result and FFI state. The evaluator and carriers remain pending
HOL correspondence review. -/
@[hol "cakeml/compiler/backend/proofs/flat_elimProofScript.sml" "flat_removal_thm"]
theorem flat_removal {C F : Type} (ffi : HolFfiState F) (clock : Nat)
    (declarations : List FlatLang.Exp) (next : FlatSem.State C F)
    (result : Option (ErrorResult FlatSem.Value)) (roots : NumSet) (tree : Spt NumSet)
    (reachable : NumSet) (removed : List FlatLang.Exp) (config : FlatSem.InstallConfig C)
    (run : FlatSem.evaluateDecs (FlatSem.initialState ffi clock config) declarations = (next, result))
    (notTypeError : result ≠ some (.abort .typeError)) (analysis : (roots, tree) = analyseCode declarations)
    (closure : reachable = closureTotal roots tree) (safe : declarations.any hasEvalDec = false)
    (filtered : removeUnreachable reachable declarations = removed) :
    ∃ targetNext, targetNext.ffi = next.ffi ∧
      FlatSem.evaluateDecs (FlatSem.initialState ffi clock config) removed = (targetNext, result) := by
  subst reachable
  have initialRelated : flatStateRel (closureTotal roots tree)
      (FlatSem.initialState ffi clock config) (FlatSem.initialState ffi clock config) := by
    simp [flatStateRel, globalsRel, FlatSem.initialState, findRefsGlobals,
      sptMem, sptDomain, storeHasNoEval]
  have eachSafe : ∀ declaration ∈ declarations, hasEvalDec declaration = false := by
    intro declaration member
    have h := (List.any_eq_false.mp safe) declaration member
    simpa using h
  exact flat_decs_removal _ declarations next result (closureTotal roots tree) removed _ run notTypeError filtered
    initialRelated eachSafe (decsClosed_analysisClosure declarations roots tree analysis.symm)

/-- Flat elimination preserves the exact result and FFI state at the same
clock whenever the source result is not a type error. This Flapjack helper
strengthens the original result-class simulation. -/
theorem flat_remove_sameClock {C F : Type} (ffi : HolFfiState F) (declarations : List FlatLang.Exp)
    (config : FlatSem.InstallConfig C) (clock : Nat) (sourceState : FlatSem.State C F)
    (result : Option (ErrorResult FlatSem.Value))
    (run : FlatSem.evaluateDecs (FlatSem.initialState ffi clock config) declarations = (sourceState, result))
    (notTypeError : result ≠ some (.abort .typeError)) :
    ∃ targetState, targetState.ffi = sourceState.ffi ∧
      FlatSem.evaluateDecs (FlatSem.initialState ffi clock config) (removeFlatProgTotal declarations) = (targetState, result) := by
  cases safe : declarations.any hasEvalDec with
  | true =>
    refine ⟨sourceState, rfl, ?_⟩
    simpa [removeFlatProgTotal, safe] using run
  | false =>
    cases analysis : analyseCode declarations with
    | mk roots tree =>
      have filtered : removeUnreachable (closureTotal roots tree) declarations = removeFlatProgTotal declarations := by
        simp [removeFlatProgTotal, safe, analysis]
      exact flat_removal ffi clock declarations sourceState result roots tree (closureTotal roots tree)
        (removeFlatProgTotal declarations) config run notTypeError analysis.symm rfl safe filtered

/-- The flat elimination pass satisfies the original evaluation simulation
relation with no added clock. The evaluator and carriers remain pending HOL
correspondence review. -/
@[hol "cakeml/compiler/backend/proofs/flat_elimProofScript.sml" "flat_remove_eval_sim"]
theorem flat_remove_evalSim {C F : Type} (ffi : HolFfiState F) (declarations : List FlatLang.Exp)
    (config : FlatSem.InstallConfig C) :
    FlatProps.evalSim ffi declarations (removeFlatProgTotal declarations) config config
      (fun source target => target = removeFlatProgTotal source) false := by
  intro clock result sourceState run allowed _
  have notTypeError : result ≠ some (.abort .typeError) := by simpa using allowed
  obtain ⟨targetState, ffiEq, evaluated⟩ := flat_remove_sameClock ffi declarations config clock sourceState result run notTypeError
  refine ⟨0, result, targetState, by simpa using evaluated, ffiEq.symm, ?_, ?_, ?_⟩
  · intro eq
    exact eq
  · intro value eq
    exact ⟨value, eq⟩
  · intro abort eq
    exact eq

/-- Flat elimination preserves the factored observational semantics whenever
the source semantics is not failure. The evaluator, semantics definition,
and carriers remain pending complete HOL correspondence review. -/
@[hol "cakeml/compiler/backend/proofs/flat_elimProofScript.sml" "flat_remove_semantics"]
theorem flat_remove_semantics {C F : Type} (ffi : HolFfiState F) (declarations : List FlatLang.Exp)
    (config : FlatSem.InstallConfig C) (notFail : FlatSem.semantics config ffi declarations ≠ .fail) :
    FlatSem.semantics config ffi declarations = FlatSem.semantics config ffi (removeFlatProgTotal declarations) := by
  classical
  have sourceSafe : ∀ clock, (FlatSem.evaluateDecs (FlatSem.initialState ffi clock config) declarations).2 ≠
      some (.abort .typeError) := by
    intro clock bad
    have failure : FlatSem.semantics config ffi declarations = .fail := by
      simp [FlatSem.semantics, show ∃ clock, (FlatSem.evaluateDecs (FlatSem.initialState ffi clock config) declarations).2 =
        some (.abort .typeError) from ⟨clock, bad⟩]
    exact notFail failure
  apply FlatSem.semantics_eq_of_same_observations config ffi declarations (removeFlatProgTotal declarations)
  intro clock
  cases sourceEval : FlatSem.evaluateDecs (FlatSem.initialState ffi clock config) declarations with
  | mk state result =>
    have notTypeError : result ≠ some (.abort .typeError) := by
      simpa [sourceEval] using sourceSafe clock
    obtain ⟨targetState, ffiEq, targetEval⟩ :=
      flat_remove_sameClock ffi declarations config clock state result sourceEval notTypeError
    simp [targetEval, ffiEq]

end Flapjack.Compiler.Backend.FlatElim
