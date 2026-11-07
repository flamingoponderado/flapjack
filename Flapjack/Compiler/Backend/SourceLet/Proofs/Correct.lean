import Flapjack.Compiler.Backend.SourceLet.Proofs.Repeated

/-! Declaration-list correctness for the source let-lifting pass. -/
namespace Flapjack.Compiler.Backend.SourceLet
open Flapjack.AstHOL Flapjack.SemanticPrimitivesHOL Flapjack.EvaluateHOL Flapjack.EvaluateProps
open Flapjack.NamespaceHOL

/-- A declaration-list simulation used while assembling the pass proof.
This Flapjack predicate is not a separate HOL declaration. -/
def DecsPreserve {F : Type} (source target : List Dec) : Prop :=
  ∀ (state next : State F) (env : SemEnv Value) (result : Result (SemEnv Value) Value),
    evaluateDecs state env source = (next, result) → result ≠ .err (.abort .typeError) →
    evaluateDecs state env target = (next, result)

/-- Independent head and tail simulations compose, without assuming either
target evaluation result. This Flapjack helper has no separate HOL declaration. -/
theorem decsPreserve_cons {F : Type} (d d' : Dec) (ds ds' : List Dec)
    (head : DecsPreserve (F := F) [d] [d']) (tail : DecsPreserve (F := F) ds ds') :
    DecsPreserve (F := F) (d :: ds) (d' :: ds') := by
  intro state last env result source safe
  rw [evaluateDecs_cons] at source
  cases first : evaluateDecs state env [d] with
  | mk middle firstResult =>
    cases firstResult with
    | err error =>
      have firstPair : (middle, .err error) = (last, result) := by simpa [first] using source
      have firstSafe : (Result.err error : Result (SemEnv Value) Value) ≠ .err (.abort .typeError) := by
        intro bad
        apply safe
        have resultEq := congrArg Prod.snd firstPair
        simpa [bad] using resultEq.symm
      have replacement := head state middle env (.err error) first firstSafe
      rw [evaluateDecs_cons, replacement]
      exact firstPair
    | val inner =>
      cases rest : evaluateDecs middle (extendDecEnv inner env) ds with
      | mk next restResult =>
        have sourcePair : (next, combineDecResult inner restResult) = (last, result) := by
          simpa [first, rest] using source
        have restSafe : restResult ≠ .err (.abort .typeError) := by
          intro bad
          apply safe
          have resultEq := congrArg Prod.snd sourcePair
          simpa [bad, combineDecResult] using resultEq.symm
        have newHead := head state middle env (.val inner) first (by simp)
        have newTail := tail middle next (extendDecEnv inner env) restResult rest restSafe
        rw [evaluateDecs_cons, newHead]
        simp only
        rw [newTail]
        exact sourcePair

/-- A module preserves evaluation when its contained declarations do. This
Flapjack helper has no separate HOL declaration. -/
theorem decsPreserve_module {F : Type} (name : ModN) (ds ds' : List Dec)
    (inner : DecsPreserve (F := F) ds ds') :
    DecsPreserve (F := F) [.dmod name ds] [.dmod name ds'] := by
  intro state last env result source safe
  cases run : evaluateDecs state env ds with
  | mk next innerResult =>
    cases innerResult with
    | err error =>
      have pair : (next, .err error) = (last, result) := by
        simpa [evaluateDecs, run] using source
      have innerSafe : (Result.err error : Result (SemEnv Value) Value) ≠ .err (.abort .typeError) := by
        intro bad
        apply safe
        have resultEq := congrArg Prod.snd pair
        simpa [bad] using resultEq.symm
      have replacement := inner state next env (.err error) run innerSafe
      simpa [evaluateDecs, replacement] using pair
    | val innerEnv =>
      have replacement := inner state next env (.val innerEnv) run (by simp)
      simpa [evaluateDecs, run, replacement] using source

/-- Private and visible parts of a local declaration compose under their
respective declaration-list induction hypotheses. This Flapjack helper has
no separate HOL declaration. -/
theorem decsPreserve_local {F : Type} (locals locals' body body' : List Dec)
    (localIH : DecsPreserve (F := F) locals locals') (bodyIH : DecsPreserve (F := F) body body') :
    DecsPreserve (F := F) [.dlocal locals body] [.dlocal locals' body'] := by
  intro state last env result source safe
  rw [evaluateDecs_local] at source ⊢
  cases run : evaluateDecs state env locals with
  | mk next localResult =>
    cases localResult with
    | err error =>
      have pair : (next, .err error) = (last, result) := by simpa [run] using source
      have localSafe : (Result.err error : Result (SemEnv Value) Value) ≠ .err (.abort .typeError) := by
        intro bad
        apply safe
        have resultEq := congrArg Prod.snd pair
        simpa [bad] using resultEq.symm
      have replacement := localIH state next env (.err error) run localSafe
      rw [replacement]
      exact pair
    | val localEnv =>
      have bodyRun : evaluateDecs next (extendDecEnv localEnv env) body = (last, result) := by
        simpa [run] using source
      have replacement := localIH state next env (.val localEnv) run (by simp)
      rw [replacement]
      exact bodyIH next last (extendDecEnv localEnv env) result bodyRun safe

/-- A successful lifting sequence preserves evaluation of its declaration.
This Flapjack helper specializes the repeated-lifting theorem. -/
theorem decsPreserve_lifted {F : Type} (d : Dec) (pre : List Dec) (final : Dec)
    (lifted : liftLets [] d = some (pre, final)) :
    DecsPreserve (F := F) [d] [.dlocal pre [final]] := by
  intro state next env result source safe
  let empty : SemEnv Value := ⟨nsEmpty, nsEmpty⟩
  have emptyRun : evaluateDecs state env ([] : List Dec).reverse = (state, .val empty) := by
    simp only [List.reverse_nil, evaluateDecs]
    rfl
  have emptyExtend : extendDecEnv empty env = env := by
    cases env with
    | mk vars constructors => cases vars; cases constructors; rfl
  apply evaluate_lift_lets [] d state state next env empty result pre final emptyRun
  · simpa only [emptyExtend] using source
  · exact safe
  · exact lifted

/-- All declarations compiled by source let-lifting preserve their clocked
evaluation whenever the source result is not a type error. This Flapjack
predicate form assembles the result-shaped HOL theorem below. -/
theorem compileDecs_preserve {F : Type} (ds : List Dec) : DecsPreserve (F := F) ds (compileDecs ds) := by
  induction ds using compileDecs.induct with
  | case1 =>
    intro state next env result source safe
    simpa [compileDecs] using source
  | case2 d ds pre final lifted ih =>
    have head := decsPreserve_lifted (F := F) d pre final lifted
    have compiled : compileDecs (d :: ds) = .dlocal pre [final] :: compileDecs ds := by
      rw [compileDecs.eq_def]
      dsimp only
      rw [lifted]
    rw [compiled]
    exact decsPreserve_cons d (.dlocal pre [final]) ds (compileDecs ds) head ih
  | case3 ds name inner lifted innerIH tailIH =>
    have head := decsPreserve_module name inner (compileDecs inner) innerIH
    simpa only [compileDecs, lifted] using decsPreserve_cons (.dmod name inner) (.dmod name (compileDecs inner))
      ds (compileDecs ds) head tailIH
  | case4 ds locals body lifted localIH bodyIH tailIH =>
    have head := decsPreserve_local locals (compileDecs locals) body (compileDecs body) localIH bodyIH
    simpa only [compileDecs, lifted] using decsPreserve_cons (.dlocal locals body)
      (.dlocal (compileDecs locals) (compileDecs body)) ds (compileDecs ds) head tailIH
  | case5 d ds lifted noMod noLocal tailIH =>
    have head : DecsPreserve (F := F) [d] [d] := by
      intro state next env result source safe
      exact source
    have compiled : compileDecs (d :: ds) = d :: compileDecs ds := by
      cases d with
      | dmod name inner => exact (noMod name inner rfl).elim
      | dlocal locals body => exact (noLocal locals body rfl).elim
      | _ => simp [compileDecs, lifted]
    rw [compiled]
    exact decsPreserve_cons d d ds (compileDecs ds) head tailIH

/-- The original declaration-list evaluation preservation theorem for source
let-lifting, including the non-type-error hypothesis. -/
@[hol "cakeml/compiler/backend/proofs/source_letProofScript.sml" "compile_decs_correct"]
theorem compile_decs_correct {F : Type} (state next : State F) (env : SemEnv Value)
    (ds : List Dec) (result : Result (SemEnv Value) Value)
    (source : evaluateDecs state env ds = (next, result)) (safe : result ≠ .err (.abort .typeError)) :
    evaluateDecs state env (compileDecs ds) = (next, result) :=
  compileDecs_preserve ds state next env result source safe

end Flapjack.Compiler.Backend.SourceLet
