module

public import Flapjack.Compiler.Backend.Semantics.BviProps.AdjustOracle
public import Flapjack.Compiler.Backend.Semantics.BviProps.AdjustOracleEval
public import Flapjack.Compiler.Backend.Semantics.BviSem.EvaluateList
public import Flapjack.HolRef

@[expose] public section

/-!
# Adjusted-oracle predicates of HOL `bviProps`

Counterpart of `cakeml/compiler/backend/semantics/bviPropsScript.sml:743-766`:
`adj_orac_ok_def`, `adj_orac_rel_def` and `adj_orac_simps`. The projection-form
`adjustOracleOk` in `AdjustOracle.lean` stays untagged infrastructure; the
tagged definitions below follow HOL's binder and premise shape, and the
untagged `adjustOracleOkHOL_iff` relates the two.
-/

namespace Flapjack.Compiler.Backend.BviProps
open Flapjack.Compiler.Backend.BviSem
open Flapjack.Compiler.Backend.BvlSem (Value)
open Flapjack.SemanticPrimitivesHOL (Result ErrorResult Abort)

namespace AdjustOracleHOLCarrier
/-- Canonical BVI reference-map state representation roundtrip. -/
theorem holFmapAsFiniteSupportWitness {C F : Type} :
    (∀ s : BviStateBroad C F, (BviState.ofBroad s).toBroad = s) ∧
      (∀ s : BviState C F, BviState.ofBroad s.toBroad = s) :=
  BviSem.holFmapAsFiniteSupportWitness
end AdjustOracleHOLCarrier

/-- The adjusted callback agrees with the original at every oracle entry. -/
@[hol "cakeml/compiler/backend/semantics/bviPropsScript.sml" "adj_orac_ok_def"
  (fmap_as_finite_support := [refs])]
def adjustOracleOkHOL {C D F : Type} (compiler : Compiler D) (f : C → D)
    (state : BviState C F) : Prop :=
  ∀ (n : Nat) (x : C) (y : List (Nat × Nat × Bvi.Exp)),
    state.compileOracle n = (x, y) →
      Option.map (Prod.map id (Prod.map id f)) (state.compile x y) = compiler (f x) y

/-- A target state is the source state with its callback adjusted, provided
the callbacks agree at every oracle entry. -/
@[hol "cakeml/compiler/backend/semantics/bviPropsScript.sml" "adj_orac_rel_def"
  (fmap_as_finite_support := [refs])]
def adjustOracleRel {C D F : Type} (compiler : Compiler D) (f : C → D)
    (source : BviState C F) (target : BviState D F) : Prop :=
  adjustOracleOkHOL compiler f source ∧ target = adjustOracle compiler f source

/-- Flapjack helper: `Prod.map` written with projections. -/
theorem prodMap_eq {α β γ δ : Type} (f : α → γ) (g : β → δ) :
    Prod.map f g = fun x => (f x.1, g x.2) := by
  funext x
  cases x
  rfl

/-- Flapjack helper: the source-shaped callback agreement is the projection
form used by the untagged adjustment lemmas. -/
theorem adjustOracleOkHOL_iff {C D F : Type} (compiler : Compiler D) (f : C → D)
    (state : BviState C F) :
    adjustOracleOkHOL compiler f state ↔ adjustOracleOk compiler f state := by
  constructor
  · intro ok n
    have applied := ok n (state.compileOracle n).1 (state.compileOracle n).2 rfl
    simpa [adjustOracleOk, prodMap_eq] using applied
  · intro ok n x y found
    simp only [adjustOracleOk] at ok
    have applied := ok n
    simp only [found] at applied
    simpa [prodMap_eq] using applied

/-- The adjusted state keeps every runtime field, commutes with clock changes
and preserves callback agreement. -/
@[hol "cakeml/compiler/backend/semantics/bviPropsScript.sml" "adj_orac_simps"
  (fmap_as_finite_support := [refs])]
theorem adjustOracle_simps {C D F : Type} (compiler : Compiler D) (f : C → D)
    (state : BviState C F) (n k : Nat) :
    (adjustOracle compiler f state).clock = state.clock ∧
      (adjustOracle compiler f state).code = state.code ∧
      (adjustOracle compiler f state).refs = state.refs ∧
      (adjustOracle compiler f state).global = state.global ∧
      (adjustOracle compiler f state).ffi = state.ffi ∧
      decClock n (adjustOracle compiler f state) = adjustOracle compiler f (decClock n state) ∧
      { adjustOracle compiler f state with clock := k } =
        adjustOracle compiler f { state with clock := k } ∧
      (adjustOracleOkHOL compiler f (decClock n state) ↔ adjustOracleOkHOL compiler f state) ∧
      (adjustOracleOkHOL compiler f { state with clock := k } ↔
        adjustOracleOkHOL compiler f state) := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_, ?_⟩
  · rfl
  · rfl

/-- Successful installation commutes with oracle adjustment and preserves
callback agreement. -/
@[hol "cakeml/compiler/backend/semantics/bviPropsScript.sml" "do_install_adj_orac"
  (fmap_as_finite_support := [refs])]
theorem adjustOracle_doInstall {C D F : Type} (args : List Value) (state : BviState C F)
    (value : Value) (next : BviState C F) (compiler : Compiler D) (f : C → D)
    (premise : adjustOracleOkHOL compiler f state ∧
      (doInstall (R := ExnOrRet) args state = .val (value, next))) :
    (doInstall (R := ExnOrRet) args (adjustOracle compiler f state) =
        .val (value, adjustOracle compiler f next)) ∧ adjustOracleOkHOL compiler f next := by
  obtain ⟨ok, run⟩ := premise
  have okProj := (adjustOracleOkHOL_iff compiler f state).1 ok
  have applied := doInstall_adjustOracle compiler f args state next value okProj run
  exact ⟨applied.1, (adjustOracleOkHOL_iff compiler f next).2 applied.2⟩

/-- Primitive application commutes with oracle adjustment: successful results
carry the adjusted state and callback agreement, non-type errors are unchanged. -/
@[hol "cakeml/compiler/backend/semantics/bviPropsScript.sml" "do_app_adj_orac"
  (fmap_as_finite_support := [refs])]
theorem adjustOracle_doApp {C D F : Type} (compiler : Compiler D) (f : C → D)
    (state : BviState C F) (op : ClosLang.Op) (args : List Value)
    (ok : adjustOracleOkHOL compiler f state) :
    (∀ (value : Value) (next : BviState C F), doApp op args state = .val (value, next) →
      doApp op args (adjustOracle compiler f state) =
          .val (value, adjustOracle compiler f next) ∧
        adjustOracleOkHOL compiler f next) ∧
      (∀ (error : ErrorResult ExnOrRet), doApp op args state = .err error ∧
          error ≠ .abort .typeError →
        doApp op args (adjustOracle compiler f state) = .err error) := by
  have okProj := (adjustOracleOkHOL_iff compiler f state).1 ok
  constructor
  · intro value next run
    have applied := doApp_adjustOracle_success compiler f op args state next value okProj run
    exact ⟨applied.1, (adjustOracleOkHOL_iff compiler f next).2 applied.2⟩
  · intro error run
    obtain ⟨runErr, notType⟩ := run
    exact doApp_adjustOracle_error compiler f op args state error notType runErr

/-- The disabled pass's initial state adjusts to the downstream initial state. -/
@[hol "cakeml/compiler/backend/semantics/bviPropsScript.sml" "adj_orac_initial_state"
  (fmap_as_finite_support := [refs])]
theorem adjustOracle_initial_state {C D F : Type} (compiler : Compiler D)
    (ffi : HolFfiState F) (code : Spt (Nat × Bvi.Exp)) (oracle : CompileOracle (C × D))
    (clock : Nat) :
    adjustOracle compiler Prod.snd
        (initialState ffi code oracle (BackendProps.stateCc (Function.curry id) compiler) clock :
          BviState (C × D) F) =
      (initialState ffi code (BackendProps.stateCo (Function.curry id) oracle) compiler clock :
        BviState D F) :=
  adjustOracle_identity_initial ffi code oracle compiler clock

/-- The disabled pass's initial state satisfies callback agreement. -/
@[hol "cakeml/compiler/backend/semantics/bviPropsScript.sml" "adj_orac_ok_initial_state"
  (fmap_as_finite_support := [refs])]
theorem adjustOracleOk_initial_state {C D F : Type} (compiler : Compiler D)
    (ffi : HolFfiState F) (code : Spt (Nat × Bvi.Exp)) (oracle : CompileOracle (C × D))
    (clock : Nat) :
    adjustOracleOkHOL compiler Prod.snd
      (initialState ffi code oracle (BackendProps.stateCc (Function.curry id) compiler) clock :
        BviState (C × D) F) :=
  (adjustOracleOkHOL_iff compiler Prod.snd _).2
    (adjustOracleOk_identity_initial ffi code oracle compiler clock)

/-- Evaluation whose result is not a type error commutes with oracle
adjustment and preserves callback agreement. -/
@[hol "cakeml/compiler/backend/semantics/bviPropsScript.sml" "evaluate_adj_orac"
  (fmap_as_finite_support := [refs])]
theorem evaluate_adj_orac {C D F : Type} (expressions : List Bvi.Exp) (env : List Value)
    (state : BviState C F) (result : BviResult) (next : BviState C F)
    (compiler : Compiler D) (f : C → D)
    (premise : evaluateTuple (expressions, env, state) = (result, next) ∧
      result ≠ .err (.abort .typeError) ∧ adjustOracleOkHOL compiler f state) :
    evaluateTuple (expressions, env, adjustOracle compiler f state) =
        (result, adjustOracle compiler f next) ∧ adjustOracleOkHOL compiler f next := by
  obtain ⟨run, notType, ok⟩ := premise
  have okProj := (adjustOracleOkHOL_iff compiler f state).1 ok
  rw [evaluateTuple] at run ⊢
  have applied := evaluate_adjustOracle compiler f expressions env state next result run
    notType okProj
  exact ⟨applied.1, (adjustOracleOkHOL_iff compiler f next).2 applied.2⟩

/-- Evaluation of the disabled pass's initial state agrees with the downstream
initial state up to the oracle adjustment, keeping the FFI state. -/
@[hol "cakeml/compiler/backend/semantics/bviPropsScript.sml" "evaluate_CURRY_I"
  (fmap_as_finite_support := [refs])]
theorem evaluate_CURRY_I {C D F : Type} (expressions : List Bvi.Exp) (env : List Value)
    (ffi : HolFfiState F) (code : Spt (Nat × Bvi.Exp)) (oracle : CompileOracle (C × D))
    (compiler : Compiler D) (clock : Nat) (result : BviResult)
    (state : BviState (C × D) F)
    (premise : evaluateTuple (expressions, env,
        (initialState ffi code oracle (BackendProps.stateCc (Function.curry id) compiler) clock :
          BviState (C × D) F)) = (result, state) ∧
      result ≠ .err (.abort .typeError)) :
    ∃ next : BviState D F,
      evaluateTuple (expressions, env,
        (initialState ffi code (BackendProps.stateCo (Function.curry id) oracle) compiler clock :
          BviState D F)) = (result, next) ∧ next.ffi = state.ffi := by
  obtain ⟨run, notType⟩ := premise
  have ok := adjustOracleOk_initial_state compiler ffi code oracle clock
  have applied := evaluate_adj_orac expressions env
    (initialState ffi code oracle (BackendProps.stateCc (Function.curry id) compiler) clock)
    result state compiler Prod.snd ⟨run, notType, ok⟩
  refine ⟨adjustOracle compiler Prod.snd state, ?_, ?_⟩
  · rw [← adjustOracle_initial_state]
    exact applied.1
  · exact (adjustOracle_simps compiler Prod.snd state 0 0).2.2.2.2.1

end Flapjack.Compiler.Backend.BviProps
