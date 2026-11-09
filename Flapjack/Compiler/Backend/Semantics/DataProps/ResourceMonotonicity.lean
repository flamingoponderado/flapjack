module

public import Flapjack.Compiler.Backend.Semantics.DataProps.PrimitiveResources

-- Proofs below unfold private helpers of these modules.
import all Flapjack.Compiler.Backend.Semantics.DataSem.Evaluate
@[expose] public section

/-! Compositional source event and resource monotonicity. -/
namespace Flapjack.Compiler.Backend.DataSem
open Flapjack Flapjack.SemanticPrimitivesHOL

/-- Flapjack induction property toward the source evaluator's event, stack,
and safety monotonicity theorems. It applies to the actual evaluator result. -/
def ResourceMono {C F : Type} (program : DataLang.Prog) (state : State C F) : Prop :=
  state.ffi.ioEvents <+: (evaluate program state).2.ffi.ioEvents ∧
  BackendProps.optionLe state.stackMax (evaluate program state).2.stackMax ∧
  ((evaluate program state).2.safeForSpace = true → state.safeForSpace = true)

/-- Skipping preserves all three observations. -/
theorem resourceMono_skip {C F : Type} (state : State C F) : ResourceMono .skip state := by
  simp [ResourceMono, evaluate, BackendProps.optionLe_refl]

/-- A local move either preserves resource fields or reports a type error. -/
theorem resourceMono_move {C F : Type} (dest src : Nat) (state : State C F) :
    ResourceMono (.move dest src) state := by
  cases found : getVar src state.locals <;>
    simp [ResourceMono, evaluate, found, setVar, BackendProps.optionLe_refl]

/-- Clock exhaustion and decrement both leave resource observations intact. -/
theorem resourceMono_tick {C F : Type} (state : State C F) : ResourceMono .tick state := by
  by_cases zero : state.clock = 0 <;>
    simp [ResourceMono, evaluate, zero, flushState, decClock, BackendProps.optionLe_refl]

/-- Returning a value list preserves the observed resource fields, including
the failed-variable-lookup case. -/
theorem resourceMono_return {C F : Type} (names : List Nat) (state : State C F) :
    ResourceMono (.return names) state := by
  cases found : getVars names state.locals <;>
    simp [ResourceMono, evaluate, found, flushState, BackendProps.optionLe_refl]

/-- A successful exception jump changes only local and control data. -/
theorem jumpExc_resource_frame {C F : Type} (state next : State C F)
    (run : jumpExc state = some next) :
    next.ffi = state.ffi ∧ next.stackMax = state.stackMax ∧ next.safeForSpace = state.safeForSpace := by
  unfold jumpExc at run
  split at run
  · split at run
    · simp only [Option.some.injEq] at run
      subst next
      exact ⟨rfl, rfl, rfl⟩
    · contradiction
  · contradiction

/-- Raising either jumps to a saved handler or reports a type error; neither
case changes the three resource observations. -/
theorem resourceMono_raise {C F : Type} (name : Nat) (state : State C F) :
    ResourceMono (.raise name) state := by
  cases found : getVar name state.locals with
  | none => simp [ResourceMono, evaluate, found, BackendProps.optionLe_refl]
  | some value =>
    cases jump : jumpExc state with
    | none => simp [ResourceMono, evaluate, found, jump, BackendProps.optionLe_refl]
    | some next =>
      obtain ⟨ffi, stack, safe⟩ := jumpExc_resource_frame state next jump
      simp [ResourceMono, evaluate, found, jump, ffi, stack, safe, BackendProps.optionLe_refl]

/-- A successful live-variable cut preserves the observed resources. -/
theorem cutStateOpt_resource_frame {C F : Type} (names : Option NumSet) (state next : State C F)
    (run : cutStateOpt names state = some next) :
    next.ffi = state.ffi ∧ next.stackMax = state.stackMax ∧ next.safeForSpace = state.safeForSpace := by
  cases names with
  | none => simp [cutStateOpt] at run; subst next; exact ⟨rfl, rfl, rfl⟩
  | some names =>
    cases cut : cutEnv names state.locals with
    | none => simp [cutStateOpt, cutState, cut] at run
    | some env =>
      simp [cutStateOpt, cutState, cut] at run
      subst next
      exact ⟨rfl, rfl, rfl⟩

/-- Every successful source primitive application satisfies the event,
stack and safety properties required by the evaluator induction. -/
theorem doApp_resource_frame {C F : Type} (op : ClosLang.Op) (args : List Value)
    (state next : State C F) (value : Value)
    (run : doApp op args state = .val (value, next)) :
    state.ffi.ioEvents <+: next.ffi.ioEvents ∧ BackendProps.optionLe state.stackMax next.stackMax ∧
      (next.safeForSpace = true → state.safeForSpace = true) := by
  by_cases install : op = .install
  · subst op
    exact doApp_install_resource_frame args state next value run
  · simp only [doApp] at run
    repeat' (split at run <;> try simp_all)
    all_goals exact accounted_resource_frame op args state _ next value (by assumption) run

/-- Every assignment is resource-monotone, including failed reads, cuts and primitive errors. -/
theorem resourceMono_assign_all {C F : Type} (dest : Nat) (op : ClosLang.Op) (names : List Nat)
    (live : Option NumSet) (state : State C F) :
    ResourceMono (.assign dest op names live) state := by
  by_cases bad : (DataLang.opRequiresNames op == live.isNone) = true
  · simp [ResourceMono, evaluate, bad, BackendProps.optionLe_refl]
  · cases reads : getVars names state.locals with
    | none => simp [ResourceMono, evaluate, bad, reads, BackendProps.optionLe_refl]
    | some values =>
      cases cut : cutStateOpt live state with
      | none => simp [ResourceMono, evaluate, bad, reads, cut, BackendProps.optionLe_refl]
      | some prepared =>
        obtain ⟨ffi, stack, safe⟩ := cutStateOpt_resource_frame live state prepared cut
        cases application : doApp op values prepared with
        | err error =>
          cases op <;> simp [ResourceMono, evaluate, bad, reads, cut, application, flushState,
            installSfs, ffi, stack, safe, BackendProps.optionLe_refl]
        | val pair =>
          obtain ⟨value, after⟩ := pair
          obtain ⟨events, bound, safeBefore⟩ := doApp_resource_frame op values prepared after value application
          cases op <;> simp [ResourceMono, evaluate, bad, reads, cut, application, setVar,
            installSfs, ffi, stack, safe] at events bound safeBefore ⊢ <;> tauto

/-- Clock-bounded form of sequence composition for the well-founded source
evaluator induction. -/
theorem resourceMono_seq_bounded {C F : Type} (first second : DataLang.Prog) (state : State C F)
    (firstMono : ResourceMono first state)
    (secondMono : ∀ next : State C F, next.clock ≤ state.clock → ResourceMono second next) :
    ResourceMono (.seq first second) state := by
  cases firstRun : evaluate first state with
  | mk result mid =>
    have firstFacts : state.ffi.ioEvents <+: mid.ffi.ioEvents ∧
        BackendProps.optionLe state.stackMax mid.stackMax ∧
        (mid.safeForSpace = true → state.safeForSpace = true) := by
      simpa [ResourceMono, firstRun] using firstMono
    cases result with
    | some result =>
      simpa [ResourceMono, evaluate, firstRun, fixClock] using firstFacts
    | none =>
      let clamped := { mid with clock := min state.clock mid.clock }
      have bound : clamped.clock ≤ state.clock := by simp [clamped]
      have secondFacts := secondMono clamped bound
      have seqRun : evaluate (.seq first second) state = evaluate second clamped := by
        simp [evaluate, firstRun, fixClock, clamped]
      rw [ResourceMono, seqRun]
      refine ⟨?_, ?_, ?_⟩
      · exact List.IsPrefix.trans firstFacts.1 secondFacts.1
      · exact BackendProps.optionLe_trans _ _ _ ⟨firstFacts.2.1, secondFacts.2.1⟩
      · exact fun safe => firstFacts.2.2 (secondFacts.2.2 safe)

/-- A conditional inherits source resource monotonicity from either branch. -/
theorem resourceMono_if {C F : Type} (name : Nat) (yes no : DataLang.Prog) (state : State C F)
    (yesMono : ResourceMono yes state) (noMono : ResourceMono no state) :
    ResourceMono (.ifThenElse name yes no) state := by
  cases found : getVar name state.locals with
  | none => simp [ResourceMono, evaluate, found, BackendProps.optionLe_refl]
  | some value =>
    by_cases yes : isBool true value
    · simpa [ResourceMono, evaluate, found, yes] using yesMono
    · by_cases no : isBool false value
      · simpa [ResourceMono, evaluate, found, yes, no] using noMono
      · simp [ResourceMono, evaluate, found, yes, no, BackendProps.optionLe_refl]

/-- Source allocation bookkeeping itself satisfies the three properties,
including when cutting the environment fails. -/
theorem resourceMono_makeSpace {C F : Type} (amount : Nat) (names : NumSet) (state : State C F) :
    ResourceMono (.makeSpace amount names) state := by
  cases cut : cutEnv names state.locals with
  | none => simp [ResourceMono, evaluate, cut, BackendProps.optionLe_refl]
  | some env =>
    simp [ResourceMono, evaluate, cut, addSpace, BackendProps.optionLe_refl]
    tauto

end Flapjack.Compiler.Backend.DataSem
