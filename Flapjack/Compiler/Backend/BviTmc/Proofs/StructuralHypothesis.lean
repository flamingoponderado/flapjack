import Flapjack.Compiler.Backend.BviTmc.Proofs.ExtractionSafety
import Flapjack.Compiler.Backend.BviTmc.Proofs.OperationSimulation
import Flapjack.Compiler.Backend.BviTmc.Proofs.VariableSimulation

/-! Same-clock structural induction for TMC evaluation. -/
namespace Flapjack.Compiler.Backend.BviTmc.StructuralHypothesis
open BviTmc BviSem BvlSem ListSimulation ClockHypothesis

/-- Flapjack infrastructure: ordinary list simulation and, when the list is
a singleton, its wrapper and worker simulation conclusions. -/
def GeneralPost {C F : Type} (xs : List Bvi.Exp) (source : BviState (Nat × C) F)
    (target : BviState C F) (env1 env2 : List Value) (opt : Bool) (f : HolFiniteMapExact Nat Nat)
    (loc : Nat) (result : BviResult) (final : BviState (Nat × C) F) : Prop :=
  Core xs env2 f target result final ∧
    ∀ e, xs = [e] → SingletonPost e source target env1 env2 opt f loc result final

/-- Flapjack infrastructure: simulations of expression lists of smaller
structural weight at clocks no greater than the current clock. -/
def SmallerWeightIH {C F : Type} (clock weight : Nat) : Prop :=
  ∀ (xs : List Bvi.Exp) (source : BviState (Nat × C) F) (target : BviState C F)
    (env1 env2 : List Value) (opt : Bool) (f : HolFiniteMapExact Nat Nat) (loc : Nat)
    (result : BviResult) (final : BviState (Nat × C) F),
    source.clock ≤ clock → expsWeight xs < weight → evaluate xs env1 source = (result, final) →
    (∀ e ∈ xs, noMutcons e) → envRel opt f env1 env2 → stateRel f source target →
    (opt = true → xs.length = 1) → result ≠ .err (.abort .typeError) →
    GeneralPost xs source target env1 env2 opt f loc result final

/-- Flapjack infrastructure: a non-singleton expression list is simulated
from the smaller-weight induction hypothesis. -/
theorem evaluate_cons_cons_from_weight {C F : Type} (first second : Bvi.Exp) (rest : List Bvi.Exp)
    (source : BviState (Nat × C) F) (target : BviState C F) (env1 env2 : List Value)
    (opt : Bool) (f : HolFiniteMapExact Nat Nat) (loc : Nat) (result : BviResult)
    (final : BviState (Nat × C) F)
    (run : evaluate (first :: second :: rest) env1 source = (result, final))
    (safe : ∀ e ∈ first :: second :: rest, noMutcons e) (environments : envRel opt f env1 env2)
    (states : stateRel f source target) (optLength : opt = true → (first :: second :: rest).length = 1)
    (notTypeError : result ≠ .err (.abort .typeError))
    (ih : SmallerWeightIH (C := C) (F := F) source.clock (expsWeight (first :: second :: rest))) :
    GeneralPost (first :: second :: rest) source target env1 env2 opt f loc result final := by
  have optFalse : opt = false := by
    cases opt with
    | false => rfl
    | true => have impossible := optLength rfl; simp at impossible
  have falseEnv : envRel false f env1 env2 := by simpa [optFalse] using environments
  have headWeight : expsWeight [first] < expsWeight (first :: second :: rest) := by
    simp only [BviSem.expsWeight]
    have positive := BviSem.expWeight_pos second
    omega
  have tailWeight : expsWeight (second :: rest) < expsWeight (first :: second :: rest) := by
    simp only [BviSem.expsWeight]
    omega
  have headSafe : noMutcons first := safe first (by simp)
  have tailSafe : ∀ e ∈ second :: rest, noMutcons e := fun e member => safe e (by simp [member])
  refine ⟨?_, ?_⟩
  · apply evaluate_cons_cons first second rest source env1 result final f target env2 run notTypeError falseEnv
    · intro r mid headRun noError
      exact (ih [first] source target env1 env2 false f loc r mid (Nat.le_refl _) headWeight headRun
        (by simpa using headSafe) falseEnv states (by simp) noError).1
    · intro r mid g t ⟨value, headRun⟩ tailRun env nextStates noError
      have clock := evaluate_clock_le [first] env1 source
      rw [headRun] at clock
      exact (ih (second :: rest) mid t env1 env2 false g loc r final clock tailWeight tailRun
        tailSafe env nextStates (by simp) noError).1
  · intro e impossible
    simp at impossible

/-- Flapjack infrastructure: the extracted-expression singleton case follows
from the common smaller-weight and smaller-clock induction hypotheses. -/
theorem evaluate_extracted_from_weight {C F : Type} (loc : Nat) (cb : CallBlock) (e : Bvi.Exp)
    (bindings : List Bvi.Exp) (source : BviState (Nat × C) F) (target : BviState C F)
    (env1 env2 : List Value) (opt : Bool) (f : HolFiniteMapExact Nat Nat) (result : BviResult)
    (final : BviState (Nat × C) F) (run : evaluate [e] env1 source = (result, final))
    (extracted : toBlockSource env1.length loc e = some (bindings, cb))
    (notTypeError : result ≠ .err (.abort .typeError)) (safe : noMutcons e)
    (environments : envRel opt f env1 env2) (states : stateRel f source target)
    (weightIH : SmallerWeightIH (C := C) (F := F) source.clock (expsWeight [e]))
    (clockIH : SmallerClockIH (C := C) (F := F) source.clock) :
    SingletonPost e source target env1 env2 opt f loc result final := by
  apply ExtractionSafety.evaluate_extracted_from_structural_induction loc cb e bindings source target env1 env2
    opt f result final run extracted notTypeError safe environments states ?_ clockIH
  intro xs smaller safeXs r mid xsRun noError
  have smallerList : expsWeight xs < expsWeight [e] := by
    simp only [BviSem.expsWeight]
    omega
  exact (weightIH xs source target env1 env2 false f loc r mid (Nat.le_refl _) smallerList xsRun safeXs
    (envRel_relax opt f env1 env2 environments) states (by simp) noError).1

/-- Flapjack infrastructure: the non-extracted primitive-operation case
follows from the common smaller-weight induction hypothesis. -/
theorem evaluate_op_from_weight {C F : Type} (loc : Nat) (op : ClosLang.Op) (args : List Bvi.Exp)
    (source : BviState (Nat × C) F) (target : BviState C F) (env1 env2 : List Value)
    (opt : Bool) (f : HolFiniteMapExact Nat Nat) (result : BviResult) (final : BviState (Nat × C) F)
    (run : evaluate [.op op args] env1 source = (result, final))
    (notTypeError : result ≠ .err (.abort .typeError)) (safe : noMutcons (.op op args))
    (environments : envRel opt f env1 env2) (states : stateRel f source target)
    (notExtracted : toBlockSource env1.length loc (.op op args) = none)
    (ih : SmallerWeightIH (C := C) (F := F) source.clock (expsWeight [.op op args])) :
    SingletonPost (.op op args) source target env1 env2 opt f loc result final := by
  rw [noMutcons.eq_def] at safe
  dsimp only at safe
  have argWeight : expsWeight args < expsWeight [.op op args] := by
    simp [BviSem.expsWeight, BviSem.expWeight]
    omega
  have argsSafe : ∀ e ∈ args, noMutcons e := fun e member => safe.2 ⟨e, member⟩
  have argsIH : ∀ r mid, evaluate args env1 source = (r, mid) →
      r ≠ .err (.abort .typeError) → Core args env2 f target r mid := by
    intro r mid argsRun noError
    exact (ih args source target env1 env2 false f loc r mid (Nat.le_refl _) argWeight argsRun argsSafe
      (envRel_relax opt f env1 env2 environments) states (by simp) noError).1
  exact OperationSimulation.evaluate_op_non_extracted op args source env1 result final opt f target env2 loc
    run notTypeError safe.1 environments states notExtracted argsIH

/-- Flapjack infrastructure: the variable case in the shared singleton-post
form used by the structural induction. -/
theorem evaluate_variable_post {C F : Type} (loc index : Nat) (source : BviState (Nat × C) F)
    (target : BviState C F) (env1 env2 : List Value) (opt : Bool) (f : HolFiniteMapExact Nat Nat)
    (result : BviResult) (final : BviState (Nat × C) F)
    (run : evaluate [.var index] env1 source = (result, final))
    (notTypeError : result ≠ .err (.abort .typeError)) (environments : envRel opt f env1 env2)
    (states : stateRel f source target) : SingletonPost (.var index) source target env1 env2 opt f loc result final := by
  obtain ⟨next, g, targetResult, targetRun, related, nextStates, extension, fresh, unchanged, still, optimized⟩ :=
    VariableSimulation.evaluate_variable index source env1 result final opt f target env2 loc run environments states notTypeError
  refine ⟨⟨next, g, targetResult, targetRun, related, nextStates, extension, fresh, unchanged, still⟩, ?_⟩
  intro dest code
  obtain ⟨wrap, worker⟩ := optimized dest code
  constructor
  · intro wrapper rewrite
    exact wrap wrapper ⟨rfl, rewrite⟩
  · intro optTrue ptr c hole notFinal pointer
    exact worker optTrue env1.length (env1.length + 1) ptr
      (rewriteWorkerSource loc dest env1.length (env1.length + 1) env1.length (.var index))
      ⟨rfl, rfl, ⟨c, hole⟩, notFinal, rfl, pointer⟩

end Flapjack.Compiler.Backend.BviTmc.StructuralHypothesis
