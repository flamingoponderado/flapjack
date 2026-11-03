import Flapjack.Compiler.Backend.ClosKnown.Proofs.ApproxGlobalSafety
import Flapjack.Compiler.Backend.ClosKnown.Proofs.Syntax
import Flapjack.Compiler.Backend.ClosKnown.Proofs.MappedGlobals
import Flapjack.Compiler.Backend.Semantics.ClosProps.GlobalSafety
import Flapjack.Compiler.Backend.Semantics.ClosSem.Install

/-! Global-write safety of dynamic closure-code installation. -/
namespace Flapjack.Compiler.Backend.ClosKnown
open ClosSem ClosProps ClosProps.StateGlobalSafety
open Flapjack.SemanticPrimitivesHOL
open FlatProps (emptyGlobalBag)

/-- The state representation used by the installation safety results. -/
theorem holFmapAsFiniteSupportWitness {C F : Type} :
    (∀ s : StateBroad C F, (State.ofBroad s).toBroad = s) ∧
      (∀ s : State C F, State.ofBroad s.toBroad = s) :=
  ClosSem.holFmapAsFiniteSupportWitness

/-- The first `n` programs in a polymorphic compile oracle. -/
@[hol "cakeml/compiler/backend/proofs/clos_knownProofScript.sml" "first_n_exps_def"]
def firstNExps {α β γ : Type} (co : Nat → β × α × γ) (n : Nat) : List α :=
  List.ofFn (fun i : Fin n => (co i.val).2.1)

/-- Splitting the sequence of installed programs follows oracle shifts. -/
@[hol "cakeml/compiler/backend/proofs/clos_knownProofScript.sml" "first_n_exps_shift_seq"]
theorem firstNExpsShiftSeq {α β γ : Type} (co : Nat → α × β × γ) (n k : Nat) :
    firstNExps co (n + k) = firstNExps co k ++ firstNExps (Flapjack.holShiftSeq k co) n := by
  rw [Nat.add_comm n k]
  simp [firstNExps, List.ofFn_add, Flapjack.holShiftSeq, Nat.add_comm]

/-- The global-write set of two successive oracle prefixes is their union.
This is a Lean helper for the evaluator induction, with no separate HOL declaration. -/
theorem firstNExpsWritesShift {α γ : Type} (co : Nat → α × List ClosLang.Exp × γ)
    (n k : Nat) :
    {i | elistGlobals (List.flatten (firstNExps co (n + k))) i ≠ 0} =
      {i | elistGlobals (List.flatten (firstNExps co k)) i ≠ 0} ∪
      {i | elistGlobals (List.flatten (firstNExps (Flapjack.holShiftSeq k co) n)) i ≠ 0} := by
  ext i
  rw [firstNExpsShiftSeq]
  simp [elistGlobals_append]
  classical
  by_cases h : elistGlobals (List.flatten (firstNExps co k)) i = 0 <;> simp_all

/-- Every oracle program at an index below the limit occurs in the prefix. -/
@[hol "cakeml/compiler/backend/proofs/clos_knownProofScript.sml" "MEM_first_n_exps"]
theorem memFirstNExps {α β γ : Type} (k n : Nat) (bound : k < n)
    (co : Nat → α × β × γ) : (co k).2.1 ∈ firstNExps co n := by
  exact List.mem_ofFn.mpr ⟨⟨k, bound⟩, rfl⟩

/-- Shifting an oracle by zero leaves it unchanged. -/
@[hol "cakeml/compiler/backend/proofs/clos_knownProofScript.sml" "shift_seq_zero"]
theorem shiftSeqZero {α : Type} (co : Nat → α) : Flapjack.holShiftSeq 0 co = co := by
  funext n
  simp [Flapjack.holShiftSeq]

/-- Successive oracle shifts add their offsets. -/
@[hol "cakeml/compiler/backend/proofs/clos_knownProofScript.sml" "shift_seq_add"]
theorem shiftSeqAdd {α : Type} (co : Nat → α) (k1 k2 : Nat) :
    Flapjack.holShiftSeq k2 (Flapjack.holShiftSeq k1 co) = Flapjack.holShiftSeq (k1 + k2) co := by
  funext n
  simp [Flapjack.holShiftSeq, Nat.add_comm, Nat.add_left_comm]

/-- Advancing a safe oracle preserves global-write safety. -/
@[hol "cakeml/compiler/backend/proofs/clos_knownProofScript.sml" "ssgc_free_co_shift_seq"
  (fmap_as_finite_support := [refs, code])]
theorem ssgcFreeCoShiftSeq {C F : Type} (s : State C F) (safe : ssgcFree s) :
    ∀ k, ssgcFree {s with compileOracle := Flapjack.holShiftSeq k s.compileOracle} := by
  intro k
  rcases safe with ⟨code, arrays, thunks, globals, oracle⟩
  refine ⟨code, arrays, thunks, globals, ?_⟩
  intro n es aux found
  exact oracle (n + k) es aux found

/-- Updating a code map with safe entries preserves safety of every lookup.
This is a Lean helper without a separate HOL declaration. -/
private theorem safeCodeUpdateList (code : HolFiniteMapExact Nat (Nat × ClosLang.Exp))
    (entries : List (Nat × Nat × ClosLang.Exp))
    (codeSafe : ∀ n arity body, code.lookup n = some (arity, body) →
      setGlobals body = emptyGlobalBag)
    (entriesSafe : ∀ n arity body, (n, arity, body) ∈ entries →
      setGlobals body = emptyGlobalBag) :
    ∀ n arity body, (code.updateListEq entries).lookup n = some (arity, body) →
      setGlobals body = emptyGlobalBag := by
  induction entries generalizing code with
  | nil => simpa [HolFiniteMapExact.lookup_updateListEq] using codeSafe
  | cons entry rest ih =>
    rcases entry with ⟨index, arity, body⟩
    have headSafe := entriesSafe index arity body (by simp)
    have updateSafe : ∀ n a b, (code.updateEq (index, arity, body)).lookup n =
        some (a, b) → setGlobals b = emptyGlobalBag := by
      intro n a b found
      by_cases eq : n = index
      · simp [HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL, eq] at found
        rcases found with ⟨_, rfl⟩
        exact headSafe
      · apply codeSafe n a b
        simpa [HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL, eq] using found
    have tailSafe : ∀ n arity body, (n, arity, body) ∈ rest →
        setGlobals body = emptyGlobalBag := by
      intro n a b member
      exact entriesSafe n a b (by simp [member])
    simpa [HolFiniteMapExact.lookup_updateListEq, FUPDATE_LIST_HOL_cons,
      HolFiniteMapExact.updateEq] using ih (code.updateEq (index, arity, body)) updateSafe tailSafe

/-- Installing the oracle's auxiliary code and shifting it preserves safety. -/
@[hol "cakeml/compiler/backend/proofs/clos_knownProofScript.sml" "ssgc_free_do_install"
  (fmap_as_finite_support := [refs, code])]
theorem ssgcFreeDoInstall {C F : Type} (s : State C F) (safe : ssgcFree s) :
    ssgcFree {s with compileOracle := Flapjack.holShiftSeq 1 s.compileOracle, code := s.code.updateListEq (s.compileOracle 0).2.2} := by
  rcases safe with ⟨code, arrays, thunks, globals, oracle⟩
  refine ⟨?_, arrays, thunks, globals, ?_⟩
  · apply safeCodeUpdateList _ _ code
    intro n arity body member
    have allSafe := (elistGlobalsEmpty _).1 (oracle 0 _ _ rfl).2
    apply allSafe body
    exact List.mem_map.mpr ⟨(n, arity, body), member, rfl⟩
  · intro n es aux found
    exact oracle (n + 1) es aux found


/-- Successful dynamic installation preserves safety and exposes the
installed program and advanced oracle. -/
@[hol "cakeml/compiler/backend/proofs/clos_knownProofScript.sml" "do_install_ssgc"
  (fmap_as_finite_support := [refs, code])]
theorem doInstallSsgc {C F : Type} (values : List ClosSem.Value) (s0 : State C F)
    (es : List ClosLang.Exp) (s1 : State C F)
    (h : doInstall values s0 = (.val es, s1) ∧ ssgcFree s0) :
    ssgcFree s1 ∧ (∀ e ∈ es, esgcFree e) ∧ es ≠ [] ∧
      s1.compileOracle = Flapjack.holShiftSeq 1 s0.compileOracle ∧
      firstNExps s0.compileOracle 1 = [es] ∧
      mglobalsExtend s0.globals ∅ s1.globals := by
  rcases h with ⟨run, safe⟩
  unfold doInstall at run
  repeat' split at run
  all_goals simp_all
  all_goals split at run <;> simp_all
  rcases run with ⟨_, rfl⟩
  have installed := ssgcFreeDoInstall s0 safe
  have oracleSafe := safe.2.2.2.2 0 _ _ (Prod.eta _)
  have esSafe : ∀ e ∈ es, esgcFree e := by simpa [*] using oracleSafe.1
  refine ⟨?_, esSafe, rfl, ?_, mglobalsExtendRefl _ _⟩
  · simpa [ssgcFree, *] using installed
  · simp [firstNExps, *]


/-- A failed installation preserves safety and globals while advancing the
oracle by a finite shift. This helper has no separate HOL declaration. -/
theorem doInstallErrorSafety {C F : Type} (values : List ClosSem.Value)
    (s0 s1 : ClosSem.State C F) (error : ErrorResult ClosSem.Value)
    (safe : ssgcFree s0) (run : doInstall values s0 = (.err error, s1)) :
    ssgcFree s1 ∧ rsgcFree (.err error) ∧ ∃ n,
      s1.compileOracle = Flapjack.holShiftSeq n s0.compileOracle ∧ s1.globals = s0.globals := by
  unfold doInstall at run
  repeat' split at run
  all_goals simp_all
  all_goals try (solve | rcases run with ⟨rfl, _⟩; exact ⟨by simp [rsgcFree], 0, shiftSeqZero _⟩)
  all_goals split at run <;> simp_all
  all_goals try (solve | rcases run with ⟨rfl, _⟩; exact ⟨by simp [rsgcFree], 0, shiftSeqZero _⟩)
  rcases run with ⟨rfl, rfl⟩
  have installed := ssgcFreeDoInstall s0 safe
  refine ⟨?_, by simp [rsgcFree], ⟨1, rfl⟩, rfl⟩
  simpa [ssgcFree, *] using installed

end Flapjack.Compiler.Backend.ClosKnown
