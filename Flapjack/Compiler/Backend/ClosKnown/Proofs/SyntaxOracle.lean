import Flapjack.Compiler.Backend.ClosKnown.Proofs.StateOracle
import Flapjack.Compiler.Backend.ClosKnown.Proofs.Syntax
import Flapjack.Compiler.Backend.BackendProps.OracleMonotonic
import Flapjack.Compiler.Backend.BackendProps.Pure
import Flapjack.Compiler.Backend.ClosFvs.Proofs.Syntax
import Flapjack.Compiler.Backend.ClosKnown.Proofs.OracleGlobals
import Flapjack.Compiler.Backend.ClosKnown.Proofs.KnownSubspt
import Flapjack.Compiler.Backend.ClosKnown.Proofs.OracleMonotonic

/-! Source syntax and oracle preconditions for the known-function pass. -/
namespace Flapjack.Compiler.Backend.ClosKnown
open ClosLang ClosProps BackendProps
open Relations.StateRelation.Oracle PreserveSafety
open OracleGlobals UniqueGlobalsPort KnownSubspt OracleMonotonic

/-- The source optimizer's assumptions on its future compilation oracle. -/
@[hol "cakeml/compiler/backend/proofs/clos_knownProofScript.sml" "syntax_oracle_ok_def"]
def syntaxOracleOk {C : Type} (c : Config) (xs : List ClosLang.Exp)
    (co : Nat → (Spt ValApprox × C) × (List ClosLang.Exp × List (Nat × Nat × ClosLang.Exp)))
    (conf : Spt ValApprox) : Prop :=
  syntaxOk xs ∧
  isStateOracle (compileInc (α := List (Nat × Nat × ClosLang.Exp)) c)
    (pureCo (ClosFvs.compileInc (β := Nat × Nat × ClosLang.Exp)) ∘ co) ∧
  conf = (co 0).1.1 ∧
  oracleMonotonic (fun entry => {i | elistGlobals entry.2.1 i ≠ 0}) (· < ·)
    {i | elistGlobals xs i ≠ 0} co ∧
  ∀ n, syntaxOk (co n).2.1 ∧ (co n).2.2 = []

/-- The initial traversal and oracle recurrence preserve safety of every
future global approximation. -/
@[hol "cakeml/compiler/backend/proofs/clos_knownProofScript.sml" "syntax_oracle_ok_state_sgc_free"]
theorem syntaxOracleOk_stateSgcFree {C : Type} (c : Config) (xs : List ClosLang.Exp)
    (co : Nat → (Spt ValApprox × C) × (List ClosLang.Exp × List (Nat × Nat × ClosLang.Exp)))
    (g : Spt ValApprox) (ys : List (ClosLang.Exp × ValApprox))
    (oracle : syntaxOracleOk c xs co g)
    (known : knownListTotal c (ClosFvs.compile xs) [] .ln = (ys, g)) :
    oracleStateSgcFree co := by
  obtain ⟨initial, recurrence, first, _, programs⟩ := oracle
  intro n
  induction n with
  | zero =>
    have safe := knownPreservesEsgcFree c (ClosFvs.compile xs) [] .ln ys g
      ⟨known, ?_, by simp, ?_⟩
    · simpa [first] using safe.2.2
    · simpa [ClosFvs.compile, esgcFreeList_iff] using
        (ClosFvs.removeList_esgcFree xs 0).mpr (by simpa [esgcFreeList_iff] using initial.2.2)
    · simp [globalsApproxSgcFree]
  | succ n ih =>
    have safeInput : ∀ e ∈ ClosFvs.compile (co n).2.1, esgcFree e := by
      simpa [ClosFvs.compile, esgcFreeList_iff] using
        (ClosFvs.removeList_esgcFree (co n).2.1 0).mpr
          (by simpa [esgcFreeList_iff] using (programs n).1.2.2)
    cases hk : knownListTotal (resetInlineFactor c) (ClosFvs.compile (co n).2.1) []
        (co n).1.1 with
    | mk eas next =>
      have safe := knownPreservesEsgcFree (resetInlineFactor c) (ClosFvs.compile (co n).2.1)
        [] (co n).1.1 eas next ⟨hk, safeInput, by simp, ih⟩
      have eq := recurrence n
      simp [pureCo, ClosFvs.compileInc, compileInc, hk] at eq
      simpa [eq] using safe.2.2

/-- Strict ordering makes writes in different oracle entries disjoint, so
per-program uniqueness extends to every finite oracle prefix. -/
@[hol "cakeml/compiler/backend/proofs/clos_knownProofScript.sml" "monotonic_unique_set_globals"]
theorem monotonicUniqueSetGlobals {A B : Type} (xs : List ClosLang.Exp)
    (co : Nat → A × List ClosLang.Exp × B)
    (ordered : oracleMonotonic (fun entry => {i | elistGlobals entry.2.1 i ≠ 0}) (· < ·)
      {i | elistGlobals xs i ≠ 0} co)
    (distinct : (∀ i, elistGlobals xs i ≤ 1) ∧
      ∀ n i, elistGlobals (co n).2.1 i ≤ 1) :
    uniqueSetGlobals xs co := by
  intro n key
  induction n with
  | zero => simpa [firstNExps] using distinct.1 key
  | succ n ih =>
    have shift := firstNExpsShiftSeq co 1 n
    simp only [Nat.add_comm 1 n] at shift
    rw [shift]
    have one : firstNExps (Flapjack.holShiftSeq n co) 1 = [(co n).2.1] := by
      simp [firstNExps, List.ofFn_succ, Flapjack.holShiftSeq]
    rw [one]
    simp only [List.flatten_append, List.flatten_cons, List.flatten_nil, List.append_nil,
      elistGlobals_append] at ih ⊢
    have disjointInitial : elistGlobals xs key = 0 ∨ elistGlobals (co n).2.1 key = 0 := by
      by_contra h
      push Not at h
      have impossible := ordered.2 n key key h.1 h.2
      omega
    have disjointPrefix : elistGlobals (List.flatten (firstNExps co n)) key = 0 ∨
        elistGlobals (co n).2.1 key = 0 := by
      by_contra h
      push Not at h
      obtain ⟨k, lt, written⟩ := elistGlobalsFirstNExpsExists key co n h.1
      have impossible := ordered.1 k n key key lt written h.2
      omega
    have lastBound := distinct.2 n key
    omega

/-- Global approximations produced from an empty tree are disjoint from
later oracle writes when the write sets are strictly ordered. -/
@[hol "cakeml/compiler/backend/proofs/clos_knownProofScript.sml" "monotonic_gapprox_disjoint"]
theorem monotonicGapproxDisjoint {A B : Type} (c : Config) (xs : List ClosLang.Exp)
    (aenv : List ValApprox) (ys : List (ClosLang.Exp × ValApprox)) (g : Spt ValApprox)
    (co : Nat → A × List ClosLang.Exp × B) (bag : Nat → Nat)
    (known : knownListTotal c xs aenv .ln = (ys, g))
    (ordered : oracleMonotonic (fun entry => {i | elistGlobals entry.2.1 i ≠ 0}) (· < ·)
      {i | bag i ≠ 0} co)
    (bagEq : bag = elistGlobals xs) : oracleGapproxDisjoint g co := by
  intro n
  apply Set.disjoint_left.mpr
  intro key member written
  have changed := knownListTotalChangedGlobalsAltSet c xs aenv .ln ys g known key member
  have sourceWrite : elistGlobals xs key ≠ 0 := by
    rcases changed with old | written
    · simp [sptMem, sptDomain] at old
    · exact written
  have impossible := ordered.2 n key key (by simpa [bagEq] using sourceWrite) written
  omega

/-- The state oracle can add only globals written by its earlier programs. -/
@[hol "cakeml/compiler/backend/proofs/clos_knownProofScript.sml" "state_oracle_domain"]
theorem stateOracleDomain {C A : Type} (c : Config)
    (co : Nat → (Spt ValApprox × C) × (List ClosLang.Exp × A))
    (oracle : isStateOracle (compileInc c) co) (n : Nat) :
    ∀ key, domainBag (co n).1.1 key ≤ domainBag (co 0).1.1 key +
      elistGlobals (List.flatten (firstNExps co n)) key := by
  classical
  induction n with
  | zero => simp [firstNExps, elistGlobals, FlatProps.emptyGlobalBag]
  | succ n ih =>
    intro key
    cases hk : knownListTotal (resetInlineFactor c) (co n).2.1 [] (co n).1.1 with
    | mk eas next =>
      have eq := oracle n
      simp [compileInc, hk] at eq
      have change := knownListTotalChangedGlobalsAltSet (resetInlineFactor c)
        (co n).2.1 [] (co n).1.1 eas next hk key
      have step : domainBag next key ≤ domainBag (co n).1.1 key + elistGlobals (co n).2.1 key := by
        by_cases old : sptMem key (co n).1.1
        · simp [domainBag, old]; split <;> omega
        · by_cases new : sptMem key next
          · have written := (change new).resolve_left old
            simp [domainBag, old, new]; omega
          · simp [domainBag, old, new]
      have shift := firstNExpsShiftSeq co 1 n
      simp only [Nat.add_comm 1 n] at shift
      rw [shift]
      have one : firstNExps (Flapjack.holShiftSeq n co) 1 = [(co n).2.1] := by
        simp [firstNExps, List.ofFn_succ, Flapjack.holShiftSeq]
      rw [one]
      simp only [List.flatten_append, List.flatten_cons, List.flatten_nil, List.append_nil,
        elistGlobals_append]
      rw [eq]
      have prev := ih key
      omega

end Flapjack.Compiler.Backend.ClosKnown
