module

public import Flapjack.Compiler.Backend.ClosKnown.Proofs.StateOracle
public import Flapjack.Compiler.Backend.ClosKnown.Proofs.Syntax
public import Flapjack.Compiler.Backend.BackendProps.OracleMonotonic
public import Flapjack.Compiler.Backend.BackendProps.Pure
public import Flapjack.Compiler.Backend.ClosFvs.Proofs.Syntax
public import Flapjack.Compiler.Backend.ClosKnown.Proofs.OracleGlobals
public import Flapjack.Compiler.Backend.ClosKnown.Proofs.KnownSubspt
public import Flapjack.Compiler.Backend.ClosKnown.Proofs.OracleMonotonic

@[expose] public section


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
  | zero => simp [firstNExps, elistGlobals, FlatProps.emptyGlobalBag, Flapjack.emptyBag]
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

/-- The source syntax and ordered oracle ensure that incremental
optimization preserves each earlier approximation tree. -/
@[hol "cakeml/compiler/backend/proofs/clos_knownProofScript.sml" "syntax_oracle_ok_gapprox_subspt"]
theorem syntaxOracleOk_gapproxSubspt {C : Type} (c : Config) (xs : List ClosLang.Exp)
    (co : Nat → (Spt ValApprox × C) × (List ClosLang.Exp × List (Nat × Nat × ClosLang.Exp)))
    (g : Spt ValApprox) (ys : List (ClosLang.Exp × ValApprox))
    (oracle : syntaxOracleOk c xs co g)
    (known : knownListTotal c (ClosFvs.compile xs) [] .ln = (ys, g)) :
    oracleGapproxSubspt co := by
  obtain ⟨_, recurrence, first, ordered, _⟩ := oracle
  have initial : oracleGapproxDisjoint g co := by
    apply monotonicGapproxDisjoint c (ClosFvs.compile xs) [] ys g co (elistGlobals xs) known ordered
    simpa [ClosFvs.compile] using (ClosFvs.removeList_globals xs 0).symm
  have future : ∀ n k, n ≤ k → gapproxDisjoint (co n).1.1 (co k).2.1 := by
    intro n
    induction n with
    | zero =>
      intro k _
      simpa [first] using initial k
    | succ n ih =>
      intro k le
      apply Set.disjoint_left.mpr
      intro key member written
      cases hk : knownListTotal (resetInlineFactor c) (ClosFvs.compile (co n).2.1) []
          (co n).1.1 with
      | mk eas next =>
        have eq := recurrence n
        simp [pureCo, ClosFvs.compileInc, compileInc, hk] at eq
        have nextMember : sptMem key next := by simpa [eq] using member
        have changed := knownListTotalChangedGlobalsAltSet (resetInlineFactor c)
          (ClosFvs.compile (co n).2.1) [] (co n).1.1 eas next hk key nextMember
        rcases changed with old | new
        · exact (Set.disjoint_left.mp (ih k (by omega))) old written
        · have sourceWrite : elistGlobals (co n).2.1 key ≠ 0 := by
            simpa [ClosFvs.compile, ClosFvs.removeList_globals] using new
          have impossible := ordered.1 n k key key (by omega) sourceWrite written
          omega
  intro n key member
  have noWrite : elistGlobals (ClosFvs.compile (co n).2.1) key = 0 := by
    have disjoint := Set.disjoint_left.mp (future n n (Nat.le_refl n)) member
    by_contra h
    apply disjoint
    simpa [ClosFvs.compile, ClosFvs.removeList_globals] using h
  cases hk : knownListTotal (resetInlineFactor c) (ClosFvs.compile (co n).2.1) []
      (co n).1.1 with
  | mk eas next =>
    have unchanged := knownListTotalLookupUnchanged (resetInlineFactor c)
      (ClosFvs.compile (co n).2.1) [] (co n).1.1 key noWrite
    rw [hk] at unchanged
    have eq := recurrence n
    simp [pureCo, ClosFvs.compileInc, compileInc, hk] at eq
    have ⟨value, lookup⟩ := (sptMem_iff_lookup key (co n).1.1).1 member
    have nextLookup : sptLookup key next = some value := unchanged.trans lookup
    rw [eq]
    exact ⟨(sptMem_iff_lookup key next).2 ⟨value, nextLookup⟩, unchanged⟩

/-- Free-variable cleanup preserves the global-write bag of every oracle
prefix. This is a Lean helper for connecting the cleanup and optimizer. -/
theorem fvsOraclePrefixGlobals {A B D : Type}
    (co : Nat → A × (List ClosLang.Exp × B)) (n : Nat) :
    elistGlobals (List.flatten (firstNExps
      (pureCo (ClosFvs.compileInc (β := D)) ∘ co) n)) =
      elistGlobals (List.flatten (firstNExps co n)) := by
  induction n with
  | zero => simp [firstNExps]
  | succ n ih =>
    have src := firstNExpsShiftSeq co 1 n
    have dst := firstNExpsShiftSeq (pureCo (ClosFvs.compileInc (β := D)) ∘ co) 1 n
    simp only [Nat.add_comm 1 n] at src dst
    rw [src, dst]
    have srcOne : firstNExps (Flapjack.holShiftSeq n co) 1 = [(co n).2.1] := by
      simp [firstNExps, List.ofFn_succ, Flapjack.holShiftSeq]
    have dstOne : firstNExps
        (Flapjack.holShiftSeq n (pureCo (ClosFvs.compileInc (β := D)) ∘ co)) 1 =
        [ClosFvs.compile (co n).2.1] := by
      simp [firstNExps, List.ofFn_succ, Flapjack.holShiftSeq, pureCo, ClosFvs.compileInc]
    rw [srcOne, dstOne]
    simp only [List.flatten_append, List.flatten_cons, List.flatten_nil, List.append_nil]
    funext key
    simp only [elistGlobals_append, ih, ClosFvs.compile, ClosFvs.removeList_globals]

/-- Free-variable cleanup turns the source syntax-oracle condition into the
individual premises used by the optimizer's observational theorem. This
is Lean-side pass composition, not a separate HOL declaration. -/
theorem syntaxOracleOk_fvsKnownPremises {C : Type} (c : Config) (xs : List ClosLang.Exp)
    (co : Nat → (Spt ValApprox × C) × (List ClosLang.Exp × List (Nat × Nat × ClosLang.Exp)))
    (g : Spt ValApprox) (ys : List (ClosLang.Exp × ValApprox))
    (oracle : syntaxOracleOk c xs co g)
    (known : knownListTotal c (ClosFvs.compile xs) [] .ln = (ys, g)) :
    let fco := pureCo (ClosFvs.compileInc (β := Nat × Nat × ClosLang.Exp)) ∘ co
    let fxs := ClosFvs.compile xs
    (∀ n, (fco n).2.2 = []) ∧ (∀ n, fvMax 0 (fco n).2.1) ∧
      (∀ n es aux, (fco n).2 = (es, aux) → ∀ e ∈ es, esgcFree e) ∧
      everyFnVarsNone fxs ∧ coEveryFnVarsNone fco ∧ oracleGapproxSubspt fco ∧
      oracleStateSgcFree fco ∧ isStateOracle (compileInc c) fco ∧ uniqueSetGlobals fxs fco ∧
      (∀ e ∈ fxs, esgcFree e) ∧ fvMax 0 fxs ∧ (fco 0).1.1 = g ∧
      oracleGapproxDisjoint g fco ∧ knownListTotal c fxs [] .ln = (ys, g) := by
  have ⟨input, recurrence, first, ordered, programs⟩ := oracle
  have mono := syntaxOracleOk_gapproxSubspt c xs co g ys oracle known
  have safe := syntaxOracleOk_stateSgcFree c xs co g ys oracle known
  have unique := monotonicUniqueSetGlobals xs co ordered ⟨input.2.1, fun n => (programs n).1.2.1⟩
  have disjoint := monotonicGapproxDisjoint c (ClosFvs.compile xs) [] ys g co (elistGlobals xs)
    known ordered (by simpa [ClosFvs.compile] using (ClosFvs.removeList_globals xs 0).symm)
  dsimp only
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, recurrence, ?_, ?_, ?_, ?_, ?_, known⟩
  · intro n; rfl
  · intro n
    exact ClosFvs.removeList_fvMax _ 0 (programs n).1.1
  · intro n es aux eq e mem
    have esEq : es = ClosFvs.compile (co n).2.1 := by
      have := congrArg Prod.fst eq
      simpa [pureCo, ClosFvs.compileInc] using this.symm
    subst es
    have safety := (ClosFvs.removeList_esgcFree (co n).2.1 0).mpr
      (by simpa [esgcFreeList_iff] using (programs n).1.2.2)
    exact (esgcFreeList_iff _).mp safety e mem
  · exact (ClosFvs.removeList_varsNone xs 0).mpr input.1
  · intro n es aux eq
    have esEq : es = ClosFvs.compile (co n).2.1 := by
      have := congrArg Prod.fst eq
      simpa [pureCo, ClosFvs.compileInc] using this.symm
    have auxEq : aux = [] := by
      have := congrArg Prod.snd eq
      simpa [pureCo, ClosFvs.compileInc] using this.symm
    subst es; subst aux
    exact ⟨(ClosFvs.removeList_varsNone _ 0).mpr (programs n).1.1, by simp [everyFnVarsNone]⟩
  · simpa [oracleGapproxSubspt, pureCo] using mono
  · simpa [oracleStateSgcFree, pureCo] using safe
  · intro n key
    have bound := unique n key
    simpa [elistGlobals_append, ClosFvs.compile, ClosFvs.removeList_globals,
      fvsOraclePrefixGlobals] using bound
  · have safety := (ClosFvs.removeList_esgcFree xs 0).mpr
      (by simpa [esgcFreeList_iff] using input.2.2)
    exact (esgcFreeList_iff _).mp safety
  · exact ClosFvs.removeList_fvMax xs 0 input.1
  · simpa [pureCo] using first.symm
  · intro n
    simpa [oracleGapproxDisjoint, gapproxDisjoint, pureCo, ClosFvs.compileInc,
      ClosFvs.compile, ClosFvs.removeList_globals] using disjoint n

end Flapjack.Compiler.Backend.ClosKnown
