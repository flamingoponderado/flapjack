module

public import Flapjack.Compiler.Backend.ClosKnown.Proofs.ApproxEvaluate
public import Flapjack.Compiler.Backend.Semantics.ClosSem.EvaluateOracleAdvance

@[expose] public section


/-! Disjointness of approximation domains from future oracle writes. -/
namespace Flapjack.Compiler.Backend.ClosKnown.OracleGlobals
open ClosSem ClosProps UniqueGlobalsPort

/-- The closure state uses canonical finite-map fields. -/
theorem holFmapAsFiniteSupportWitness {C F : Type} :
    (∀ s : ClosSem.StateBroad C F, (ClosSem.State.ofBroad s).toBroad = s) ∧
      (∀ s : ClosSem.State C F, ClosSem.State.ofBroad s.toBroad = s) :=
  ClosSem.holFmapAsFiniteSupportWitness

/-- Approximation entries are disjoint from a program's global writes. -/
@[hol "cakeml/compiler/backend/proofs/clos_knownProofScript.sml" "gapprox_disjoint_def"]
def gapproxDisjoint {α : Type} (g : Spt α) (xs : List ClosLang.Exp) : Prop :=
  Disjoint {i | sptMem i g} {i | elistGlobals xs i ≠ 0}


/-- Approximation disjointness splits over lists and operation arguments. -/
@[hol "cakeml/compiler/backend/proofs/clos_knownProofScript.sml" "gapprox_disjoint_rw"]
theorem gapproxDisjointRw {α : Type} (g : Spt α) (x y : ClosLang.Exp)
    (xs : List ClosLang.Exp) (tr : BackendCommon.Tra) (opn : ClosLang.Op) :
    (gapproxDisjoint g (x :: y :: xs) ↔ gapproxDisjoint g [x] ∧ gapproxDisjoint g (y :: xs)) ∧
    (gapproxDisjoint g [.op tr opn xs] ↔ gapproxDisjoint g xs ∧
      Disjoint {i | sptMem i g} {i | opGlobalBag opn i ≠ 0}) := by
  simp only [gapproxDisjoint, Set.disjoint_left, Set.mem_ofPred_eq, not_not,
    elistGlobals, setGlobals, FlatProps.unionGlobalBag, FlatProps.emptyGlobalBag,
    Nat.add_zero, Nat.add_eq_zero_iff, forall_and, Flapjack.bagUnion, Flapjack.emptyBag]
  tauto

/-- Every future oracle program is disjoint from the approximation domain. -/
@[hol "cakeml/compiler/backend/proofs/clos_knownProofScript.sml" "oracle_gapprox_disjoint_def"]
def oracleGapproxDisjoint {Index α β γ : Type} (g : Spt α)
    (co : Index → β × List ClosLang.Exp × γ) : Prop :=
  ∀ n, gapproxDisjoint g (co n).2.1

/-- Shifting an oracle preserves approximation disjointness. -/
@[hol "cakeml/compiler/backend/proofs/clos_knownProofScript.sml" "oracle_gapprox_disjoint_shift_seq"]
theorem oracleGapproxDisjointShift {α β γ : Type} (g : Spt α)
    (co : Nat → β × List ClosLang.Exp × γ) (h : oracleGapproxDisjoint g co) :
    ∀ k, oracleGapproxDisjoint g (Flapjack.holShiftSeq k co) := by
  intro k n
  exact h (n + k)

/-- A bag contribution from a member program is retained by flattening. -/
private theorem flattenWritesMember (parts : List (List ClosLang.Exp)) (es : List ClosLang.Exp)
    (key : Nat) (member : es ∈ parts) (written : elistGlobals es key ≠ 0) :
    elistGlobals parts.flatten key ≠ 0 := by
  induction parts with
  | nil => simp at member
  | cons first rest ih =>
    simp only [List.mem_cons] at member
    simp only [List.flatten_cons, elistGlobals_append]
    rcases member with same | tail
    · subst first
      omega
    · have restWritten := ih tail
      omega

/-- A write by a program in an oracle prefix appears in the flattened prefix. -/
@[hol "cakeml/compiler/backend/proofs/clos_knownProofScript.sml" "elist_globals_first_n_exps_lemma"]
theorem elistGlobalsFirstNExps {α β : Type} (i k : Nat)
    (co : Nat → α × List ClosLang.Exp × β) (written : elistGlobals (co k).2.1 i ≠ 0) :
    ∀ n, k < n → elistGlobals (List.flatten (firstNExps co n)) i ≠ 0 := by
  intro n bound
  exact flattenWritesMember _ _ i (memFirstNExps k n bound co) written

/-- A write in a flattened sequence comes from one of its members. -/
private theorem flattenWritesExists (parts : List (List ClosLang.Exp)) (key : Nat)
    (written : elistGlobals parts.flatten key ≠ 0) :
    ∃ es ∈ parts, elistGlobals es key ≠ 0 := by
  induction parts with
  | nil => simp [elistGlobals, FlatProps.emptyGlobalBag, Flapjack.emptyBag] at written
  | cons es rest ih =>
    simp only [List.flatten_cons, elistGlobals_append] at written
    by_cases head : elistGlobals es key = 0
    · have tail : elistGlobals rest.flatten key ≠ 0 := by omega
      obtain ⟨ys, mem, write⟩ := ih tail
      exact ⟨ys, List.mem_cons_of_mem _ mem, write⟩
    · exact ⟨es, List.mem_cons_self .., head⟩

/-- Every write in a finite oracle prefix comes from a program in that prefix. -/
@[hol "cakeml/compiler/backend/proofs/clos_knownProofScript.sml" "elist_globals_first_n_exps_exists"]
theorem elistGlobalsFirstNExpsExists {α β : Type} (i : Nat)
    (co : Nat → α × List ClosLang.Exp × β) (n : Nat)
    (written : elistGlobals (List.flatten (firstNExps co n)) i ≠ 0) :
    ∃ k, k < n ∧ elistGlobals (co k).2.1 i ≠ 0 := by
  obtain ⟨es, member, write⟩ := flattenWritesExists _ i written
  obtain ⟨k, equal⟩ := List.mem_ofFn.mp (show es ∈ List.ofFn (fun k : Fin n => (co k.val).2.1) from member)
  exact ⟨k.val, k.isLt, by simpa [equal] using write⟩

/-- Oracle disjointness is equivalent to disjointness from every finite prefix. -/
@[hol "cakeml/compiler/backend/proofs/clos_knownProofScript.sml" "oracle_gapprox_disjoint_first_n_exps"]
theorem oracleGapproxDisjointFirstN {α β γ : Type} (g : Spt α)
    (co : Nat → β × List ClosLang.Exp × γ) :
    oracleGapproxDisjoint g co ↔ ∀ n, gapproxDisjoint g (List.flatten (firstNExps co n)) := by
  constructor
  · intro oracle n
    apply Set.disjoint_left.mpr
    intro i member written
    obtain ⟨k, _, write⟩ := elistGlobalsFirstNExpsExists i co n written
    exact (Set.disjoint_left.mp (oracle k)) member write
  · intro prefixes k
    apply Set.disjoint_left.mpr
    intro i member written
    have pref := prefixes (k + 1)
    exact (Set.disjoint_left.mp pref) member (elistGlobalsFirstNExps i k co written (k + 1) (by omega))

/-- Optimizing a uniquely writing program preserves disjointness from every
later oracle program. -/
@[hol "cakeml/compiler/backend/proofs/clos_knownProofScript.sml" "oracle_gapprox_disjoint_shift_seq_unique_set_globals"
  (fmap_as_finite_support := [refs, code])]
theorem oracleGapproxDisjointShiftUnique {C F : Type}
    (c : Config) (xs : List ClosLang.Exp) (aenv : List ValApprox)
    (g0 : Spt ValApprox) (eas : List (ClosLang.Exp × ValApprox)) (g : Spt ValApprox)
    (s0 : State C F) (k : Nat)
    (h : knownListTotal c xs aenv g0 = (eas, g) ∧
      uniqueSetGlobals xs s0.compileOracle ∧ oracleGapproxDisjoint g0 s0.compileOracle) :
    oracleGapproxDisjoint g (Flapjack.holShiftSeq k s0.compileOracle) := by
  rcases h with ⟨run, unique, oracle⟩
  intro n
  apply Set.disjoint_left.mpr
  intro i member written
  obtain ⟨a, lookup⟩ := (sptMem_iff_lookup i g).1 member
  rcases knownListTotalChangedGlobalsCases c xs aenv g0 eas g run i a lookup with old | changed
  · have oldMember := (sptMem_iff_lookup i g0).2 ⟨a, old⟩
    exact (Set.disjoint_left.mp (oracle (n + k))) oldMember written
  · have original : elistGlobals (s0.compileOracle (n + k)).2.1 i ≠ 0 := written
    have future := elistGlobalsFirstNExps i (n + k) s0.compileOracle original (n + k + 1) (by omega)
    have bound := unique (n + k + 1) i
    simp only [elistGlobals_append] at bound
    omega

/-- Processing the first oracle program preserves disjointness for all later
oracle programs when the complete oracle writes each global at most once. -/
@[hol "cakeml/compiler/backend/proofs/clos_knownProofScript.sml" "oracle_gapprox_disjoint_Install"]
theorem oracleGapproxDisjointInstall {α β : Type} (c : Config)
    (co : Nat → α × List ClosLang.Exp × β) (g0 : Spt ValApprox)
    (eas : List (ClosLang.Exp × ValApprox)) (g : Spt ValApprox)
    (h : knownListTotal c (co 0).2.1 [] g0 = (eas, g) ∧
      uniqueSetGlobals [] co ∧ oracleGapproxDisjoint g0 co) :
    oracleGapproxDisjoint g (Flapjack.holShiftSeq 1 co) := by
  rcases h with ⟨run, unique, oracle⟩
  intro n
  apply Set.disjoint_left.mpr
  intro i member written
  obtain ⟨a, lookup⟩ := (sptMem_iff_lookup i g).1 member
  rcases knownListTotalChangedGlobalsCases c (co 0).2.1 [] g0 eas g run i a lookup with old | changed
  · exact (Set.disjoint_left.mp (oracle (n + 1))) ((sptMem_iff_lookup i g0).2 ⟨a, old⟩) written
  · have future := elistGlobalsFirstNExps i n (Flapjack.holShiftSeq 1 co) written (n + 1) (by omega)
    have bound := unique ((n + 1) + 1) i
    simp only [List.nil_append] at bound
    rw [firstNExpsShiftSeq] at bound
    simp only [List.flatten_append, elistGlobals_append] at bound
    have one : firstNExps co 1 = [(co 0).2.1] := by simp [firstNExps, List.ofFn_succ]
    rw [one] at bound
    simp only [List.flatten_cons, List.flatten_nil, List.append_nil] at bound
    omega

/-- Restricting an approximation tree preserves disjointness of its oracle. -/
@[hol "cakeml/compiler/backend/proofs/clos_knownProofScript.sml" "oracle_gapprox_disjoint_subspt"]
theorem oracleGapproxDisjointSubspt {Index α β γ : Type} (g0 g : Spt α)
    (co : Index → β × List ClosLang.Exp × γ)
    (h : sptSubspt g0 g ∧ oracleGapproxDisjoint g co) : oracleGapproxDisjoint g0 co := by
  intro n
  apply Set.disjoint_left.mpr
  intro i member written
  exact (Set.disjoint_left.mp (h.2 n)) (h.1 i member).1 written

/-- Writes by an oracle program remain in any shifted prefix containing it. -/
@[hol "cakeml/compiler/backend/proofs/clos_knownProofScript.sml" "elist_globals_first_n_exps_shift_seq_lemma"]
theorem elistGlobalsFirstNExpsShift {α β : Type} (i k : Nat)
    (co : Nat → α × List ClosLang.Exp × β) (written : elistGlobals (co k).2.1 i ≠ 0) :
    ∀ m n, m < k ∧ k < m + n →
      elistGlobals (List.flatten (firstNExps (Flapjack.holShiftSeq m co) n)) i ≠ 0 := by
  intro m n ⟨h1, h2⟩
  have indexed : elistGlobals ((Flapjack.holShiftSeq m co) (k - m)).2.1 i ≠ 0 := by
    simpa [Flapjack.holShiftSeq, Nat.sub_add_cancel (Nat.le_of_lt h1)] using written
  exact elistGlobalsFirstNExps i (k - m) (Flapjack.holShiftSeq m co) indexed n (by omega)

/-- Every evaluation advances the compile oracle by some finite amount. -/
@[hol "cakeml/compiler/backend/proofs/clos_knownProofScript.sml" "evaluate_IMP_shift_seq"
  (fmap_as_finite_support := [refs, code])]
theorem evaluateImpShiftSeq {C F : Type} (es : List ClosLang.Exp) (env : List ClosSem.Value)
    (s0 : State C F) (res : Flapjack.SemanticPrimitivesHOL.Result (List ClosSem.Value) ClosSem.Value)
    (s : State C F) (run : evaluate es env s0 = (res, s)) :
    ∃ k, s.compileOracle = Flapjack.holShiftSeq k s0.compileOracle :=
  evaluate_oracle_advance.1 es env s0 s res run

/-- Every closure application advances the compile oracle by a finite amount. -/
@[hol "cakeml/compiler/backend/proofs/clos_knownProofScript.sml" "evaluate_app_IMP_shift_seq"
  (fmap_as_finite_support := [refs, code])]
theorem evaluateAppImpShiftSeq {C F : Type} (location : Option Nat) (function : ClosSem.Value)
    (args : List ClosSem.Value) (s0 : State C F)
    (result : Flapjack.SemanticPrimitivesHOL.Result (List ClosSem.Value) ClosSem.Value)
    (s : State C F) (run : evaluateApp location function args s0 = (result, s)) :
    ∃ k, s.compileOracle = Flapjack.holShiftSeq k s0.compileOracle :=
  evaluate_oracle_advance.2 (s0.clock + 1) location function args s0 s result (Nat.lt_succ_self _) run

/-- Evaluation preserves global-write uniqueness for an arbitrary program. -/
@[hol "cakeml/compiler/backend/proofs/clos_knownProofScript.sml" "unique_set_globals_evaluate"
  (fmap_as_finite_support := [refs, code])]
theorem uniqueSetGlobalsEvaluate {C F : Type} (es xs : List ClosLang.Exp)
    (env : List ClosSem.Value) (s1 s2 : State C F)
    (res : Flapjack.SemanticPrimitivesHOL.Result (List ClosSem.Value) ClosSem.Value)
    (h : uniqueSetGlobals xs s1.compileOracle ∧ evaluate es env s1 = (res, s2)) :
    uniqueSetGlobals xs s2.compileOracle := by
  obtain ⟨n, shift⟩ := evaluateImpShiftSeq es env s1 res s2 h.2
  rw [shift]
  exact uniqueSetGlobalsShift xs s1.compileOracle h.1 n

/-- Evaluation preserves oracle disjointness for any approximation tree. -/
@[hol "cakeml/compiler/backend/proofs/clos_knownProofScript.sml" "oracle_gapprox_disjoint_evaluate"
  (fmap_as_finite_support := [refs, code])]
theorem oracleGapproxDisjointEvaluate {C F α : Type} (g : Spt α)
    (s0 : State C F) (es : List ClosLang.Exp) (env : List ClosSem.Value)
    (res : Flapjack.SemanticPrimitivesHOL.Result (List ClosSem.Value) ClosSem.Value) (s1 : State C F)
    (h : oracleGapproxDisjoint g s0.compileOracle ∧ evaluate es env s0 = (res, s1)) :
    oracleGapproxDisjoint g s1.compileOracle := by
  obtain ⟨n, shift⟩ := evaluateImpShiftSeq es env s0 res s1 h.2
  rw [shift]
  exact oracleGapproxDisjointShift g s0.compileOracle h.1 n

/-- Evaluating and optimizing the same unique program preserves oracle
approximation disjointness in the final state. -/
@[hol "cakeml/compiler/backend/proofs/clos_knownProofScript.sml" "oracle_gapprox_disjoint_lemma"
  (fmap_as_finite_support := [refs, code])]
theorem oracleGapproxDisjointLemma {C F : Type}
    (xs : List ClosLang.Exp) (env : List ClosSem.Value) (s0 : State C F)
    (res : Flapjack.SemanticPrimitivesHOL.Result (List ClosSem.Value) ClosSem.Value) (s : State C F)
    (c : Config) (aenv : List ValApprox) (g0 : Spt ValApprox)
    (eas : List (ClosLang.Exp × ValApprox)) (g : Spt ValApprox)
    (h : evaluate xs env s0 = (res, s) ∧ knownListTotal c xs aenv g0 = (eas, g) ∧
      uniqueSetGlobals xs s0.compileOracle ∧ oracleGapproxDisjoint g0 s0.compileOracle) :
    oracleGapproxDisjoint g s.compileOracle := by
  obtain ⟨n, shift⟩ := evaluateImpShiftSeq xs env s0 res s h.1
  rw [shift]
  exact oracleGapproxDisjointShiftUnique c xs aenv g0 eas g s0 n ⟨h.2.1, h.2.2.1, h.2.2.2⟩

end Flapjack.Compiler.Backend.ClosKnown.OracleGlobals
