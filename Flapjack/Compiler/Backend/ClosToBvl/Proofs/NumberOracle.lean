module

public import Flapjack.Compiler.Backend.ClosToBvl.Proofs.NumberAddresses
public import Flapjack.Compiler.Backend.BackendProps.OracleMonotonic

@[expose] public section

/-! Ordering of addresses across the numbering oracle. -/
namespace Flapjack.Compiler.Backend.ClosToBvl
open ClosLang ClosProps BackendProps

/-- Ignoring a table preserves the auxiliary component of the program. -/
@[hol "cakeml/compiler/backend/proofs/clos_to_bvlProofScript.sml" "SND_SND_ignore_table"]
theorem snd_snd_ignoreTable {S P T Q A : Type} (f : S → P → T × Q) (st : S) (p : P × A) :
    (ClosNumber.ignoreTable f st p).2.2 = p.2 := by
  cases h : f st p.1; simp [ClosNumber.ignoreTable, h]

/-- Ignoring a table exposes the transformed main program. -/
@[hol "cakeml/compiler/backend/proofs/clos_to_bvlProofScript.sml" "FST_SND_ignore_table"]
theorem fst_snd_ignoreTable {S P T Q A : Type} (f : S → P → T × Q) (st : S) (p : P × A) :
    (ClosNumber.ignoreTable f st p).2.1 = (f st p.1).2 := by
  cases h : f st p.1; simp [ClosNumber.ignoreTable, h]

private theorem number_compile_strict (n : Nat) (es : List ClosLang.Exp) :
    n < (ClosNumber.compileInc n es).1 := by
  change n < (ClosNumber.renumberList (makeEven (n + max es.length 1)) es).1
  have bound := ClosNumber.renumberList_start_le es (makeEven (n + max es.length 1))
  have align : n + max es.length 1 ≤ makeEven (n + max es.length 1) := by
    unfold makeEven
    split <;> omega
  omega

/-- The numbering result is the next state-oracle counter. -/
@[hol "cakeml/compiler/backend/proofs/clos_to_bvlProofScript.sml" "number_oracle_FST_inc"]
theorem numberOracle_fst_inc {A C : Type}
    (co : Nat → (Nat × C) × (List ClosLang.Exp × A)) (j : Nat)
    (h : isStateOracle (ClosNumber.ignoreTable ClosNumber.compileInc) co) :
    (ClosNumber.compileInc (co j).1.1 (co j).2.1).1 = (co (j + 1)).1.1 := by
  have step := h j
  simpa [ClosNumber.ignoreTable] using step.symm

/-- Numbering oracle counters grow strictly across entries. -/
@[hol "cakeml/compiler/backend/proofs/clos_to_bvlProofScript.sml" "number_oracle_FST_strict_mono"]
theorem numberOracle_fst_strictMono {A C : Type}
    (co : Nat → (Nat × C) × (List ClosLang.Exp × A))
    (h : isStateOracle (ClosNumber.ignoreTable ClosNumber.compileInc) co) :
    ∀ j i, i < j → (co i).1.1 < (co j).1.1 := by
  have step : ∀ i, (co i).1.1 < (co (i + 1)).1.1 := by
    intro i
    rw [← numberOracle_fst_inc co i h]
    exact number_compile_strict (co i).1.1 (co i).2.1
  have strict : StrictMono (fun i => (co i).1.1) := strictMono_nat_of_lt_succ step
  intro j i hij
  exact strict hij

/-- Numbering oracle counters are monotone. -/
@[hol "cakeml/compiler/backend/proofs/clos_to_bvlProofScript.sml" "number_oracle_FST_mono"]
theorem numberOracle_fst_mono {A C : Type}
    (co : Nat → (Nat × C) × (List ClosLang.Exp × A))
    (h : isStateOracle (ClosNumber.ignoreTable ClosNumber.compileInc) co) :
    ∀ j i, i ≤ j → (co i).1.1 ≤ (co j).1.1 := by
  intro j i hij
  rcases Nat.lt_or_eq_of_le hij with lt | equal
  · exact Nat.le_of_lt (numberOracle_fst_strictMono co h j i lt)
  · subst j; exact Nat.le_refl _

/-- Numbering orders future code locations after the initial numbered program. -/
@[hol "cakeml/compiler/backend/proofs/clos_to_bvlProofScript.sml" "renumber_code_locs_monotonic"]
theorem renumberCodeLocs_monotonic {A C : Type}
    (co : Nat → (Nat × C) × (List ClosLang.Exp × A)) (n : Nat) (exps : List ClosLang.Exp)
    (h : isStateOracle (ClosNumber.ignoreTable ClosNumber.compileInc) co ∧
      (ClosNumber.renumberList n exps).1 ≤ (co 0).1.1) :
    oracleMonotonic
      (fun entry : C × (List ClosLang.Exp × A) => {x | x ∈ codeLocations entry.2.1})
      (· < ·) {x | x ∈ codeLocations (ClosNumber.renumberList n exps).2}
      (stateCo (ClosNumber.ignoreTable ClosNumber.compileInc) co) := by
  have bounds : ∀ i x,
      x ∈ codeLocations (stateCo (ClosNumber.ignoreTable ClosNumber.compileInc) co i).2.1 →
      (co i).1.1 < x ∧ x < (co (i + 1)).1.1 := by
    intro i x member
    have source : x ∈ codeLocations (ClosNumber.compileInc (co i).1.1 (co i).2.1).2 := by
      simpa [stateCo, fst_snd_ignoreTable] using member
    have bounds := mem_numberCompileInc_locs x (co i).1.1 (co i).2.1 source
    rw [numberOracle_fst_inc co i h.1] at bounds
    exact bounds
  constructor
  · intro i j x y ij hx hy
    have left := bounds i x hx
    have right := bounds j y hy
    have middle := numberOracle_fst_mono co h.1 j (i + 1) (by omega)
    omega
  · intro i x y hx hy
    have first := ClosNumber.renumberList_codeLocations_distinct n exps
    have left := first.2.2 x hx
    have right := bounds i y hy
    have middle := numberOracle_fst_mono co h.1 i 0 (Nat.zero_le i)
    omega

/-- Numbering produces an oracle whose required addresses increase across entries. -/
@[hol "cakeml/compiler/backend/proofs/clos_to_bvlProofScript.sml" "renumber_code_locs_monotonic_req"]
theorem renumberCodeLocs_monotonic_req {A C : Type}
    (co : Nat → (Nat × C) × (List ClosLang.Exp × List (Nat × A × ClosLang.Exp)))
    (initial : Set Nat) (offs : Nat)
    (h : isStateOracle (ClosNumber.ignoreTable ClosNumber.compileInc) co ∧
      (∀ x ∈ initial, x < (co 0).1.1 + offs) ∧
      (∀ n, (co n).2.2 = [])) :
    oracleMonotonic
      (fun entry : C × (List ClosLang.Exp × List (Nat × A × ClosLang.Exp)) =>
        {x | x ∈ (reqCompileIncAddrs [Nat.succ] entry.2).map (offs + ·)})
      (· < ·) initial (stateCo (ClosNumber.ignoreTable ClosNumber.compileInc) co) := by
  have bounds : ∀ i x,
      x ∈ (reqCompileIncAddrs [Nat.succ]
        (stateCo (ClosNumber.ignoreTable ClosNumber.compileInc) co i).2).map (offs + ·) →
      (co i).1.1 + offs ≤ x ∧ x < (co (i + 1)).1.1 + offs := by
    intro i x member
    obtain ⟨label, member, rfl⟩ := List.mem_map.mp member
    have source : label ∈ reqCompileIncAddrs [Nat.succ]
        (ClosNumber.ignoreTable ClosNumber.compileInc (co i).1.1 (co i).2).2 := by
      simpa [stateCo] using member
    have b := mem_number_req label (co i).1.1 (co i).2 ⟨source, h.2.2 i⟩
    rw [numberOracle_fst_inc co i h.1] at b
    omega
  constructor
  · intro i j x y ij hx hy
    have a := bounds i x hx
    have b := bounds j y hy
    have mid := numberOracle_fst_mono co h.1 j (i + 1) (by omega)
    omega
  · intro i x y hx hy
    have a := h.2.1 x hx
    have b := bounds i y hy
    have mid := numberOracle_fst_mono co h.1 i 0 (Nat.zero_le i)
    omega
end Flapjack.Compiler.Backend.ClosToBvl
