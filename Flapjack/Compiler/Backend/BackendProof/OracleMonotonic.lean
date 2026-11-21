module

public import Flapjack.Compiler.Backend.BackendProps.OracleMonotonic
public import Flapjack.Compiler.Backend.BackendProof.CakeOrac

@[expose] public section

/-! backendProofScript.sml 1589-1662 and 1791-1839: generic introduction rules
for `oracle_monotonic`, and their instances for `cake_orac`. -/
namespace Flapjack.Compiler.Backend.BackendProof

open Flapjack Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Backend.BackendDefs
open Flapjack.Compiler.Backend.BackendProps

/-- Exact HOL `oracle_monotonic_slice` (`backendProofScript.sml:1589-1608`).
`PREIMAGE g {z}` is `g ⁻¹' {z}`, `(≠)` is `fun x y => x ≠ y`, and HOL's free
`f`, `init_s` and `orac` are explicit. -/
@[hol "cakeml/compiler/backend/proofs/backendProofScript.sml" "oracle_monotonic_slice"]
theorem oracleMonotonic_slice {α β γ : Type} (f : γ → Set α) (initS : Set α)
    (orac : Nat → γ) :
    ∀ g : α → β,
      (∀ z, oracleMonotonic (fun x => f x ∩ g ⁻¹' {z}) (fun x y => x ≠ y)
        (initS ∩ g ⁻¹' {z}) orac) →
      oracleMonotonic f (fun x y => x ≠ y) initS orac := by
  intro g h
  constructor
  · intro i j x y hij hx hy hxy
    subst hxy
    exact (h (g x)).1 i j x x hij ⟨hx, rfl⟩ ⟨hy, rfl⟩ rfl
  · intro i x y hx hy hxy
    subst hxy
    exact (h (g x)).2 i x x ⟨hx, rfl⟩ ⟨hy, rfl⟩ rfl

/-- Exact HOL `oracle_monotonic_rel_mono` (`backendProofScript.sml:1610-1615`). -/
@[hol "cakeml/compiler/backend/proofs/backendProofScript.sml" "oracle_monotonic_rel_mono"]
theorem oracleMonotonic_relMono {α β : Type} (f : β → Set α) (initS : Set α)
    (orac : Nat → β) :
    ∀ R R' : α → α → Prop, (∀ x y, R x y → R' x y) ∧ oracleMonotonic f R initS orac →
      oracleMonotonic f R' initS orac := by
  intro R R' ⟨hR, h1, h2⟩
  exact ⟨fun i j x y a b c => hR _ _ (h1 i j x y a b c),
    fun i x y a b => hR _ _ (h2 i x y a b)⟩

/-- Exact HOL `oracle_monotonic_state_with_inv` (`backendProofScript.sml:1617-1642`).
HOL's free `orac`, `St`, `f_inc` and `f` are explicit. -/
@[hol "cakeml/compiler/backend/proofs/backendProofScript.sml" "oracle_monotonic_state_with_inv"]
theorem oracleMonotonic_stateWithInv {α β γ δ : Type} (orac : Nat → (α × β) × γ)
    (St : Set Nat) (fInc : α → γ → α × δ) (f : β × δ → Set Nat) :
    ∀ (P : α → Prop) (nF : α → Nat),
      P (orac 0).1.1 ∧ (∀ x, x ∈ St → x < nF (orac 0).1.1) ∧
      (∀ (i : Nat) (st : α) (prog : γ) (st' : α) (prog' : δ) (stEx : β),
        fInc st prog = (st', prog') ∧ P st ∧ orac i = ((st, stEx), prog) →
        P st' ∧ nF st ≤ nF st' ∧ ∀ (cfg : β) (x : Nat), x ∈ f (cfg, prog') →
          nF st ≤ x ∧ x < nF st') ∧
      isStateOracle fInc orac →
      oracleMonotonic f (· < ·) St (stateCo fInc orac) := by
  intro P nF ⟨hP0, hSt, hstep, hso⟩
  have step : ∀ i, P (orac i).1.1 → P (orac (i + 1)).1.1 ∧
      nF (orac i).1.1 ≤ nF (orac (i + 1)).1.1 ∧
      ∀ x, x ∈ f (stateCo fInc orac i) → nF (orac i).1.1 ≤ x ∧ x < nF (orac (i + 1)).1.1 := by
    intro i hp
    have h := hstep i (orac i).1.1 (orac i).2 (fInc (orac i).1.1 (orac i).2).1
      (fInc (orac i).1.1 (orac i).2).2 (orac i).1.2 ⟨rfl, hp, rfl⟩
    rw [hso i]
    exact ⟨h.1, h.2.1, fun x hx => h.2.2 _ x hx⟩
  have hPall : ∀ i, P (orac i).1.1 := by
    intro i; induction i with
    | zero => exact hP0
    | succ n ih => exact (step n ih).1
  have mono : ∀ i j, i ≤ j → nF (orac i).1.1 ≤ nF (orac j).1.1 := by
    intro i j hij
    induction j, hij using Nat.le_induction with
    | base => exact le_rfl
    | succ n _ ih => exact ih.trans (step n (hPall n)).2.1
  constructor
  · intro i j x y hij hx hy
    have a := ((step i (hPall i)).2.2 x hx).2
    have b := ((step j (hPall j)).2.2 y hy).1
    have c := mono (i + 1) j hij
    omega
  · intro i x y hx hy
    have a := hSt x hx
    have b := ((step i (hPall i)).2.2 y hy).1
    have c := mono 0 i (Nat.zero_le i)
    omega

/-- Exact HOL `oracle_monotonic_bounded_state` (`backendProofScript.sml:1644-1662`). -/
@[hol "cakeml/compiler/backend/proofs/backendProofScript.sml" "oracle_monotonic_bounded_state"]
theorem oracleMonotonic_boundedState {α : Type} (St : Set Nat) (orac : Nat → α)
    (f : α → Set Nat) :
    ∀ nF : α → Nat,
      (∀ x, x ∈ St → x < nF (orac 0)) ∧
      (∀ i, nF (orac i) ≤ nF (orac (i + 1)) ∧
        ∀ x, x ∈ f (orac i) → nF (orac i) ≤ x ∧ x < nF (orac (i + 1))) →
      oracleMonotonic f (· < ·) St orac := by
  intro nF ⟨hSt, hstep⟩
  have mono : ∀ i j, i ≤ j → nF (orac i) ≤ nF (orac j) := by
    intro i j hij
    induction j, hij using Nat.le_induction with
    | base => exact le_rfl
    | succ n _ ih => exact ih.trans (hstep n).1
  constructor
  · intro i j x y hij hx hy
    have a := ((hstep i).2 x hx).2
    have b := ((hstep j).2 y hy).1
    have c := mono (i + 1) j hij
    omega
  · intro i x y hx hy
    have a := hSt x hx
    have b := ((hstep i).2 y hy).1
    have c := mono 0 i (Nat.zero_le i)
    omega

/-- Exact HOL `oracle_monotonic_subset_inject` (`backendProofScript.sml:1791-1799`).
`IMAGE g` is `g ''`. -/
@[hol "cakeml/compiler/backend/proofs/backendProofScript.sml" "oracle_monotonic_subset_inject"]
theorem oracleMonotonic_subsetInject {α β γ δ : Type} (R : β → β → Prop) (R' : α → α → Prop)
    (initSet' : Set α) (initSet : Set β) (f' : γ → Set α) (co' : Nat → γ)
    (f : δ → Set β) (co : Nat → δ) :
    ∀ g : α → β,
      (∀ x y, R (g x) (g y) → R' x y) ∧ g '' initSet' ⊆ initSet ∧
        (∀ n, g '' f' (co' n) ⊆ f (co n)) →
      oracleMonotonic f R initSet co → oracleMonotonic f' R' initSet' co' := by
  intro g ⟨hR, hi, hf⟩ ⟨h1, h2⟩
  constructor
  · intro i j x y hij hx hy
    exact hR _ _ (h1 i j _ _ hij (hf i ⟨x, hx, rfl⟩) (hf j ⟨y, hy, rfl⟩))
  · intro i x y hx hy
    exact hR _ _ (h2 i _ _ (hi ⟨x, hx, rfl⟩) (hf i ⟨y, hy, rfl⟩))

/-- Exact HOL `oracle_monotonic_handle_init_component`
(`backendProofScript.sml:1801-1808`). `DIFF` is set difference. -/
@[hol "cakeml/compiler/backend/proofs/backendProofScript.sml"
  "oracle_monotonic_handle_init_component"]
theorem oracleMonotonic_handleInitComponent {α β : Type} (f : β → Set α) (co : Nat → β)
    (R : α → α → Prop) (initSet : Set α) :
    ∀ D : Set α,
      (∀ i x y, x ∈ D ∧ y ∈ f (co i) → R x y) ∧ oracleMonotonic f R (initSet \ D) co →
      oracleMonotonic f R initSet co := by
  intro D ⟨hD, h1, h2⟩
  refine ⟨h1, fun i x y hx hy => ?_⟩
  by_cases hxD : x ∈ D
  · exact hD i x y ⟨hxD, hy⟩
  · exact h2 i x y ⟨hx, hxD⟩ hy

/-- Exact HOL `oracle_monotonic_cake_orac_to_I` (`backendProofScript.sml:1810-1817`).
HOL `I` is `id`; the free variables are explicit. -/
@[hol "cakeml/compiler/backend/proofs/backendProofScript.sml" "oracle_monotonic_cake_orac_to_I"
  (words_as_type_indexed_bitvec)]
theorem oracleMonotonic_cakeOrac_to_I {width : Nat} [NeZero width] {α β γ : Type}
    (f : β × γ → Set α) (cfgF : Flapjack.Compiler.Backend.Backend.Config → β)
    (pF : BackendProgs width → γ) (R : α → α → Prop) (initSt : Set α)
    (asmConf : AsmConfigExact width) (c' : Flapjack.Compiler.Backend.Backend.Config)
    (syntaxOrac : Nat → (Nat × Nat) × List AstHOL.Dec) :
    oracleMonotonic (fun (cfg, p) => f (cfgF cfg, pF p)) R initSt
        (cakeOrac asmConf c' syntaxOrac id id) →
      oracleMonotonic f R initSt (cakeOrac asmConf c' syntaxOrac cfgF pF) := by
  intro h
  exact oracleMonotonic_subset _ _ _ _ _ _ R ⟨le_rfl, fun _ => le_rfl⟩ h

/-- Exact HOL `cake_orac_monotonic_bounded_state` (`backendProofScript.sml:1819-1839`).
HOL's free `St`, `c'`, `asm_conf`, `syntax` (`syntaxOrac`), `f`, `cfg_f` and
`p_f` are explicit; `T` is `true`. -/
@[hol "cakeml/compiler/backend/proofs/backendProofScript.sml" "cake_orac_monotonic_bounded_state"
  (words_as_type_indexed_bitvec)]
theorem cakeOrac_monotonicBoundedState {width : Nat} [NeZero width] {β γ : Type}
    (St : Set Nat) (c' : Flapjack.Compiler.Backend.Backend.Config)
    (asmConf : AsmConfigExact width) (syntaxOrac : Nat → (Nat × Nat) × List AstHOL.Dec)
    (f : β × γ → Set Nat) (cfgF : Flapjack.Compiler.Backend.Backend.Config → β)
    (pF : BackendProgs width → γ) :
    ∀ nF : Flapjack.Compiler.Backend.Backend.Config → Nat,
      (∀ x, x ∈ St → x < nF c') ∧
      (∀ (i : Nat) (c2 : Flapjack.Compiler.Backend.Backend.Config) (ps : BackendProgs width),
        let c1 := cakeConfigs asmConf c' syntaxOrac i
        compileIncProgs true asmConf c1 (syntaxOrac i) = (c2, ps) →
          nF c1 ≤ nF c2 ∧ ∀ x, x ∈ f (cfgF c1, pF ps) → nF c1 ≤ x ∧ x < nF c2) →
      oracleMonotonic f (· < ·) St (cakeOrac asmConf c' syntaxOrac cfgF pF) := by
  intro nF ⟨h0, hs⟩
  apply oracleMonotonic_cakeOrac_to_I
  refine oracleMonotonic_boundedState St _ _ (nF ∘ Prod.fst) ⟨?_, ?_⟩
  · intro x hx
    simp only [Function.comp_apply, cakeOrac_eq_pair, id]
    exact h0 x hx
  · intro i
    rcases hr : compileIncProgs true asmConf (cakeConfigs asmConf c' syntaxOrac i) (syntaxOrac i)
      with ⟨c2, ps⟩
    have h := hs i c2 ps hr
    have hnext : cakeConfigs asmConf c' syntaxOrac (i + 1) = c2 := by
      show (compileIncProgs true asmConf (cakeConfigs asmConf c' syntaxOrac i) (syntaxOrac i)).1 = c2
      rw [hr]
    simp only [Function.comp_apply, cakeOrac_eq_pair, id, hnext, hr]
    exact ⟨h.1, fun x hx => h.2 x hx⟩

end Flapjack.Compiler.Backend.BackendProof
