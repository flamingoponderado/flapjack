module

public import Flapjack.Compiler.Backend.BvlToBvi.SourceProgram
public import Flapjack.Compiler.Backend.BvlToBvi.Proofs.AuxNameRange
public import Flapjack.Compiler.Backend.BviTailrec.Proofs.CodeLabels
public import Flapjack.Compiler.Backend.BviTailrec.Proofs.RewriteCorrespondence
public import Flapjack.Compiler.Backend.BviTmc.Proofs.CodeRelation
public import Flapjack.Compiler.Backend.BviTmc.Proofs.RewriteCorrespondence
public import Flapjack.Compiler.Backend.BvlInline.SourceCompile
public import Flapjack.Compiler.Backend.BvlInline.Proofs.ProgramProduction
public import Flapjack.Compiler.Backend.BviInline.Source
public import Flapjack.Compiler.Backend.BviInline.Proofs.CodeLabels
public import Flapjack.Compiler.Backend.BackendProps.OracleMonotonic

@[expose] public section

/-! backendProofScript.sml 1666-1702 and 1752-1789: function-name facts for
the BVL-to-BVI passes (namespace avoidance, inlining keeps names). -/
namespace Flapjack.Compiler.Backend.BackendProof

open Flapjack Flapjack.Compiler.Backend.BackendProps

/-- Exact HOL `compile_prog_avoids_nss_2` (`backendProofScript.sml:1666-1678`).
`MEM` is list membership; HOL's free variables are explicit. -/
@[hol "cakeml/compiler/backend/proofs/backendProofScript.sml" "compile_prog_avoids_nss_2"]
theorem compileProg_avoidsNss2 (start f : Nat) (prog : List (Nat × Nat × Bvl.Exp))
    (loc : Nat) (code : List (Nat × Nat × Bvi.Exp)) (newState k : Nat) :
    BvlToBvi.compileProgSource start f prog = (loc, code, newState) ∧
      k ∈ code.map Prod.fst ∧ k % bvlToBviNamespaces = 2 →
      k < bvlNumStubs := by
  rintro ⟨h, hk, hm⟩
  rcases hc : BvlToBvi.compileProgramsSource f prog with ⟨cd, m⟩
  simp only [BvlToBvi.compileProgSource, hc, Prod.mk.injEq] at h
  obtain ⟨-, rfl, -⟩ := h
  rw [List.map_append, List.mem_append] at hk
  rcases hk with hk | hk
  · simp only [BvlToBvi.stubs, List.map_cons, List.map_nil, List.mem_cons,
      List.not_mem_nil, or_false] at hk
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  · have hd := (BvlToBvi.Proofs.compileList_codeLabelsDomain f prog cd m hc).2
    have hk' : k ∈ {x : Nat | x ∈ (appListAppend cd).map Prod.fst} := hk
    rw [hd] at hk'
    have hns : bvlToBviNamespaces = 4 := rfl
    have hst : bvlNumStubs % 4 = 0 ∨ bvlNumStubs % 4 = 3 := by decide
    rcases hk' with ⟨j, -, rfl⟩ | ⟨j, rfl, -⟩ <;> simp only [hns] at * <;> omega

/-- Exact HOL `tailrec_compile_prog_MEM_not_nss_2`
(`backendProofScript.sml:1680-1690`). -/
@[hol "cakeml/compiler/backend/proofs/backendProofScript.sml" "tailrec_compile_prog_MEM_not_nss_2"]
theorem tailrecCompileProg_mem_notNss2 :
    ∀ (ys xs : List (Nat × Nat × Bvi.Exp)) (n1 n e : Nat) (doIt : Bool),
      BviTailrec.compileProgSource doIt n xs = (n1, ys) ∧ e ∈ ys.map Prod.fst ∧
        n % bvlToBviNamespaces = 2 ∧ e % bvlToBviNamespaces ≠ 2 →
      e ∈ xs.map Prod.fst := by
  rintro ys xs n1 n e doIt ⟨h, he, hn, hne⟩
  rcases BviTailrec.Proofs.compileProg_mem doIt n xs n1 ys e ⟨h, he⟩ with h1 | ⟨-, -, k, rfl⟩
  · exact h1
  · have hns : bvlToBviNamespaces = 4 := rfl
    rw [hns] at hn hne
    omega

/-- Exact HOL `tmc_compile_prog_MEM_not_nss_3` (`backendProofScript.sml:1692-1702`). -/
@[hol "cakeml/compiler/backend/proofs/backendProofScript.sml" "tmc_compile_prog_MEM_not_nss_3"]
theorem tmcCompileProg_mem_notNss3 :
    ∀ (ys xs : List (Nat × Nat × Bvi.Exp)) (n1 n e : Nat) (doIt : Bool),
      BviTmc.compileProgSource doIt n xs = (n1, ys) ∧ e ∈ ys.map Prod.fst ∧
        n % bvlToBviNamespaces = 3 ∧ e % bvlToBviNamespaces ≠ 3 →
      e ∈ xs.map Prod.fst := by
  rintro ys xs n1 n e doIt ⟨h, he, hn, hne⟩
  rcases BviTmc.compileProgSource_mem doIt n n1 e xs ys h he with h1 | ⟨-, -, k, rfl⟩
  · exact h1
  · have hns : Flapjack.bvlToBviNamespaces = 4 := rfl
    rw [hns] at hn hne
    omega

/-- Exact HOL `inline_compile_inc_names` (`backendProofScript.sml:1752-1761`). -/
@[hol "cakeml/compiler/backend/proofs/backendProofScript.sml" "inline_compile_inc_names"]
theorem inlineCompileInc_names (l : Nat) (b : Bool) (i : Nat) (spt : Spt (Nat × Bvl.Exp))
    (prog : List (Nat × Nat × Bvl.Exp)) (inlines : Spt (Nat × Bvl.Exp))
    (prog3 : List (Nat × Nat × Bvl.Exp)) :
    BvlInline.compileInc l b i spt prog = (inlines, prog3) →
      prog3.map Prod.fst = prog.map Prod.fst := by
  intro h
  rcases ht : BvlInline.tickCompileProg l spt prog with ⟨cache, p⟩
  simp only [BvlInline.compileInc, ht, Prod.mk.injEq] at h
  obtain ⟨-, rfl⟩ := h
  have names := BvlInline.tickInlineAllNames l spt prog () cache p [] ht
  simp only [List.reverse_nil, List.map_nil, List.nil_append] at names
  rw [names, List.map_map]
  congr 1

/-- Exact HOL `bvi_inline_state_co_MAP_FST` (`backendProofScript.sml:1763-1771`). -/
@[hol "cakeml/compiler/backend/proofs/backendProofScript.sml" "bvi_inline_state_co_MAP_FST"]
theorem bviInline_stateCo_mapFst {α β : Type}
    (co : β → (Spt (Nat × Bvi.Exp) × α) × List (Nat × Nat × Bvi.Exp)) (n : β) :
    (stateCo BviInline.compileIncSource co n).2.map Prod.fst = (co n).2.map Prod.fst := by
  rcases h : BviInline.compileIncSource (co n).1.1 (co n).2 with ⟨cs1, p1⟩
  simp only [stateCo, h]
  exact BviInline.Proofs.compileInc_mapFst _ _ _ _ h

/-- Exact HOL `oracle_monotonic_bvi_inline` (`backendProofScript.sml:1773-1781`).
HOL `set` is the membership set; boolean equality is `↔`. -/
@[hol "cakeml/compiler/backend/proofs/backendProofScript.sml" "oracle_monotonic_bvi_inline"]
theorem oracleMonotonic_bviInline {α : Type} (R : Nat → Nat → Prop) (init : Set Nat)
    (co : Nat → (Spt (Nat × Bvi.Exp) × α) × List (Nat × Nat × Bvi.Exp)) :
    oracleMonotonic ((fun l => {x | x ∈ l}) ∘ List.map Prod.fst ∘ Prod.snd) R init
        (stateCo BviInline.compileIncSource co) ↔
      oracleMonotonic ((fun l => {x | x ∈ l}) ∘ List.map Prod.fst ∘ Prod.snd) R init co := by
  have h : ∀ n, (stateCo BviInline.compileIncSource co n).2.map Prod.fst =
      (co n).2.map Prod.fst := bviInline_stateCo_mapFst co
  simp only [oracleMonotonic, Function.comp_apply, h]

/-- Exact HOL `oracle_monotonic_bvi_inline_inter` (`backendProofScript.sml:1783-1789`). -/
@[hol "cakeml/compiler/backend/proofs/backendProofScript.sml" "oracle_monotonic_bvi_inline_inter"]
theorem oracleMonotonic_bviInline_inter {α : Type} (s : Set Nat) (R : Nat → Nat → Prop)
    (init : Set Nat) (co : Nat → (Spt (Nat × Bvi.Exp) × α) × List (Nat × Nat × Bvi.Exp)) :
    oracleMonotonic (fun x : α × List (Nat × Nat × Bvi.Exp) => {y | y ∈ x.2.map Prod.fst} ∩ s)
        R init (stateCo BviInline.compileIncSource co) ↔
      oracleMonotonic (fun x : (Spt (Nat × Bvi.Exp) × α) × List (Nat × Nat × Bvi.Exp) =>
        {y | y ∈ x.2.map Prod.fst} ∩ s) R init co := by
  have h : ∀ n, (stateCo BviInline.compileIncSource co n).2.map Prod.fst =
      (co n).2.map Prod.fst := bviInline_stateCo_mapFst co
  simp only [oracleMonotonic, h]

end Flapjack.Compiler.Backend.BackendProof
