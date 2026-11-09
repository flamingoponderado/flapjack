module

public import Flapjack.Compiler.Backend.ClosToBvl.ExtractName.Original
public import Flapjack.Compiler.Backend.ClosToBvl.Layout
public import Flapjack.Compiler.Backend.Semantics.ClosProps.CodeLocations
public import Flapjack.HolRef

@[expose] public section

/-! Address requirements for the incremental closure compiler. -/
namespace Flapjack.Compiler.Backend.ClosToBvl
open ClosLang ClosProps

/-- Addresses assigned to the extracted entry-point expression chain. -/
@[hol "cakeml/compiler/backend/proofs/clos_to_bvlProofScript.sml" "extracted_addrs_def"]
noncomputable def extractedAddrs (exps : List Exp) : List Nat :=
  if exps = [] then [0]
  else let (n, realExps) := extractNameSource exps
       (List.range (max 1 realExps.length)).map (n + ·)

/-- The locations an incremental compiler input requires, including each
extra transformation of locations in the initial expression list. -/
@[hol "cakeml/compiler/backend/proofs/clos_to_bvlProofScript.sml" "req_compile_inc_addrs_def"]
noncomputable def reqCompileIncAddrs {α : Type} (extra : List (Nat → Nat))
    (program : List Exp × List (Nat × α × Exp)) : List Nat :=
  let (exps, code) := program
  extractedAddrs exps ++ codeLocations exps ++ code.map Prod.fst ++
    codeLocations (code.map (fun t => t.2.2)) ++
    (extra.map (fun f => (codeLocations exps).map f)).flatten

/-- The initial expression carries a nonnegative integer entry name. -/
@[hol "cakeml/compiler/backend/proofs/clos_to_bvlProofScript.sml" "can_extract_def"]
def canExtract (exps : List Exp) : Prop :=
  ∃ tr n rest, exps = .op tr (.intOp (.const (Int.ofNat n))) [] :: rest

/-- Chained expression labels form the complete range, with one entry for an
empty expression list. -/
@[hol "cakeml/compiler/backend/proofs/clos_to_bvlProofScript.sml" "MAP_FST_chain_exps_any"]
theorem mapFst_chainExps_any (start : Nat) (exps : List Exp) :
    (chainExps start exps).map Prod.fst =
      (List.range (max 1 exps.length)).map (start + ·) := by
  induction exps generalizing start with
  | nil => simp [chainExps]
  | cons first rest ih =>
    cases rest with
    | nil => simp [chainExps]
    | cons second tail =>
      have step := ih (start + 1)
      simp only [chainExps, List.map_cons] at step ⊢
      simp only [List.length_cons] at step ⊢
      rw [Nat.max_eq_right (by omega : 1 ≤ tail.length + 1)] at step
      rw [Nat.max_eq_right (by omega : 1 ≤ tail.length + 1 + 1)]
      rw [List.range_succ_eq_map]
      simp only [List.map_cons, List.map_map, Function.comp_def]
      congr 1
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using step

/-- Extracting the entry point gives exactly the chained-entry addresses. -/
@[hol "cakeml/compiler/backend/proofs/clos_to_bvlProofScript.sml" "extract_name_MAP_FST_addrs"]
theorem extractName_mapFst_addrs (exps : List Exp) (n : Nat) (realExps : List Exp)
    (h : extractNameSource exps = (n, realExps)) :
    (chainExps n realExps).map Prod.fst = extractedAddrs exps := by
  cases exps with
  | nil =>
    simp [extractNameSource] at h
    rcases h with ⟨rfl, rfl⟩
    simp [extractedAddrs, chainExps]
  | cons e es =>
    rw [mapFst_chainExps_any]
    simp [extractedAddrs, h]

end Flapjack.Compiler.Backend.ClosToBvl
