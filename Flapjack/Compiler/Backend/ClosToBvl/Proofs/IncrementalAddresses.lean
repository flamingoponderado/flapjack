module

public import Flapjack.Compiler.Backend.ClosToBvl.ExtractName.Original
public import Flapjack.Compiler.Backend.ClosToBvl.Layout
public import Flapjack.Compiler.Backend.ClosToBvl.SourceInc
public import Flapjack.Compiler.Backend.ClosToBvl.Proofs.LabelOrigins
public import Flapjack.Compiler.Backend.ClosToBvl.Proofs.ChainLocations
public import Flapjack.Compiler.Backend.Semantics.ClosProps.CodeLocations
public import Flapjack.HolRef

@[expose] public section

/-! Address requirements for the incremental closure compiler. -/
namespace Flapjack.Compiler.Backend.ClosToBvl
open ClosLang ClosProps

/-- The list arithmetic used when reserving at least one entry address. -/
@[hol "cakeml/compiler/backend/proofs/clos_to_bvlProofScript.sml" "trivia_1"]
theorem incrementalAddress_trivia {α : Type} (x : Nat) (xs : List α) (v : α) :
    List.range 1 = [0] ∧ max 1 (x + 1) = x + 1 ∧
      (if xs = [] then [v] else xs).length = max 1 xs.length := by
  constructor
  · rfl
  constructor
  · omega
  · cases xs <;> simp

/-- A list has a head and tail exactly when it is nonempty. -/
@[hol "cakeml/compiler/backend/proofs/clos_to_bvlProofScript.sml" "EXISTS_CONS_NOT_NULL"]
theorem existsCons_notNull {α : Type} (ys : List α) :
    (∃ x xs, ys = x :: xs) ↔ ¬ ys.isEmpty := by
  cases ys <;> simp

/-- An operation contributes the locations in its arguments followed by the tail. -/
@[hol "cakeml/compiler/backend/proofs/clos_to_bvlProofScript.sml" "code_locs_Op_cons"]
theorem codeLocations_op_cons (c : List ClosLang.Exp) (b : ClosLang.Op)
    (a : BackendCommon.Tra) (xs : List ClosLang.Exp) :
    codeLocations (.op a b c :: xs) = codeLocations c ++ codeLocations xs := by
  rfl

/-- Addresses assigned to the extracted entry-point expression chain. -/
@[hol "cakeml/compiler/backend/proofs/clos_to_bvlProofScript.sml" "extracted_addrs_def"]
noncomputable def extractedAddrs (exps : List ClosLang.Exp) : List Nat :=
  if exps = [] then [0]
  else let (n, realExps) := extractNameSource exps
       (List.range (max 1 realExps.length)).map (n + ·)

/-- The locations an incremental compiler input requires, including each
extra transformation of locations in the initial expression list. -/
@[hol "cakeml/compiler/backend/proofs/clos_to_bvlProofScript.sml" "req_compile_inc_addrs_def"]
noncomputable def reqCompileIncAddrs {α : Type} (extra : List (Nat → Nat))
    (program : List ClosLang.Exp × List (Nat × α × ClosLang.Exp)) : List Nat :=
  let (exps, code) := program
  extractedAddrs exps ++ codeLocations exps ++ code.map Prod.fst ++
    codeLocations (code.map (fun t => t.2.2)) ++
    (extra.map (fun f => (codeLocations exps).map f)).flatten

/-- The initial expression carries a nonnegative integer entry name. -/
@[hol "cakeml/compiler/backend/proofs/clos_to_bvlProofScript.sml" "can_extract_def"]
def canExtract (exps : List ClosLang.Exp) : Prop :=
  ∃ tr n rest, exps = .op tr (.intOp (.const (Int.ofNat n))) [] :: rest

/-- An extractable entry expression has either an empty or nonempty tail. -/
@[hol "cakeml/compiler/backend/proofs/clos_to_bvlProofScript.sml" "can_extract_to_case"]
theorem canExtract_to_case (exps : List ClosLang.Exp) :
    canExtract exps →
      (∃ tr n, exps = [.op tr (.intOp (.const (Int.ofNat n))) []]) ∨
      (∃ tr n e rest, exps = .op tr (.intOp (.const (Int.ofNat n))) [] :: e :: rest) := by
  rintro ⟨tr, n, rest, rfl⟩
  cases rest with
  | nil => exact Or.inl ⟨tr, n, rfl⟩
  | cons e rest => exact Or.inr ⟨tr, n, e, rest, rfl⟩

/-- Extracting the entry point gives exactly the chained-entry addresses. -/
@[hol "cakeml/compiler/backend/proofs/clos_to_bvlProofScript.sml" "extract_name_MAP_FST_addrs"]
theorem extractName_mapFst_addrs (exps : List ClosLang.Exp) (n : Nat) (realExps : List ClosLang.Exp)
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

/-- Extracting a name preserves all closure code locations. -/
@[hol "cakeml/compiler/backend/proofs/clos_to_bvlProofScript.sml" "extract_name_code_locs"]
theorem extractName_codeLocations (exps : List ClosLang.Exp) (n : Nat) (realExps : List ClosLang.Exp)
    (h : extractNameSource exps = (n, realExps)) :
    codeLocations realExps = codeLocations exps := by
  rw [extractNameSource_eq_extractName] at h
  cases exps with
  | nil => simp [extractName] at h; simp_all [codeLocations]
  | cons e es =>
    cases e <;> simp only [extractName] at h
    all_goals repeat (first | split at h | cases h)
    all_goals simp_all [codeLocations, codeLocationsExp]
    all_goals rcases h with ⟨_, rfl⟩
    all_goals simp [codeLocations, codeLocationsExp]

private theorem incAddressPerm (maxApp : Nat) (program : List ClosLang.Exp × List (Nat × Nat × ClosLang.Exp)) :
    ((compileInc maxApp program).map Prod.fst).Perm
      ((reqCompileIncAddrs [] program).map (numStubs maxApp + ·)) := by
  obtain ⟨exps, code⟩ := program
  cases h : extractNameSource exps with
  | mk start realExps =>
    have extracted := extractName_mapFst_addrs exps start realExps h
    have locations := extractName_codeLocations exps start realExps h
    have chain := chainExps_codeLocations start realExps
    have compiled := compileProg_codeLocs maxApp (chainExps start realExps ++ code)
    simp only [compileInc, h]
    rw [compiled]
    simp only [List.map_append, codeLocations_append, chain, locations]
    simp only [reqCompileIncAddrs, List.map_nil, List.flatten_nil, List.append_nil]
    rw [← extracted]
    simp only [List.map_append, List.map_reverse, List.map_map, Function.comp_def]
    apply List.perm_iff_count.mpr
    intro label
    simp only [List.count_append, List.count_reverse]
    ac_rfl
/-- Incremental compilation preserves required-address distinctness and
emits only shifted required addresses. -/
@[hol "cakeml/compiler/backend/proofs/clos_to_bvlProofScript.sml" "compile_inc_req_addrs"]
theorem compileInc_reqAddrs (program : List ClosLang.Exp × List (Nat × Nat × ClosLang.Exp))
    (maxApp : Nat) :
    (((reqCompileIncAddrs [] program).Nodup → ((compileInc maxApp program).map Prod.fst).Nodup) ∧
      {x | x ∈ (compileInc maxApp program).map Prod.fst} ⊆
        {x | x ∈ (reqCompileIncAddrs [] program).map (numStubs maxApp + ·)}) := by
  have perm := incAddressPerm maxApp program
  constructor
  · intro nodup
    apply perm.nodup_iff.mpr
    exact (List.nodup_map_iff (fun _ _ equal => Nat.add_left_cancel equal)).2 nodup
  · intro label member
    exact perm.mem_iff.mp member

end Flapjack.Compiler.Backend.ClosToBvl
