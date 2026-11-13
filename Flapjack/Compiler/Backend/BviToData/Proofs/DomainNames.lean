module

public import Flapjack.Compiler.Backend.BviToData.Proofs.CutEnv

@[expose] public section

/-! Domains of the compiler's sparse live-name sets. -/
namespace Flapjack.Compiler.Backend.BviToData
open Flapjack

/-- The generated sparse set has exactly the input names as its domain. -/
@[hol "cakeml/compiler/backend/proofs/bvi_to_dataProofScript.sml" "domain_list_to_num_set2"]
theorem domain_namesOfList (names : List Nat) :
    sptDomain (namesOfList names) = {key | key ∈ names} := by
  funext key
  apply propext
  exact namesOfList_mem names key

/-- Inserting a list extends the tree's domain by precisely those names. -/
@[hol "cakeml/compiler/backend/proofs/bvi_to_dataProofScript.sml" "domain_list_insert2"]
theorem domain_listInsert (names : List Nat) (tree : NumSet) :
    sptDomain (sptListInsert names tree) = {key | key ∈ names} ∪ sptDomain tree := by
  funext key
  apply propext
  change sptMem key (sptListInsert names tree) ↔ key ∈ names ∨ sptMem key tree
  induction names generalizing tree with
  | nil => simp [sptListInsert]
  | cons name names ih =>
    rw [sptListInsert, ih, sptMem_sptInsert]
    simp [List.mem_cons, or_assoc, or_comm, or_left_comm]

end Flapjack.Compiler.Backend.BviToData
