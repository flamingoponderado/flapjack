module

public import Flapjack.Compiler.Backend.BvlToBvi.Config
public import Mathlib.Algebra.Ring.Parity
import Lean.Elab.Tactic.Omega

@[expose] public section

namespace Flapjack.Compiler.Backend.BvlToBvi.Proofs

/-- Adding an even multiple of two preserves oddness. -/
@[hol "cakeml/compiler/backend/proofs/bvl_to_bviProofScript.sml" "ODD_lemma"]
theorem odd_double_add (n k : Nat) : Odd (2 * n + k) ↔ Odd k := by
  simp only [Nat.odd_iff]
  omega

/-- The original interleaved namespace predicate. -/
@[hol "cakeml/compiler/backend/proofs/bvl_to_bviProofScript.sml" "in_ns_def"]
def inNs (k n : Nat) : Prop := n % bvlToBviNamespaces = k

/-- The namespace count itself belongs to namespace zero. -/
@[hol "cakeml/compiler/backend/proofs/bvl_to_bviProofScript.sml" "nss_in_ns"]
theorem namespaceCount_inNs (k : Nat) : inNs k bvlToBviNamespaces ↔ k = 0 := by
  simp [inNs, bvlToBviNamespaces, eq_comm]

/-- Multiples of the namespace count belong to namespace zero. -/
@[hol "cakeml/compiler/backend/proofs/bvl_to_bviProofScript.sml" "mult_nss_in_ns"]
theorem namespaceMultiple_inNs (k m : Nat) : inNs k (m * bvlToBviNamespaces) ↔ k = 0 := by
  simp [inNs, bvlToBviNamespaces, eq_comm]

/-- A multiple plus one belongs to namespace one. -/
@[hol "cakeml/compiler/backend/proofs/bvl_to_bviProofScript.sml" "mult_nss_in_ns_1"]
theorem namespaceMultipleOne_inNs (k m : Nat) : inNs k (m * bvlToBviNamespaces + 1) ↔ k = 1 := by
  simp [inNs, bvlToBviNamespaces, Nat.add_mod, eq_comm]

/-- A multiple plus two belongs to namespace two. -/
@[hol "cakeml/compiler/backend/proofs/bvl_to_bviProofScript.sml" "mult_nss_in_ns_2"]
theorem namespaceMultipleTwo_inNs (k m : Nat) : inNs k (m * bvlToBviNamespaces + 2) ↔ k = 2 := by
  simp [inNs, bvlToBviNamespaces, Nat.add_mod, eq_comm]

/-- Adding one moves namespace zero to namespace one. -/
@[hol "cakeml/compiler/backend/proofs/bvl_to_bviProofScript.sml" "in_ns_1_add_1"]
theorem inNs_zero_addOne (x : Nat) : inNs 0 x → inNs 1 (x + 1) := by
  simp only [inNs, bvlToBviNamespaces]
  omega

/-- Adding the stub count preserves the namespace. -/
@[hol "cakeml/compiler/backend/proofs/bvl_to_bviProofScript.sml" "in_ns_add_num_stubs"]
theorem inNs_addStubCount (k x : Nat) : inNs k (bvlNumStubs + x) ↔ inNs k x := by
  simp only [inNs, Nat.add_mod, bvlNumStubMod, Nat.zero_add, Nat.mod_mod]
/-- Namespace-zero multiples differ from namespace-one multiples. -/
@[hol "cakeml/compiler/backend/proofs/bvl_to_bviProofScript.sml" "nss_lemma"]
theorem namespaceMultiple_ne (n k : Nat) :
    n * bvlToBviNamespaces ≠ k * bvlToBviNamespaces + 1 := by
  simp only [bvlToBviNamespaces]
  omega

/-- A translated function label belongs to namespace zero. -/
@[hol "cakeml/compiler/backend/proofs/bvl_to_bviProofScript.sml" "in_ns_0_simp"]
theorem translatedLabel_inNs_zero (p : Nat) :
    inNs 0 (bvlToBviNamespaces * p + bvlNumStubs) := by
  simp [inNs, Nat.add_mod, bvlNumStubMod]

/-- A translated source name is not in namespace one. -/
@[hol "cakeml/compiler/backend/proofs/bvl_to_bviProofScript.sml" "not_in_ns_1"]
theorem translatedName_notInNsOne (name : Nat) :
    ¬ inNs 1 (bvlNumStubs + name * bvlToBviNamespaces) := by
  simp [inNs, Nat.add_mod, bvlNumStubMod]

/-- Dividing a translated name's namespace multiple recovers the name. -/
@[hol "cakeml/compiler/backend/proofs/bvl_to_bviProofScript.sml" "names_nss_DIV_nss"]
theorem nameMultiple_div (name : Nat) :
    (name * bvlToBviNamespaces) / bvlToBviNamespaces = name := by
  simp [bvlToBviNamespaces]

end Flapjack.Compiler.Backend.BvlToBvi.Proofs
