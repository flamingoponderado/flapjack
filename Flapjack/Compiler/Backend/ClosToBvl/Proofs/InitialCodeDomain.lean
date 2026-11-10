module

public import Flapjack.Compiler.Backend.ClosToBvl.Stubs
public import Flapjack.Misc.Sptree.FromList.Domain

@[expose] public section

/-! Domain of the generated closure-application stubs. -/
namespace Flapjack.Compiler.Backend.ClosToBvl

private theorem triangleLength {α : Type} (f : Nat → Nat → α) (count : Nat) :
    (((List.range count).map fun total => (List.range total).map (f total)).flatten).length =
      count * (count - 1) / 2 := by
  have twice : ∀ n, (((List.range n).map fun total => (List.range total).map (f total)).flatten).length * 2 =
      n * (n - 1) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      simp only [List.range_succ, List.map_append, List.map_cons, List.map_nil,
        List.flatten_append, List.flatten_cons, List.flatten_nil, List.append_nil,
        List.length_append, List.length_map, List.length_range]
      cases n with
      | zero => simp
      | succ n =>
        simp only [Nat.add_sub_cancel] at *
        simp only [Nat.add_mul, Nat.mul_add, Nat.one_mul, Nat.mul_one] at ih ⊢
        omega
  have h := congrArg (fun n : Nat => n / 2) (twice count)
  simpa using h

/-- The initial stub domain is the source's triangular initial segment. -/
@[hol "cakeml/compiler/backend/proofs/clos_to_bvlProofScript.sml" "domain_init_code"]
theorem domain_initCode (maxApp : Nat) (_positive : 0 < maxApp) :
    sptDomain (initCode maxApp) =
      fun key => key < maxApp + maxApp * (maxApp - 1) / 2 := by
  rw [initCode, sptDomainFromList]
  simp only [List.length_append, List.length_map, List.length_range, triangleLength]

/-- Every generated stub lies below the reserved-stub count. -/
@[hol "cakeml/compiler/backend/proofs/clos_to_bvlProofScript.sml" "domain_init_code_lt_num_stubs"]
theorem domain_initCode_lt_numStubs (maxApp key : Nat)
    (member : sptDomain (initCode maxApp) key) : key < numStubs maxApp := by
  cases maxApp with
  | zero => simp [initCode, sptFromList, sptDomain] at member
  | succ n =>
    rw [domain_initCode (n + 1) (by omega)] at member
    simp only [numStubs]
    omega

end Flapjack.Compiler.Backend.ClosToBvl
