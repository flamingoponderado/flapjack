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

/-- HOL uses this triangular-table indexing calculation in its stub proof. -/
private theorem triangleLookup {α : Type} (f : Nat → Nat → α) (limit total previous : Nat)
    (hp : previous < total) (ht : total < limit) :
    (((List.range limit).map fun n => (List.range n).map (f n)).flatten)[previous + total * (total - 1) / 2]? = some (f total previous) := by
  induction limit with
  | zero => omega
  | succ limit ih =>
    have expand : (((List.range (limit + 1)).map fun n => (List.range n).map (f n)).flatten) =
        (((List.range limit).map fun n => (List.range n).map (f n)).flatten) ++
          (List.range limit).map (f limit) := by
      simp [List.range_succ, List.map_append]
    rw [expand, List.getElem?_append]
    by_cases same : total = limit
    · subst limit
      rw [triangleLength f total]
      simp [hp]
    · have inside : total < limit := by omega
      have prior := ih inside
      have idxBound : previous + total * (total - 1) / 2 <
          (((List.range limit).map fun n => (List.range n).map (f n)).flatten).length :=
        List.getElem?_eq_some_iff.mp prior |>.choose
      rw [ite_eq_left idxBound]
      exact prior

/-- Initial code contains every generic and partial-application stub. -/
@[hol "cakeml/compiler/backend/proofs/clos_to_bvlProofScript.sml" "init_code_ok"]
theorem initCode_ok (maxApp : Nat) (_positive : 0 < maxApp) :
    (∀ n, n < maxApp → sptLookup (genericAppFnLocation n) (initCode maxApp) =
      some (n + 2, generateGenericApp maxApp n)) ∧
    (∀ total previous, total < maxApp ∧ previous < total →
      sptLookup (partialAppFnLocation maxApp total previous) (initCode maxApp) =
        some (total - previous + 1, generatePartialAppClosureFn total previous)) := by
  constructor
  · intro n hn
    simp [initCode, sptLookupFromList_getElem?, genericAppFnLocation, List.getElem?_append, hn]
  · intro total previous ⟨ht, hp⟩
    rw [initCode, sptLookupFromList_getElem?]
    simp only [partialAppFnLocation, List.getElem?_append, List.length_map, List.length_range]
    have out : ¬ maxApp + total * (total - 1) / 2 + previous < maxApp := by omega
    simp only [out, ↓reduceIte]
    have eq : maxApp + total * (total - 1) / 2 + previous - maxApp =
        previous + total * (total - 1) / 2 := by omega
    rw [eq]
    exact triangleLookup (fun t p => (t - p + 1, generatePartialAppClosureFn t p)) maxApp total previous hp ht


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
