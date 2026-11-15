module

public import Flapjack.Compiler.Backend.ClosToBvl.Stubs
public import Flapjack.Misc.Sptree.FromList.Domain
public import Flapjack.Misc.ListEl

@[expose] public section

/-! Domain of the generated closure-application stubs. -/
namespace Flapjack.Compiler.Backend.ClosToBvl

/-- A row of a flattened rectangular table recovers its row and column. -/
@[hol "cakeml/compiler/backend/proofs/clos_to_bvlProofScript.sml" "twod_table_lemma"]
theorem twodTableLemma {α : Type} (f : Nat → Nat → α) (x y z : Nat) :
    z ≤ y →
    (List.range z).map (fun t => f ((t + x * y) / y) ((t + x * y) % y)) =
      (List.range z).map (fun t => f x t) := by
  intro hz
  apply List.map_congr_left
  intro t ht
  have bound : t < y := by simp only [List.mem_range] at ht; omega
  have positive : 0 < y := by omega
  simp [Nat.add_mul_div_right t x positive, Nat.div_eq_of_lt bound, Nat.mod_eq_of_lt bound]

/-- Flattening a rectangular table gives row-major division and remainder indices. -/
@[hol "cakeml/compiler/backend/proofs/clos_to_bvlProofScript.sml" "twod_table"]
theorem twodTable {α : Type} (f : Nat → Nat → α) (x y : Nat) :
    0 < y →
    (((List.range x).map fun m => (List.range y).map (f m)).flatten) =
      (List.range (x * y)).map (fun n => f (n / y) (n % y)) := by
  intro hy
  induction x with
  | zero => simp
  | succ x ih =>
    simp only [List.range_succ, List.map_append, List.map_cons, List.map_nil,
      List.flatten_append, List.flatten_cons, List.flatten_nil, List.append_nil]
    rw [ih]
    have size : (x + 1) * y = x * y + y := by simp [Nat.add_mul]
    rw [size, List.range_add, List.map_append, List.map_map]
    congr 1
    simpa only [Function.comp_def, Nat.add_comm] using (twodTableLemma f x y y (Nat.le_refl y)).symm

/-- A row and column within a rectangle determine an index within its area. -/
@[hol "cakeml/compiler/backend/proofs/clos_to_bvlProofScript.sml" "less_rectangle"]
theorem lessRectangle (x y m n : Nat) :
    m < x ∧ n < y → x * n + m < x * y := by
  intro ⟨hm, hn⟩
  have h := Nat.mul_le_mul_left x (show n + 1 ≤ y by omega)
  simp only [Nat.mul_add, Nat.mul_one] at h
  omega

/-- The same rectangle bound with the summands and factors exchanged. -/
@[hol "cakeml/compiler/backend/proofs/clos_to_bvlProofScript.sml" "less_rectangle2"]
theorem lessRectangle2 (x y m n : Nat) :
    m < x ∧ n < y → m + n * x < x * y := by
  intro h
  simpa only [Nat.add_comm, Nat.mul_comm] using lessRectangle x y m n h

/-- Split equality with a conditional into its two Boolean cases. -/
@[hol "cakeml/compiler/backend/proofs/clos_to_bvlProofScript.sml" "if_expand"]
theorem ifExpand {α : Type} (w : α) (x : Bool) (y z : α) :
    ((if x then y else z) = w) ↔
      ((x = true ∧ y = w) ∨ (¬ x = true ∧ z = w)) := by
  cases x <;> simp

/-- The length of the generated triangular table. -/
@[hol "cakeml/compiler/backend/proofs/clos_to_bvlProofScript.sml" "triangle_table_size"]
theorem triangleTableSize {α : Type} (count : Nat) (f : Nat → Nat → α) :
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
      rw [triangleTableSize total f]
      simp [hp]
    · have inside : total < limit := by omega
      have prior := ih inside
      have idxBound : previous + total * (total - 1) / 2 <
          (((List.range limit).map fun n => (List.range n).map (f n)).flatten).length :=
        List.getElem?_eq_some_iff.mp prior |>.choose
      rw [if_pos idxBound]
      exact prior

/-- A generated triangular-table slot lies within the table. -/
@[hol "cakeml/compiler/backend/proofs/clos_to_bvlProofScript.sml" "triangle_div_lemma"]
theorem triangleDivLemma (maxApp n tot : Nat) :
    tot < maxApp ∧ n < tot →
      n + tot * (tot - 1) / 2 < maxApp * (maxApp - 1) / 2 := by
  intro ⟨ht, hn⟩
  have entry := triangleLookup (fun _ _ => ()) maxApp tot n hn ht
  have bound := (List.getElem?_eq_some_iff.mp entry).1
  simpa only [triangleTableSize] using bound

/-- The sum of the first natural numbers is their triangular number. -/
@[hol "cakeml/compiler/backend/proofs/clos_to_bvlProofScript.sml" "sum_genlist_triangle"]
theorem sumGenlistTriangle (x : Nat) :
    ((List.range x).map (fun y => y)).sum = x * (x - 1) / 2 := by
  simpa [List.length_flatten, List.map_map, Function.comp_def] using
    triangleTableSize x (fun _ _ => ())

/-- The successor form of the triangular sum. -/
@[hol "cakeml/compiler/backend/proofs/clos_to_bvlProofScript.sml" "sum_genlist_triangle_help"]
theorem sumGenlistTriangleHelp (x : Nat) :
    ((List.range (x + 1)).map (fun y => y)).sum = x * (x + 1) / 2 := by
  simpa only [Nat.add_sub_cancel, Nat.mul_comm] using sumGenlistTriangle (x + 1)

/-- Successive triangular offsets grow across distinct table rows. -/
@[hol "cakeml/compiler/backend/proofs/clos_to_bvlProofScript.sml" "tri_lemma"]
theorem triLemma (tot maxApp : Nat) :
    tot < maxApp →
      tot + tot * (tot - 1) / 2 < maxApp + (maxApp - 1) * (maxApp - 2) / 2 := by
  intro ht
  cases maxApp with
  | zero => omega
  | succ k =>
    have step : (k + 1) * ((k + 1) - 1) / 2 = k * (k - 1) / 2 + k := by
      have h := triangleTableSize (k + 1) (fun _ _ => ())
      simp only [List.range_succ, List.map_append, List.map_cons, List.map_nil,
        List.flatten_append, List.flatten_cons, List.flatten_nil, List.append_nil,
        List.length_append, List.length_map, List.length_range, triangleTableSize] at h
      omega
    have sub : k + 1 - 2 = k - 1 := by omega
    simp only [Nat.add_sub_cancel, sub] at step ⊢
    by_cases positive : 0 < tot
    · have bound := triangleDivLemma (k + 1) (tot - 1) tot ⟨ht, by omega⟩
      simp only [Nat.add_sub_cancel] at bound
      omega
    · have zero : tot = 0 := by omega
      subst tot
      simp only [Nat.zero_sub, Nat.zero_mul, Nat.zero_div, Nat.zero_add]
      omega

/-- A bounded entry of a triangular table is unaffected by a suffix. -/
@[hol "cakeml/compiler/backend/proofs/clos_to_bvlProofScript.sml" "triangle_el"]
theorem triangleEl {α β : Type} (n tot maxApp : Nat) (stuff : List α)
    (f : Nat → Nat → α) (_g : β) :
    letI : Nonempty α := ⟨f 0 0⟩
    n < tot ∧ tot < maxApp →
    holEl (n + tot * (tot - 1) / 2)
      ((((List.range maxApp).map fun t => (List.range t).map (f t)).flatten) ++ stuff) =
      f tot n := by
  let _ : Nonempty α := ⟨f 0 0⟩
  intro ⟨hn, ht⟩
  have entry := triangleLookup f maxApp tot n hn ht
  have entryBound := (List.getElem?_eq_some_iff.mp entry).1
  rw [holEl_eq_getElem _ _ (by simp only [List.length_append]; omega)]
  rw [List.getElem_append_left entryBound]
  exact (List.getElem?_eq_some_iff.mp entry).2

/-- A bounded entry of a triangular table has its generated value. -/
@[hol "cakeml/compiler/backend/proofs/clos_to_bvlProofScript.sml" "triangle_el_no_suff"]
theorem triangleElNoSuff {α β : Type} (n tot maxApp : Nat)
    (f : Nat → Nat → α) (g : β) :
    letI : Nonempty α := ⟨f 0 0⟩
    n < tot ∧ tot < maxApp →
    holEl (n + tot * (tot - 1) / 2)
      (((List.range maxApp).map fun t => (List.range t).map (f t)).flatten) = f tot n := by
  simpa using triangleEl n tot maxApp [] f g

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
  simp only [List.length_append, List.length_map, List.length_range, triangleTableSize]

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
