import Flapjack.Compiler.Backend.WordAlloc.KeyMaps
import Flapjack.Compiler.Backend.WordAlloc.Proofs.StrongLocalsRel
import Flapjack.Compiler.Backend.Semantics.WordSem.Alloc
import Flapjack.Compiler.Backend.Semantics.WordSem.EnvListSupport

/-!
# Word allocation environment-list and GC frame lemmas

Counterpart of `word_allocProofScript.sml:381-735`: the permutation-oracle
lemmas for `env_to_list`/`list_rearrange`, the GC frame lemma and the small
key-map facts consumed by `evaluate_apply_colour`. HOL sets are predicates on
`Nat`; `INJ f s UNIV` is rendered as injectivity of `f` on `s`.

HOL's `[local]` `GENLIST_MAP` (`:415`) is not ported: it states a `GENLIST`/`EL`
fact about HOL's `list_rearrange` body, whereas the reviewed Lean rendering of
`list_rearrange_def` indexes with a bound proof, so `list_rearrange_MAP` is
proved directly from that rendering.
-/

namespace Flapjack.WordAlloc

namespace EnvFrameWitnesses

/-- Canonical imported WordSem carrier roundtrip for the state-field ports. -/
theorem holFmapAsFiniteSupportWitness
    {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : WordSemStateBroad width C F) (h : state.FiniteSupport),
        (WordSemStateBroad.ofBroad state h).toBroad = state) ∧
      (∀ state : WordSemStateFiniteExact width C F,
        WordSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  WordSemStateExact.holFmapAsFiniteSupportWitness

end EnvFrameWitnesses

open EnvFrameWitnesses

/-- Exact HOL `gc_frame` (`word_allocProofScript.sml:565-594`): a successful
garbage collection changes only the stack, store and memory. -/
@[hol "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "gc_frame"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem gcFrame {width : Nat} [NeZero width] {C F : Type}
    (st st' : WordSemStateFiniteExact width C F)
    (h : WordSemStateFiniteExact.gc st = some st') :
    st'.fpRegs = st.fpRegs ∧
    st'.mdomain = st.mdomain ∧
    st'.shMdomain = st.shMdomain ∧
    st'.gcFun = st.gcFun ∧
    st'.handler = st.handler ∧
    st'.clock = st.clock ∧
    st'.code = st.code ∧
    st'.locals = st.locals ∧
    st'.localsSize = st.localsSize ∧
    st'.stackSize = st.stackSize ∧
    st'.stackMax = st.stackMax ∧
    st'.stackLimit = st.stackLimit ∧
    st'.be = st.be ∧
    st'.ffi = st.ffi ∧
    st'.compile = st.compile ∧
    st'.compileOracle = st.compileOracle ∧
    st'.codeBuffer = st.codeBuffer ∧
    st'.dataBuffer = st.dataBuffer ∧
    st'.permute = st.permute ∧
    st'.termdep = st.termdep := by
  unfold WordSemStateFiniteExact.gc at h
  simp only at h
  split at h
  · cases h
  · split at h
    · cases h
    · cases h
      exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
        rfl, rfl, rfl, rfl⟩

/-- Exact HOL `LENGTH_list_rerrange` (`word_allocProofScript.sml:394-398`). -/
@[hol "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "LENGTH_list_rerrange"]
theorem lengthListRearrange {α : Type} (mover : Nat → Nat) (xs : List α) :
    (wordSemListRearrange mover xs).length = xs.length := by
  unfold wordSemListRearrange
  split <;> simp

/-! ### HOL library `sort_PERM` over the exact mergesort rendering

Untagged: `mergesort_tail` and `sort_PERM` are HOL standard-library
declarations (`HOL/src/sort/mergesortScript.sml`), outside `cakeml/`. -/

theorem mergeTailPerm {α : Type} (negate : Bool) (r : α → α → Bool) :
    ∀ (left right acc : List α),
      (Basis.Pure.MlList.mergeTail negate r left right acc).Perm (left ++ right ++ acc)
  | [], [], acc => by rw [Basis.Pure.MlList.mergeTail.eq_1]; simp
  | head :: tail, [], acc => by
      rw [Basis.Pure.MlList.mergeTail.eq_2 _ _ _ _ (by simp)]
      simp only [List.append_nil]
      exact List.Perm.append_right _ (List.reverse_perm _)
  | [], head :: tail, acc => by
      rw [Basis.Pure.MlList.mergeTail.eq_3 _ _ _ _ (by simp)]
      simp only [List.nil_append]
      exact List.Perm.append_right _ (List.reverse_perm _)
  | x :: l1, y :: l2, acc => by
      rw [Basis.Pure.MlList.mergeTail.eq_4]
      split
      · refine (mergeTailPerm negate r l1 (y :: l2) (x :: acc)).trans ?_
        classical
        rw [List.perm_iff_count]; intro a
        simp only [List.count_cons, List.count_append, List.cons_append]; omega
      · refine (mergeTailPerm negate r (x :: l1) l2 (y :: acc)).trans ?_
        classical
        rw [List.perm_iff_count]; intro a
        simp only [List.count_cons, List.count_append, List.cons_append]; omega
  termination_by left right _ => left.length + right.length
  decreasing_by all_goals simp +arith

theorem sort2TailPerm {α : Type} (negate : Bool) (r : α → α → Bool) (x y : α) :
    (Basis.Pure.MlList.sort2Tail negate r x y).Perm [x, y] := by
  unfold Basis.Pure.MlList.sort2Tail
  split
  · exact List.Perm.refl _
  · exact List.Perm.swap _ _ _

theorem sort3TailPerm {α : Type} (negate : Bool) (r : α → α → Bool) (x y z : α) :
    (Basis.Pure.MlList.sort3Tail negate r x y z).Perm [x, y, z] := by
  classical
  unfold Basis.Pure.MlList.sort3Tail
  repeat' split
  all_goals
    rw [List.perm_iff_count]
    intro a
    simp only [List.count_cons, List.count_nil]
    try omega

theorem mergesortNTailPerm {α : Type} (r : α → α → Bool) :
    ∀ (size : Nat) (negate : Bool) (xs : List α), size ≤ xs.length →
      (Basis.Pure.MlList.mergesortNTail negate r size xs).Perm (xs.take size) := by
  intro size
  induction size using Nat.strongRecOn with
  | ind size ih =>
      intro negate xs hsize
      match size, xs, hsize with
      | 0, xs, _ => simp [Basis.Pure.MlList.mergesortNTail.eq_1]
      | 1, x :: _, _ => rw [Basis.Pure.MlList.mergesortNTail.eq_2]; simp
      | 2, x :: y :: _, _ =>
          rw [Basis.Pure.MlList.mergesortNTail.eq_4]
          simpa using sort2TailPerm negate r x y
      | 3, x :: y :: z :: _, _ =>
          rw [Basis.Pure.MlList.mergesortNTail.eq_7]
          simpa using sort3TailPerm negate r x y z
      | n + 4, xs, hsize =>
          rw [Basis.Pure.MlList.mergesortNTail.eq_11]
          have hfirst : (n + 4) / 2 ≤ xs.length := by omega
          have hsecond : n + 4 - (n + 4) / 2 ≤ (xs.drop ((n + 4) / 2)).length := by
            simp only [List.length_drop]; omega
          have hleft := ih ((n + 4) / 2) (by omega) (!negate) xs hfirst
          have hright := ih (n + 4 - (n + 4) / 2) (by omega) (!negate)
            (xs.drop ((n + 4) / 2)) hsecond
          refine (mergeTailPerm _ _ _ _ _).trans ?_
          rw [List.append_nil]
          refine (List.Perm.append hleft hright).trans ?_
          have : xs.take (n + 4) = xs.take ((n + 4) / 2) ++
              (xs.drop ((n + 4) / 2)).take (n + 4 - (n + 4) / 2) := by
            rw [← List.take_add, Nat.add_sub_cancel' (by omega)]
          rw [this]

theorem sortPerm {α : Type} (r : α → α → Bool) (xs : List α) :
    (Basis.Pure.MlList.sort r xs).Perm xs := by
  have h := mergesortNTailPerm r xs.length false xs (Nat.le_refl _)
  simpa [Basis.Pure.MlList.sort, Basis.Pure.MlList.mergesortTail] using h

/-! ### `list_rearrange` characterisation (Flapjack infrastructure) -/

/-- Pointwise characterisation of a successful `list_rearrange`. -/
theorem listRearrangeEqOf {α : Type} (m : Nat → Nat) (xs ys : List α)
    (hb : wordSemBijCount m xs.length) (hlen : ys.length = xs.length)
    (hel : ∀ i, i < xs.length → ys[i]? = xs[m i]?) :
    wordSemListRearrange m xs = ys := by
  unfold wordSemListRearrange
  rw [dif_pos hb]
  apply List.ext_getElem?
  intro i
  by_cases hi : i < xs.length
  · rw [hel i hi]
    simp [hi, List.getElem?_eq_getElem (hb.1.1 i hi)]
  · have h1 : ys[i]? = none := List.getElem?_eq_none (by omega)
    rw [h1]
    simp [hi]

/-- A rearrangement witness: `m` is a bijection of the index range carrying
`xs` to `ys`. -/
def RearrangeWitness {α : Type} (m : Nat → Nat) (xs ys : List α) : Prop :=
  wordSemBijCount m xs.length ∧ ys.length = xs.length ∧
    ∀ i, i < xs.length → ys[i]? = xs[m i]?

theorem bijCountId (n : Nat) : wordSemBijCount id n :=
  ⟨⟨fun _ hx => hx, fun _ _ _ _ h => h⟩, ⟨fun _ hx => hx, fun x hx => ⟨x, hx, rfl⟩⟩⟩

theorem rearrangeWitnessOfPerm {α : Type} {xs ys : List α} (h : xs.Perm ys) :
    ∃ m, RearrangeWitness m xs ys := by
  induction h with
  | nil => exact ⟨id, bijCountId 0, rfl, fun i hi => by simp at hi⟩
  | @cons x l1 l2 _ ih =>
      obtain ⟨m, hb, hlen, hel⟩ := ih
      refine ⟨fun i => if i = 0 then 0 else m (i - 1) + 1, ?_, by simp [hlen], ?_⟩
      · obtain ⟨⟨hin, hinj⟩, ⟨-, hsurj⟩⟩ := hb
        simp only [List.length_cons]
        have hin' : ∀ i, i < l1.length + 1 →
            (if i = 0 then 0 else m (i - 1) + 1) < l1.length + 1 := by
          intro i hi
          split
          · omega
          · have := hin (i - 1) (by omega); omega
        refine ⟨⟨hin', ?_⟩, ⟨hin', ?_⟩⟩
        · intro a ha b hb' hab
          by_cases a0 : a = 0 <;> by_cases b0 : b = 0 <;> simp only [a0, b0, if_true,
            if_false] at hab
          · omega
          · omega
          · omega
          · have := hinj (a - 1) (by omega) (b - 1) (by omega) (by omega); omega
        · intro a ha
          by_cases a0 : a = 0
          · exact ⟨0, by omega, by simp [a0]⟩
          · obtain ⟨b, hb', hbm⟩ := hsurj (a - 1) (by omega)
            exact ⟨b + 1, by omega, by simp [hbm]; omega⟩
      · intro i hi
        cases i with
        | zero => simp
        | succ i =>
            simp only [List.length_cons] at hi
            simp [hel i (by omega)]
  | swap x y l =>
      refine ⟨fun i => if i = 0 then 1 else if i = 1 then 0 else i, ?_, by simp, ?_⟩
      · simp only [List.length_cons]
        have hin : ∀ i, i < l.length + 1 + 1 →
            (if i = 0 then 1 else if i = 1 then 0 else i) < l.length + 1 + 1 := by
          intro i hi; split <;> (try split) <;> omega
        refine ⟨⟨hin, ?_⟩, ⟨hin, ?_⟩⟩
        · intro a _ b _ hab
          by_cases a0 : a = 0 <;> by_cases a1 : a = 1 <;> by_cases b0 : b = 0 <;>
            by_cases b1 : b = 1 <;> simp [a0, a1, b0, b1] at hab <;> omega
        · intro a ha
          by_cases a0 : a = 0
          · exact ⟨1, by omega, by simp [a0]⟩
          · by_cases a1 : a = 1
            · exact ⟨0, by omega, by simp [a1]⟩
            · exact ⟨a, ha, by simp [a0, a1]⟩
      · intro i hi
        match i with
        | 0 => simp
        | 1 => simp
        | i + 2 => simp
  | trans _ _ ih1 ih2 =>
      obtain ⟨m1, ⟨⟨hin1, hinj1⟩, ⟨-, hsurj1⟩⟩, hlen1, hel1⟩ := ih1
      obtain ⟨m2, ⟨⟨hin2, hinj2⟩, ⟨-, hsurj2⟩⟩, hlen2, hel2⟩ := ih2
      rw [hlen1] at hin2 hinj2 hsurj2 hel2
      refine ⟨m1 ∘ m2, ?_, by rw [hlen2, hlen1], ?_⟩
      · have hin : ∀ x, x < _ → (m1 ∘ m2) x < _ := fun x hx => hin1 _ (hin2 x hx)
        refine ⟨⟨hin, ?_⟩, ⟨hin, ?_⟩⟩
        · intro a ha b hb hab
          exact hinj2 a ha b hb (hinj1 _ (hin2 a ha) _ (hin2 b hb) hab)
        · intro a ha
          obtain ⟨b, hb, hbm⟩ := hsurj1 a ha
          obtain ⟨c, hc, hcm⟩ := hsurj2 b hb
          exact ⟨c, hc, by simp [Function.comp, hcm, hbm]⟩
      · intro i hi
        rw [hel2 i hi, hel1 (m2 i) (hin2 i hi)]
        rfl

/-- Exact HOL `list_rearrange_perm` (`word_allocProofScript.sml:403-413`). -/
@[hol "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "list_rearrange_perm"]
theorem listRearrangePerm {α : Type} (xs ys : List α) (h : xs.Perm ys) :
    ∃ perm, wordSemListRearrange perm xs = ys := by
  obtain ⟨m, hb, hlen, hel⟩ := rearrangeWitnessOfPerm h
  exact ⟨m, listRearrangeEqOf m xs ys hb hlen hel⟩

/-! ### HOL library `ALL_DISTINCT_MAP_FST_toAList` (untagged Sptree support) -/

private theorem sptAccZero (index : Nat) : sptAcc index 0 = index := by
  rw [sptAcc_eq]; simp

theorem sptFoldiSplit {α : Type} (tree : Spt α) :
    ∀ (index : Nat) (acc : List (Nat × α)),
      ∃ emitted, sptFoldi (fun k v entries => (k, v) :: entries) index acc tree =
          emitted ++ acc ∧ (emitted.map Prod.fst).Nodup ∧
          ∀ p ∈ emitted, ∃ k, p.1 = sptAcc index k := by
  induction tree with
  | ln => intro index acc; exact ⟨[], by simp [sptFoldi], by simp, by simp⟩
  | ls v =>
      intro index acc
      exact ⟨[(index, v)], by simp [sptFoldi], by simp,
        by intro p hp; simp at hp; subst hp; exact ⟨0, (sptAccZero index).symm⟩⟩
  | bn left right ihl ihr =>
      intro index acc
      obtain ⟨el, hl, hlnd, hlk⟩ := ihl (index + 2 * lrNext index) acc
      obtain ⟨er, hr, hrnd, hrk⟩ := ihr (index + lrNext index) (el ++ acc)
      refine ⟨er ++ el, ?_, ?_, ?_⟩
      · change sptFoldi _ (index + lrNext index)
          (sptFoldi _ (index + 2 * lrNext index) acc left) right = _
        rw [hl, hr, List.append_assoc]
      · rw [List.map_append, List.nodup_append]
        refine ⟨hrnd, hlnd, ?_⟩
        intro a ha b hb hab
        obtain ⟨pa, hpa, rfl⟩ := List.mem_map.mp ha
        obtain ⟨pb, hpb, rfl⟩ := List.mem_map.mp hb
        obtain ⟨ka, hka⟩ := hrk pa hpa
        obtain ⟨kb, hkb⟩ := hlk pb hpb
        rw [hka, hkb, sptAcc_childRight, sptAcc_childLeft] at hab
        have := sptAcc_injective index hab
        omega
      · intro p hp
        rcases List.mem_append.mp hp with h | h
        · obtain ⟨k, hk⟩ := hrk p h; exact ⟨2 * k + 1, by rw [hk, sptAcc_childRight]⟩
        · obtain ⟨k, hk⟩ := hlk p h; exact ⟨2 * k + 2, by rw [hk, sptAcc_childLeft]⟩
  | bs left v right ihl ihr =>
      intro index acc
      obtain ⟨el, hl, hlnd, hlk⟩ := ihl (index + 2 * lrNext index) acc
      obtain ⟨er, hr, hrnd, hrk⟩ := ihr (index + lrNext index) ((index, v) :: (el ++ acc))
      refine ⟨er ++ (index, v) :: el, ?_, ?_, ?_⟩
      · change sptFoldi _ (index + lrNext index)
          ((index, v) :: sptFoldi _ (index + 2 * lrNext index) acc left) right = _
        rw [hl, hr]; simp
      · have hroot : ∀ p ∈ el, p.1 ≠ index := by
          intro p hp heq
          obtain ⟨k, hk⟩ := hlk p hp
          rw [hk, sptAcc_childLeft] at heq
          have := sptAcc_injective index (heq.trans (sptAccZero index).symm)
          omega
        rw [List.map_append, List.nodup_append]
        refine ⟨hrnd, ?_, ?_⟩
        · simp only [List.map_cons, List.nodup_cons]
          refine ⟨?_, hlnd⟩
          intro hm
          obtain ⟨p, hp, hpe⟩ := List.mem_map.mp hm
          exact hroot p hp hpe
        · intro a ha b hb hab
          obtain ⟨pa, hpa, rfl⟩ := List.mem_map.mp ha
          obtain ⟨ka, hka⟩ := hrk pa hpa
          rw [hka, sptAcc_childRight] at hab
          simp only [List.map_cons, List.mem_cons] at hb
          rcases hb with hb | hb
          · rw [hb] at hab
            have := sptAcc_injective index (hab.trans (sptAccZero index).symm)
            omega
          · obtain ⟨pb, hpb, rfl⟩ := List.mem_map.mp hb
            obtain ⟨kb, hkb⟩ := hlk pb hpb
            rw [hkb, sptAcc_childLeft] at hab
            have := sptAcc_injective index hab
            omega
      · intro p hp
        simp only [List.mem_append, List.mem_cons] at hp
        rcases hp with h | h | h
        · obtain ⟨k, hk⟩ := hrk p h; exact ⟨2 * k + 1, by rw [hk, sptAcc_childRight]⟩
        · subst h; exact ⟨0, (sptAccZero index).symm⟩
        · obtain ⟨k, hk⟩ := hlk p h; exact ⟨2 * k + 2, by rw [hk, sptAcc_childLeft]⟩

theorem sptToAListKeysNodup {α : Type} (tree : Spt α) :
    ((sptToAList tree).map Prod.fst).Nodup := by
  obtain ⟨e, he, hnd, -⟩ := sptFoldiSplit tree 0 []
  simpa [sptToAList, he] using hnd

/-! ### `list_rearrange` is a permutation (HOL `PERM_list_rearrange`) -/

theorem listRearrangePermSelf {α : Type} (m : Nat → Nat) (xs : List α) :
    (wordSemListRearrange m xs).Perm xs := by
  by_cases hb : wordSemBijCount m xs.length
  · have hsome : (wordSemListRearrange m xs).map some =
        ((List.range xs.length).map m).map (fun j => xs[j]?) := by
      apply List.ext_getElem?
      intro i
      unfold wordSemListRearrange
      rw [dif_pos hb]
      by_cases hi : i < xs.length
      · simp [hi, List.getElem?_eq_getElem (hb.1.1 i hi)]
      · simp [hi]
    have hxs : xs.map some = (List.range xs.length).map (fun j => xs[j]?) := by
      apply List.ext_getElem?
      intro i
      by_cases hi : i < xs.length <;> simp [hi]
    have hrange : ((List.range xs.length).map m).Perm (List.range xs.length) := by
      rw [List.perm_ext_iff_of_nodup]
      · intro a
        simp only [List.mem_map, List.mem_range]
        constructor
        · rintro ⟨b, hb', rfl⟩; exact hb.1.1 b hb'
        · intro ha; obtain ⟨b, hb', hbm⟩ := hb.2.2 a ha; exact ⟨b, hb', hbm⟩
      · rw [List.Nodup, List.pairwise_map]
        exact List.nodup_range.imp_of_mem (fun {a b} ha hb' hne heq =>
          hne (hb.1.2 a (List.mem_range.mp ha) b (List.mem_range.mp hb') heq))
      · exact List.nodup_range
    have hp : ((wordSemListRearrange m xs).map some).Perm (xs.map some) := by
      rw [hsome, hxs]; exact hrange.map _
    have := hp.filterMap id
    simpa using this
  · unfold wordSemListRearrange
    rw [dif_neg hb]

theorem listRearrangeGetElem? {α : Type} (m : Nat → Nat) (xs : List α)
    (hb : wordSemBijCount m xs.length) (i : Nat) (hi : i < xs.length) :
    (wordSemListRearrange m xs)[i]? = xs[m i]? := by
  unfold wordSemListRearrange
  rw [dif_pos hb]
  simp [hi, List.getElem?_eq_getElem (hb.1.1 i hi)]

/-- Exact HOL `list_rearrange_MAP` (`word_allocProofScript.sml:425-429`). -/
@[hol "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "list_rearrange_MAP"]
theorem listRearrangeMap {α β : Type} :
    ∀ (l : List α) (f : α → β) (m : Nat → Nat),
      wordSemListRearrange m (l.map f) = (wordSemListRearrange m l).map f := by
  intro l f m
  by_cases hb : wordSemBijCount m l.length
  · have hb' : wordSemBijCount m (l.map f).length := by simpa using hb
    apply listRearrangeEqOf m _ _ hb' (by simp [lengthListRearrange])
    intro i hi
    simp only [List.length_map] at hi
    rw [List.getElem?_map, listRearrangeGetElem? m l hb i hi, List.getElem?_map]
  · have hb' : ¬ wordSemBijCount m (l.map f).length := by simpa using hb
    unfold wordSemListRearrange
    rw [dif_neg hb', dif_neg hb]

/-- Keys of the sorted `toAList` enumeration are exactly the tree domain. -/
private theorem sortToAListKeys {α : Type} (r : Nat × α → Nat × α → Bool)
    (x : Spt α) (k : Nat) :
    k ∈ (Basis.Pure.MlList.sort r (sptToAList x)).map Prod.fst ↔ sptDomain x k := by
  simp only [List.mem_map]
  constructor
  · rintro ⟨⟨a, v⟩, hmem, rfl⟩
    rw [wordSemSort_mem_iff, sptToAList_mem_iff_lookup] at hmem
    simp [sptDomain, hmem]
  · intro hk
    obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp hk
    exact ⟨(k, v), by rw [wordSemSort_mem_iff, sptToAList_mem_iff_lookup]; exact hv, rfl⟩

private theorem rearrangeKeys {α β : Type} (perm : Nat → Nat) (ls : List (α × β)) (k : α) :
    k ∈ (wordSemListRearrange perm ls).map Prod.fst ↔ k ∈ ls.map Prod.fst := by
  simp only [List.mem_map]
  constructor
  · rintro ⟨p, hp, rfl⟩; exact ⟨p, (wordSemListRearrange_mem_iff perm ls p).mp hp, rfl⟩
  · rintro ⟨p, hp, rfl⟩; exact ⟨p, (wordSemListRearrange_mem_iff perm ls p).mpr hp, rfl⟩

/-- Exact HOL `list_rearrange_keys` (`word_allocProofScript.sml:682-688`). -/
@[hol "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "list_rearrange_keys"]
theorem listRearrangeKeys {α β : Type} (perm : Nat → Nat) (ls e : List (α × β))
    (h : wordSemListRearrange perm ls = e) :
    (fun k => k ∈ e.map Prod.fst) = (fun k => k ∈ ls.map Prod.fst) := by
  subst h
  funext k
  exact propext (rearrangeKeys perm ls k)

/-- Exact HOL `list_rearrange_keys_2` (`word_allocProofScript.sml:690-694`). -/
@[hol "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "list_rearrange_keys_2"]
theorem listRearrangeKeysTwo {α β : Type} (perm : Nat → Nat) (ls : List (α × β)) :
    (fun k => k ∈ (wordSemListRearrange perm ls).map Prod.fst) =
      (fun k => k ∈ ls.map Prod.fst) := by
  funext k
  exact propext (rearrangeKeys perm ls k)

/-- Exact HOL `MAP_FST_list_rearrange_keys_SORT`
(`word_allocProofScript.sml:696-702`). -/
@[hol "cakeml/compiler/backend/proofs/word_allocProofScript.sml"
  "MAP_FST_list_rearrange_keys_SORT" (words_as_type_indexed_bitvec)]
theorem mapFstListRearrangeKeysSort {width : Nat} [NeZero width] (perm : Nat → Nat)
    (x : Spt (WordLocW width)) :
    (fun k => k ∈ (wordSemListRearrange perm
      (Basis.Pure.MlList.sort wordSemKeyValCompare (sptToAList x))).map Prod.fst) =
      sptDomain x := by
  funext k
  exact propext ((rearrangeKeys perm _ k).trans (sortToAListKeys _ x k))

/-- Exact HOL `MAP_FST_keys_SORT` (`word_allocProofScript.sml:704-708`). HOL's
comparison `f` is arbitrary; the tree payload type is generic. -/
@[hol "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "MAP_FST_keys_SORT"]
theorem mapFstKeysSort {α : Type} (f : Nat × α → Nat × α → Bool) (x : Spt α) :
    (fun k => k ∈ (Basis.Pure.MlList.sort f (sptToAList x)).map Prod.fst) = sptDomain x := by
  funext k
  exact propext (sortToAListKeys f x k)

/-- Exact HOL `env_to_list_keys` (`word_allocProofScript.sml:669-680`). -/
@[hol "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "env_to_list_keys"
  (words_as_type_indexed_bitvec)]
theorem envToListKeys {width : Nat} [NeZero width] (x : Spt (WordLocW width))
    (perm : Nat → Nat → Nat) :
    let (l, _permute) := wordSemEnvToList x perm
    (fun k => k ∈ l.map Prod.fst) = sptDomain x := by
  exact mapFstListRearrangeKeysSort (perm 0) x

/-- Exact HOL `key_map_implies` (`word_allocProofScript.sml:724-734`). -/
@[hol "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "key_map_implies"]
theorem keyMapImplies {α β γ : Type} (f : α → β) (l' : List (α × γ)) (l : List (β × γ))
    (h : l'.map (fun (a, b) => (f a, b)) = l) :
    (l'.map Prod.fst).map f = l.map Prod.fst := by
  subst h
  simp [List.map_map, Function.comp_def]

/-- Exact HOL `nummaps_to_nummap` (`word_allocProofScript.sml:381-386`). -/
@[hol "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "nummaps_to_nummap"]
theorem nummapsToNummap {α β : Type} (f : Nat → Nat) (a : Spt α × Spt β) :
    (applyNummapsKey f a).1 = applyNummapKey f a.1 ∧
      (applyNummapsKey f a).2 = applyNummapKey f a.2 :=
  ⟨rfl, rfl⟩

/-- Exact HOL `INJ_union` (`word_allocProofScript.sml:388-392`), with
`INJ f s t` expanded as HOL `INJ_DEF`: `f` maps `s` into `t` and is injective
on `s`; set union is pointwise disjunction. -/
@[hol "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "INJ_union"]
theorem injUnion {α β : Type} (f : α → β) (A B : α → Prop) (C : β → Prop)
    (h : (∀ x, (A x ∨ B x) → C (f x)) ∧
      (∀ x y, (A x ∨ B x) → (A y ∨ B y) → f x = f y → x = y)) :
    ((∀ x, A x → C (f x)) ∧ (∀ x y, A x → A y → f x = f y → x = y)) ∧
      ((∀ x, B x → C (f x)) ∧ (∀ x y, B x → B y → f x = f y → x = y)) :=
  ⟨⟨fun x hx => h.1 x (Or.inl hx), fun x y hx hy => h.2 x y (Or.inl hx) (Or.inl hy)⟩,
    ⟨fun x hx => h.1 x (Or.inr hx), fun x y hx hy => h.2 x y (Or.inr hx) (Or.inr hy)⟩⟩

private theorem sortedKeysNodup {α : Type} (r : Nat × α → Nat × α → Bool) (x : Spt α) :
    ((Basis.Pure.MlList.sort r (sptToAList x)).map Prod.fst).Nodup :=
  ((sortPerm r (sptToAList x)).map Prod.fst).nodup_iff.mpr (sptToAListKeysNodup x)

private theorem sortedMem {α : Type} (r : Nat × α → Nat × α → Bool) (x : Spt α)
    (k : Nat) (v : α) :
    (k, v) ∈ Basis.Pure.MlList.sort r (sptToAList x) ↔ sptLookup k x = some v := by
  rw [wordSemSort_mem_iff, sptToAList_mem_iff_lookup]

/-- Exact HOL `env_to_list_perm` (`word_allocProofScript.sml:442-513`): when the
target environment is the injective image of the source under `f` (with the
live-scoped strong relation on the whole source domain), a source permutation
oracle reproduces the renamed target environment list, and its continuation
can be chosen as any `tperm`. -/
@[hol "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "env_to_list_perm"
  (words_as_type_indexed_bitvec)]
theorem envToListPerm {width : Nat} [NeZero width] :
    ∀ (y x : Spt (WordLocW width)) (f : Nat → Nat) (perm tperm : Nat → Nat → Nat),
      sptDomain y = (fun key => ∃ source, sptDomain x source ∧ f source = key) ∧
      (∀ a b, sptDomain x a → sptDomain x b → f a = f b → a = b) ∧
      strongLocalsRel f (sptDomain x) x y →
      let (l, _permute) := wordSemEnvToList y perm
      ∃ perm', let (l', permute') := wordSemEnvToList x perm'
        permute' = tperm ∧ l'.map (fun (a, b) => (f a, b)) = l := by
  intro y x f perm tperm ⟨hdom, hinj, hrel⟩
  simp only [wordSemEnvToList]
  generalize hxls : Basis.Pure.MlList.sort wordSemKeyValCompare (sptToAList x) = xls
  generalize hyls : Basis.Pure.MlList.sort wordSemKeyValCompare (sptToAList y) = yls
  let g : Nat × WordLocW width → Nat × WordLocW width := fun (a, b) => (f a, b)
  have hxkeys : (xls.map Prod.fst).Nodup := hxls ▸ sortedKeysNodup _ x
  have hykeys : (yls.map Prod.fst).Nodup := hyls ▸ sortedKeysNodup _ y
  have hxmem : ∀ k v, (k, v) ∈ xls ↔ sptLookup k x = some v := fun k v => hxls ▸ sortedMem _ x k v
  have hymem : ∀ k v, (k, v) ∈ yls ↔ sptLookup k y = some v := fun k v => hyls ▸ sortedMem _ y k v
  have hgkeys : ((xls.map g).map Prod.fst).Nodup := by
    have : (xls.map g).map Prod.fst = (xls.map Prod.fst).map f := by
      simp [g, List.map_map, Function.comp_def]
    rw [this, List.Nodup, List.pairwise_map]
    refine hxkeys.imp_of_mem (fun {a b} ha hb hne heq => hne ?_)
    have hdx : ∀ k, k ∈ xls.map Prod.fst → sptDomain x k := by
      intro k hk
      obtain ⟨⟨k', v⟩, hm, rfl⟩ := List.mem_map.mp hk
      simp [sptDomain, (hxmem k' v).mp hm]
    exact hinj a b (hdx a ha) (hdx b hb) heq
  have hP : (xls.map g).Perm yls := by
    have nodupOfKeys : ∀ l : List (Nat × WordLocW width), (l.map Prod.fst).Nodup → l.Nodup :=
      fun l h => List.Pairwise.of_map Prod.fst (fun a b h' heq => h' (congrArg _ heq)) h
    rw [List.perm_ext_iff_of_nodup (nodupOfKeys _ hgkeys) (nodupOfKeys _ hykeys)]
    rintro ⟨k, v⟩
    constructor
    · intro hm
      obtain ⟨⟨a, w⟩, ha, he⟩ := List.mem_map.mp hm
      simp only [g, Prod.mk.injEq] at he
      obtain ⟨rfl, rfl⟩ := he
      have hl := (hxmem a w).mp ha
      exact (hymem _ _).mpr (hrel a w ⟨by simp [sptDomain, hl], hl⟩)
    · intro hm
      have hl := (hymem k v).mp hm
      have hk : sptDomain y k := by simp [sptDomain, hl]
      rw [hdom] at hk
      obtain ⟨a, ha, rfl⟩ := hk
      obtain ⟨w, hw⟩ := Option.isSome_iff_exists.mp ha
      have hw' := hrel a w ⟨ha, hw⟩
      rw [hl] at hw'
      cases hw'
      exact List.mem_map.mpr ⟨(a, v), (hxmem a v).mpr hw, rfl⟩
  obtain ⟨p, hp⟩ := listRearrangePerm (xls.map g) (wordSemListRearrange (perm 0) yls)
    (hP.trans (listRearrangePermSelf (perm 0) yls).symm)
  refine ⟨fun n => if n = 0 then p else tperm (n - 1), ?_⟩
  simp only
  refine ⟨?_, ?_⟩
  · funext n
    simp
  · rw [← hp, listRearrangeMap, if_pos trivial]

end Flapjack.WordAlloc
