module

public import Flapjack.Pancake.Semantics.PanProps
public import Flapjack.Pancake.PanLang.Shape

@[expose] public section

/-!
# `with_shape` lemmas over the exact shape carrier

Exact ports of the HOL `with_shape` lemmas of
`cakeml/pancake/semantics/panPropsScript.sml` (`length_with_shape_eq_shape` at
line 265 through `el_el_with_shape` at line 568).  HOL's `shape` (mlstring
named) is the tagged `ShapeHOL`, `size_of_shape` is the tagged `sizeOfShapeHOL`,
`with_shape` is the tagged `withShapeHOL` (`Flapjack/Pancake/PanLang/Shape.lean`),
`TAKE`/`DROP` are `List.take`/`List.drop`, `ALL_DISTINCT` is `List.Nodup`,
`MEM` is list membership, `EL` is the dependent `getElem` (with the length side
conditions discharged from the conjoined premise) and the total `elHOL` where a
premise conjunction indexes a list before its bound conjunct can be projected
from that same conjunction, and `DISJOINT (set x) (set y)` is the element-level
`ListDisjoint` rendering.  HOL's `EVERY is_wf_shape_nil shs` is membership over
the tagged `isWfShapeNilHOL`.  Each theorem takes HOL's premises as one
conjoined premise in HOL order and HOL's binder order.

The production `Shape`-carrier versions in `Flapjack/Pancake/PanLang.lean`
remain Flapjack-specific infrastructure for the executed compiler and its
proofs; these are the faithful carriers.
-/

namespace Flapjack

open Flapjack.Pancake.PanLang (ShapeHOL sizeOfShapeHOL sizeOfShapesHOL
  sizeOfShapesHOL_cons sizeOfShapesHOL_nil sizeOfShapeHOL_comb withShapeHOL)

/-! ## Carrier infrastructure (no HOL declaration of their own) -/

/-- Additivity of the flat shape size over an appended shape list.  Untagged
    support: HOL only uses `SUM (MAP size_of_shape ...)` and its append lemmas. -/
theorem sizeOfShapesHOL_append (left right : List ShapeHOL) :
    sizeOfShapesHOL (left ++ right) =
      sizeOfShapesHOL left + sizeOfShapesHOL right := by
  induction left with
  | nil => simp
  | cons shape shapes ih =>
      simp only [List.cons_append, sizeOfShapesHOL_cons, ih]
      omega

/-- `size_of_shape (Comb (h :: t)) = size_of_shape h + size_of_shape (Comb t)`,
    the clause-level form of the tagged `sizeOfShapeHOL`. -/
theorem sizeOfShapeHOL_comb_cons (head : ShapeHOL) (tail : List ShapeHOL) :
    sizeOfShapeHOL (.comb (head :: tail)) =
      sizeOfShapeHOL head + sizeOfShapeHOL (.comb tail) := by
  simp only [sizeOfShapeHOL_comb, sizeOfShapesHOL_cons]

/-- Additivity of `size_of_shape` over an appended shape list. -/
theorem sizeOfShapeHOL_comb_append (left right : List ShapeHOL) :
    sizeOfShapeHOL (.comb (left ++ right)) =
      sizeOfShapeHOL (.comb left) + sizeOfShapeHOL (.comb right) := by
  simp only [sizeOfShapeHOL_comb, sizeOfShapesHOL_append]

/-- One sub-list per requested shape, so the split has the shape list's length.
    Untagged support for the indexed statements below. -/
theorem withShapeHOLLength (shapes : List ShapeHOL) (values : List α) :
    (withShapeHOL shapes values).length = shapes.length := by
  induction shapes generalizing values with
  | nil => simp [withShapeHOL]
  | cons shape shapes ih => simp [withShapeHOL, ih]

/-- HOL's total `EL`: out of range it returns `ARB`.  Untagged infrastructure
    for the premise conjunctions below, where HOL indexes a list before the
    bound conjunct can be projected from the same conjunction; `List.getD` with
    `Classical.arbitrary` is the `ARB` fallback. -/
noncomputable def elHOL {α : Type} [Nonempty α] (l : List α) (n : Nat) : α :=
  l.getD n (Classical.choice ‹Nonempty α›)

theorem elHOL_eq_getElem {α : Type} [Nonempty α] (l : List α) (n : Nat)
    (h : n < l.length) : elHOL l n = l[n]'h := by
  simp [elHOL, List.getElem?_eq_getElem h]

instance : Nonempty ShapeHOL := ⟨.one⟩

/-! ## The HOL lemmas -/

/-- Exact port of HOL `panProps$length_with_shape_eq_shape`
    (`panPropsScript.sml:265-267`): `LENGTH ns = size_of_shape (Comb sh) ==>
    LENGTH sh = LENGTH (with_shape sh ns)`.  HOL's premise is a single
    proposition, kept as one premise. -/
@[hol "cakeml/pancake/semantics/panPropsScript.sml" "length_with_shape_eq_shape"]
theorem lengthWithShapeEqShapeHOL (shapes : List ShapeHOL) (values : List α)
    (hvalues : values.length = sizeOfShapeHOL (.comb shapes)) :
    shapes.length = (withShapeHOL shapes values).length := by
  have _ := hvalues
  rw [withShapeHOLLength]

/-- Exact port of HOL `panProps$all_distinct_with_shape`
    (`panPropsScript.sml:286-289`): `ALL_DISTINCT ns /\ n < LENGTH sh /\
    LENGTH ns = size_of_shape (Comb sh) ==> ALL_DISTINCT (EL n (with_shape sh ns))`,
    with HOL's three conjuncts as one premise. -/
@[hol "cakeml/pancake/semantics/panPropsScript.sml" "all_distinct_with_shape"]
theorem allDistinctWithShapeHOL (shapes : List ShapeHOL) (values : List α) (n : Nat)
    (h : values.Nodup ∧ n < shapes.length ∧
      values.length = sizeOfShapeHOL (.comb shapes)) :
    ((withShapeHOL shapes values)[n]'(by rw [withShapeHOLLength]; exact h.2.1)).Nodup := by
  obtain ⟨hdistinct, hn, hvalues⟩ := h
  show ((withShapeHOL shapes values)[n]'(by rw [withShapeHOLLength]; exact hn)).Nodup
  revert values n
  induction shapes with
  | nil => intro values n hdistinct hn hvalues; exact absurd hn (Nat.not_lt_zero n)
  | cons shape shapes ih =>
      intro values n hdistinct hn hvalues
      cases n with
      | zero =>
          simp only [withShapeHOL]
          exact hdistinct.take
      | succ k =>
          simp only [withShapeHOL]
          simp only [List.length_cons] at hn
          have hn' : k < shapes.length := by omega
          have hvalues' : (values.drop (sizeOfShapeHOL shape)).length =
              sizeOfShapeHOL (.comb shapes) := by
            rw [List.length_drop, hvalues, sizeOfShapeHOL_comb_cons,
              Nat.add_sub_cancel_left]
          exact ih (values.drop (sizeOfShapeHOL shape)) k hdistinct.drop hn' hvalues'

/-- Exact port of HOL `panProps$el_mem_with_shape`
    (`panPropsScript.sml:307-310`): `n < LENGTH (with_shape sh ns) /\
    LENGTH ns = size_of_shape (Comb sh) /\ MEM x (EL n (with_shape sh ns)) ==>
    MEM x ns`, with HOL's three conjuncts as one premise.  The premise's
    `EL n (with_shape sh ns)` uses the total `elHOL` rendering because its
    bound is the first conjunct of that same conjunction. -/
@[hol "cakeml/pancake/semantics/panPropsScript.sml" "el_mem_with_shape"]
theorem elMemWithShapeHOL (shapes : List ShapeHOL) (values : List α) (n : Nat)
    (x : α)
    (h : n < (withShapeHOL shapes values).length ∧
      values.length = sizeOfShapeHOL (.comb shapes) ∧
      x ∈ elHOL (withShapeHOL shapes values) n) :
    x ∈ values := by
  obtain ⟨hn, hvalues, hmem⟩ := h
  rw [elHOL_eq_getElem _ _ hn] at hmem
  revert values n x
  induction shapes with
  | nil =>
      intro values n x hn hvalues hmem
      simp [withShapeHOL] at hn
  | cons shape shapes ih =>
      intro values n x hn hvalues hmem
      simp only [withShapeHOL] at hn hmem
      cases n with
      | zero =>
          exact List.mem_of_mem_take (by simpa using hmem)
      | succ k =>
          apply List.mem_of_mem_drop
          have hk : k < (withShapeHOL shapes (values.drop (sizeOfShapeHOL shape))).length := by
            simp only [List.length_cons] at hn
            omega
          have hvalues' : (values.drop (sizeOfShapeHOL shape)).length =
              sizeOfShapeHOL (.comb shapes) := by
            rw [List.length_drop, hvalues, sizeOfShapeHOL_comb_cons,
              Nat.add_sub_cancel_left]
          exact ih (values.drop (sizeOfShapeHOL shape)) k x hk hvalues' hmem

/-- Exact port of HOL `panProps$mem_with_shape_length`
    (`panPropsScript.sml:328-331`): `LENGTH ns = size_of_shape (Comb sh) /\
    n < LENGTH sh ==> MEM (EL n (with_shape sh ns)) (with_shape sh ns)`, with
    HOL's two conjuncts as one premise. -/
@[hol "cakeml/pancake/semantics/panPropsScript.sml" "mem_with_shape_length"]
theorem memWithShapeLengthHOL (shapes : List ShapeHOL) (values : List α) (n : Nat)
    (h : values.length = sizeOfShapeHOL (.comb shapes) ∧ n < shapes.length) :
    (withShapeHOL shapes values)[n]'(by rw [withShapeHOLLength]; exact h.2) ∈
      withShapeHOL shapes values := by
  exact List.getElem_mem _

/-- Exact port of HOL `panProps$with_shape_el_take_drop_eq`
    (`panPropsScript.sml:341-344`): `LENGTH ns = size_of_shape (Comb sh) /\
    n < LENGTH sh ==> EL n (with_shape sh ns) = TAKE (size_of_shape (EL n sh))
    (DROP (size_of_shape (Comb (TAKE n sh))) ns)`, with HOL's two conjuncts as
    one premise. -/
@[hol "cakeml/pancake/semantics/panPropsScript.sml" "with_shape_el_take_drop_eq"]
theorem withShapeElTakeDropEqHOL (shapes : List ShapeHOL) (values : List α)
    (n : Nat)
    (h : values.length = sizeOfShapeHOL (.comb shapes) ∧ n < shapes.length) :
    (withShapeHOL shapes values)[n]'(by rw [withShapeHOLLength]; exact h.2) =
      (values.drop (sizeOfShapeHOL (.comb (shapes.take n)))).take
        (sizeOfShapeHOL (shapes[n]'h.2)) := by
  obtain ⟨hvalues, hn⟩ := h
  show (withShapeHOL shapes values)[n]'(by rw [withShapeHOLLength]; exact hn) =
      (values.drop (sizeOfShapeHOL (.comb (shapes.take n)))).take
        (sizeOfShapeHOL (shapes[n]'hn))
  revert values n
  induction shapes with
  | nil => intro values n hvalues hn; exact absurd hn (Nat.not_lt_zero n)
  | cons shape shapes ih =>
      intro values n hvalues hn
      cases n with
      | zero => simp [withShapeHOL]
      | succ k =>
          have hn' : k < shapes.length := by
            simp only [List.length_cons] at hn
            omega
          have hvalues' : (values.drop (sizeOfShapeHOL shape)).length =
              sizeOfShapeHOL (.comb shapes) := by
            rw [List.length_drop, hvalues, sizeOfShapeHOL_comb_cons,
              Nat.add_sub_cancel_left]
          simp only [withShapeHOL, List.getElem_cons_succ, List.take_succ_cons]
          rw [ih (values.drop (sizeOfShapeHOL shape)) k hvalues' hn']
          rw [sizeOfShapeHOL_comb_cons]
          rw [← List.drop_drop]

/-- The head shape's size is bounded by the size of the remaining suffix. -/
theorem sizeOfShapeHOLDropHeadSizeLe (shapes : List ShapeHOL) (n : Nat)
    (hn : n < shapes.length) :
    sizeOfShapeHOL (shapes[n]'hn) ≤ sizeOfShapeHOL (.comb (shapes.drop n)) := by
  rw [List.drop_eq_getElem_cons (l := shapes) hn, sizeOfShapeHOL_comb_cons]
  omega

/-- The `n`-th group has exactly `size_of_shape (EL n sh)` elements: the length
    obligation HOL discharges inside `list_rel_flatten_with_shape_length`
    (`pan_to_crepProofScript.sml:549`).  It supplies the `getElem` bound that
    HOL's total `EL` does not need. -/
theorem withShapeHOLGetElemLength (shapes : List ShapeHOL) (values : List α)
    (n : Nat)
    (hvalues : values.length = sizeOfShapeHOL (.comb shapes))
    (hn : n < shapes.length) :
    ((withShapeHOL shapes values)[n]'(by rw [withShapeHOLLength]; exact hn)).length =
      sizeOfShapeHOL (shapes[n]'hn) := by
  rw [withShapeElTakeDropEqHOL shapes values n ⟨hvalues, hn⟩, List.length_take]
  have hdrop : (values.drop (sizeOfShapeHOL (.comb (shapes.take n)))).length =
      sizeOfShapeHOL (.comb (shapes.drop n)) := by
    have h : sizeOfShapeHOL (.comb shapes) =
        sizeOfShapeHOL (.comb (shapes.take n)) +
          sizeOfShapeHOL (.comb (shapes.drop n)) := by
      simpa [List.take_append_drop] using
        sizeOfShapeHOL_comb_append (shapes.take n) (shapes.drop n)
    rw [List.length_drop, hvalues, h, Nat.add_sub_cancel_left]
  rw [hdrop]
  exact Nat.min_eq_left (sizeOfShapeHOLDropHeadSizeLe shapes n hn)

/-- Two components of the split selected by distinct indices are disjoint when
    the flat value list is distinct.  Untagged support for the two `DISJOINT`
    ports: the strictly increasing window case. -/
theorem listDisjointWithShapeHOLGetElemLt (shapes : List ShapeHOL) (values : List α)
    (n n' : Nat) (hdistinct : values.Nodup)
    (hn : n < shapes.length) (hn' : n' < shapes.length) (hlt : n < n')
    (hvalues : values.length = sizeOfShapeHOL (.comb shapes)) :
    ListDisjoint
      ((withShapeHOL shapes values)[n]'(by rw [withShapeHOLLength]; exact hn))
      ((withShapeHOL shapes values)[n']'(by rw [withShapeHOLLength]; exact hn')) := by
  have hnPre : values.length = sizeOfShapeHOL (.comb shapes) ∧ n < shapes.length :=
    ⟨hvalues, hn⟩
  have hn'Pre : values.length = sizeOfShapeHOL (.comb shapes) ∧ n' < shapes.length :=
    ⟨hvalues, hn'⟩
  rw [withShapeElTakeDropEqHOL shapes values n hnPre,
    withShapeElTakeDropEqHOL shapes values n' hn'Pre]
  have htake : shapes.take n' = shapes.take n ++ (shapes.drop n).take (n' - n) := by
    have h := List.take_add (l := shapes) (i := n) (j := n' - n)
    have hsum : n + (n' - n) = n' := by omega
    rwa [hsum] at h
  have hsize : sizeOfShapeHOL (.comb (shapes.take n')) =
      sizeOfShapeHOL (.comb (shapes.take n)) +
        sizeOfShapeHOL (.comb ((shapes.drop n).take (n' - n))) := by
    rw [htake, sizeOfShapeHOL_comb_append]
  rw [hsize]
  have hle : sizeOfShapeHOL (shapes[n]'hn) ≤
      sizeOfShapeHOL (.comb ((shapes.drop n).take (n' - n))) := by
    obtain ⟨k, hk⟩ : ∃ k, n' - n = k + 1 := ⟨n' - n - 1, by omega⟩
    rw [hk, List.drop_eq_getElem_cons (l := shapes) hn, List.take_succ_cons,
      sizeOfShapeHOL_comb_cons]
    omega
  exact listDisjoint_drop_take_drop_take values
    (sizeOfShapeHOL (.comb (shapes.take n)))
    (sizeOfShapeHOL (shapes[n]'hn))
    (sizeOfShapeHOL (.comb ((shapes.drop n).take (n' - n))))
    (sizeOfShapeHOL (shapes[n']'hn')) hle hdistinct

/-- Exact port of HOL `panProps$all_distinct_with_shape_distinct`
    (`panPropsScript.sml:357-408`): `ALL_DISTINCT ns`, the size hypothesis,
    membership of `x` and `y` in the split, `x <> y`, `x <> []` and `y <> []`
    imply `DISJOINT (set x) (set y)`, with HOL's seven conjuncts as one
    premise. -/
@[hol "cakeml/pancake/semantics/panPropsScript.sml" "all_distinct_with_shape_distinct"]
theorem allDistinctWithShapeDistinctHOL (shapes : List ShapeHOL) (values : List α)
    (x y : List α)
    (h : values.Nodup ∧ values.length = sizeOfShapeHOL (.comb shapes) ∧
      x ∈ withShapeHOL shapes values ∧ y ∈ withShapeHOL shapes values ∧
      x ≠ y ∧ x ≠ [] ∧ y ≠ []) :
    ListDisjoint x y := by
  obtain ⟨hdistinct, hvalues, hx, hy, hne, _, _⟩ := h
  obtain ⟨n, hn, hnx⟩ := List.getElem_of_mem hx
  obtain ⟨n', hn', hn'y⟩ := List.getElem_of_mem hy
  have hnlen : n < shapes.length := by rw [withShapeHOLLength] at hn; exact hn
  have hn'len : n' < shapes.length := by rw [withShapeHOLLength] at hn'; exact hn'
  by_cases heq : n = n'
  · subst n'
    exact absurd (hnx.symm.trans hn'y) hne
  · rcases Nat.lt_or_gt_of_ne heq with hlt | hlt
    · rw [← hnx, ← hn'y]
      exact listDisjointWithShapeHOLGetElemLt shapes values n n' hdistinct hnlen hn'len
        hlt hvalues
    · rw [← hnx, ← hn'y]
      intro value hleft hright
      exact listDisjointWithShapeHOLGetElemLt shapes values n' n hdistinct hn'len hnlen
        hlt hvalues value hright hleft

/-- Exact port of HOL `panProps$all_distinct_disjoint_with_shape`
    (`panPropsScript.sml:409-451`): `ALL_DISTINCT ns`, the two index bounds,
    `n <> n'` and the size hypothesis imply
    `DISJOINT (set (EL n (with_shape sh ns))) (set (EL n' (with_shape sh ns)))`,
    with HOL's five conjuncts as one premise. -/
@[hol "cakeml/pancake/semantics/panPropsScript.sml" "all_distinct_disjoint_with_shape"]
theorem allDistinctDisjointWithShapeHOL (shapes : List ShapeHOL) (values : List α)
    (n n' : Nat)
    (h : values.Nodup ∧ n < shapes.length ∧ n' < shapes.length ∧ n ≠ n' ∧
      values.length = sizeOfShapeHOL (.comb shapes)) :
    ListDisjoint
      ((withShapeHOL shapes values)[n]'(by rw [withShapeHOLLength]; exact h.2.1))
      ((withShapeHOL shapes values)[n']'(by rw [withShapeHOLLength]; exact h.2.2.1)) := by
  obtain ⟨hdistinct, hn, hn', hne, hvalues⟩ := h
  show ListDisjoint
      ((withShapeHOL shapes values)[n]'(by rw [withShapeHOLLength]; exact hn))
      ((withShapeHOL shapes values)[n']'(by rw [withShapeHOLLength]; exact hn'))
  rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
  · exact listDisjointWithShapeHOLGetElemLt shapes values n n' hdistinct hn hn'
      hlt hvalues
  · intro value hleft hright
    exact listDisjointWithShapeHOLGetElemLt shapes values n' n hdistinct hn' hn
      hlt hvalues value hright hleft

/-- Exact port of HOL `panProps$all_distinct_mem_zip_disjoint_with_shape`
    (`panPropsScript.sml:452-475`): two triples of the aligned
    `(label, shape, component)` view whose labels differ have disjoint
    components.  The binders are HOL's own (`x a xs y b ys`), the seven
    conjuncts are one premise, and each HOL triple `(x,a,xs)` is the nested pair
    `(x, (a, xs))` inside `labels.zip (shapes.zip ...)`.  Lean core has no
    `List.mem_zip`, so the membership conjuncts are read through the untagged
    `mem_zip_getElem`. -/
@[hol "cakeml/pancake/semantics/panPropsScript.sml" "all_distinct_mem_zip_disjoint_with_shape"]
theorem allDistinctMemZipDisjointWithShapeHOL (labels : List α)
    (shapes : List ShapeHOL) (values : List β)
    (x : α) (a : ShapeHOL) (xs : List β) (y : α) (b : ShapeHOL) (ys : List β)
    (h : labels.length = shapes.length ∧
      shapes.length = (withShapeHOL shapes values).length ∧ values.Nodup ∧
      values.length = sizeOfShapeHOL (.comb shapes) ∧
      (x, (a, xs)) ∈ labels.zip (shapes.zip (withShapeHOL shapes values)) ∧
      (y, (b, ys)) ∈ labels.zip (shapes.zip (withShapeHOL shapes values)) ∧
      x ≠ y) :
    ListDisjoint xs ys := by
  obtain ⟨hlabels, hshapes, hdistinct, hvalues, hleft, hright, hne⟩ := h
  obtain ⟨i, hi, _hiInner, hleftFirst, hleftSecond⟩ :=
    mem_zip_getElem labels (shapes.zip (withShapeHOL shapes values)) (x, (a, xs)) hleft
  obtain ⟨j, hj, _hjInner, hrightFirst, hrightSecond⟩ :=
    mem_zip_getElem labels (shapes.zip (withShapeHOL shapes values)) (y, (b, ys)) hright
  rw [List.getElem_zip] at hleftSecond
  rw [List.getElem_zip] at hrightSecond
  have hiShapes : i < shapes.length := by
    rw [hlabels] at hi
    exact hi
  have hjShapes : j < shapes.length := by
    rw [hlabels] at hj
    exact hj
  have hiValues : i < (withShapeHOL shapes values).length := by
    rw [hshapes] at hiShapes
    exact hiShapes
  have hjValues : j < (withShapeHOL shapes values).length := by
    rw [hshapes] at hjShapes
    exact hjShapes
  have hleftLabel : labels[i]'hi = x := hleftFirst
  have hrightLabel : labels[j]'hj = y := hrightFirst
  have hleftComponent : xs = (withShapeHOL shapes values)[i]'hiValues := by
    have hpair : (shapes[i]'hiShapes, (withShapeHOL shapes values)[i]'hiValues) =
        (a, xs) := hleftSecond
    exact (Prod.mk.inj hpair).2.symm
  have hrightComponent : ys = (withShapeHOL shapes values)[j]'hjValues := by
    have hpair : (shapes[j]'hjShapes, (withShapeHOL shapes values)[j]'hjValues) =
        (b, ys) := hrightSecond
    exact (Prod.mk.inj hpair).2.symm
  have hneIndex : i ≠ j := by
    intro heq
    subst heq
    exact hne (by rw [← hleftLabel, ← hrightLabel])
  rw [hleftComponent, hrightComponent]
  exact allDistinctDisjointWithShapeHOL shapes values i j
    ⟨hdistinct, hiShapes, hjShapes, hneIndex, hvalues⟩

/-- Exact port of HOL `panProps$el_el_with_shape`
    (`panPropsScript.sml:568-583`): `LENGTH xs = size_of_shape (Comb shs)`,
    `n < LENGTH shs`, `n' < size_of_shape (EL n shs)` and
    `EVERY is_wf_shape_nil shs` imply `EL n' (EL n (with_shape shs xs)) =
    EL (n' + size_of_shape (Comb (TAKE n shs))) xs`, with HOL's four conjuncts
    as one premise.  The premise's `EL n shs` uses the total `elHOL` rendering
    because its bound is another conjunct of the same conjunction; the
    conclusion keeps the dependent `getElem` with the bound projected from the
    premise. -/
@[hol "cakeml/pancake/semantics/panPropsScript.sml" "el_el_with_shape"]
theorem elElWithShapeHOL (shapes : List ShapeHOL) (values : List α) (n n' : Nat)
    (h : values.length = sizeOfShapeHOL (.comb shapes) ∧ n < shapes.length ∧
      n' < sizeOfShapeHOL (elHOL shapes n) ∧
      (∀ shape, shape ∈ shapes → isWfShapeNilHOL shape = true)) :
    ((withShapeHOL shapes values)[n]'(by rw [withShapeHOLLength]; exact h.2.1))[n']'(by
        rw [withShapeHOLGetElemLength shapes values n h.1 h.2.1]
        rw [← elHOL_eq_getElem shapes n h.2.1]
        exact h.2.2.1) =
      values[n' + sizeOfShapeHOL (.comb (shapes.take n))]'(by
        have hdrop : sizeOfShapeHOL (.comb (shapes.take n)) +
              sizeOfShapeHOL (.comb (shapes.drop n)) =
            sizeOfShapeHOL (.comb shapes) := by
          rw [← sizeOfShapeHOL_comb_append, List.take_append_drop n shapes]
        have hn'get : n' < sizeOfShapeHOL (shapes[n]'h.2.1) := by
          simpa [elHOL_eq_getElem shapes n h.2.1] using h.2.2.1
        rw [h.1, ← hdrop]
        have hle := sizeOfShapeHOLDropHeadSizeLe shapes n h.2.1
        omega) := by
  obtain ⟨hvalues, hn, hn', hwf⟩ := h
  show ((withShapeHOL shapes values)[n]'(by rw [withShapeHOLLength]; exact hn))[n']'(by
        rw [withShapeHOLGetElemLength shapes values n hvalues hn]
        rw [← elHOL_eq_getElem shapes n hn]
        exact hn') =
      values[n' + sizeOfShapeHOL (.comb (shapes.take n))]'(by
        have hdrop : sizeOfShapeHOL (.comb (shapes.take n)) +
              sizeOfShapeHOL (.comb (shapes.drop n)) =
            sizeOfShapeHOL (.comb shapes) := by
          rw [← sizeOfShapeHOL_comb_append, List.take_append_drop n shapes]
        rw [hvalues, ← hdrop]
        rw [elHOL_eq_getElem shapes n hn] at hn'
        have hle := sizeOfShapeHOLDropHeadSizeLe shapes n hn
        omega)
  have hn'get : n' < sizeOfShapeHOL (shapes[n]'hn) := by
    rwa [elHOL_eq_getElem shapes n hn] at hn'
  have _ := hwf
  simp only [withShapeElTakeDropEqHOL shapes values n ⟨hvalues, hn⟩,
    List.getElem_take, List.getElem_drop]
  congr 1
  omega

end Flapjack
