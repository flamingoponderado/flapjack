module

public import Flapjack.Basis.Pure.MlString.Order
public import Flapjack.FiniteMap.Toto
public import Flapjack.FiniteMap.Comparison
public import Flapjack.Misc.Relation
public import Flapjack.Misc.Irreflexive
public import Flapjack.Misc.StrongOrder
public import Flapjack.Misc.ListEl

@[expose] public section

/-!
# Cake `mlstring` order properties

Counterparts of `string_lt_def`/`string_le_def`
(`HOL/src/string/stringScript.sml`) and of the ordering theorems in
`cakeml/basis/pure/mlstringScript.sml`.

HOL proves `TotOrd compare` through `mlstring_lt_inv_image`
(`mlstring_lt = inv_image string_lt explode`) together with `stringTheory`'s
`string_lt_trans`, `string_lt_antisym` and `string_lt_cases`. The same route is
taken here: `stringLt` is HOL's lexicographic comparison of `char list` over
`HolChar = BitVec 8`, `compare` is proved to agree with the same lexicographic
comparison applied to `explode`, and `TotOrd compare` then yields the order laws
directly.

`inv_image` is `combinTheory.inv_image_def` (`inv_image f g x = f (g x)`), so
`mlstringLt_invImage` is stated as the function equality of HOL, and
`mlstringLt_explode` is its pointwise unfolding.
-/

namespace Flapjack.Basis.Pure.MlString.Order

open Flapjack.Basis.Pure.MlString.MlString

/-! ## Byte order facts

`HolChar = BitVec 8` carries only the core `LT`/`LE` instances, so the usual
order lemmas are restated here through `BitVec.lt_def`/`BitVec.le_def`. -/

/-- `BitVec` order is asymmetric. -/
private theorem holChar_lt_asymm {a b : HolChar} (h : a < b) : ¬ b < a := by
  simp only [BitVec.lt_def] at h ⊢
  omega

/-- `BitVec` order is irreflexive. -/
private theorem holChar_lt_irrefl (a : HolChar) : ¬ a < a := by
  simp only [BitVec.lt_def]
  omega

/-- `BitVec` order is transitive. -/
private theorem holChar_lt_trans {a b c : HolChar} (h1 : a < b) (h2 : b < c) : a < c := by
  simp only [BitVec.lt_def] at h1 h2 ⊢
  omega

/-- `BitVec` order is total. -/
private theorem holChar_lt_or_gt_of_ne {a b : HolChar} (h : a ≠ b) : a < b ∨ b < a := by
  have hne : a.toNat ≠ b.toNat := by
    intro heq
    exact h (BitVec.eq_of_toNat_eq heq)
  simp only [BitVec.lt_def]
  omega

/-- `BitVec` order is antisymmetric. -/
private theorem holChar_le_antisymm {a b : HolChar} (h1 : a ≤ b) (h2 : b ≤ a) : a = b := by
  simp only [BitVec.le_def] at h1 h2
  exact BitVec.eq_of_toNat_eq (by omega)

/-- `BitVec` `≤` is `¬ >`. -/
private theorem holChar_le_of_not_gt {a b : HolChar} (h : ¬ a > b) : a ≤ b := by
  simp only [BitVec.le_def, BitVec.lt_def] at h ⊢
  omega

/-- `BitVec` `≤` splits into `<` or `=`. -/
private theorem holChar_lt_or_eq_of_le {a b : HolChar} (h : a ≤ b) : a < b ∨ a = b := by
  simp only [BitVec.le_def] at h
  simp only [BitVec.lt_def]
  by_cases hlt : a.toNat < b.toNat
  · exact Or.inl hlt
  · exact Or.inr (BitVec.eq_of_toNat_eq (by omega))

/-- `BitVec` `≤` and `<` compose. -/
private theorem holChar_le_lt_trans {a b c : HolChar} (h1 : a ≤ b) (h2 : b < c) : a < c := by
  simp only [BitVec.le_def] at h1
  simp only [BitVec.lt_def] at h2 ⊢
  omega

/-! ## HOL `stringTheory` lexicographic order on `char list` -/

/-- Original `string_lt_def` (`HOL/src/string/stringScript.sml:615-620`):
`EMPTYSTRING` is below every `STRING`, and the first differing character
decides. `HolChar` is `BitVec 8`, whose `<` is HOL `char_lt`. -/
@[hol "HOL/src/string/stringScript.sml" "string_lt_def"]
def stringLt : List HolChar → List HolChar → Bool
  | _, [] => false
  | [], _ :: _ => true
  | c1 :: s1, c2 :: s2 => c1 < c2 || (c1 = c2 && stringLt s1 s2)

/-- Original `string_le_def` (`stringScript.sml:622`):
`string_le s1 s2 ⇔ (s1 = s2) \/ string_lt s1 s2`. -/
@[hol "HOL/src/string/stringScript.sml" "string_le_def"]
def stringLe (s1 s2 : List HolChar) : Bool := s1 = s2 || stringLt s1 s2

/-! ## The lexicographic walk used by `compare_aux` -/

/-- Lexicographic comparison of character lists, matching the `Ordering` walk
of `compare_aux` step for step. Lean-side workhorse; no HOL counterpart. -/
private def cmpList : List HolChar → List HolChar → Ordering
  | [], [] => .eq
  | _ :: _, [] => .gt
  | [], _ :: _ => .lt
  | c1 :: t1, c2 :: t2 =>
    if c2 < c1 then .gt else if c1 < c2 then .lt else cmpList t1 t2

/-- `string_lt` agrees with the `Ordering` walk. -/
private theorem stringLt_eq_cmpList (l1 l2 : List HolChar) :
    stringLt l1 l2 = true ↔ cmpList l1 l2 = .lt := by
  induction l1 generalizing l2 with
  | nil =>
    cases l2 with
    | nil => simp [stringLt, cmpList]
    | cons c2 t2 => simp [stringLt, cmpList]
  | cons c1 t1 ih =>
    cases l2 with
    | nil => simp [stringLt, cmpList]
    | cons c2 t2 =>
      simp only [stringLt, cmpList, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq]
      by_cases h2 : c2 < c1
      · have h1 : ¬ c1 < c2 := holChar_lt_asymm h2
        have hne : c1 ≠ c2 := by
          intro heq
          rw [heq] at h2
          exact absurd h2 (holChar_lt_irrefl _)
        simp [h2, h1, hne]
      · by_cases h1 : c1 < c2
        · have hne : c1 ≠ c2 := by
            intro heq
            rw [heq] at h1
            exact absurd h1 (holChar_lt_irrefl _)
          simp [h2, h1, hne]
        · have hceq : c1 = c2 := holChar_le_antisymm (holChar_le_of_not_gt h2)
            (holChar_le_of_not_gt h1)
          simp [hceq, ih]

/-- The `Ordering` walk is `.eq` exactly on equal lists. -/
private theorem cmpList_eq_iff (l1 l2 : List HolChar) : cmpList l1 l2 = .eq ↔ l1 = l2 := by
  induction l1 generalizing l2 with
  | nil =>
    cases l2 with
    | nil => simp [cmpList]
    | cons c2 t2 => simp [cmpList]
  | cons c1 t1 ih =>
    cases l2 with
    | nil => simp [cmpList]
    | cons c2 t2 =>
      simp only [cmpList]
      by_cases h2 : c2 < c1
      · have h1 : ¬ c1 < c2 := holChar_lt_asymm h2
        have hne : c1 ≠ c2 := by
          intro heq
          rw [heq] at h2
          exact absurd h2 (holChar_lt_irrefl _)
        simp [h2, hne]
      · by_cases h1 : c1 < c2
        · have hne : c1 ≠ c2 := by
            intro heq
            rw [heq] at h1
            exact absurd h1 (holChar_lt_irrefl _)
          simp [h2, h1, hne]
        · have hceq : c1 = c2 := holChar_le_antisymm (holChar_le_of_not_gt h2)
            (holChar_le_of_not_gt h1)
          simp [hceq, ih]

/-- The `Ordering` walk reverses `.gt` and `.lt`. -/
private theorem cmpList_antisym (l1 l2 : List HolChar) :
    cmpList l1 l2 = .gt ↔ cmpList l2 l1 = .lt := by
  induction l1 generalizing l2 with
  | nil =>
    cases l2 with
    | nil => simp [cmpList]
    | cons c2 t2 => simp [cmpList]
  | cons c1 t1 ih =>
    cases l2 with
    | nil => simp [cmpList]
    | cons c2 t2 =>
      simp only [cmpList]
      by_cases h2 : c2 < c1
      · have h1 : ¬ c1 < c2 := holChar_lt_asymm h2
        simp [h2, h1]
      · by_cases h1 : c1 < c2
        · simp [h2, h1]
        · simp [h2, h1, ih]

/-- Strict transitivity of the `Ordering` walk. -/
private theorem cmpList_trans (l1 l2 l3 : List HolChar)
    (h1 : cmpList l1 l2 = .lt) (h2 : cmpList l2 l3 = .lt) : cmpList l1 l3 = .lt := by
  induction l1 generalizing l2 l3 with
  | nil =>
    cases l2 with
    | nil => simp [cmpList] at h1
    | cons b t2 =>
      cases l3 with
      | nil => simp [cmpList] at h2
      | cons c t3 => simp [cmpList]
  | cons a t1 ih =>
    cases l2 with
    | nil => simp [cmpList] at h1
    | cons b t2 =>
      cases l3 with
      | nil => simp [cmpList] at h2
      | cons c t3 =>
        simp only [cmpList] at h1 h2 ⊢
        have hba : ¬ b < a := by
          intro hb
          rw [if_pos hb] at h1
          simp at h1
        have h1' : a < b ∨ cmpList t1 t2 = .lt := by
          rw [if_neg hba] at h1
          by_cases hab : a < b
          · exact Or.inl hab
          · right
            rw [if_neg hab] at h1
            exact h1
        have hcb : ¬ c < b := by
          intro hc
          rw [if_pos hc] at h2
          simp at h2
        have h2' : b < c ∨ cmpList t2 t3 = .lt := by
          rw [if_neg hcb] at h2
          by_cases hbc : b < c
          · exact Or.inl hbc
          · right
            rw [if_neg hbc] at h2
            exact h2
        have hca : ¬ c < a := by
          rcases h1' with hab | h12
          · rcases h2' with hbc | h23
            · intro hc
              exact holChar_lt_asymm (holChar_lt_trans hab hbc) hc
            · intro hc
              exact hcb (holChar_lt_trans hc hab)
          · intro hc
            exact hba (holChar_le_lt_trans (holChar_le_of_not_gt hcb) hc)
        rw [if_neg hca]
        rcases h1' with hab | h12
        · rcases h2' with hbc | h23
          · rw [if_pos (holChar_lt_trans hab hbc)]
          · have hac : a < c := by
              by_cases hac' : a < c
              · exact hac'
              · rcases holChar_lt_or_eq_of_le (holChar_le_of_not_gt hac') with hlt | heq
                · exact absurd hlt hca
                · rw [← heq] at hab
                  rw [if_pos hab] at h2
                  simp at h2
            rw [if_pos hac]
        · rcases h2' with hbc | h23
          · have hac : a < c := by
              by_cases hac' : a < c
              · exact hac'
              · rcases holChar_lt_or_eq_of_le (holChar_le_of_not_gt hac') with hlt | heq
                · exact absurd (holChar_lt_trans hbc hlt) hba
                · rw [heq] at hbc
                  rw [if_pos hbc] at h1
                  simp at h1
            rw [if_pos hac]
          · have h13 : cmpList t1 t3 = .lt := ih t2 t3 h12 h23
            by_cases hac : a < c
            · rw [if_pos hac]
            · rw [if_neg hac, h13]

/-- A proper prefix is smaller. -/
private theorem cmpList_self_append (l r : List HolChar) (hr : r ≠ []) :
    cmpList l (l ++ r) = .lt := by
  induction l with
  | nil =>
    cases r with
    | nil => exact absurd rfl hr
    | cons c t => simp [cmpList]
  | cons c t ih =>
    simp [cmpList, ih]

/-- A proper prefix is greater from the right. -/
private theorem cmpList_append_self (l r : List HolChar) (hr : r ≠ []) :
    cmpList (l ++ r) l = .gt := by
  induction l with
  | nil =>
    cases r with
    | nil => exact absurd rfl hr
    | cons c t => simp [cmpList]
  | cons c t ih =>
    simp [cmpList, ih]

/-- Two equal-length lists that differ decide the walk of their prefixes. -/
private theorem cmpList_take (n : Nat) (l1 l2 : List HolChar)
    (h : cmpList (l1.take n) (l2.take n) ≠ .eq) :
    cmpList l1 l2 = cmpList (l1.take n) (l2.take n) := by
  induction n generalizing l1 l2 with
  | zero =>
    simp [cmpList] at h
  | succ n ih =>
    cases l1 with
    | nil =>
      cases l2 with
      | nil => simp [cmpList] at h
      | cons c2 t2 => simp [cmpList]
    | cons c1 t1 =>
      cases l2 with
      | nil => simp [cmpList]
      | cons c2 t2 =>
        simp only [List.take_succ_cons] at h ⊢
        by_cases h2 : c2 < c1
        · simp [cmpList, h2]
        · by_cases h1 : c1 < c2
          · simp [cmpList, h2, h1]
          · have hne : cmpList (t1.take n) (t2.take n) ≠ .eq := by
              intro hc
              apply h
              simp [cmpList, h2, h1, hc]
            simp only [cmpList, h2, h1, if_false]
            exact ih t1 t2 hne

/-! ## `stringTheory` order laws on `char list` -/

/-- Original `string_lt_nonrefl`. -/
@[hol "HOL/src/string/stringScript.sml" "string_lt_nonrefl"]
theorem stringLt_nonrefl (s : List HolChar) : ¬(stringLt s s = true) := by
  rw [stringLt_eq_cmpList]
  intro h
  have heq : cmpList s s = .eq := (cmpList_eq_iff s s).mpr rfl
  rw [heq] at h
  simp at h

/-- Original `string_lt_antisym`. -/
@[hol "HOL/src/string/stringScript.sml" "string_lt_antisym"]
theorem stringLt_antisym (s t : List HolChar) :
    ¬(stringLt s t = true ∧ stringLt t s = true) := by
  rw [stringLt_eq_cmpList, stringLt_eq_cmpList]
  intro h
  have hgt : cmpList t s = .gt := (cmpList_antisym t s).mpr h.1
  rw [hgt] at h
  simp at h

/-- Original `string_lt_cases`. -/
@[hol "HOL/src/string/stringScript.sml" "string_lt_cases"]
theorem stringLt_cases (s t : List HolChar) :
    s = t ∨ stringLt s t = true ∨ stringLt t s = true := by
  rw [stringLt_eq_cmpList, stringLt_eq_cmpList]
  generalize hc : cmpList s t = o
  cases o with
  | lt => exact Or.inr (Or.inl rfl)
  | gt => exact Or.inr (Or.inr ((cmpList_antisym s t).mp hc))
  | eq => exact Or.inl ((cmpList_eq_iff s t).mp hc)

/-- Original `string_lt_trans`. -/
@[hol "HOL/src/string/stringScript.sml" "string_lt_trans"]
theorem stringLt_trans (s1 s2 s3 : List HolChar)
    (h : stringLt s1 s2 = true ∧ stringLt s2 s3 = true) :
    stringLt s1 s3 = true := by
  simp only [stringLt_eq_cmpList] at h ⊢
  exact cmpList_trans _ _ _ h.1 h.2

/-! ## `compare_aux` and `compare` -/

/-- One unfolding step of `compare_aux` at a positive length. -/
private theorem compareAux_succ (s1 s2 : MlString) (ord : Ordering) (start n : Nat) :
    compareAux s1 s2 ord start (n + 1) =
      (if strsub s2 start < strsub s1 start then .gt
       else if strsub s1 start < strsub s2 start then .lt
       else compareAux s1 s2 ord (start + 1) n) := by
  rw [compareAux]
  simp

/-- Original `compare_aux_spec`: over a bounded window, the walk returns the
carried order when the window agrees and the lexicographic comparison of the
window otherwise. -/
private theorem compareAux_take (s1 s2 : MlString) (ord : Ordering) (start n : Nat)
    (h1 : start + n ≤ strlen s1) (h2 : start + n ≤ strlen s2) :
    compareAux s1 s2 ord start n =
      (if ((explode s1).drop start).take n = ((explode s2).drop start).take n then ord
       else cmpList (((explode s1).drop start).take n)
         (((explode s2).drop start).take n)) := by
  induction n generalizing start with
  | zero =>
    rw [compareAux]
    simp
  | succ n ih =>
    have hs1 : start < strlen s1 := by omega
    have hs2 : start < strlen s2 := by omega
    have hlen1 : strlen s1 = (explode s1).length := strlen_eq_explode_length s1
    have hlen2 : strlen s2 = (explode s2).length := strlen_eq_explode_length s2
    have hs1' : start < (explode s1).length := by omega
    have hs2' : start < (explode s2).length := by omega
    have hd1 : (explode s1).drop start =
        (explode s1)[start] :: (explode s1).drop (start + 1) :=
      List.drop_eq_getElem_cons hs1'
    have hd2 : (explode s2).drop start =
        (explode s2)[start] :: (explode s2).drop (start + 1) :=
      List.drop_eq_getElem_cons hs2'
    have hsub1 : strsub s1 start = (explode s1)[start] := by
      rw [strsub, holEl_eq_getElem start (explode s1) hs1']
    have hsub2 : strsub s2 start = (explode s2)[start] := by
      rw [strsub, holEl_eq_getElem start (explode s2) hs2']
    have hih := ih (start + 1) (by omega) (by omega)
    rw [compareAux_succ, hsub1, hsub2, hd1, hd2, List.take_succ_cons, List.take_succ_cons, hih]
    simp only [cmpList]
    by_cases hall : (explode s1)[start] :: ((explode s1).drop (start + 1)).take n =
        (explode s2)[start] :: ((explode s2).drop (start + 1)).take n
    · rw [if_pos hall]
      have hc : (explode s1)[start] = (explode s2)[start] :=
        ((List.cons.injEq _ _ _ _).mp hall).1
      have ht : ((explode s1).drop (start + 1)).take n =
          ((explode s2).drop (start + 1)).take n :=
        ((List.cons.injEq _ _ _ _).mp hall).2
      rw [hc, ht]
      simp
    · rw [if_neg hall]
      by_cases hc : (explode s1)[start] = (explode s2)[start]
      · have ht : ((explode s1).drop (start + 1)).take n ≠
            ((explode s2).drop (start + 1)).take n := by
          intro hteq
          exact hall (by rw [hc, hteq])
        rw [hc]
        rw [if_neg (holChar_lt_irrefl _), if_neg (holChar_lt_irrefl _), if_neg ht]
        simp
      · rcases holChar_lt_or_gt_of_ne hc with hlt | hgt
        · have hgt' : ¬ (explode s2)[start] < (explode s1)[start] := holChar_lt_asymm hlt
          rw [if_neg hgt', if_pos hlt]
          simp [hgt', hlt]
        · have hlt' : ¬ (explode s1)[start] < (explode s2)[start] := holChar_lt_asymm hgt
          rw [if_pos hgt, if_neg hlt']
          simp [hgt]

/-- `compare` is the lexicographic comparison of the underlying character lists. -/
private theorem compare_eq_cmpList (s1 s2 : MlString) :
    compare s1 s2 = cmpList (explode s1) (explode s2) := by
  have hlen1 : strlen s1 = (explode s1).length := strlen_eq_explode_length s1
  have hlen2 : strlen s2 = (explode s2).length := strlen_eq_explode_length s2
  rw [compare]
  by_cases hlt : strlen s1 < strlen s2
  · rw [if_pos hlt]
    have htake1 : (explode s1).take (strlen s1) = explode s1 := by
      rw [hlen1, List.take_length]
    have hspec := compareAux_take s1 s2 .lt 0 (strlen s1) (by omega) (by omega)
    simp only [List.drop_zero] at hspec
    rw [hspec, htake1]
    by_cases heq : explode s1 = (explode s2).take (strlen s1)
    · rw [if_pos heq]
      have hsplit : explode s2 = explode s1 ++ (explode s2).drop (strlen s1) := by
        rw [heq]
        exact (List.take_append_drop (strlen s1) (explode s2)).symm
      have hrest : (explode s2).drop (strlen s1) ≠ [] := by
        intro hnil
        have hlen : (explode s2).length = strlen s1 := by
          rw [← List.take_append_drop (strlen s1) (explode s2), hnil, List.append_nil]
          rw [← heq, hlen1]
        omega
      rw [hsplit]
      exact (cmpList_self_append (explode s1) _ hrest).symm
    · rw [if_neg heq]
      have hne : cmpList (explode s1) ((explode s2).take (strlen s1)) ≠ .eq := by
        intro hc
        exact heq ((cmpList_eq_iff _ _).mp hc)
      have h := cmpList_take (strlen s1) (explode s1) (explode s2) (by rwa [htake1])
      rw [htake1] at h
      exact h.symm
  · by_cases hlt2 : strlen s2 < strlen s1
    · rw [if_neg hlt]
      rw [if_pos hlt2]
      have htake2 : (explode s2).take (strlen s2) = explode s2 := by
        rw [hlen2, List.take_length]
      have hspec := compareAux_take s1 s2 .gt 0 (strlen s2) (by omega) (by omega)
      simp only [List.drop_zero] at hspec
      rw [hspec, htake2]
      by_cases heq : (explode s1).take (strlen s2) = explode s2
      · rw [if_pos heq]
        have hsplit : explode s1 = explode s2 ++ (explode s1).drop (strlen s2) := by
          rw [← heq]
          exact (List.take_append_drop (strlen s2) (explode s1)).symm
        have hrest : (explode s1).drop (strlen s2) ≠ [] := by
          intro hnil
          have hlen : (explode s1).length = strlen s2 := by
            rw [← List.take_append_drop (strlen s2) (explode s1), hnil, List.append_nil]
            rw [heq, hlen2]
          omega
        rw [hsplit]
        exact (cmpList_append_self (explode s2) _ hrest).symm
      · rw [if_neg heq]
        have hne : cmpList ((explode s1).take (strlen s2)) (explode s2) ≠ .eq := by
          intro hc
          exact heq ((cmpList_eq_iff _ _).mp hc)
        have h := cmpList_take (strlen s2) (explode s1) (explode s2) (by rwa [htake2])
        rw [htake2] at h
        exact h.symm
    · rw [if_neg hlt, if_neg hlt2]
      have hlen_eq : strlen s1 = strlen s2 := by omega
      have htake1 : (explode s1).take (strlen s2) = explode s1 := by
        rw [← hlen_eq, hlen1, List.take_length]
      have htake2 : (explode s2).take (strlen s2) = explode s2 := by
        rw [hlen2, List.take_length]
      have hspec := compareAux_take s1 s2 .eq 0 (strlen s2) (by omega) (by omega)
      simp only [List.drop_zero] at hspec
      rw [hspec, htake1, htake2]
      by_cases heq : explode s1 = explode s2
      · rw [if_pos heq, heq]
        exact ((cmpList_eq_iff (explode s2) (explode s2)).mpr rfl).symm
      · rw [if_neg heq]

/-- `explode` is injective. -/
private theorem explode_eq_iff (s1 s2 : MlString) : explode s1 = explode s2 ↔ s1 = s2 := by
  cases s1 with
  | implode d1 =>
    cases s2 with
    | implode d2 =>
      simp [explode]

/-! ## Order laws -/

/-- Pointwise unfolding of `mlstring_lt_inv_image`. -/
theorem mlstringLt_explode (s1 s2 : MlString) :
    mlstringLt s1 s2 = stringLt (explode s1) (explode s2) := by
  have hiff : (mlstringLt s1 s2 = true) ↔ (stringLt (explode s1) (explode s2) = true) := by
    rw [stringLt_eq_cmpList]
    simp only [mlstringLt, decide_eq_true_eq, compare_eq_cmpList]
  cases h1 : mlstringLt s1 s2 with
  | true =>
    cases h2 : stringLt (explode s1) (explode s2) with
    | true => rfl
    | false => simp [h1, h2] at hiff
  | false =>
    cases h2 : stringLt (explode s1) (explode s2) with
    | true => simp [h1, h2] at hiff
    | false => rfl

/-- Original `mlstring_lt_inv_image`: `mlstring_lt = inv_image string_lt explode`
(`combinTheory.inv_image_def`, so the right side is
`fun s1 s2 => string_lt (explode s1) (explode s2)`). -/
@[hol "cakeml/basis/pure/mlstringScript.sml" "mlstring_lt_inv_image"]
theorem mlstringLt_invImage :
    mlstringLt = fun s1 s2 => stringLt (explode s1) (explode s2) := by
  funext s1
  funext s2
  exact mlstringLt_explode s1 s2

/-- `mlstring_lt` agrees with the `Ordering` walk on `explode`. -/
private theorem mlstringLt_eq (s1 s2 : MlString) :
    mlstringLt s1 s2 = true ↔ cmpList (explode s1) (explode s2) = .lt := by
  rw [mlstringLt_explode, stringLt_eq_cmpList]

/-- `mlstring_le` agrees with the `Ordering` walk on `explode`. -/
private theorem mlstringLe_eq (s1 s2 : MlString) :
    mlstringLe s1 s2 = true ↔ cmpList (explode s1) (explode s2) ≠ .gt := by
  simp only [mlstringLe, decide_eq_true_eq, compare_eq_cmpList]

/-- The walk is never `.gt` exactly when the lists agree or are `.lt`. -/
private theorem cmpList_not_gt (l1 l2 : List HolChar) :
    cmpList l1 l2 ≠ .gt ↔ l1 = l2 ∨ cmpList l1 l2 = .lt := by
  generalize hc : cmpList l1 l2 = o
  cases o with
  | gt =>
    have hne : l1 ≠ l2 := by
      intro hlr
      rw [hlr] at hc
      have heq : cmpList l2 l2 = .eq := (cmpList_eq_iff l2 l2).mpr rfl
      rw [heq] at hc
      simp at hc
    simp [hne]
  | lt => simp
  | eq =>
    have hlr : l1 = l2 := (cmpList_eq_iff l1 l2).mp hc
    simp [hlr]

/-- Original `TotOrd_compare`: `compare` is a total-order comparator. -/
@[hol "cakeml/basis/pure/mlstringScript.sml" "TotOrd_compare"]
theorem totOrd_compare : Flapjack.FiniteMap.Toto.totOrd compare := by
  refine ⟨?_, ?_, ?_⟩
  · intro x y
    rw [compare_eq_cmpList, cmpList_eq_iff, explode_eq_iff]
  · intro x y
    rw [compare_eq_cmpList, compare_eq_cmpList]
    exact cmpList_antisym (explode x) (explode y)
  · intro x y z h
    simp only [compare_eq_cmpList] at h ⊢
    exact cmpList_trans _ _ _ h.1 h.2

/-- Original `good_cmp_compare`: the seven `good_cmp` clauses follow from
`TotOrd_compare`. -/
@[hol "cakeml/basis/pure/mlstringScript.sml" "good_cmp_compare"]
theorem goodCmp_compare : Flapjack.FiniteMap.Comparison.goodCmp compare :=
  Flapjack.FiniteMap.Comparison.totOrderImpGoodCmp compare totOrd_compare

/-- Original `mlstring_lt_antisym`. -/
@[hol "cakeml/basis/pure/mlstringScript.sml" "mlstring_lt_antisym"]
theorem mlstringLt_antisym (s t : MlString) :
    ¬(mlstringLt s t = true ∧ mlstringLt t s = true) := by
  rw [mlstringLt_eq, mlstringLt_eq]
  intro h
  have hgt : cmpList (explode t) (explode s) = .gt :=
    (cmpList_antisym (explode t) (explode s)).mpr h.1
  rw [hgt] at h
  simp at h

/-- Original `mlstring_lt_cases`. -/
@[hol "cakeml/basis/pure/mlstringScript.sml" "mlstring_lt_cases"]
theorem mlstringLt_cases (s t : MlString) :
    s = t ∨ mlstringLt s t = true ∨ mlstringLt t s = true := by
  rw [mlstringLt_eq, mlstringLt_eq]
  generalize hc : cmpList (explode s) (explode t) = o
  cases o with
  | lt => exact Or.inr (Or.inl rfl)
  | gt => exact Or.inr (Or.inr ((cmpList_antisym (explode s) (explode t)).mp hc))
  | eq => exact Or.inl ((explode_eq_iff _ _).mp ((cmpList_eq_iff _ _).mp hc))

/-- Original `mlstring_lt_nonrefl`. -/
@[hol "cakeml/basis/pure/mlstringScript.sml" "mlstring_lt_nonrefl"]
theorem mlstringLt_nonrefl (s : MlString) : ¬(mlstringLt s s = true) := by
  rw [mlstringLt_eq]
  intro h
  have heq : cmpList (explode s) (explode s) = .eq := (cmpList_eq_iff _ _).mpr rfl
  rw [heq] at h
  simp at h

/-- Original `mlstring_lt_trans`. -/
@[hol "cakeml/basis/pure/mlstringScript.sml" "mlstring_lt_trans"]
theorem mlstringLt_trans (s1 s2 s3 : MlString)
    (h : mlstringLt s1 s2 = true ∧ mlstringLt s2 s3 = true) :
    mlstringLt s1 s3 = true := by
  simp only [mlstringLt_eq] at h ⊢
  exact cmpList_trans _ _ _ h.1 h.2

/-- Original `mlstring_le_thm`. -/
@[hol "cakeml/basis/pure/mlstringScript.sml" "mlstring_le_thm"]
theorem mlstringLe_thm (s1 s2 : MlString) :
    mlstringLe s1 s2 = true ↔ s1 = s2 ∨ mlstringLt s1 s2 = true := by
  rw [mlstringLe_eq, mlstringLt_eq, ← explode_eq_iff]
  exact cmpList_not_gt (explode s1) (explode s2)

/-- Original `mlstring_gt_thm`. -/
@[hol "cakeml/basis/pure/mlstringScript.sml" "mlstring_gt_thm"]
theorem mlstringGt_thm (s1 s2 : MlString) :
    mlstringGt s1 s2 = true ↔ mlstringLt s2 s1 = true := by
  rw [mlstringGt, mlstringLt_eq]
  simp only [decide_eq_true_eq, compare_eq_cmpList]
  exact cmpList_antisym (explode s1) (explode s2)

/-- Original `mlstring_ge_thm`. -/
@[hol "cakeml/basis/pure/mlstringScript.sml" "mlstring_ge_thm"]
theorem mlstringGe_thm (s1 s2 : MlString) :
    mlstringGe s1 s2 = true ↔ mlstringLe s2 s1 = true := by
  rw [mlstringGe, mlstringLe_eq]
  simp only [decide_eq_true_eq, compare_eq_cmpList]
  constructor
  · intro h hb
    exact h ((cmpList_antisym (explode s2) (explode s1)).mp hb)
  · intro h ha
    exact h ((cmpList_antisym (explode s2) (explode s1)).mpr ha)

/-- Original `transitive_mlstring_le`. -/
@[hol "cakeml/basis/pure/mlstringScript.sml" "transitive_mlstring_le"]
theorem transitive_mlstringLe : holTransitive (fun x y => mlstringLe x y = true) := by
  intro x y z h
  change mlstringLe x y = true ∧ mlstringLe y z = true at h
  simp only [mlstringLe_thm] at h ⊢
  obtain ⟨hxy, hyz⟩ := h
  apply Or.elim hxy
  · intro heq
    apply Or.elim hyz
    · intro heq2
      exact Or.inl (heq.trans heq2)
    · intro hlt
      rw [← heq] at hlt
      exact Or.inr hlt
  · intro hlt
    apply Or.elim hyz
    · intro heq2
      rw [heq2] at hlt
      exact Or.inr hlt
    · intro hlt2
      exact Or.inr (mlstringLt_trans x y z ⟨hlt, hlt2⟩)

/-- Original `antisymmetric_mlstring_le`. -/
@[hol "cakeml/basis/pure/mlstringScript.sml" "antisymmetric_mlstring_le"]
theorem antisymmetric_mlstringLe :
    holAntisymmetric (fun x y => mlstringLe x y = true) := by
  intro x y h
  change mlstringLe x y = true ∧ mlstringLe y x = true at h
  simp only [mlstringLe_thm] at h
  obtain ⟨hxy, hyx⟩ := h
  apply Or.elim hxy
  · intro heq
    exact heq
  · intro hlt
    apply Or.elim hyx
    · intro heq
      exact heq.symm
    · intro hlt2
      exact absurd ⟨hlt, hlt2⟩ (mlstringLt_antisym x y)

/-- Original `string_lt_total`. -/
@[hol "cakeml/basis/pure/mlstringScript.sml" "string_lt_total"]
theorem stringLt_total (s1 s2 : List HolChar)
    (h : ¬(stringLt s1 s2 = true) ∧ ¬(stringLt s2 s1 = true)) : s1 = s2 := by
  rw [stringLt_eq_cmpList, stringLt_eq_cmpList] at h
  obtain ⟨h1, h2⟩ := h
  cases hc : cmpList s1 s2 with
  | lt => exact absurd hc h1
  | gt => exact absurd ((cmpList_antisym s1 s2).mp hc) h2
  | eq => exact (cmpList_eq_iff s1 s2).mp hc

/-- Original `total_mlstring_le`. -/
@[hol "cakeml/basis/pure/mlstringScript.sml" "total_mlstring_le"]
theorem total_mlstringLe : holTotal (fun x y => mlstringLe x y = true) := by
  intro x y
  change mlstringLe x y = true ∨ mlstringLe y x = true
  rcases mlstringLt_cases x y with heq | hlt | hgt
  · left
    rw [mlstringLe_thm]
    exact Or.inl heq
  · left
    rw [mlstringLe_thm]
    exact Or.inr hlt
  · right
    rw [mlstringLe_thm]
    exact Or.inr hgt

/-- Original `strlit_le_strlit`: `strlit` is the `implode` constructor. -/
@[hol "cakeml/basis/pure/mlstringScript.sml" "strlit_le_strlit"]
theorem strlit_le_strlit (s1 s2 : List HolChar) :
    mlstringLe (.implode s1) (.implode s2) = true ↔ stringLe s1 s2 = true := by
  rw [mlstringLe_thm, mlstringLt_explode, stringLe]
  simp only [explode_implode, Bool.or_eq_true, decide_eq_true_eq, MlString.implode.injEq]

/-- Original `transitive_mlstring_lt` (HOL `[local]`). -/
private theorem transitive_mlstringLt : holTransitive (fun x y => mlstringLt x y = true) := by
  intro x y z h
  change mlstringLt x y = true ∧ mlstringLt y z = true at h
  exact mlstringLt_trans x y z h

/-- Original `irreflexive_mlstring_lt` (HOL `[local]`). -/
private theorem irreflexive_mlstringLt : holIrreflexive (fun x y => mlstringLt x y = true) := by
  intro x h
  change mlstringLt x x = true at h
  exact mlstringLt_nonrefl x h

/-- Original `trichotomous_mlstring_lt` (HOL `[local]`). -/
private theorem trichotomous_mlstringLt :
    holTrichotomous (fun x y => mlstringLt x y = true) := by
  intro a b
  change mlstringLt a b = true ∨ mlstringLt b a = true ∨ a = b
  rcases mlstringLt_cases a b with heq | hlt | hgt
  · exact Or.inr (Or.inr heq)
  · exact Or.inl hlt
  · exact Or.inr (Or.inl hgt)

/-- Original `StrongLinearOrder_mlstring_lt`. -/
@[hol "cakeml/basis/pure/mlstringScript.sml" "StrongLinearOrder_mlstring_lt"]
theorem strongLinearOrder_mlstringLt :
    holStrongLinearOrder (fun x y => mlstringLt x y = true) :=
  ⟨⟨irreflexive_mlstringLt, transitive_mlstringLt⟩, trichotomous_mlstringLt⟩

/-! ## `fast_lt` and friends -/

/-- Original `fast_lt_nonrefl`. -/
@[hol "cakeml/basis/pure/mlstringScript.sml" "fast_lt_nonrefl"]
theorem fastLt_nonrefl (s : MlString) : ¬(fastLt s s = true) := by
  simp [fastLt, mlstringLt_nonrefl]

/-- Original `fast_lt_trans`. -/
@[hol "cakeml/basis/pure/mlstringScript.sml" "fast_lt_trans"]
theorem fastLt_trans (s1 s2 s3 : MlString)
    (h : fastLt s1 s2 = true ∧ fastLt s2 s3 = true) : fastLt s1 s3 = true := by
  simp only [fastLt] at h ⊢
  have h1 := h.1
  have h2 := h.2
  by_cases h12 : strlen s1 = strlen s2
  · by_cases h23 : strlen s2 = strlen s3
    · rw [if_pos h12] at h1
      rw [if_pos h23] at h2
      rw [if_pos (h12.trans h23)]
      exact mlstringLt_trans s1 s2 s3 ⟨h1, h2⟩
    · rw [if_pos h12] at h1
      rw [if_neg h23] at h2
      simp only [decide_eq_true_eq] at h2
      rw [if_neg (by omega)]
      simp only [decide_eq_true_eq]
      omega
  · by_cases h23 : strlen s2 = strlen s3
    · rw [if_neg h12] at h1
      rw [if_pos h23] at h2
      simp only [decide_eq_true_eq] at h1
      rw [if_neg (by omega)]
      simp only [decide_eq_true_eq]
      omega
    · rw [if_neg h12] at h1
      rw [if_neg h23] at h2
      simp only [decide_eq_true_eq] at h1 h2
      by_cases h13 : strlen s1 = strlen s3
      · rw [if_pos h13]
        exact absurd h1 (by omega)
      · rw [if_neg h13]
        simp only [decide_eq_true_eq]
        omega

/-- Original `fast_le_thm`. -/
@[hol "cakeml/basis/pure/mlstringScript.sml" "fast_le_thm"]
theorem fastLe_thm (s1 s2 : MlString) :
    fastLe s1 s2 = true ↔ s1 = s2 ∨ fastLt s1 s2 = true := by
  by_cases hlen : strlen s1 = strlen s2
  · simp only [fastLe, fastLt, hlen, if_true]
    exact mlstringLe_thm s1 s2
  · simp only [fastLe, fastLt, hlen, if_false, decide_eq_true_eq]
    constructor
    · intro hle
      by_cases heq : s1 = s2
      · exact Or.inl heq
      · exact Or.inr (Nat.lt_of_le_of_ne hle hlen)
    · intro h
      apply Or.elim h
      · intro heq
        rw [heq]
        exact Nat.le_refl _
      · intro hlt
        exact Nat.le_of_lt hlt

/-- Original `fast_gt_thm`. -/
@[hol "cakeml/basis/pure/mlstringScript.sml" "fast_gt_thm"]
theorem fastGt_thm (s1 s2 : MlString) :
    fastGt s1 s2 = true ↔ fastLt s2 s1 = true := by
  by_cases hlen : strlen s1 = strlen s2
  · rw [fastGt, if_pos hlen, fastLt, if_pos hlen.symm]
    exact mlstringGt_thm s1 s2
  · rw [fastGt, if_neg hlen, fastLt, if_neg (Ne.symm hlen)]

/-- Original `fast_ge_thm`. -/
@[hol "cakeml/basis/pure/mlstringScript.sml" "fast_ge_thm"]
theorem fastGe_thm (s1 s2 : MlString) :
    fastGe s1 s2 = true ↔ fastLe s2 s1 = true := by
  by_cases hlen : strlen s1 = strlen s2
  · rw [fastGe, if_pos hlen, fastLe, if_pos hlen.symm]
    exact mlstringGe_thm s1 s2
  · rw [fastGe, if_neg hlen, fastLe, if_neg (Ne.symm hlen)]

/-- Original `transitive_fast_le`. -/
@[hol "cakeml/basis/pure/mlstringScript.sml" "transitive_fast_le"]
theorem transitive_fastLe : holTransitive (fun x y => fastLe x y = true) := by
  intro x y z h
  change fastLe x y = true ∧ fastLe y z = true at h
  simp only [fastLe_thm] at h ⊢
  obtain ⟨hxy, hyz⟩ := h
  apply Or.elim hxy
  · intro heq
    apply Or.elim hyz
    · intro heq2
      exact Or.inl (heq.trans heq2)
    · intro hlt
      rw [← heq] at hlt
      exact Or.inr hlt
  · intro hlt
    apply Or.elim hyz
    · intro heq2
      rw [heq2] at hlt
      exact Or.inr hlt
    · intro hlt2
      exact Or.inr (fastLt_trans x y z ⟨hlt, hlt2⟩)

/-- Original `antisymmetric_fast_le`. -/
@[hol "cakeml/basis/pure/mlstringScript.sml" "antisymmetric_fast_le"]
theorem antisymmetric_fastLe : holAntisymmetric (fun x y => fastLe x y = true) := by
  intro x y h
  change fastLe x y = true ∧ fastLe y x = true at h
  simp only [fastLe_thm] at h
  obtain ⟨hxy, hyx⟩ := h
  apply Or.elim hxy
  · intro heq
    exact heq
  · intro hlt
    apply Or.elim hyx
    · intro heq
      exact heq.symm
    · intro hlt2
      exact absurd (fastLt_trans x y x ⟨hlt, hlt2⟩) (fastLt_nonrefl x)

/-- Original `total_fast_le`. -/
@[hol "cakeml/basis/pure/mlstringScript.sml" "total_fast_le"]
theorem total_fastLe : holTotal (fun x y => fastLe x y = true) := by
  intro x y
  change fastLe x y = true ∨ fastLe y x = true
  by_cases hlen : strlen x = strlen y
  · rw [fastLe, fastLe, if_pos hlen, if_pos hlen.symm]
    exact total_mlstringLe x y
  · rw [fastLe, fastLe, if_neg hlen, if_neg (Ne.symm hlen)]
    simp only [decide_eq_true_eq]
    by_cases hle : strlen x ≤ strlen y
    · exact Or.inl hle
    · exact Or.inr (by omega)

/-- Original `transitive_fast_lt`. -/
@[hol "cakeml/basis/pure/mlstringScript.sml" "transitive_fast_lt"]
theorem transitive_fastLt : holTransitive (fun x y => fastLt x y = true) := by
  intro x y z h
  change fastLt x y = true ∧ fastLt y z = true at h
  exact fastLt_trans x y z h

/-- Original `irreflexive_fast_lt`. -/
@[hol "cakeml/basis/pure/mlstringScript.sml" "irreflexive_fast_lt"]
theorem irreflexive_fastLt : holIrreflexive (fun x y => fastLt x y = true) := by
  intro x h
  change fastLt x x = true at h
  exact fastLt_nonrefl x h

/-- Original `trichotomous_fast_lt`. -/
@[hol "cakeml/basis/pure/mlstringScript.sml" "trichotomous_fast_lt"]
theorem trichotomous_fastLt : holTrichotomous (fun x y => fastLt x y = true) := by
  intro a b
  change fastLt a b = true ∨ fastLt b a = true ∨ a = b
  by_cases hlen : strlen a = strlen b
  · rw [fastLt, fastLt, if_pos hlen, if_pos hlen.symm]
    rcases trichotomous_mlstringLt a b with h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
  · simp only [fastLt, hlen, Ne.symm hlen, if_false, decide_eq_true_eq]
    by_cases hlt : strlen a < strlen b
    · exact Or.inl hlt
    · exact Or.inr (Or.inl (by omega))

/-- Original `StrongLinearOrder_fast_lt`. -/
@[hol "cakeml/basis/pure/mlstringScript.sml" "StrongLinearOrder_fast_lt"]
theorem strongLinearOrder_fastLt :
    holStrongLinearOrder (fun x y => fastLt x y = true) :=
  ⟨⟨irreflexive_fastLt, transitive_fastLt⟩, trichotomous_fastLt⟩

end Flapjack.Basis.Pure.MlString.Order
