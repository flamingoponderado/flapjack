import Flapjack.Misc.Sptree
import Flapjack.Misc.Sptree.Wf

namespace Flapjack

/-- Exact HOL `sptree$inter_eq` (`sptreeScript.sml:294-316`, pinned HOL submodule): keep
only keys present in both trees with equal values, with the `mk_BN`/`mk_BS` collapsing;
all four clauses and their inner `case` splits are literal. -/
@[hol "hol4/src/finite_maps/sptreeScript.sml" "inter_eq_def"]
def sptInterEq {α : Type} [DecidableEq α] : Spt α → Spt α → Spt α
  | .ln, _ => .ln
  | .ls a, t =>
      match t with
      | .ln => .ln
      | .ls b => if a = b then .ls a else .ln
      | .bn _ _ => .ln
      | .bs _ b _ => if a = b then .ls a else .ln
  | .bn t1 t2, t =>
      match t with
      | .ln => .ln
      | .ls _ => .ln
      | .bn t1' t2' => sptMkBN (sptInterEq t1 t1') (sptInterEq t2 t2')
      | .bs t1' _ t2' => sptMkBN (sptInterEq t1 t1') (sptInterEq t2 t2')
  | .bs t1 a t2, t =>
      match t with
      | .ln => .ln
      | .ls a' => if a' = a then .ls a else .ln
      | .bn t1' t2' => sptMkBN (sptInterEq t1 t1') (sptInterEq t2 t2')
      | .bs t1' a' t2' =>
          if a' = a then sptMkBS (sptInterEq t1 t1') a (sptInterEq t2 t2')
          else sptMkBN (sptInterEq t1 t1') (sptInterEq t2 t2')

/-- Exact HOL `lookup_inter_eq` (`sptreeScript.sml:383-394`, pinned HOL submodule). -/
@[hol "hol4/src/finite_maps/sptreeScript.sml" "lookup_inter_eq"]
theorem sptLookupInterEq {α : Type} [DecidableEq α] :
    ∀ (m1 m2 : Spt α) (k : Nat),
      sptLookup k (sptInterEq m1 m2) =
        match sptLookup k m1 with
        | none => none
        | some v => if sptLookup k m2 = some v then some v else none := by
  intro m1
  induction m1 with
  | ln => intro m2 k; simp [sptInterEq, sptLookup]
  | ls a =>
      intro m2 k
      cases m2 <;> simp only [sptInterEq] <;> by_cases hk : k = 0 <;>
        simp [sptLookup, hk] <;> split <;> simp_all [sptLookup, eq_comm]
  | bn l r ihl ihr =>
      intro m2 k
      cases m2 with
      | ln => by_cases hk : k = 0 <;> simp [sptInterEq, sptLookup, hk] <;> split <;> rfl
      | ls b => by_cases hk : k = 0 <;> simp [sptInterEq, sptLookup, hk] <;> split <;> rfl
      | bn l' r' =>
          simp only [sptInterEq]
          rw [sptLookupMkBN]
          by_cases hk : k = 0
          · simp [sptLookup, hk]
          · simp only [sptLookup, hk, if_false]
            split <;> first | exact ihl _ _ | exact ihr _ _
      | bs l' b r' =>
          simp only [sptInterEq]
          rw [sptLookupMkBN]
          by_cases hk : k = 0
          · simp [sptLookup, hk]
          · simp only [sptLookup, hk, if_false]
            split <;> first | exact ihl _ _ | exact ihr _ _
  | bs l a r ihl ihr =>
      intro m2 k
      cases m2 with
      | ln => by_cases hk : k = 0 <;> simp [sptInterEq, sptLookup, hk] <;> split <;> rfl
      | ls b =>
          by_cases hk : k = 0 <;> by_cases hab : b = a <;>
            simp [sptInterEq, sptLookup, hk, hab] <;> split <;> simp_all [eq_comm]
      | bn l' r' =>
          simp only [sptInterEq]
          rw [sptLookupMkBN]
          by_cases hk : k = 0
          · simp [sptLookup, hk]
          · simp only [sptLookup, hk, if_false]
            split <;> first | exact ihl _ _ | exact ihr _ _
      | bs l' b r' =>
          simp only [sptInterEq]
          by_cases hab : b = a
          · rw [if_pos hab, sptLookupMkBS]
            by_cases hk : k = 0
            · simp [sptLookup, hk, hab]
            · simp only [sptLookup, hk, if_false]
              split <;> first | exact ihl _ _ | exact ihr _ _
          · rw [if_neg hab, sptLookupMkBN]
            by_cases hk : k = 0
            · simp [sptLookup, hk, hab]
            · simp only [sptLookup, hk, if_false]
              split <;> first | exact ihl _ _ | exact ihr _ _

end Flapjack
