import Flapjack.Misc.Sptree

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

end Flapjack
