import Flapjack.HolRef
import Flapjack.Misc.Sptree

namespace Flapjack

/-- Exact HOL sptree `foldi` (`sptreeScript.sml:737-748`) with HOL's generic
accumulator type. `sptFoldi` is its instance at association-list
accumulators (`sptFoldi_eq_sptFoldiGen`). -/
@[hol "hol4/src/finite_maps/sptreeScript.sml" "foldi_def"]
def sptFoldiGen {α β : Type} (f : Nat → α → β → β) (i : Nat) (acc : β) : Spt α → β
  | .ln => acc
  | .ls a => f i a acc
  | .bn t1 t2 =>
      let inc := lrNext i
      sptFoldiGen f (i + inc) (sptFoldiGen f (i + 2 * inc) acc t1) t2
  | .bs t1 a t2 =>
      let inc := lrNext i
      sptFoldiGen f (i + inc) (f i a (sptFoldiGen f (i + 2 * inc) acc t1)) t2

/-- The association-list `sptFoldi` is the generic `foldi` at that accumulator. -/
theorem sptFoldi_eq_sptFoldiGen {α : Type} (f : Nat → α → List (Nat × α) → List (Nat × α)) :
    ∀ (t : Spt α) (i : Nat) (acc : List (Nat × α)), sptFoldi f i acc t = sptFoldiGen f i acc t := by
  intro t
  induction t with
  | ln => intro i acc; rfl
  | ls a => intro i acc; rfl
  | bn t1 t2 ih1 ih2 => intro i acc; simp only [sptFoldi, sptFoldiGen, ih1, ih2]
  | bs t1 a t2 ih1 ih2 => intro i acc; simp only [sptFoldi, sptFoldiGen, ih1, ih2]

end Flapjack

namespace Flapjack

private theorem sptFoldiGenConsAppend {α : Type} :
    ∀ (t : Spt α) (i : Nat) (init : List (Nat × α)),
      sptFoldiGen (fun k v l => (k, v) :: l) i init t =
        sptFoldiGen (fun k v l => (k, v) :: l) i [] t ++ init := by
  intro t
  induction t with
  | ln => intro i init; rfl
  | ls a => intro i init; rfl
  | bn t1 t2 ih1 ih2 =>
      intro i init
      simp only [sptFoldiGen]
      rw [ih1 _ init, ih2 _ (sptFoldiGen _ _ [] t1 ++ init), ih2 _ (sptFoldiGen _ _ [] t1)]
      simp
  | bs t1 a t2 ih1 ih2 =>
      intro i init
      simp only [sptFoldiGen]
      rw [ih1 _ init, ih2 _ ((i, a) :: (sptFoldiGen _ _ [] t1 ++ init)),
        ih2 _ ((i, a) :: sptFoldiGen _ _ [] t1)]
      simp

private theorem sptFoldiGenFoldr {α β : Type} (f : Nat → α → β → β) :
    ∀ (t : Spt α) (i : Nat) (a : β),
      sptFoldiGen f i a t =
        (sptFoldiGen (fun k v l => (k, v) :: l) i [] t).foldr (fun p acc => f p.1 p.2 acc) a := by
  intro t
  induction t with
  | ln => intro i a; rfl
  | ls x => intro i a; rfl
  | bn t1 t2 ih1 ih2 =>
      intro i a
      simp only [sptFoldiGen]
      rw [ih2, ih1, sptFoldiGenConsAppend t2 _
        (sptFoldiGen (fun k v l => (k, v) :: l) (i + 2 * lrNext i) [] t1), List.foldr_append]
  | bs t1 x t2 ih1 ih2 =>
      intro i a
      simp only [sptFoldiGen]
      rw [ih2, ih1, sptFoldiGenConsAppend t2 _
        ((i, x) :: sptFoldiGen (fun k v l => (k, v) :: l) (i + 2 * lrNext i) [] t1),
        List.foldr_append]
      rfl

/-- Exact HOL `foldi_FOLDR_toAList` (`sptreeScript.sml:1100-1104`); `UNCURRY f`
applied to a pair `p` is `f p.1 p.2`. -/
@[hol "hol4/src/finite_maps/sptreeScript.sml" "foldi_FOLDR_toAList"]
theorem sptFoldiGenFoldrToAList {α β : Type} :
    ∀ (f : Nat → α → β → β) (a : β) (t : Spt α),
      sptFoldiGen f 0 a t = (sptToAList t).foldr (fun p acc => f p.1 p.2 acc) a := by
  intro f a t
  rw [sptFoldiGenFoldr f t 0 a, sptToAList, sptFoldi_eq_sptFoldiGen]

end Flapjack
