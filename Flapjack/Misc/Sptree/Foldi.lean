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
