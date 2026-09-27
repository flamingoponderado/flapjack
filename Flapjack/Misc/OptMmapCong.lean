/-
Copyright (c) 2026 Flapjack contributors. All rights reserved.
Released under Apache 2.0 license as described in the file COPYING.
Authors: Flapjack contributors
-/
import Flapjack.HolRef

/-!
# Exact port of HOL `misc$OPT_MMAP_CONG`

This module ports the CakeML HOL standard-library congruence rule
`cakeml/misc/miscScript.sml:2481`

```
Theorem OPT_MMAP_CONG[defncong]:
   !l1 l2 f f'.
     (l1 = l2) /\
     (!x. MEM x l2 ==> (f x = f' x))
     ==> (OPT_MMAP f l1 = OPT_MMAP f' l2)
```

HOL's `OPT_MMAP f l` (a fold over `l` collecting the `SOME` results into an
option list) is rendered here by the core `List.mapM`.  The two hypotheses are
the list equality and the pointwise agreement of `f` and `f'` on members of the
(shared) list, exactly as in HOL.
-/

namespace Flapjack

@[hol "cakeml/misc/miscScript.sml" "OPT_MMAP_CONG"]
theorem optMmapCongHOL {α β : Type} (l1 l2 : List α) (f f' : α → Option β)
    (hlen : l1 = l2) (h : ∀ x, x ∈ l2 → f x = f' x) :
    l1.mapM f = l2.mapM f' := by
  subst hlen
  induction l1 with
  | nil => rfl
  | cons a t ih =>
      simp only [List.mapM_cons]
      rw [h a (by simp), ih (fun x hx => h x (by simp [hx]))]

/-- Exact port of HOL's `misc$IMP_OPT_MMAP_EQ`
(`cakeml/misc/miscScript.sml:2491`):

```
Theorem IMP_OPT_MMAP_EQ:
   !l1 l2. (MAP f1 l1 = MAP f2 l2) ==> (OPT_MMAP f1 l1 = OPT_MMAP f2 l2)
```

The HOL declaration quantifies only `l1`/`l2` and leaves `f1`/`f2` free, so
the stored theorem is schematic in `f1`/`f2` (implicitly universally
quantified whenever it is instantiated).  The Lean statement makes those two
quantifiers explicit; `MAP` is `List.map` and `OPT_MMAP` is `List.mapM`.
Used to relate the compiled-expression image list with the source evaluation
list in the `compile_exp_val_rel` `Op`/`Panop` cases. -/
@[hol "cakeml/misc/miscScript.sml" "IMP_OPT_MMAP_EQ"]
theorem impOptMmapEq {α β γ : Type} (f1 : α → Option γ) (f2 : β → Option γ)
    (l1 : List α) (l2 : List β) (h : l1.map f1 = l2.map f2) :
    l1.mapM f1 = l2.mapM f2 := by
  induction l1 generalizing l2 with
  | nil =>
      cases l2 with
      | nil => rfl
      | cons b bs => simp at h
  | cons a as ih =>
      cases l2 with
      | nil => simp at h
      | cons b bs =>
          simp only [List.map_cons, List.mapM_cons] at h ⊢
          injection h with hhead htail
          rw [hhead, ih bs htail]

end Flapjack
