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

end Flapjack
