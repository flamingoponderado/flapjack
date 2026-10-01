import Flapjack.Misc.Sptree.Mapi

namespace Flapjack.Test.SptMapiParity
open Flapjack

/-! Kernel replay of direct original HOL indexed-map observations. Exact trees
are compared, including malformed-tree normalization, asymmetric key order,
nonzero starting indices, and different input/output payload types. These
finite observations do not establish cross-prover equivalence. -/

-- mi_empty=T
example : sptMapi (fun k (x : Nat) => k + x) .ln = .ln := by decide +kernel
-- mi_leaf=T
example : sptMapi (fun k (x : Nat) => k + x) (.ls 7) = .ls 7 := by decide +kernel
-- mi_children=T
example : sptMapi (fun k (x : Nat) => (k,x)) (.bn (.ls 10) (.ls 20)) =
    .bn (.ls (2,10)) (.ls (1,20)) := by decide +kernel
-- mi_root=T
example : sptMapi (fun k (x : Nat) => (k,x)) (.bs (.ls 10) 30 (.ls 20)) =
    .bs (.ls (2,10)) (0,30) (.ls (1,20)) := by decide +kernel
-- mi_nested=T
example : sptMapi (fun k (x : Nat) => (k,x))
    (.bs (.bs (.ls 7) 8 (.ls 9)) 10 (.bn (.ls 11) (.ls 12))) =
    .bs (.bs (.ls (6,7)) (2,8) (.ls (4,9))) (0,10)
      (.bn (.ls (5,11)) (.ls (3,12))) := by decide +kernel
-- mi_raw_bn=T
example : sptMapi (fun k (x : Nat) => k + x) (.bn .ln .ln) = .ln := by decide +kernel
-- mi_raw_bs=T
example : sptMapi (fun k (x : Nat) => k + x) (.bs .ln 7 .ln) = .ls 7 := by decide +kernel
-- mi_raw_nested=T
example : sptMapi (fun k (x : Nat) => (k,x))
    (.bs (.bn .ln .ln) 7 (.bs .ln 8 .ln)) =
    .bs .ln (0,7) (.ls (1,8)) := by decide +kernel
-- mi_index3=T
example : sptMapi0 (fun k (x : Nat) => (k,x)) 3 (.bs (.ls 10) 30 (.ls 20)) =
    .bs (.ls (11,10)) (3,30) (.ls (7,20)) := by decide +kernel
-- mi_index6=T
example : sptMapi0 (fun k (x : Nat) => (k,x)) 6 (.bn (.ls 10) (.ls 20)) =
    .bn (.ls (14,10)) (.ls (10,20)) := by decide +kernel
-- mi_bool_nat=T
example : sptMapi (fun k (x : Bool) => if x then k + 100 else k)
    (.bs (.ls false) true (.ls true)) = .bs (.ls 2) 100 (.ls 101) := by decide +kernel
-- mi_nat_bool=T
example : sptMapi (fun k (x : Nat) => decide (k = x))
    (.bs (.ls 2) 0 (.ls 9)) = .bs (.ls true) true (.ls false) := by decide +kernel

end Flapjack.Test.SptMapiParity
