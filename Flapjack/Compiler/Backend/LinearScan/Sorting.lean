import Flapjack.HolRef
import Flapjack.Compiler.Backend.LinearScan.HiddenState
import Flapjack.Basis.Pure.MlList
import Flapjack.Misc.MiscThe

/-!
# linear_scan register exchange, adjacency lists and in-array sorting

Ports of `linear_scanScript.sml:707-956`. HOL's well-founded definitions
(`partition_regs`, `sort_regs`, `sorted_regs_to_list` and their move
counterparts) use the same measures as the HOL `Termination` proofs; their
HOL `if` tests are Lean dependent `if`s only so that the termination proof can
use the tested fact. `option_CASE x d (\x.x)` is `Option.elim x d id`-style
`match`. Proof-side ports; the executed allocator is unchanged.
-/

namespace Flapjack.LinearScan

open Flapjack.RegAlloc Flapjack.Translator.Monadic.MonadBase

/-- HOL `find_reg_exchange` (`linear_scanScript.sml:707-720`). -/
@[hol "cakeml/compiler/backend/reg_alloc/linear_scanScript.sml" "find_reg_exchange_def"]
def findRegExchange : List Nat → Spt Nat → Spt Nat → LsM (Spt Nat × Spt Nat)
  | [], exch, invexch => ret (exch, invexch)
  | r :: rs, exch, invexch =>
      bind (colorsSub r) fun col1 =>
        let fcol1 := r / 2
        let col2 := (sptLookup fcol1 invexch).elim fcol1 (fun x => x)
        let fcol2 := (sptLookup col1 exch).elim col1 (fun x => x)
        findRegExchange rs (sptInsert col1 fcol1 (sptInsert col2 fcol2 exch))
          (sptInsert fcol1 col1 (sptInsert fcol2 col2 invexch))

/-- HOL `MAP_colors` (`linear_scanScript.sml:722-733`). -/
@[hol "cakeml/compiler/backend/reg_alloc/linear_scanScript.sml" "MAP_colors_def"]
def mapColors (f : Nat → Nat) : Nat → LsM Unit
  | 0 => ret ()
  | n + 1 =>
      bind (colorsSub n) fun col =>
        ignoreBind (updateColors n (f col)) (mapColors f n)

/-- HOL `apply_reg_exchange` (`linear_scanScript.sml:735-742`). -/
@[hol "cakeml/compiler/backend/reg_alloc/linear_scanScript.sml" "apply_reg_exchange_def"]
def applyRegExchange (phyregs : List Nat) : LsM Unit :=
  bind (findRegExchange phyregs .ln .ln) fun (exch, _invexch) =>
    bind colorsLength fun col_size =>
      mapColors (fun c => (sptLookup c exch).elim c (fun x => x)) col_size

/-- HOL `st_ex_FOLDL` (`linear_scanScript.sml:744-754`). -/
@[hol "cakeml/compiler/backend/reg_alloc/linear_scanScript.sml" "st_ex_FOLDL_def"]
def stExFoldl {state value elem exception : Type}
    (f : value → elem → M state value exception) : value → List elem → M state value exception
  | e, [] => ret e
  | e, x :: xs => bind (f e x) fun e' => stExFoldl f e' xs

/-- HOL `st_ex_FILTER_good` (`linear_scanScript.sml:757-773`): an
order-preserving monadic filter. -/
@[hol "cakeml/compiler/backend/reg_alloc/linear_scanScript.sml" "st_ex_FILTER_good_def"]
def stExFilterGood {state elem exception : Type}
    (P : elem → M state Bool exception) : List elem → M state (List elem) exception
  | [] => ret []
  | x :: xs =>
      bind (P x) fun Px =>
        if Px then bind (stExFilterGood P xs) fun filter_xs => ret (x :: filter_xs)
        else stExFilterGood P xs

/-- HOL `edges_to_adjlist` (`linear_scanScript.sml:775-792`). -/
@[hol "cakeml/compiler/backend/reg_alloc/linear_scanScript.sml" "edges_to_adjlist_def"]
def edgesToAdjlist : List (Nat × Nat) → Spt (List Nat) → LsM (Spt (List Nat))
  | [], acc => ret acc
  | (a, b) :: abs, acc =>
      if a = b then edgesToAdjlist abs acc
      else
        bind (intBegSub a) fun bega =>
          bind (intBegSub b) fun begb =>
            if bega < begb ∨ (bega = begb ∧ a ≤ b) then
              edgesToAdjlist abs (sptInsert b (a :: miscThe [] (sptLookup b acc)) acc)
            else edgesToAdjlist abs (sptInsert a (b :: miscThe [] (sptLookup a acc)) acc)

/-- HOL `sort_moves_rev` (`linear_scanScript.sml:794-797`). -/
@[hol "cakeml/compiler/backend/reg_alloc/linear_scanScript.sml" "sort_moves_rev_def"]
def sortMovesRev {α : Type} (ls : List (Nat × α)) : List (Nat × α) :=
  Basis.Pure.MlList.sort (fun (p, _) (p', _) => decide (p < p')) ls

/-- HOL `swap_regs` (`linear_scanScript.sml:799-807`). -/
@[hol "cakeml/compiler/backend/reg_alloc/linear_scanScript.sml" "swap_regs_def"]
def swapRegs (i1 i2 : Nat) : LsM Unit :=
  bind (sortedRegsSub i1) fun r1 =>
    bind (sortedRegsSub i2) fun r2 =>
      ignoreBind (updateSortedRegs i1 r2) (updateSortedRegs i2 r1)

/-- HOL `partition_regs` (`linear_scanScript.sml:809-827`), measure `r - l`. -/
@[hol "cakeml/compiler/backend/reg_alloc/linear_scanScript.sml" "partition_regs_def"]
def partitionRegs (l rpiv : Nat) (begrpiv : Int) (r : Nat) : LsM Nat :=
  if h : r ≤ l then ret l
  else
    bind (sortedRegsSub l) fun reg =>
      bind (intBegSub reg) fun begreg =>
        if begreg < begrpiv ∨ (begreg = begrpiv ∧ reg ≤ rpiv) then
          partitionRegs (l + 1) rpiv begrpiv r
        else ignoreBind (swapRegs l (r - 1)) (partitionRegs l rpiv begrpiv (r - 1))
termination_by r - l
decreasing_by all_goals omega

/-- HOL `sort_regs` (`linear_scanScript.sml:829-850`), measure `r - l`; the
source's `m <= l \/ r < m` guard is kept. -/
@[hol "cakeml/compiler/backend/reg_alloc/linear_scanScript.sml" "sort_regs_def"]
def sortRegs (l r : Nat) : LsM Unit :=
  if h : r ≤ l + 1 then ret ()
  else
    bind (sortedRegsSub l) fun rpiv =>
      bind (intBegSub rpiv) fun begrpiv =>
        bind (partitionRegs (l + 1) rpiv begrpiv r) fun m =>
          ignoreBind (swapRegs l (m - 1))
            (if h2 : m ≤ l ∨ r < m then ret ()
            else ignoreBind (sortRegs l (m - 1)) (sortRegs m r))
termination_by r - l
decreasing_by all_goals omega

/-- HOL `list_to_sorted_regs` (`linear_scanScript.sml:852-863`). -/
@[hol "cakeml/compiler/backend/reg_alloc/linear_scanScript.sml" "list_to_sorted_regs_def"]
def listToSortedRegs : List Nat → Nat → LsM Unit
  | [], _ => ret ()
  | r :: rs, n => ignoreBind (updateSortedRegs n r) (listToSortedRegs rs (n + 1))

/-- HOL `sorted_regs_to_list` (`linear_scanScript.sml:865-877`), measure `last - n`. -/
@[hol "cakeml/compiler/backend/reg_alloc/linear_scanScript.sml" "sorted_regs_to_list_def"]
def sortedRegsToList (n last : Nat) : LsM (List Nat) :=
  if h : last ≤ n then ret []
  else
    bind (sortedRegsSub n) fun r =>
      bind (sortedRegsToList (n + 1) last) fun l => ret (r :: l)
termination_by last - n
decreasing_by omega

/-- HOL `swap_moves` (`linear_scanScript.sml:879-887`). -/
@[hol "cakeml/compiler/backend/reg_alloc/linear_scanScript.sml" "swap_moves_def"]
def swapMoves (i1 i2 : Nat) : LsM Unit :=
  bind (sortedMovesSub i1) fun r1 =>
    bind (sortedMovesSub i2) fun r2 =>
      ignoreBind (updateSortedMoves i1 r2) (updateSortedMoves i2 r1)

/-- HOL `partition_moves` (`linear_scanScript.sml:889-906`), measure `r - l`. -/
@[hol "cakeml/compiler/backend/reg_alloc/linear_scanScript.sml" "partition_moves_def"]
def partitionMoves (l ppiv r : Nat) : LsM Nat :=
  if h : r ≤ l then ret l
  else
    bind (sortedMovesSub l) fun move =>
      if move.1 < ppiv then partitionMoves (l + 1) ppiv r
      else ignoreBind (swapMoves l (r - 1)) (partitionMoves l ppiv (r - 1))
termination_by r - l
decreasing_by all_goals omega

/-- HOL `sort_moves` (`linear_scanScript.sml:908-928`), measure `r - l`. -/
@[hol "cakeml/compiler/backend/reg_alloc/linear_scanScript.sml" "sort_moves_def"]
def sortMoves (l r : Nat) : LsM Unit :=
  if h : r ≤ l + 1 then ret ()
  else
    bind (sortedMovesSub l) fun piv =>
      bind (partitionMoves (l + 1) piv.1 r) fun m =>
        ignoreBind (swapMoves l (m - 1))
          (if h2 : m ≤ l ∨ r < m then ret ()
          else ignoreBind (sortMoves l (m - 1)) (sortMoves m r))
termination_by r - l
decreasing_by all_goals omega

/-- HOL `list_to_sorted_moves` (`linear_scanScript.sml:931-942`). -/
@[hol "cakeml/compiler/backend/reg_alloc/linear_scanScript.sml" "list_to_sorted_moves_def"]
def listToSortedMoves : List (Nat × (Nat × Nat)) → Nat → LsM Unit
  | [], _ => ret ()
  | r :: rs, n => ignoreBind (updateSortedMoves n r) (listToSortedMoves rs (n + 1))

/-- HOL `sorted_moves_to_list` (`linear_scanScript.sml:944-956`), measure `len - n`. -/
@[hol "cakeml/compiler/backend/reg_alloc/linear_scanScript.sml" "sorted_moves_to_list_def"]
def sortedMovesToList (n len : Nat) : LsM (List (Nat × (Nat × Nat))) :=
  if h : len ≤ n then ret []
  else
    bind (sortedMovesSub n) fun r =>
      bind (sortedMovesToList (n + 1) len) fun l => ret (r :: l)
termination_by len - n
decreasing_by omega

end Flapjack.LinearScan
