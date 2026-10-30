import Flapjack.Compiler.Backend.LinearScan.ProductionIntervals
import Flapjack.Compiler.Backend.LinearScan.Sorting

/-!
Array-backed linear-scan sorting and exchange operations. These are
Flapjack-specific executable candidates, proved to simulate the source-shaped
operations; the production compiler has not yet been routed through them.
-/
namespace Flapjack.LinearScan.Production

open Flapjack.RegAlloc Flapjack.Translator.Monadic.MonadBase

def swapRegs (i1 i2 : Nat) : FastM Unit :=
  bind (sortedRegsSub i1) fun r1 =>
    bind (sortedRegsSub i2) fun r2 =>
      ignoreBind (updateSortedRegs i1 r2) (updateSortedRegs i2 r1)

theorem swapRegs_correct (i1 i2 : Nat) :
    Simulates (swapRegs i1 i2) (LinearScan.swapRegs i1 i2) := by
  simp only [swapRegs, LinearScan.swapRegs]
  apply simulates_bind _ _ _ _ (sortedRegsSub_correct i1)
  intro r1
  apply simulates_bind _ _ _ _ (sortedRegsSub_correct i2)
  intro r2
  exact simulates_ignoreBind _ _ _ _ (updateSortedRegs_correct i1 r2)
    (updateSortedRegs_correct i2 r1)

def partitionRegs (l rpiv : Nat) (begrpiv : Int) (r : Nat) : FastM Nat :=
  if h : r ≤ l then ret l
  else
    bind (sortedRegsSub l) fun reg =>
      bind (intBegSub reg) fun begreg =>
        if begreg < begrpiv ∨ (begreg = begrpiv ∧ reg ≤ rpiv) then
          partitionRegs (l + 1) rpiv begrpiv r
        else ignoreBind (swapRegs l (r - 1)) (partitionRegs l rpiv begrpiv (r - 1))
termination_by r - l
decreasing_by all_goals omega

theorem partitionRegs_correct (l rpiv : Nat) (begrpiv : Int) (r : Nat) :
    Simulates (partitionRegs l rpiv begrpiv r) (LinearScan.partitionRegs l rpiv begrpiv r) := by
  rw [partitionRegs, LinearScan.partitionRegs]
  by_cases h : r ≤ l
  · simp only [dif_pos h]
    exact simulates_ret l
  · simp only [dif_neg h]
    apply simulates_bind _ _ _ _ (sortedRegsSub_correct l)
    intro reg
    apply simulates_bind _ _ _ _ (intBegSub_correct reg)
    intro begreg
    by_cases hc : begreg < begrpiv ∨ (begreg = begrpiv ∧ reg ≤ rpiv)
    · simp only [if_pos hc]
      exact partitionRegs_correct (l + 1) rpiv begrpiv r
    · simp only [if_neg hc]
      exact simulates_ignoreBind _ _ _ _ (swapRegs_correct l (r - 1))
        (partitionRegs_correct l rpiv begrpiv (r - 1))
termination_by r - l
decreasing_by all_goals omega

def sortRegs (l r : Nat) : FastM Unit :=
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

theorem sortRegs_correct (l r : Nat) :
    Simulates (sortRegs l r) (LinearScan.sortRegs l r) := by
  rw [sortRegs, LinearScan.sortRegs]
  by_cases h : r ≤ l + 1
  · simp only [dif_pos h]
    exact simulates_ret ()
  · simp only [dif_neg h]
    apply simulates_bind _ _ _ _ (sortedRegsSub_correct l)
    intro rpiv
    apply simulates_bind _ _ _ _ (intBegSub_correct rpiv)
    intro begrpiv
    apply simulates_bind _ _ _ _ (partitionRegs_correct (l + 1) rpiv begrpiv r)
    intro m
    apply simulates_ignoreBind _ _ _ _ (swapRegs_correct l (m - 1))
    by_cases hm : m ≤ l ∨ r < m
    · simp only [dif_pos hm]
      exact simulates_ret ()
    · simp only [dif_neg hm]
      exact simulates_ignoreBind _ _ _ _ (sortRegs_correct l (m - 1)) (sortRegs_correct m r)
termination_by r - l
decreasing_by all_goals omega

def swapMoves (i1 i2 : Nat) : FastM Unit :=
  bind (sortedMovesSub i1) fun r1 =>
    bind (sortedMovesSub i2) fun r2 =>
      ignoreBind (updateSortedMoves i1 r2) (updateSortedMoves i2 r1)

theorem swapMoves_correct (i1 i2 : Nat) :
    Simulates (swapMoves i1 i2) (LinearScan.swapMoves i1 i2) := by
  simp only [swapMoves, LinearScan.swapMoves]
  apply simulates_bind _ _ _ _ (sortedMovesSub_correct i1)
  intro r1
  apply simulates_bind _ _ _ _ (sortedMovesSub_correct i2)
  intro r2
  exact simulates_ignoreBind _ _ _ _ (updateSortedMoves_correct i1 r2)
    (updateSortedMoves_correct i2 r1)

def partitionMoves (l ppiv r : Nat) : FastM Nat :=
  if h : r ≤ l then ret l
  else
    bind (sortedMovesSub l) fun move =>
      if move.1 < ppiv then partitionMoves (l + 1) ppiv r
      else ignoreBind (swapMoves l (r - 1)) (partitionMoves l ppiv (r - 1))
termination_by r - l
decreasing_by all_goals omega

theorem partitionMoves_correct (l ppiv r : Nat) :
    Simulates (partitionMoves l ppiv r) (LinearScan.partitionMoves l ppiv r) := by
  rw [partitionMoves, LinearScan.partitionMoves]
  by_cases h : r ≤ l
  · simp only [dif_pos h]
    exact simulates_ret l
  · simp only [dif_neg h]
    apply simulates_bind _ _ _ _ (sortedMovesSub_correct l)
    intro move
    by_cases hc : move.1 < ppiv
    · simp only [if_pos hc]
      exact partitionMoves_correct (l + 1) ppiv r
    · simp only [if_neg hc]
      exact simulates_ignoreBind _ _ _ _ (swapMoves_correct l (r - 1))
        (partitionMoves_correct l ppiv (r - 1))
termination_by r - l
decreasing_by all_goals omega

def sortMoves (l r : Nat) : FastM Unit :=
  if h : r ≤ l + 1 then ret ()
  else
    bind (sortedMovesSub l) fun piv =>
      bind (partitionMoves (l + 1) piv.1 r) fun m =>
        ignoreBind (swapMoves l (m - 1))
          (if h2 : m ≤ l ∨ r < m then ret ()
          else ignoreBind (sortMoves l (m - 1)) (sortMoves m r))
termination_by r - l
decreasing_by all_goals omega

theorem sortMoves_correct (l r : Nat) :
    Simulates (sortMoves l r) (LinearScan.sortMoves l r) := by
  rw [sortMoves, LinearScan.sortMoves]
  by_cases h : r ≤ l + 1
  · simp only [dif_pos h]
    exact simulates_ret ()
  · simp only [dif_neg h]
    apply simulates_bind _ _ _ _ (sortedMovesSub_correct l)
    intro piv
    apply simulates_bind _ _ _ _ (partitionMoves_correct (l + 1) piv.1 r)
    intro m
    apply simulates_ignoreBind _ _ _ _ (swapMoves_correct l (m - 1))
    by_cases hm : m ≤ l ∨ r < m
    · simp only [dif_pos hm]
      exact simulates_ret ()
    · simp only [dif_neg hm]
      exact simulates_ignoreBind _ _ _ _ (sortMoves_correct l (m - 1)) (sortMoves_correct m r)
termination_by r - l
decreasing_by all_goals omega

def listToSortedRegs : List Nat → Nat → FastM Unit
  | [], _ => ret ()
  | r :: rs, n => ignoreBind (updateSortedRegs n r) (listToSortedRegs rs (n + 1))

theorem listToSortedRegs_correct (rs : List Nat) (n : Nat) :
    Simulates (listToSortedRegs rs n) (LinearScan.listToSortedRegs rs n) := by
  induction rs generalizing n with
  | nil => exact simulates_ret ()
  | cons r rs ih =>
    simp only [listToSortedRegs, LinearScan.listToSortedRegs]
    exact simulates_ignoreBind _ _ _ _ (updateSortedRegs_correct n r) (ih (n + 1))

def sortedRegsToList (n last : Nat) : FastM (List Nat) :=
  if h : last ≤ n then ret []
  else
    bind (sortedRegsSub n) fun r =>
      bind (sortedRegsToList (n + 1) last) fun l => ret (r :: l)
termination_by last - n
decreasing_by omega

theorem sortedRegsToList_correct (n last : Nat) :
    Simulates (sortedRegsToList n last) (LinearScan.sortedRegsToList n last) := by
  rw [sortedRegsToList, LinearScan.sortedRegsToList]
  by_cases h : last ≤ n
  · simp only [dif_pos h]
    exact simulates_ret []
  · simp only [dif_neg h]
    apply simulates_bind _ _ _ _ (sortedRegsSub_correct n)
    intro r
    apply simulates_bind _ _ _ _ (sortedRegsToList_correct (n + 1) last)
    intro l
    exact simulates_ret (r :: l)
termination_by last - n
decreasing_by omega

def listToSortedMoves : List (Nat × (Nat × Nat)) → Nat → FastM Unit
  | [], _ => ret ()
  | r :: rs, n => ignoreBind (updateSortedMoves n r) (listToSortedMoves rs (n + 1))

theorem listToSortedMoves_correct (rs : List (Nat × (Nat × Nat))) (n : Nat) :
    Simulates (listToSortedMoves rs n) (LinearScan.listToSortedMoves rs n) := by
  induction rs generalizing n with
  | nil => exact simulates_ret ()
  | cons r rs ih =>
    simp only [listToSortedMoves, LinearScan.listToSortedMoves]
    exact simulates_ignoreBind _ _ _ _ (updateSortedMoves_correct n r) (ih (n + 1))

def sortedMovesToList (n len : Nat) : FastM (List (Nat × (Nat × Nat))) :=
  if h : len ≤ n then ret []
  else
    bind (sortedMovesSub n) fun r =>
      bind (sortedMovesToList (n + 1) len) fun l => ret (r :: l)
termination_by len - n
decreasing_by omega

theorem sortedMovesToList_correct (n len : Nat) :
    Simulates (sortedMovesToList n len) (LinearScan.sortedMovesToList n len) := by
  rw [sortedMovesToList, LinearScan.sortedMovesToList]
  by_cases h : len ≤ n
  · simp only [dif_pos h]
    exact simulates_ret []
  · simp only [dif_neg h]
    apply simulates_bind _ _ _ _ (sortedMovesSub_correct n)
    intro r
    apply simulates_bind _ _ _ _ (sortedMovesToList_correct (n + 1) len)
    intro l
    exact simulates_ret (r :: l)
termination_by len - n
decreasing_by omega

def findRegExchange : List Nat → Spt Nat → Spt Nat → FastM (Spt Nat × Spt Nat)
  | [], exch, invexch => ret (exch, invexch)
  | r :: rs, exch, invexch =>
      bind (colorsSub r) fun col1 =>
        let fcol1 := r / 2
        let col2 := (sptLookup fcol1 invexch).elim fcol1 (fun x => x)
        let fcol2 := (sptLookup col1 exch).elim col1 (fun x => x)
        findRegExchange rs (sptInsert col1 fcol1 (sptInsert col2 fcol2 exch))
          (sptInsert fcol1 col1 (sptInsert fcol2 col2 invexch))

theorem findRegExchange_correct (rs : List Nat) (exch invexch : Spt Nat) :
    Simulates (findRegExchange rs exch invexch) (LinearScan.findRegExchange rs exch invexch) := by
  induction rs generalizing exch invexch with
  | nil => exact simulates_ret _
  | cons r rs ih =>
    simp only [findRegExchange, LinearScan.findRegExchange]
    apply simulates_bind _ _ _ _ (colorsSub_correct r)
    intro col
    exact ih _ _

def mapColors (f : Nat → Nat) : Nat → FastM Unit
  | 0 => ret ()
  | n + 1 =>
      bind (colorsSub n) fun col =>
        ignoreBind (updateColors n (f col)) (mapColors f n)

theorem mapColors_correct (f : Nat → Nat) (n : Nat) :
    Simulates (mapColors f n) (LinearScan.mapColors f n) := by
  induction n with
  | zero => exact simulates_ret ()
  | succ n ih =>
    simp only [mapColors, LinearScan.mapColors]
    apply simulates_bind _ _ _ _ (colorsSub_correct n)
    intro col
    exact simulates_ignoreBind _ _ _ _ (updateColors_correct n (f col)) ih

def applyRegExchange (phyregs : List Nat) : FastM Unit :=
  bind (findRegExchange phyregs .ln .ln) fun (exch, _invexch) =>
    bind colorsLength fun col_size =>
      mapColors (fun c => (sptLookup c exch).elim c (fun x => x)) col_size

theorem applyRegExchange_correct (phyregs : List Nat) :
    Simulates (applyRegExchange phyregs) (LinearScan.applyRegExchange phyregs) := by
  simp only [applyRegExchange, LinearScan.applyRegExchange]
  apply simulates_bind _ _ _ _ (findRegExchange_correct phyregs .ln .ln)
  rintro ⟨exch, invexch⟩
  apply simulates_bind _ _ _ _ colorsLength_correct
  intro size
  exact mapColors_correct _ size

def edgesToAdjlist : List (Nat × Nat) → Spt (List Nat) → FastM (Spt (List Nat))
  | [], acc => ret acc
  | (a, b) :: abs, acc =>
      if a = b then edgesToAdjlist abs acc
      else
        bind (intBegSub a) fun bega =>
          bind (intBegSub b) fun begb =>
            if bega < begb ∨ (bega = begb ∧ a ≤ b) then
              edgesToAdjlist abs (sptInsert b (a :: miscThe [] (sptLookup b acc)) acc)
            else edgesToAdjlist abs (sptInsert a (b :: miscThe [] (sptLookup a acc)) acc)

theorem edgesToAdjlist_correct (edges : List (Nat × Nat)) (acc : Spt (List Nat)) :
    Simulates (edgesToAdjlist edges acc) (LinearScan.edgesToAdjlist edges acc) := by
  induction edges generalizing acc with
  | nil => exact simulates_ret _
  | cons edge edges ih =>
    rcases edge with ⟨a, b⟩
    simp only [edgesToAdjlist, LinearScan.edgesToAdjlist]
    by_cases h : a = b
    · simp only [if_pos h]
      exact ih acc
    · simp only [if_neg h]
      apply simulates_bind _ _ _ _ (intBegSub_correct a)
      intro bega
      apply simulates_bind _ _ _ _ (intBegSub_correct b)
      intro begb
      by_cases hc : bega < begb ∨ (bega = begb ∧ a ≤ b)
      · simp only [if_pos hc]
        exact ih _
      · simp only [if_neg hc]
        exact ih _

theorem stExFoldl_correct {value elem : Type}
    (fast : value → elem → FastM value) (source : value → elem → LsM value)
    (h : ∀ value elem, Simulates (fast value elem) (source value elem))
    (initial : value) (xs : List elem) :
    Simulates (stExFoldl fast initial xs) (stExFoldl source initial xs) := by
  induction xs generalizing initial with
  | nil => exact simulates_ret initial
  | cons x xs ih =>
    simp only [stExFoldl]
    apply simulates_bind _ _ _ _ (h initial x)
    intro next
    exact ih next

theorem stExFilterGood_correct {elem : Type}
    (fast : elem → FastM Bool) (source : elem → LsM Bool)
    (h : ∀ x, Simulates (fast x) (source x)) (xs : List elem) :
    Simulates (stExFilterGood fast xs) (stExFilterGood source xs) := by
  induction xs with
  | nil => exact simulates_ret []
  | cons x xs ih =>
    simp only [stExFilterGood]
    apply simulates_bind _ _ _ _ (h x)
    intro keep
    cases keep with
    | false => exact ih
    | true =>
      apply simulates_bind _ _ _ _ ih
      intro rest
      exact simulates_ret (x :: rest)

end Flapjack.LinearScan.Production
