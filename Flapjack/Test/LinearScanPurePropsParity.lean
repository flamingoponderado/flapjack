import Flapjack.Compiler.Backend.LinearScan
import Flapjack.Misc.Sptree.ToAList
namespace Flapjack.Test.LinearScanPurePropsParity
open RegAlloc LinearScan
-- Replay of the eighteen original linear_scan_pure_props_probe rows for the
-- proposition-valued linear_scan definitions (HOL `K 0` is `fun _ => 0`).
-- The check_intervals rows hold without any fact about `THE NONE` (here the
-- opaque `holTheNone`), exactly as in HOL. Finite observations only; no
-- allocator soundness or production routing is claimed.
example : checkNumberProperty (fun n live => n = -1 ∧ live = .ln) (.writes [1]) 0
    (sptInsert 1 () .ln) := by
  simp only [checkNumberProperty]; decide +kernel
example : ¬ checkNumberProperty (fun n _ => -1 ≤ n)
    (.seq (.reads [1]) (.branch (.writes [2]) (.writes [3]))) 0 .ln := by
  simp only [checkNumberProperty, sizeOfLiveTree]; decide +kernel
example : checkNumberProperty (fun n live => ¬ (n = -2 ∧ sptLookup 2 live = some ()))
    (.branch (.writes [1]) (.reads [2])) 0 .ln := by
  simp only [checkNumberProperty, sizeOfLiveTree]; decide +kernel
example : ¬ checkNumberPropertyStrong (fun n live => ¬ (n = -2 ∧ sptLookup 2 live = some ()))
    (.branch (.writes [1]) (.reads [2])) 0 .ln := by
  simp only [checkNumberPropertyStrong, sizeOfLiveTree, getLiveBackward]; decide +kernel
example : ¬ checkNumberPropertyStrong (fun n live => sptLookup 1 live = none ∨ n = -1)
    (.seq (.reads [2]) (.reads [1])) 0 .ln := by
  simp only [checkNumberPropertyStrong, sizeOfLiveTree, getLiveBackward]; decide +kernel
example : checkStartliveProp (.writes [1]) 5 (sptInsert 1 3 .ln) (sptInsert 1 7 .ln) 0 := by
  intro r hr
  simp only [List.mem_singleton] at hr
  subst hr
  exact ⟨by decide +kernel, 7, by decide +kernel, by decide⟩
example : ¬ checkStartliveProp (.writes [1]) 5 .ln (sptInsert 1 7 .ln) 6 := by
  intro h
  have := (h 1 (by simp)).1
  simp [sptLookup] at this
example : ¬ checkStartliveProp (.writes [1]) 5 .ln (sptInsert 2 7 .ln) 0 := by
  intro h
  obtain ⟨v, hv, -⟩ := (h 1 (by simp)).2
  have hn : sptLookup 1 (sptInsert 2 (7 : Int) .ln) = none := by decide +kernel
  rw [hn] at hv
  cases hv
example : checkStartliveProp (.branch (.writes [1]) (.reads [])) 0 .ln (sptInsert 1 0 .ln) (-1) := by
  refine ⟨?_, trivial⟩
  intro r hr
  simp only [List.mem_singleton] at hr
  subst hr
  exact ⟨by simp [sptLookup, sizeOfLiveTree], 0, by decide +kernel, by simp [sizeOfLiveTree]⟩
example : liveTreeRegisters (.seq (.reads [1]) (.branch (.writes [2]) (.reads []))) 2 := by
  simp [liveTreeRegisters]
example : ¬ liveTreeRegisters (.seq (.reads [1]) (.branch (.writes [2]) (.reads []))) 3 := by
  simp [liveTreeRegisters]
example : intervalIntersect (-3, -1) (-1, 4) := by simp only [intervalIntersect]; decide
example : ¬ intervalIntersect (-3, -2) (-1, 4) := by simp only [intervalIntersect]; decide
example : pointInsideInterval (-3, -1) (-1) := by simp only [pointInsideInterval]; decide
example : ¬ pointInsideInterval (-3, -1) 0 := by simp only [pointInsideInterval]; decide
example : holThe (some (3 : Int)) = 3 := rfl
example : checkIntervals (fun _ => 0) (sptInsert 1 0 (sptInsert 2 5 .ln)) (sptInsert 1 1 .ln) := by
  have b1 : sptLookup 1 (sptInsert 1 (0 : Int) (sptInsert 2 5 .ln)) = some 0 := by decide +kernel
  have b2 : sptLookup 2 (sptInsert 1 (0 : Int) (sptInsert 2 5 .ln)) = some 5 := by decide +kernel
  have e1 : sptLookup 1 (sptInsert 1 (1 : Int) .ln) = some 1 := by decide +kernel
  have e2 : sptLookup 2 (sptInsert 1 (1 : Int) .ln) = none := by decide +kernel
  intro r1 r2 ⟨d1, d2, hi, _⟩
  rw [sptDomainInsert, sptDomainInsert] at d1 d2
  have ln : ∀ r, ¬ sptDomain (Spt.ln : Spt Int) r := by intro r; simp [sptDomain, sptLookup]
  rcases d1 with rfl | rfl | h1
  · rcases d2 with rfl | rfl | h2
    · rfl
    · rw [b1, b2, e1, e2] at hi; simp only [holThe, intervalIntersect] at hi; omega
    · exact absurd h2 (ln _)
  · rcases d2 with rfl | rfl | h2
    · rw [b1, b2, e1, e2] at hi; simp only [holThe, intervalIntersect] at hi; omega
    · rfl
    · exact absurd h2 (ln _)
  · exact absurd h1 (ln _)
example : ¬ checkIntervals (fun _ => 0) (sptInsert 1 0 (sptInsert 2 0 .ln))
    (sptInsert 1 5 (sptInsert 2 5 .ln)) := by
  intro h
  have b1 : sptLookup 1 (sptInsert 1 (0 : Int) (sptInsert 2 0 .ln)) = some 0 := by decide +kernel
  have b2 : sptLookup 2 (sptInsert 1 (0 : Int) (sptInsert 2 0 .ln)) = some 0 := by decide +kernel
  have e1 : sptLookup 1 (sptInsert 1 (5 : Int) (sptInsert 2 5 .ln)) = some 5 := by decide +kernel
  have e2 : sptLookup 2 (sptInsert 1 (5 : Int) (sptInsert 2 5 .ln)) = some 5 := by decide +kernel
  have := h 1 2 ⟨by simp [sptDomain, b1], by simp [sptDomain, b2],
    by rw [b1, b2, e1, e2]; simp only [holThe, intervalIntersect]; decide, rfl⟩
  exact absurd this (by decide +kernel)
end Flapjack.Test.LinearScanPurePropsParity
