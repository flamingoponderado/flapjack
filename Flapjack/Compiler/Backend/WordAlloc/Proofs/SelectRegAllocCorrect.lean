import Flapjack.HolRef
import Flapjack.Compiler.Backend.WordAlloc.SelectRegAlloc
import Flapjack.Compiler.Backend.LinearScan.Proofs.TopLevelCorrect
import Flapjack.Compiler.Backend.RegAlloc.Proofs.DoRegAllocCorrect

/-!
# word_allocProof: correctness of the register-allocator dispatch

Port of `word_allocProofScript.sml:3371-3396`, `select_reg_alloc_correct`: whichever
allocator `select_reg_alloc` dispatches to (linear scan for `4 ≤ alg`, otherwise the
simple or iterated-register-coalescing graph allocator), it succeeds with a colouring that
passes the `check_clash_tree` oracle, respects the register conventions, is supported on
the clash tree and separates every forced pair. Renderings as in `reg_alloc_correct`.
-/

namespace Flapjack.WordAlloc

open Flapjack Flapjack.RegAlloc

/-- Exact HOL `select_reg_alloc_correct` (`word_allocProofScript.sml:3371-3396`). -/
@[hol "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "select_reg_alloc_correct"]
theorem selectRegAllocCorrect :
    ∀ (alg : Nat) (spillcosts : Option (Spt Nat)) (k : Nat)
      (heu_moves : List (Nat × (Nat × Nat))) (tree : ClashTree) (forced : List (Nat × Nat))
      (fs : NumSet),
      (∀ m ∈ forced, inClashTree tree m.1 ∧ inClashTree tree m.2) →
      ∃ spcol livein flivein,
        selectRegAlloc alg spillcosts k heu_moves tree forced fs = .success spcol ∧
        checkClashTree (spDefault spcol) tree .ln .ln = some (livein, flivein) ∧
        (∀ r, inClashTree tree r →
          sptDomain spcol r ∧
            if isPhyVar r then spDefault spcol r = r / 2
            else if isStackVar r then k ≤ spDefault spcol r
            else True) ∧
        (∀ r, sptDomain spcol r → inClashTree tree r) ∧
        ∀ m ∈ forced, spDefault spcol m.1 = spDefault spcol m.2 → m.1 = m.2 := by
  intro alg spillcosts k heu_moves tree forced fs hforced
  by_cases h : 4 ≤ alg
  · obtain ⟨col, livein, flivein, hrun, hcc, hdom, hsup, hfor⟩ :=
      LinearScan.linearScanRegAllocCorrect k heu_moves tree forced hforced
    exact ⟨col, livein, flivein, by rw [selectRegAlloc, if_pos h]; exact hrun, hcc, hdom, hsup,
      hfor⟩
  · obtain ⟨col, livein, flivein, hrun, hcc, hdom, hsup, hfor⟩ :=
      regAllocCorrect (if alg ≤ 1 then .Simple else .IRC) spillcosts k heu_moves tree forced fs
        hforced
    exact ⟨col, livein, flivein, by rw [selectRegAlloc, if_neg h]; exact hrun, hcc, hdom, hsup,
      hfor⟩

end Flapjack.WordAlloc
