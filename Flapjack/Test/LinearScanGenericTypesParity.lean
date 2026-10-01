import Flapjack.Compiler.Backend.LinearScan.TopLevel

namespace Flapjack.Test.LinearScanGenericTypesParity
open Flapjack Flapjack.RegAlloc Flapjack.LinearScan Flapjack.Translator.Monadic.MonadBase
/-! Lean counterparts of the original polymorphic carriers captured in
`scripts/hol-probes/linear_scan_generic_types_probe.out`: each declaration is
elaborated at a non-`Nat`/non-`StateException` instance of the carrier that
HOL leaves polymorphic. These checks fix the binders' generality only; they do
not establish cross-assistant equivalence. -/

-- check_col: (num -> num) -> α num_map -> (α num_map # num_set) option
example : checkCol (fun n => n + 1) (.ls true : Spt Bool) = some (.ls true, .bn .ln (.ls ())) := by
  decide +kernel
-- check_intervals: (num -> α) -> ...
example : checkIntervals (fun _ => true) .ln .ln := by
  intro r1 r2 h; exact absurd h.1 (by simp [sptDomain, sptLookup])
-- *_length: generic exception γ
example : (colorsLength : M LinearScanHiddenState Nat Bool)
    ⟨[1, 2], [], [], [], []⟩ = (.success 2, ⟨[1, 2], [], [], [], []⟩) := rfl
example : (sortedMovesLength : M LinearScanHiddenState Nat Unit)
    ⟨[], [], [], [], [(0, 1, 2)]⟩ = (.success 1, ⟨[], [], [], [], [(0, 1, 2)]⟩) := rfl
-- find_last_stealable: (α # num) list
example : findLastStealable ([] : List (Bool × Nat)) .ln ⟨[], [], [], [], []⟩ =
    (.success none, ⟨[], [], [], [], []⟩) := rfl
-- run_i_linear_scan_hidden_state: arbitrary result β and exception γ
example : runILinearScanHiddenState (fun s => ((.failure true : Exc Nat Bool), s))
    ⟨(1, 0), (0, 0), (0, 0), (0, 0), (0, (0, 0, 0))⟩ = .failure true := rfl
-- linear_reg_alloc_and_extract_coloration: unused nmax : α
example : linearRegAllocAndExtractColoration (.delta [] []) 3 [] [] [] .ln "unused"
    ⟨[0], [0], [0], [0], []⟩ =
    linearRegAllocAndExtractColoration (.delta [] []) 3 [] [] [] .ln (0 : Nat)
      ⟨[0], [0], [0], [0], []⟩ := rfl

end Flapjack.Test.LinearScanGenericTypesParity
