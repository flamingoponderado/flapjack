import Flapjack.HolRef
import Flapjack.Misc.Sptree

namespace Flapjack.Compiler.Backend.WordToWord

/-- The complete source configuration. HOL `num_map` is the concrete sptree,
not a finite-map function; both fields retain their literal carriers. -/
@[hol "cakeml/compiler/backend/word_to_wordScript.sml" "config"]
structure Config where
  regAlg : Nat
  colOracle : List (Option (Flapjack.Spt Nat))

/-- Consume exactly the requested prefix when enough oracle entries remain.
An insufficient oracle supplies an entirely fresh list of `NONE` entries,
discarding the short remainder, exactly as in the original definition. -/
@[hol "cakeml/compiler/backend/word_to_wordScript.sml" "next_n_oracle_def"]
def nextNOracle (n : Nat) (col : List (Option (Flapjack.Spt Nat))) :
    List (Option (Flapjack.Spt Nat)) × List (Option (Flapjack.Spt Nat)) :=
  if n ≤ col.length then (col.take n, col.drop n)
  else (List.replicate n none, [])

/-- Flapjack infrastructure for the compiler's ZIP bound; the original proof
derives this fact inline, without a separately named HOL theorem. -/
theorem nextNOracle_length (n : Nat) (col : List (Option (Flapjack.Spt Nat))) :
    (nextNOracle n col).1.length = n := by
  unfold nextNOracle
  split
  · simp_all
  · simp

end Flapjack.Compiler.Backend.WordToWord
