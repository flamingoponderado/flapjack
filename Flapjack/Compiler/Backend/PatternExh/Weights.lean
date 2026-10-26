import Flapjack.Compiler.Backend.PatternExh.Matrix

/-! Measures used by CakeML to justify exhaustiveness recursion. -/
namespace Flapjack.Compiler.Backend.PatternExh
open PatternSemantics

mutual
/-- Count the constructor, reference and alternative nodes of a pattern. -/
@[hol "cakeml/compiler/backend/pattern_matching/pattern_exhScript.sml" "pat_weight_def"]
def patWeight : Pat → Nat
  | .any | .lit _ => 0
  | .or p q => 1 + patWeight p + patWeight q
  | .ref p => 1 + patWeight p
  | .cons _ ps => 1 + patsWeight ps

/-- Sum pattern weights in a row. -/
@[hol "cakeml/compiler/backend/pattern_matching/pattern_exhScript.sml" "pat_weight_def"]
def patsWeight : List Pat → Nat
  | [] => 0
  | p :: ps => patWeight p + patsWeight ps
end

/-- Sum the weights of the rows in a matrix. -/
@[hol "cakeml/compiler/backend/pattern_matching/pattern_exhScript.sml" "mat_weight_def"]
def matWeight : List (List Pat) → Nat
  | [] => 0
  | r :: rows => patsWeight r + matWeight rows

/-- Count all matrix columns across rows. -/
@[hol "cakeml/compiler/backend/pattern_matching/pattern_exhScript.sml" "mat_len_def"]
def matLen : List (List Pat) → Nat
  | [] => 0
  | r :: rows => r.length + matLen rows

/-- Largest matrix weight in a list of matrices. -/
@[hol "cakeml/compiler/backend/pattern_matching/pattern_exhScript.sml" "mats_weight_def"]
def matsWeight : List (List (List Pat)) → Nat
  | [] => 0
  | m :: ms => max (matWeight m) (matsWeight ms)

/-- Largest matrix length in a list of matrices. -/
@[hol "cakeml/compiler/backend/pattern_matching/pattern_exhScript.sml" "mats_len_def"]
def matsLen : List (List (List Pat)) → Nat
  | [] => 0
  | m :: ms => max (matLen m) (matsLen ms)

/-- Bounded replay of HOL `exh_all`. Failure means the supplied step budget
was exhausted; no claim that a particular budget suffices is made. This helper
is not tagged as the total HOL recursion. -/
def exhAllFuel : Nat → List (List (List Pat)) → Option Bool
  | 0, _ => none
  | _ + 1, [] => some true
  | _ + 1, [] :: _ => some false
  | fuel + 1, (r :: rows) :: ms =>
      if r.isEmpty then exhAllFuel fuel ms
      else match colCtors (r :: rows) with
        | none => exhAllFuel fuel (defaultMat (r :: rows) :: ms)
        | some cs => exhAllFuel fuel (specMats cs (r :: rows) ++ ms)

/-- Bounded exhaustiveness check for pattern rows. The total HOL `exh_rows`
and the source proof that `exh_all` agrees with it remain to be ported. -/
def exhRowsFuel {α : Type} (fuel : Nat) (rows : List (Pat × α)) : Option Bool :=
  exhAllFuel fuel [orRows rows]

end Flapjack.Compiler.Backend.PatternExh
