import Flapjack.Misc.BalancedMap.Core
import Flapjack.Misc.Sptree
import Flapjack.Pancake.WordLang

/-! Source-shaped native CSE knowledge. Both register maps retain the literal
sparse-tree carrier, both fact maps retain every balanced-tree constructor and
cached size, and store facts retain the source association-list order. This
native port is a prerequisite for full CSE; the distinct executed knowledge
carrier and its routing correspondence remain separate open work. -/
namespace Flapjack.Compiler.Backend.WordCse
open Flapjack

/-- The five original knowledge fields. `WordStoreHOL` fixes the reviewed
phantom parameter to Unit and retains the fixed 5-bit Temp payload; no word
width or finite-map representation translation is involved. -/
@[hol "cakeml/compiler/backend/word_cseScript.sml" "knowledge"]
structure Knowledge where
  toCanonical : Spt Nat
  toLatest : Spt Nat
  getsMem : List (WordStoreHOL × Nat)
  instrsMem : Misc.BalancedMap.Map (List Nat) Nat
  loadsMem : Misc.BalancedMap.Map (List Nat) Nat
  deriving Repr, DecidableEq

/-- Original empty sparse trees, empty store list, and literal empty balanced
maps; no cached-size repair or canonicalization is performed. -/
@[hol "cakeml/compiler/backend/word_cseScript.sml" "empty_data_def"]
def emptyData : Knowledge :=
  ⟨.ln, .ln, [], Misc.BalancedMap.empty, Misc.BalancedMap.empty⟩

@[hol "cakeml/compiler/backend/word_cseScript.sml" "keep_data_def"]
def keepData {α : Type} (canon : Spt α) (written : Nat) : Bool :=
  (sptLookup written canon).isNone

@[hol "cakeml/compiler/backend/word_cseScript.sml" "invalidate_data_def"]
def invalidateData (data : Knowledge) (written : Nat) : Knowledge :=
  if keepData data.toCanonical written then data else emptyData

/-- Literal left-to-right recursive invalidation, retaining the original
argument order and both equations for arbitrary register lists. -/
@[hol "cakeml/compiler/backend/word_cseScript.sml" "invalidate_regs_def"]
def invalidateRegs (data : Knowledge) : List Nat → Knowledge
  | [] => data
  | register :: registers => invalidateRegs (invalidateData data register) registers

end Flapjack.Compiler.Backend.WordCse
