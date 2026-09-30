import Flapjack.Compiler.Backend.WordToStackRegFormat
import Flapjack.Misc.Sptree

/-! Exact Spt/cutsets bitmap boundary for the Word-to-Stack compiler.
The full comp/compile_prog/compile_semantics port and production routing remain
open. Existing list-domain helpers are retained as infrastructure, not exact
HOL ports; the equations below connect them to the literal source carriers. -/
namespace Flapjack.Compiler.Backend.WordToStack
open Flapjack Flapjack.Compiler.Backend.StackLang

/-- Source write_bitmap: enumerate the actual unit Spt, map its register keys
with truncating subtraction, append the terminal bit, then pack width-1 chunks.
The payload is ignored exactly as in HOL; no wf/domain-order premise is added. -/
@[hol "cakeml/compiler/backend/word_to_stackScript.sml" "write_bitmap_def"
  (words_as_type_indexed_bitvec)]
def writeBitmapExact {width : Nat} [NeZero width]
    (live : Spt Unit) (k frame : Nat) : List (BitVec width) :=
  let names := (sptToAList live).map (fun (register, _) =>
    (frame - 1) - (register / 2 - k))
  wordListW ((List.range frame).map (fun x => decide (x ∈ names)) ++ [true]) (width - 1)

/-- Native infrastructure: exact enumeration's keys instantiate the existing
list-domain helper; this is not an additional HOL theorem port. -/
theorem writeBitmapExact_eq_domain {width : Nat} [NeZero width]
    (live : Spt Unit) (k frame : Nat) :
    writeBitmapExact (width := width) live k frame =
      writeBitmapHOL ((sptToAList live).map Prod.fst) k frame := by
  unfold writeBitmapExact writeBitmapHOL
  simp only [List.map_map]
  rfl

/-- Source wLive retains both cutsets and the complete (k,f,f') tuple; only
SND live and f determine bitmap insertion, exactly as in the HOL definition. -/
@[hol "cakeml/compiler/backend/word_to_stackScript.sml" "wLive_def"
  (words_as_type_indexed_bitvec)]
def wLiveExact {width : Nat} [NeZero width]
    (live : Spt Unit × Spt Unit) (bitmaps : AppList (BitVec width) × Nat)
    (kf : Nat × Nat × Nat) : ProgM (BitVec width) × (AppList (BitVec width) × Nat) :=
  if kf.2.1 = 0 then (.skip, bitmaps)
  else
    let inserted := insertBitmap (writeBitmapExact live.2 kf.1 kf.2.2) bitmaps
    (.seq (.inst (.const kf.1 (BitVec.ofNat width (inserted.2 + 1))))
      (.stackStore kf.1 0), inserted.1)

/-- Native infrastructure: the existing wLiveW is precisely the key-domain
projection of the source cutsets; non-GCed keys are not silently combined. -/
theorem wLiveExact_eq_domain {width : Nat} [NeZero width]
    (live : Spt Unit × Spt Unit) (bitmaps : AppList (BitVec width) × Nat)
    (kf : Nat × Nat × Nat) :
    wLiveExact live bitmaps kf =
      WordToStackRegFormat.wLiveW ((sptToAList live.2).map Prod.fst) bitmaps kf.1 kf.2.1 kf.2.2 := by
  simp only [wLiveExact, WordToStackRegFormat.wLiveW, writeBitmapExact_eq_domain]

end Flapjack.Compiler.Backend.WordToStack
