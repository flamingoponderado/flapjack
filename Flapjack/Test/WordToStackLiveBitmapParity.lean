import Flapjack.Compiler.Backend.WordToStack.LiveBitmap

/-! Replays existing original HOL write_bitmap rows against the actual Spt
carrier. wLive checks additionally pin cutset selection, frame-zero behavior,
bitmap append/index and word-width index wrapping. No new oracle rows. -/
namespace Flapjack.Test.WordToStackLiveBitmapParity
open Flapjack Compiler.Backend.WordToStack
private def live (keys : List Nat) : Spt Unit := sptFromAList (keys.map (fun k => (k, ())))
#guard writeBitmapExact (width := 8) (live []) 0 4 == [16]
#guard writeBitmapExact (width := 8) (live [0]) 0 4 == [24]
#guard writeBitmapExact (width := 8) (live [0,1]) 0 4 == [24]
#guard writeBitmapExact (width := 8) (live [2,4,6]) 0 8 == [240,2]
#guard writeBitmapExact (width := 64) (live [0,2,4]) 0 64 == [0xE000000000000000,3]
#guard writeBitmapExact (width := 8) (live [0,1,2]) 0 8 == [192,3]
#guard writeBitmapExact (width := 8) (live [2,0,1]) 0 8 == [192,3]

example (a b : Spt Unit) (bm : AppList (BitVec 64) × Nat) (k f' : Nat) :
    wLiveExact (a,b) bm (k,0,f') = (.skip,bm) := by simp [wLiveExact]
#guard (wLiveExact (width := 8) (live [0],live []) (.nil,255) (3,1,4)).2.2 == 256
#guard (wLiveExact (width := 8) (live [0],live []) (.list [9],7) (3,1,4)).2.2 == 8
#guard match (wLiveExact (width := 8) (live [0],live []) (.nil,255) (3,1,4)).1 with
  | .seq (.inst (.const k v)) (.stackStore r offset) => k == 3 && v == 0 && r == 3 && offset == 0
  | _ => false
#guard match (wLiveExact (width := 8) (live [0],live []) (.list [9],7) (3,1,4)).1 with
  | .seq (.inst (.const k v)) (.stackStore r offset) => k == 3 && v == 8 && r == 3 && offset == 0
  | _ => false
example {width : Nat} [NeZero width] (tree : Spt Unit) (k f : Nat) :
    writeBitmapExact (width := width) tree k f =
      writeBitmapHOL ((sptToAList tree).map Prod.fst) k f := writeBitmapExact_eq_domain tree k f
example {width : Nat} [NeZero width] (cuts : Spt Unit × Spt Unit)
    (bm : AppList (BitVec width) × Nat) (kf : Nat × Nat × Nat) :
    wLiveExact cuts bm kf = Compiler.Backend.WordToStackRegFormat.wLiveW
      ((sptToAList cuts.2).map Prod.fst) bm kf.1 kf.2.1 kf.2.2 := wLiveExact_eq_domain cuts bm kf

def runChecks : IO Bool := do
  IO.println "PASS exact Spt Word-to-Stack bitmap/cutsets wLive (full compiler route open)"
  return true
end Flapjack.Test.WordToStackLiveBitmapParity
