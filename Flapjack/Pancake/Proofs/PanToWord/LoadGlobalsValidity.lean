import Flapjack.Pancake.CrepLang.Prog
namespace Flapjack
/-- Full original arbitrary-address/count equality. The GENLIST index is Nat,
while the global address remains the original fixed word5; expression words
retain their independent positive dimension. -/
@[hol "cakeml/pancake/proofs/pan_to_wordProofScript.sml" "load_globals_alt"
  (words_as_type_indexed_bitvec)]
theorem loadGlobalsAlt {width : Nat} [NeZero width] (address : BitVec 5) (count : Nat) :
    (loadGlobalsHOL address count : List (CrepExpHOL width)) =
      (List.range count).map
        (fun n => (CrepExpHOL.loadGlob (address + BitVec.ofNat 5 n) : CrepExpHOL width)) := by
  induction count generalizing address with
  | zero => simp [loadGlobalsHOL]
  | succ count ih =>
    rw [loadGlobalsHOL, ih, List.range_succ_eq_map, List.map_cons, List.map_map]
    simp only [show address + BitVec.ofNat 5 0 = address from BitVec.add_zero address]
    congr 1
    apply List.map_congr_left
    intro n hn
    congr 1
    simp only [Nat.succ_eq_add_one, BitVec.ofNat_add]
    ac_rfl
end Flapjack
