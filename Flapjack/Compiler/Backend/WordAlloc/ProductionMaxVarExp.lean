import Flapjack.RiscV.Allocator
import Flapjack.Pancake.LoopToWord.WordExpCarrierCodec
import Flapjack.Pancake.WordLang.MaxVarExp

namespace Flapjack.RiscV

private theorem foldMaximum {α : Type} (f : α → Nat) (values : List α) (initial : Nat) :
    values.foldl (fun acc value => max acc (f value)) initial =
      max initial (maxList (values.map f)) := by
  induction values generalizing initial with
  | nil => simp [maxList]
  | cons value values ih =>
      simp only [List.foldl_cons, List.map_cons, maxList, ih, Nat.max_assoc]

/-- Production expression maximum agrees with the native HOL-shaped expression
maximum after the total expression codec. This is Flapjack carrier infrastructure,
not a HOL theorem port. It supplies the expression prerequisite for the separate
executed program maximum and limit routing; it does not establish that route. -/
theorem wordExpCakeMaxVar_corresponds {width : Nat} [NeZero width]
    (expression : WordExp (BitVec width)) :
    wordExpCakeMaxVar expression = maxVarExpHOL (wordExpToHOL expression) := by
  induction expression using wordExpCakeMaxVar.induct
  all_goals simp_all [wordExpCakeMaxVar, wordExpToHOL, maxVarExpHOL, foldMaximum]
  congr 1
  exact List.map_congr_left (fun argument member => by simp_all)

end Flapjack.RiscV
