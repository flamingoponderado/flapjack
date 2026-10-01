import Flapjack.Compiler.Backend.WordToStack.ProductionExpressionMaximum

/-! Kernel replay of the eight freshly rerun original
`word_lang_max_var_exp_probe` inputs, through the actual production maximum
and its total codec. The final examples exercise arbitrary width and initial
scan accumulators, rather than only the original eight closed observations. -/

namespace Flapjack.Test.WordToStackExpressionMaximumParity
open Flapjack

private def inputs : List (WordExp (BitVec 8)) :=
  [.var 37, .load (.load (.var 19)), .op .add [],
   .op .add [.var 3, .load (.var 51), .var 3],
   .shift .lsl (.var 22) (.var 6), .const 255,
   .lookup (.temp 9),
   .op .sub [.load (.shift .lsr (.var 7) (.var 29)), .var 4, .const 9]]

example : inputs.map wordExpCakeMaxVar = [37, 19, 0, 51, 22, 0, 0, 29] := by
  simp only [inputs, List.map_cons, List.map_nil, wordExpCakeMaxVar,
    List.foldl_cons, List.foldl_nil]
  decide +kernel

example : (inputs.map wordExpToHOL).map maxVarExpHOL =
    [37, 19, 0, 51, 22, 0, 0, 29] := by
  have same : inputs.map wordExpCakeMaxVar =
      (inputs.map wordExpToHOL).map maxVarExpHOL := by
    simp only [List.map_map]
    apply List.map_congr_left
    intro expression _
    exact wordExpCakeMaxVar_eq_maxVarExpHOL expression
  rw [← same]
  simp only [inputs, List.map_cons, List.map_nil, wordExpCakeMaxVar,
    List.foldl_cons, List.foldl_nil]
  decide +kernel

example {width : Nat} [NeZero width] (expression : WordExp (BitVec width)) :
    wordExpCakeMaxVar expression = maxVarExpHOL (wordExpToHOL expression) :=
  wordExpCakeMaxVar_eq_maxVarExpHOL expression

example {width : Nat} [NeZero width] (initial : Nat)
    (expressions : List (WordExp (BitVec width))) :
    expressions.foldl (fun result expression => max result (wordExpCakeMaxVar expression))
        initial =
      max initial (maxList ((expressions.map wordExpToHOL).map maxVarExpHOL)) :=
  wordExpCakeMaxVar_fold_eq_maxVarExpHOL expressions initial

example : wordExpCakeMaxVar
    (.op .add [.var (2 ^ 80), .shift .lsl (.var 7) (.var (2 ^ 80 + 1)),
      .op .xor []] : WordExp (BitVec 1)) = 2 ^ 80 + 1 := by
  simp only [wordExpCakeMaxVar, List.foldl_cons, List.foldl_nil]
  decide +kernel

example : ([] : List (WordExp (BitVec 1))).foldl
    (fun result expression => max result (wordExpCakeMaxVar expression)) 99 = 99 := rfl

end Flapjack.Test.WordToStackExpressionMaximumParity
