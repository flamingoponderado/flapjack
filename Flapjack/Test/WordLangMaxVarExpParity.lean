import Flapjack.Pancake.WordLang.MaxVarExp

namespace Flapjack.Test.WordLangMaxVarExpParity

-- Original rows in word_lang_max_var_exp_probe.out, with identical inputs.
example : maxVarExpHOL (.var 37 : WordLangExpHOL (BitVec 8)) = 37 := by simp [maxVarExpHOL]
example : maxVarExpHOL (.load (.load (.var 19)) : WordLangExpHOL (BitVec 8)) = 19 := by simp [maxVarExpHOL]
example : maxVarExpHOL (.op .add [] : WordLangExpHOL (BitVec 8)) = 0 := by simp [maxVarExpHOL, maxList]
example : maxVarExpHOL (.op .add [.var 3, .load (.var 51), .var 3] : WordLangExpHOL (BitVec 8)) = 51 := by simp [maxVarExpHOL, maxList]
example : maxVarExpHOL (.shift .lsl (.var 22) (.var 6) : WordLangExpHOL (BitVec 8)) = 22 := by simp [maxVarExpHOL]
example : maxVarExpHOL (.const 255 : WordLangExpHOL (BitVec 8)) = 0 := by simp [maxVarExpHOL]
example : maxVarExpHOL (.lookup (.temp 9) : WordLangExpHOL (BitVec 8)) = 0 := by simp [maxVarExpHOL]
example : maxVarExpHOL (.op .sub [.load (.shift .lsr (.var 7) (.var 29)), .var 4, .const 9] : WordLangExpHOL (BitVec 8)) = 29 := by simp [maxVarExpHOL, maxList]

end Flapjack.Test.WordLangMaxVarExpParity
