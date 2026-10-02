import Flapjack.Compiler.Backend.StackProps.ExtractLabels

/-! Same-input kernel replay of fresh original ordered label observations.
These regressions do not establish cross-language equivalence. -/
namespace Flapjack.Test.StackPropsExtractLabelsParity
open Flapjack.Compiler.Backend.StackLang Flapjack.Compiler.Backend.StackProps

-- sel_1_skip
example : extractLabels (.skip : HolProg 1) = [] := by simp [extractLabels]

-- sel_1_inst
example : extractLabels (.inst .skip : HolProg 1) = [] := by simp [extractLabels]

-- sel_1_location
example : extractLabels (.locValue 2 9 4 : HolProg 1) = [] := by simp [extractLabels]

-- sel_1_raw
example : extractLabels (.rawCall 9 : HolProg 1) = [] := by simp [extractLabels]

-- sel_1_return
example : extractLabels (.call (some (.skip,73,11,12)) (.inl 9) none : HolProg 1) = [(11,12)] := by simp [extractLabels]

-- sel_1_both
example : extractLabels (.call (some (.skip,73,11,12)) (.inr 9) (some (.skip,21,22)) : HolProg 1) = [(11,12), (21,22)] := by simp [extractLabels]

-- sel_1_ignored
example : extractLabels (.call none (.inr 9) (some (.call (some (.skip,73,11,12)) (.inr 9) (some (.skip,21,22)),21,22)) : HolProg 1) = [] := by simp [extractLabels]

-- sel_1_loop
example : extractLabels (.loop (.call (some (.skip,73,11,12)) (.inr 9) (some (.skip,21,22))) : HolProg 1) = [(11,12), (21,22)] := by simp [extractLabels]

-- sel_1_seq
example : extractLabels (.seq (.call (some (.skip,73,11,12)) (.inl 9) none) (.call (some (.skip,73,11,12)) (.inr 9) (some (.skip,21,22))) : HolProg 1) = [(11,12), (11,12), (21,22)] := by simp [extractLabels]

-- sel_1_if
example : extractLabels (.ite .equal 0 (.imm 255) (.call (some (.skip,73,11,12)) (.inr 9) (some (.skip,21,22))) (.call (some (.skip,73,11,12)) (.inl 9) none) : HolProg 1) = [(11,12), (21,22), (11,12)] := by simp [extractLabels]

-- sel_1_nested
example : extractLabels (.call (some (.call (some (.skip,73,11,12)) (.inr 9) (some (.skip,21,22)),0,31,32)) (.inl 9) (some (.call (some (.skip,73,11,12)) (.inl 9) none,41,42)) : HolProg 1) = [(31,32), (41,42), (11,12), (21,22), (11,12)] := by simp [extractLabels]

-- sel_1_duplicate
example : extractLabels (.call (some (.call (some (.skip,73,11,12)) (.inl 9) none,0,11,12)) (.inr 9) (some (.call (some (.skip,73,11,12)) (.inl 9) none,11,12)) : HolProg 1) = [(11,12), (11,12), (11,12), (11,12)] := by simp [extractLabels]

-- sel_1_zero
example : extractLabels (.call (some (.skip,0,0,1)) (.inl 0) (some (.skip,0,0)) : HolProg 1) = [(0,1), (0,0)] := by simp [extractLabels]

-- sel_1_wide
example : extractLabels (.call (some (.skip,0,1180591620717411303424,1180591620717411303425)) (.inr 0) none : HolProg 1) = [(1180591620717411303424,1180591620717411303425)] := by simp [extractLabels]

-- sel_8_skip
example : extractLabels (.skip : HolProg 8) = [] := by simp [extractLabels]

-- sel_8_inst
example : extractLabels (.inst .skip : HolProg 8) = [] := by simp [extractLabels]

-- sel_8_location
example : extractLabels (.locValue 2 9 4 : HolProg 8) = [] := by simp [extractLabels]

-- sel_8_raw
example : extractLabels (.rawCall 9 : HolProg 8) = [] := by simp [extractLabels]

-- sel_8_return
example : extractLabels (.call (some (.skip,73,11,12)) (.inl 9) none : HolProg 8) = [(11,12)] := by simp [extractLabels]

-- sel_8_both
example : extractLabels (.call (some (.skip,73,11,12)) (.inr 9) (some (.skip,21,22)) : HolProg 8) = [(11,12), (21,22)] := by simp [extractLabels]

-- sel_8_ignored
example : extractLabels (.call none (.inr 9) (some (.call (some (.skip,73,11,12)) (.inr 9) (some (.skip,21,22)),21,22)) : HolProg 8) = [] := by simp [extractLabels]

-- sel_8_loop
example : extractLabels (.loop (.call (some (.skip,73,11,12)) (.inr 9) (some (.skip,21,22))) : HolProg 8) = [(11,12), (21,22)] := by simp [extractLabels]

-- sel_8_seq
example : extractLabels (.seq (.call (some (.skip,73,11,12)) (.inl 9) none) (.call (some (.skip,73,11,12)) (.inr 9) (some (.skip,21,22))) : HolProg 8) = [(11,12), (11,12), (21,22)] := by simp [extractLabels]

-- sel_8_if
example : extractLabels (.ite .equal 0 (.imm 255) (.call (some (.skip,73,11,12)) (.inr 9) (some (.skip,21,22))) (.call (some (.skip,73,11,12)) (.inl 9) none) : HolProg 8) = [(11,12), (21,22), (11,12)] := by simp [extractLabels]

-- sel_8_nested
example : extractLabels (.call (some (.call (some (.skip,73,11,12)) (.inr 9) (some (.skip,21,22)),0,31,32)) (.inl 9) (some (.call (some (.skip,73,11,12)) (.inl 9) none,41,42)) : HolProg 8) = [(31,32), (41,42), (11,12), (21,22), (11,12)] := by simp [extractLabels]

-- sel_8_duplicate
example : extractLabels (.call (some (.call (some (.skip,73,11,12)) (.inl 9) none,0,11,12)) (.inr 9) (some (.call (some (.skip,73,11,12)) (.inl 9) none,11,12)) : HolProg 8) = [(11,12), (11,12), (11,12), (11,12)] := by simp [extractLabels]

-- sel_8_zero
example : extractLabels (.call (some (.skip,0,0,1)) (.inl 0) (some (.skip,0,0)) : HolProg 8) = [(0,1), (0,0)] := by simp [extractLabels]

-- sel_8_wide
example : extractLabels (.call (some (.skip,0,1180591620717411303424,1180591620717411303425)) (.inr 0) none : HolProg 8) = [(1180591620717411303424,1180591620717411303425)] := by simp [extractLabels]

-- sel_64_skip
example : extractLabels (.skip : HolProg 64) = [] := by simp [extractLabels]

-- sel_64_inst
example : extractLabels (.inst .skip : HolProg 64) = [] := by simp [extractLabels]

-- sel_64_location
example : extractLabels (.locValue 2 9 4 : HolProg 64) = [] := by simp [extractLabels]

-- sel_64_raw
example : extractLabels (.rawCall 9 : HolProg 64) = [] := by simp [extractLabels]

-- sel_64_return
example : extractLabels (.call (some (.skip,73,11,12)) (.inl 9) none : HolProg 64) = [(11,12)] := by simp [extractLabels]

-- sel_64_both
example : extractLabels (.call (some (.skip,73,11,12)) (.inr 9) (some (.skip,21,22)) : HolProg 64) = [(11,12), (21,22)] := by simp [extractLabels]

-- sel_64_ignored
example : extractLabels (.call none (.inr 9) (some (.call (some (.skip,73,11,12)) (.inr 9) (some (.skip,21,22)),21,22)) : HolProg 64) = [] := by simp [extractLabels]

-- sel_64_loop
example : extractLabels (.loop (.call (some (.skip,73,11,12)) (.inr 9) (some (.skip,21,22))) : HolProg 64) = [(11,12), (21,22)] := by simp [extractLabels]

-- sel_64_seq
example : extractLabels (.seq (.call (some (.skip,73,11,12)) (.inl 9) none) (.call (some (.skip,73,11,12)) (.inr 9) (some (.skip,21,22))) : HolProg 64) = [(11,12), (11,12), (21,22)] := by simp [extractLabels]

-- sel_64_if
example : extractLabels (.ite .equal 0 (.imm 255) (.call (some (.skip,73,11,12)) (.inr 9) (some (.skip,21,22))) (.call (some (.skip,73,11,12)) (.inl 9) none) : HolProg 64) = [(11,12), (21,22), (11,12)] := by simp [extractLabels]

-- sel_64_nested
example : extractLabels (.call (some (.call (some (.skip,73,11,12)) (.inr 9) (some (.skip,21,22)),0,31,32)) (.inl 9) (some (.call (some (.skip,73,11,12)) (.inl 9) none,41,42)) : HolProg 64) = [(31,32), (41,42), (11,12), (21,22), (11,12)] := by simp [extractLabels]

-- sel_64_duplicate
example : extractLabels (.call (some (.call (some (.skip,73,11,12)) (.inl 9) none,0,11,12)) (.inr 9) (some (.call (some (.skip,73,11,12)) (.inl 9) none,11,12)) : HolProg 64) = [(11,12), (11,12), (11,12), (11,12)] := by simp [extractLabels]

-- sel_64_zero
example : extractLabels (.call (some (.skip,0,0,1)) (.inl 0) (some (.skip,0,0)) : HolProg 64) = [(0,1), (0,0)] := by simp [extractLabels]

-- sel_64_wide
example : extractLabels (.call (some (.skip,0,1180591620717411303424,1180591620717411303425)) (.inr 0) none : HolProg 64) = [(1180591620717411303424,1180591620717411303425)] := by simp [extractLabels]

-- sel_80_skip
example : extractLabels (.skip : HolProg 80) = [] := by simp [extractLabels]

-- sel_80_inst
example : extractLabels (.inst .skip : HolProg 80) = [] := by simp [extractLabels]

-- sel_80_location
example : extractLabels (.locValue 2 9 4 : HolProg 80) = [] := by simp [extractLabels]

-- sel_80_raw
example : extractLabels (.rawCall 9 : HolProg 80) = [] := by simp [extractLabels]

-- sel_80_return
example : extractLabels (.call (some (.skip,73,11,12)) (.inl 9) none : HolProg 80) = [(11,12)] := by simp [extractLabels]

-- sel_80_both
example : extractLabels (.call (some (.skip,73,11,12)) (.inr 9) (some (.skip,21,22)) : HolProg 80) = [(11,12), (21,22)] := by simp [extractLabels]

-- sel_80_ignored
example : extractLabels (.call none (.inr 9) (some (.call (some (.skip,73,11,12)) (.inr 9) (some (.skip,21,22)),21,22)) : HolProg 80) = [] := by simp [extractLabels]

-- sel_80_loop
example : extractLabels (.loop (.call (some (.skip,73,11,12)) (.inr 9) (some (.skip,21,22))) : HolProg 80) = [(11,12), (21,22)] := by simp [extractLabels]

-- sel_80_seq
example : extractLabels (.seq (.call (some (.skip,73,11,12)) (.inl 9) none) (.call (some (.skip,73,11,12)) (.inr 9) (some (.skip,21,22))) : HolProg 80) = [(11,12), (11,12), (21,22)] := by simp [extractLabels]

-- sel_80_if
example : extractLabels (.ite .equal 0 (.imm 255) (.call (some (.skip,73,11,12)) (.inr 9) (some (.skip,21,22))) (.call (some (.skip,73,11,12)) (.inl 9) none) : HolProg 80) = [(11,12), (21,22), (11,12)] := by simp [extractLabels]

-- sel_80_nested
example : extractLabels (.call (some (.call (some (.skip,73,11,12)) (.inr 9) (some (.skip,21,22)),0,31,32)) (.inl 9) (some (.call (some (.skip,73,11,12)) (.inl 9) none,41,42)) : HolProg 80) = [(31,32), (41,42), (11,12), (21,22), (11,12)] := by simp [extractLabels]

-- sel_80_duplicate
example : extractLabels (.call (some (.call (some (.skip,73,11,12)) (.inl 9) none,0,11,12)) (.inr 9) (some (.call (some (.skip,73,11,12)) (.inl 9) none,11,12)) : HolProg 80) = [(11,12), (11,12), (11,12), (11,12)] := by simp [extractLabels]

-- sel_80_zero
example : extractLabels (.call (some (.skip,0,0,1)) (.inl 0) (some (.skip,0,0)) : HolProg 80) = [(0,1), (0,0)] := by simp [extractLabels]

-- sel_80_wide
example : extractLabels (.call (some (.skip,0,1180591620717411303424,1180591620717411303425)) (.inr 0) none : HolProg 80) = [(1180591620717411303424,1180591620717411303425)] := by simp [extractLabels]

def runChecks : IO Bool := do
  IO.println "PASS original StackProps ordered labels (56 kernel rows)"
  pure true

end Flapjack.Test.StackPropsExtractLabelsParity
