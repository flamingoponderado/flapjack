import Flapjack.Misc.Sptree.Wf
import Init.Data.Prod

/-! Independent original wf/isEmpty complete outputs, including every depth-two
constructor combination, recursively malformed children, 24-level chains, and
function payloads without a payload equality instance. -/
namespace Flapjack.Test.SptreeWfDefinitionParity
open Flapjack
-- sw_tree_0
example : (sptWf (.ln : Spt Nat),sptIsEmpty (.ln : Spt Nat)) = (true,true) := by rfl
-- sw_tree_1
example : (sptWf ((.ls 7) : Spt Nat),sptIsEmpty ((.ls 7) : Spt Nat)) = (true,false) := by rfl
-- sw_tree_2
example : (sptWf ((.bn .ln .ln) : Spt Nat),sptIsEmpty ((.bn .ln .ln) : Spt Nat)) = (false,false) := by rfl
-- sw_tree_3
example : (sptWf ((.bn .ln (.ls 7)) : Spt Nat),sptIsEmpty ((.bn .ln (.ls 7)) : Spt Nat)) = (true,false) := by rfl
-- sw_tree_4
example : (sptWf ((.bn .ln (.bn .ln .ln)) : Spt Nat),sptIsEmpty ((.bn .ln (.bn .ln .ln)) : Spt Nat)) = (false,false) := by rfl
-- sw_tree_5
example : (sptWf ((.bn .ln (.bn .ln (.ls 7))) : Spt Nat),sptIsEmpty ((.bn .ln (.bn .ln (.ls 7))) : Spt Nat)) = (true,false) := by rfl
-- sw_tree_6
example : (sptWf ((.bn .ln (.bn (.ls 7) .ln)) : Spt Nat),sptIsEmpty ((.bn .ln (.bn (.ls 7) .ln)) : Spt Nat)) = (true,false) := by rfl
-- sw_tree_7
example : (sptWf ((.bn .ln (.bn (.ls 7) (.ls 7))) : Spt Nat),sptIsEmpty ((.bn .ln (.bn (.ls 7) (.ls 7))) : Spt Nat)) = (true,false) := by rfl
-- sw_tree_8
example : (sptWf ((.bn .ln (.bs .ln 9 .ln)) : Spt Nat),sptIsEmpty ((.bn .ln (.bs .ln 9 .ln)) : Spt Nat)) = (false,false) := by rfl
-- sw_tree_9
example : (sptWf ((.bn .ln (.bs .ln 9 (.ls 7))) : Spt Nat),sptIsEmpty ((.bn .ln (.bs .ln 9 (.ls 7))) : Spt Nat)) = (true,false) := by rfl
-- sw_tree_10
example : (sptWf ((.bn .ln (.bs (.ls 7) 9 .ln)) : Spt Nat),sptIsEmpty ((.bn .ln (.bs (.ls 7) 9 .ln)) : Spt Nat)) = (true,false) := by rfl
-- sw_tree_11
example : (sptWf ((.bn .ln (.bs (.ls 7) 9 (.ls 7))) : Spt Nat),sptIsEmpty ((.bn .ln (.bs (.ls 7) 9 (.ls 7))) : Spt Nat)) = (true,false) := by rfl
-- sw_tree_12
example : (sptWf ((.bn (.ls 7) .ln) : Spt Nat),sptIsEmpty ((.bn (.ls 7) .ln) : Spt Nat)) = (true,false) := by rfl
-- sw_tree_13
example : (sptWf ((.bn (.ls 7) (.ls 7)) : Spt Nat),sptIsEmpty ((.bn (.ls 7) (.ls 7)) : Spt Nat)) = (true,false) := by rfl
-- sw_tree_14
example : (sptWf ((.bn (.ls 7) (.bn .ln .ln)) : Spt Nat),sptIsEmpty ((.bn (.ls 7) (.bn .ln .ln)) : Spt Nat)) = (false,false) := by rfl
-- sw_tree_15
example : (sptWf ((.bn (.ls 7) (.bn .ln (.ls 7))) : Spt Nat),sptIsEmpty ((.bn (.ls 7) (.bn .ln (.ls 7))) : Spt Nat)) = (true,false) := by rfl
-- sw_tree_16
example : (sptWf ((.bn (.ls 7) (.bn (.ls 7) .ln)) : Spt Nat),sptIsEmpty ((.bn (.ls 7) (.bn (.ls 7) .ln)) : Spt Nat)) = (true,false) := by rfl
-- sw_tree_17
example : (sptWf ((.bn (.ls 7) (.bn (.ls 7) (.ls 7))) : Spt Nat),sptIsEmpty ((.bn (.ls 7) (.bn (.ls 7) (.ls 7))) : Spt Nat)) = (true,false) := by rfl
-- sw_tree_18
example : (sptWf ((.bn (.ls 7) (.bs .ln 9 .ln)) : Spt Nat),sptIsEmpty ((.bn (.ls 7) (.bs .ln 9 .ln)) : Spt Nat)) = (false,false) := by rfl
-- sw_tree_19
example : (sptWf ((.bn (.ls 7) (.bs .ln 9 (.ls 7))) : Spt Nat),sptIsEmpty ((.bn (.ls 7) (.bs .ln 9 (.ls 7))) : Spt Nat)) = (true,false) := by rfl
-- sw_tree_20
example : (sptWf ((.bn (.ls 7) (.bs (.ls 7) 9 .ln)) : Spt Nat),sptIsEmpty ((.bn (.ls 7) (.bs (.ls 7) 9 .ln)) : Spt Nat)) = (true,false) := by rfl
-- sw_tree_21
example : (sptWf ((.bn (.ls 7) (.bs (.ls 7) 9 (.ls 7))) : Spt Nat),sptIsEmpty ((.bn (.ls 7) (.bs (.ls 7) 9 (.ls 7))) : Spt Nat)) = (true,false) := by rfl
-- sw_tree_22
example : (sptWf ((.bn (.bn .ln .ln) .ln) : Spt Nat),sptIsEmpty ((.bn (.bn .ln .ln) .ln) : Spt Nat)) = (false,false) := by rfl
-- sw_tree_23
example : (sptWf ((.bn (.bn .ln .ln) (.ls 7)) : Spt Nat),sptIsEmpty ((.bn (.bn .ln .ln) (.ls 7)) : Spt Nat)) = (false,false) := by rfl
-- sw_tree_24
example : (sptWf ((.bn (.bn .ln .ln) (.bn .ln .ln)) : Spt Nat),sptIsEmpty ((.bn (.bn .ln .ln) (.bn .ln .ln)) : Spt Nat)) = (false,false) := by rfl
-- sw_tree_25
example : (sptWf ((.bn (.bn .ln .ln) (.bn .ln (.ls 7))) : Spt Nat),sptIsEmpty ((.bn (.bn .ln .ln) (.bn .ln (.ls 7))) : Spt Nat)) = (false,false) := by rfl
-- sw_tree_26
example : (sptWf ((.bn (.bn .ln .ln) (.bn (.ls 7) .ln)) : Spt Nat),sptIsEmpty ((.bn (.bn .ln .ln) (.bn (.ls 7) .ln)) : Spt Nat)) = (false,false) := by rfl
-- sw_tree_27
example : (sptWf ((.bn (.bn .ln .ln) (.bn (.ls 7) (.ls 7))) : Spt Nat),sptIsEmpty ((.bn (.bn .ln .ln) (.bn (.ls 7) (.ls 7))) : Spt Nat)) = (false,false) := by rfl
-- sw_tree_28
example : (sptWf ((.bn (.bn .ln .ln) (.bs .ln 9 .ln)) : Spt Nat),sptIsEmpty ((.bn (.bn .ln .ln) (.bs .ln 9 .ln)) : Spt Nat)) = (false,false) := by rfl
-- sw_tree_29
example : (sptWf ((.bn (.bn .ln .ln) (.bs .ln 9 (.ls 7))) : Spt Nat),sptIsEmpty ((.bn (.bn .ln .ln) (.bs .ln 9 (.ls 7))) : Spt Nat)) = (false,false) := by rfl
-- sw_tree_30
example : (sptWf ((.bn (.bn .ln .ln) (.bs (.ls 7) 9 .ln)) : Spt Nat),sptIsEmpty ((.bn (.bn .ln .ln) (.bs (.ls 7) 9 .ln)) : Spt Nat)) = (false,false) := by rfl
-- sw_tree_31
example : (sptWf ((.bn (.bn .ln .ln) (.bs (.ls 7) 9 (.ls 7))) : Spt Nat),sptIsEmpty ((.bn (.bn .ln .ln) (.bs (.ls 7) 9 (.ls 7))) : Spt Nat)) = (false,false) := by rfl
-- sw_tree_32
example : (sptWf ((.bn (.bn .ln (.ls 7)) .ln) : Spt Nat),sptIsEmpty ((.bn (.bn .ln (.ls 7)) .ln) : Spt Nat)) = (true,false) := by rfl
-- sw_tree_33
example : (sptWf ((.bn (.bn .ln (.ls 7)) (.ls 7)) : Spt Nat),sptIsEmpty ((.bn (.bn .ln (.ls 7)) (.ls 7)) : Spt Nat)) = (true,false) := by rfl
-- sw_tree_34
example : (sptWf ((.bn (.bn .ln (.ls 7)) (.bn .ln .ln)) : Spt Nat),sptIsEmpty ((.bn (.bn .ln (.ls 7)) (.bn .ln .ln)) : Spt Nat)) = (false,false) := by rfl
-- sw_tree_35
example : (sptWf ((.bn (.bn .ln (.ls 7)) (.bn .ln (.ls 7))) : Spt Nat),sptIsEmpty ((.bn (.bn .ln (.ls 7)) (.bn .ln (.ls 7))) : Spt Nat)) = (true,false) := by rfl
-- sw_tree_36
example : (sptWf ((.bn (.bn .ln (.ls 7)) (.bn (.ls 7) .ln)) : Spt Nat),sptIsEmpty ((.bn (.bn .ln (.ls 7)) (.bn (.ls 7) .ln)) : Spt Nat)) = (true,false) := by rfl
-- sw_tree_37
example : (sptWf ((.bn (.bn .ln (.ls 7)) (.bn (.ls 7) (.ls 7))) : Spt Nat),sptIsEmpty ((.bn (.bn .ln (.ls 7)) (.bn (.ls 7) (.ls 7))) : Spt Nat)) = (true,false) := by rfl
-- sw_tree_38
example : (sptWf ((.bn (.bn .ln (.ls 7)) (.bs .ln 9 .ln)) : Spt Nat),sptIsEmpty ((.bn (.bn .ln (.ls 7)) (.bs .ln 9 .ln)) : Spt Nat)) = (false,false) := by rfl
-- sw_tree_39
example : (sptWf ((.bn (.bn .ln (.ls 7)) (.bs .ln 9 (.ls 7))) : Spt Nat),sptIsEmpty ((.bn (.bn .ln (.ls 7)) (.bs .ln 9 (.ls 7))) : Spt Nat)) = (true,false) := by rfl
-- sw_tree_40
example : (sptWf ((.bn (.bn .ln (.ls 7)) (.bs (.ls 7) 9 .ln)) : Spt Nat),sptIsEmpty ((.bn (.bn .ln (.ls 7)) (.bs (.ls 7) 9 .ln)) : Spt Nat)) = (true,false) := by rfl
-- sw_tree_41
example : (sptWf ((.bn (.bn .ln (.ls 7)) (.bs (.ls 7) 9 (.ls 7))) : Spt Nat),sptIsEmpty ((.bn (.bn .ln (.ls 7)) (.bs (.ls 7) 9 (.ls 7))) : Spt Nat)) = (true,false) := by rfl
-- sw_tree_42
example : (sptWf ((.bn (.bn (.ls 7) .ln) .ln) : Spt Nat),sptIsEmpty ((.bn (.bn (.ls 7) .ln) .ln) : Spt Nat)) = (true,false) := by rfl
-- sw_tree_43
example : (sptWf ((.bn (.bn (.ls 7) .ln) (.ls 7)) : Spt Nat),sptIsEmpty ((.bn (.bn (.ls 7) .ln) (.ls 7)) : Spt Nat)) = (true,false) := by rfl
-- sw_tree_44
example : (sptWf ((.bn (.bn (.ls 7) .ln) (.bn .ln .ln)) : Spt Nat),sptIsEmpty ((.bn (.bn (.ls 7) .ln) (.bn .ln .ln)) : Spt Nat)) = (false,false) := by rfl
-- sw_tree_45
example : (sptWf ((.bn (.bn (.ls 7) .ln) (.bn .ln (.ls 7))) : Spt Nat),sptIsEmpty ((.bn (.bn (.ls 7) .ln) (.bn .ln (.ls 7))) : Spt Nat)) = (true,false) := by rfl
-- sw_tree_46
example : (sptWf ((.bn (.bn (.ls 7) .ln) (.bn (.ls 7) .ln)) : Spt Nat),sptIsEmpty ((.bn (.bn (.ls 7) .ln) (.bn (.ls 7) .ln)) : Spt Nat)) = (true,false) := by rfl
-- sw_tree_47
example : (sptWf ((.bn (.bn (.ls 7) .ln) (.bn (.ls 7) (.ls 7))) : Spt Nat),sptIsEmpty ((.bn (.bn (.ls 7) .ln) (.bn (.ls 7) (.ls 7))) : Spt Nat)) = (true,false) := by rfl
-- sw_tree_48
example : (sptWf ((.bn (.bn (.ls 7) .ln) (.bs .ln 9 .ln)) : Spt Nat),sptIsEmpty ((.bn (.bn (.ls 7) .ln) (.bs .ln 9 .ln)) : Spt Nat)) = (false,false) := by rfl
-- sw_tree_49
example : (sptWf ((.bn (.bn (.ls 7) .ln) (.bs .ln 9 (.ls 7))) : Spt Nat),sptIsEmpty ((.bn (.bn (.ls 7) .ln) (.bs .ln 9 (.ls 7))) : Spt Nat)) = (true,false) := by rfl
-- sw_tree_50
example : (sptWf ((.bn (.bn (.ls 7) .ln) (.bs (.ls 7) 9 .ln)) : Spt Nat),sptIsEmpty ((.bn (.bn (.ls 7) .ln) (.bs (.ls 7) 9 .ln)) : Spt Nat)) = (true,false) := by rfl
-- sw_tree_51
example : (sptWf ((.bn (.bn (.ls 7) .ln) (.bs (.ls 7) 9 (.ls 7))) : Spt Nat),sptIsEmpty ((.bn (.bn (.ls 7) .ln) (.bs (.ls 7) 9 (.ls 7))) : Spt Nat)) = (true,false) := by rfl
-- sw_tree_52
example : (sptWf ((.bn (.bn (.ls 7) (.ls 7)) .ln) : Spt Nat),sptIsEmpty ((.bn (.bn (.ls 7) (.ls 7)) .ln) : Spt Nat)) = (true,false) := by rfl
-- sw_tree_53
example : (sptWf ((.bn (.bn (.ls 7) (.ls 7)) (.ls 7)) : Spt Nat),sptIsEmpty ((.bn (.bn (.ls 7) (.ls 7)) (.ls 7)) : Spt Nat)) = (true,false) := by rfl
-- sw_tree_54
example : (sptWf ((.bn (.bn (.ls 7) (.ls 7)) (.bn .ln .ln)) : Spt Nat),sptIsEmpty ((.bn (.bn (.ls 7) (.ls 7)) (.bn .ln .ln)) : Spt Nat)) = (false,false) := by rfl
-- sw_tree_55
example : (sptWf ((.bn (.bn (.ls 7) (.ls 7)) (.bn .ln (.ls 7))) : Spt Nat),sptIsEmpty ((.bn (.bn (.ls 7) (.ls 7)) (.bn .ln (.ls 7))) : Spt Nat)) = (true,false) := by rfl
-- sw_tree_56
example : (sptWf ((.bn (.bn (.ls 7) (.ls 7)) (.bn (.ls 7) .ln)) : Spt Nat),sptIsEmpty ((.bn (.bn (.ls 7) (.ls 7)) (.bn (.ls 7) .ln)) : Spt Nat)) = (true,false) := by rfl
-- sw_tree_57
example : (sptWf ((.bn (.bn (.ls 7) (.ls 7)) (.bn (.ls 7) (.ls 7))) : Spt Nat),sptIsEmpty ((.bn (.bn (.ls 7) (.ls 7)) (.bn (.ls 7) (.ls 7))) : Spt Nat)) = (true,false) := by rfl
-- sw_tree_58
example : (sptWf ((.bn (.bn (.ls 7) (.ls 7)) (.bs .ln 9 .ln)) : Spt Nat),sptIsEmpty ((.bn (.bn (.ls 7) (.ls 7)) (.bs .ln 9 .ln)) : Spt Nat)) = (false,false) := by rfl
-- sw_tree_59
example : (sptWf ((.bn (.bn (.ls 7) (.ls 7)) (.bs .ln 9 (.ls 7))) : Spt Nat),sptIsEmpty ((.bn (.bn (.ls 7) (.ls 7)) (.bs .ln 9 (.ls 7))) : Spt Nat)) = (true,false) := by rfl
-- sw_tree_60
example : (sptWf ((.bn (.bn (.ls 7) (.ls 7)) (.bs (.ls 7) 9 .ln)) : Spt Nat),sptIsEmpty ((.bn (.bn (.ls 7) (.ls 7)) (.bs (.ls 7) 9 .ln)) : Spt Nat)) = (true,false) := by rfl
-- sw_tree_61
example : (sptWf ((.bn (.bn (.ls 7) (.ls 7)) (.bs (.ls 7) 9 (.ls 7))) : Spt Nat),sptIsEmpty ((.bn (.bn (.ls 7) (.ls 7)) (.bs (.ls 7) 9 (.ls 7))) : Spt Nat)) = (true,false) := by rfl
-- sw_tree_62
example : (sptWf ((.bn (.bs .ln 9 .ln) .ln) : Spt Nat),sptIsEmpty ((.bn (.bs .ln 9 .ln) .ln) : Spt Nat)) = (false,false) := by rfl
-- sw_tree_63
example : (sptWf ((.bn (.bs .ln 9 .ln) (.ls 7)) : Spt Nat),sptIsEmpty ((.bn (.bs .ln 9 .ln) (.ls 7)) : Spt Nat)) = (false,false) := by rfl
-- sw_tree_64
example : (sptWf ((.bn (.bs .ln 9 .ln) (.bn .ln .ln)) : Spt Nat),sptIsEmpty ((.bn (.bs .ln 9 .ln) (.bn .ln .ln)) : Spt Nat)) = (false,false) := by rfl
-- sw_tree_65
example : (sptWf ((.bn (.bs .ln 9 .ln) (.bn .ln (.ls 7))) : Spt Nat),sptIsEmpty ((.bn (.bs .ln 9 .ln) (.bn .ln (.ls 7))) : Spt Nat)) = (false,false) := by rfl
-- sw_tree_66
example : (sptWf ((.bn (.bs .ln 9 .ln) (.bn (.ls 7) .ln)) : Spt Nat),sptIsEmpty ((.bn (.bs .ln 9 .ln) (.bn (.ls 7) .ln)) : Spt Nat)) = (false,false) := by rfl
-- sw_tree_67
example : (sptWf ((.bn (.bs .ln 9 .ln) (.bn (.ls 7) (.ls 7))) : Spt Nat),sptIsEmpty ((.bn (.bs .ln 9 .ln) (.bn (.ls 7) (.ls 7))) : Spt Nat)) = (false,false) := by rfl
-- sw_tree_68
example : (sptWf ((.bn (.bs .ln 9 .ln) (.bs .ln 9 .ln)) : Spt Nat),sptIsEmpty ((.bn (.bs .ln 9 .ln) (.bs .ln 9 .ln)) : Spt Nat)) = (false,false) := by rfl
-- sw_tree_69
example : (sptWf ((.bn (.bs .ln 9 .ln) (.bs .ln 9 (.ls 7))) : Spt Nat),sptIsEmpty ((.bn (.bs .ln 9 .ln) (.bs .ln 9 (.ls 7))) : Spt Nat)) = (false,false) := by rfl
-- sw_tree_70
example : (sptWf ((.bn (.bs .ln 9 .ln) (.bs (.ls 7) 9 .ln)) : Spt Nat),sptIsEmpty ((.bn (.bs .ln 9 .ln) (.bs (.ls 7) 9 .ln)) : Spt Nat)) = (false,false) := by rfl
-- sw_tree_71
example : (sptWf ((.bn (.bs .ln 9 .ln) (.bs (.ls 7) 9 (.ls 7))) : Spt Nat),sptIsEmpty ((.bn (.bs .ln 9 .ln) (.bs (.ls 7) 9 (.ls 7))) : Spt Nat)) = (false,false) := by rfl
-- sw_tree_72
example : (sptWf ((.bn (.bs .ln 9 (.ls 7)) .ln) : Spt Nat),sptIsEmpty ((.bn (.bs .ln 9 (.ls 7)) .ln) : Spt Nat)) = (true,false) := by rfl
-- sw_tree_73
example : (sptWf ((.bn (.bs .ln 9 (.ls 7)) (.ls 7)) : Spt Nat),sptIsEmpty ((.bn (.bs .ln 9 (.ls 7)) (.ls 7)) : Spt Nat)) = (true,false) := by rfl
-- sw_tree_74
example : (sptWf ((.bn (.bs .ln 9 (.ls 7)) (.bn .ln .ln)) : Spt Nat),sptIsEmpty ((.bn (.bs .ln 9 (.ls 7)) (.bn .ln .ln)) : Spt Nat)) = (false,false) := by rfl
-- sw_tree_75
example : (sptWf ((.bn (.bs .ln 9 (.ls 7)) (.bn .ln (.ls 7))) : Spt Nat),sptIsEmpty ((.bn (.bs .ln 9 (.ls 7)) (.bn .ln (.ls 7))) : Spt Nat)) = (true,false) := by rfl
-- sw_tree_76
example : (sptWf ((.bn (.bs .ln 9 (.ls 7)) (.bn (.ls 7) .ln)) : Spt Nat),sptIsEmpty ((.bn (.bs .ln 9 (.ls 7)) (.bn (.ls 7) .ln)) : Spt Nat)) = (true,false) := by rfl
-- sw_tree_77
example : (sptWf ((.bn (.bs .ln 9 (.ls 7)) (.bn (.ls 7) (.ls 7))) : Spt Nat),sptIsEmpty ((.bn (.bs .ln 9 (.ls 7)) (.bn (.ls 7) (.ls 7))) : Spt Nat)) = (true,false) := by rfl
-- sw_tree_78
example : (sptWf ((.bn (.bs .ln 9 (.ls 7)) (.bs .ln 9 .ln)) : Spt Nat),sptIsEmpty ((.bn (.bs .ln 9 (.ls 7)) (.bs .ln 9 .ln)) : Spt Nat)) = (false,false) := by rfl
-- sw_tree_79
example : (sptWf ((.bn (.bs .ln 9 (.ls 7)) (.bs .ln 9 (.ls 7))) : Spt Nat),sptIsEmpty ((.bn (.bs .ln 9 (.ls 7)) (.bs .ln 9 (.ls 7))) : Spt Nat)) = (true,false) := by rfl
-- sw_tree_80
example : (sptWf ((.bn (.bs .ln 9 (.ls 7)) (.bs (.ls 7) 9 .ln)) : Spt Nat),sptIsEmpty ((.bn (.bs .ln 9 (.ls 7)) (.bs (.ls 7) 9 .ln)) : Spt Nat)) = (true,false) := by rfl
-- sw_tree_81
example : (sptWf ((.bn (.bs .ln 9 (.ls 7)) (.bs (.ls 7) 9 (.ls 7))) : Spt Nat),sptIsEmpty ((.bn (.bs .ln 9 (.ls 7)) (.bs (.ls 7) 9 (.ls 7))) : Spt Nat)) = (true,false) := by rfl
-- sw_tree_82
example : (sptWf ((.bn (.bs (.ls 7) 9 .ln) .ln) : Spt Nat),sptIsEmpty ((.bn (.bs (.ls 7) 9 .ln) .ln) : Spt Nat)) = (true,false) := by rfl
-- sw_tree_83
example : (sptWf ((.bn (.bs (.ls 7) 9 .ln) (.ls 7)) : Spt Nat),sptIsEmpty ((.bn (.bs (.ls 7) 9 .ln) (.ls 7)) : Spt Nat)) = (true,false) := by rfl
-- sw_tree_84
example : (sptWf ((.bn (.bs (.ls 7) 9 .ln) (.bn .ln .ln)) : Spt Nat),sptIsEmpty ((.bn (.bs (.ls 7) 9 .ln) (.bn .ln .ln)) : Spt Nat)) = (false,false) := by rfl
-- sw_tree_85
example : (sptWf ((.bn (.bs (.ls 7) 9 .ln) (.bn .ln (.ls 7))) : Spt Nat),sptIsEmpty ((.bn (.bs (.ls 7) 9 .ln) (.bn .ln (.ls 7))) : Spt Nat)) = (true,false) := by rfl
-- sw_tree_86
example : (sptWf ((.bn (.bs (.ls 7) 9 .ln) (.bn (.ls 7) .ln)) : Spt Nat),sptIsEmpty ((.bn (.bs (.ls 7) 9 .ln) (.bn (.ls 7) .ln)) : Spt Nat)) = (true,false) := by rfl
-- sw_tree_87
example : (sptWf ((.bn (.bs (.ls 7) 9 .ln) (.bn (.ls 7) (.ls 7))) : Spt Nat),sptIsEmpty ((.bn (.bs (.ls 7) 9 .ln) (.bn (.ls 7) (.ls 7))) : Spt Nat)) = (true,false) := by rfl
-- sw_tree_88
example : (sptWf ((.bn (.bs (.ls 7) 9 .ln) (.bs .ln 9 .ln)) : Spt Nat),sptIsEmpty ((.bn (.bs (.ls 7) 9 .ln) (.bs .ln 9 .ln)) : Spt Nat)) = (false,false) := by rfl
-- sw_tree_89
example : (sptWf ((.bn (.bs (.ls 7) 9 .ln) (.bs .ln 9 (.ls 7))) : Spt Nat),sptIsEmpty ((.bn (.bs (.ls 7) 9 .ln) (.bs .ln 9 (.ls 7))) : Spt Nat)) = (true,false) := by rfl
-- sw_tree_90
example : (sptWf ((.bn (.bs (.ls 7) 9 .ln) (.bs (.ls 7) 9 .ln)) : Spt Nat),sptIsEmpty ((.bn (.bs (.ls 7) 9 .ln) (.bs (.ls 7) 9 .ln)) : Spt Nat)) = (true,false) := by rfl
-- sw_tree_91
example : (sptWf ((.bn (.bs (.ls 7) 9 .ln) (.bs (.ls 7) 9 (.ls 7))) : Spt Nat),sptIsEmpty ((.bn (.bs (.ls 7) 9 .ln) (.bs (.ls 7) 9 (.ls 7))) : Spt Nat)) = (true,false) := by rfl
-- sw_tree_92
example : (sptWf ((.bn (.bs (.ls 7) 9 (.ls 7)) .ln) : Spt Nat),sptIsEmpty ((.bn (.bs (.ls 7) 9 (.ls 7)) .ln) : Spt Nat)) = (true,false) := by rfl
-- sw_tree_93
example : (sptWf ((.bn (.bs (.ls 7) 9 (.ls 7)) (.ls 7)) : Spt Nat),sptIsEmpty ((.bn (.bs (.ls 7) 9 (.ls 7)) (.ls 7)) : Spt Nat)) = (true,false) := by rfl
-- sw_tree_94
example : (sptWf ((.bn (.bs (.ls 7) 9 (.ls 7)) (.bn .ln .ln)) : Spt Nat),sptIsEmpty ((.bn (.bs (.ls 7) 9 (.ls 7)) (.bn .ln .ln)) : Spt Nat)) = (false,false) := by rfl
-- sw_tree_95
example : (sptWf ((.bn (.bs (.ls 7) 9 (.ls 7)) (.bn .ln (.ls 7))) : Spt Nat),sptIsEmpty ((.bn (.bs (.ls 7) 9 (.ls 7)) (.bn .ln (.ls 7))) : Spt Nat)) = (true,false) := by rfl
-- sw_tree_96
example : (sptWf ((.bn (.bs (.ls 7) 9 (.ls 7)) (.bn (.ls 7) .ln)) : Spt Nat),sptIsEmpty ((.bn (.bs (.ls 7) 9 (.ls 7)) (.bn (.ls 7) .ln)) : Spt Nat)) = (true,false) := by rfl
-- sw_tree_97
example : (sptWf ((.bn (.bs (.ls 7) 9 (.ls 7)) (.bn (.ls 7) (.ls 7))) : Spt Nat),sptIsEmpty ((.bn (.bs (.ls 7) 9 (.ls 7)) (.bn (.ls 7) (.ls 7))) : Spt Nat)) = (true,false) := by rfl
-- sw_tree_98
example : (sptWf ((.bn (.bs (.ls 7) 9 (.ls 7)) (.bs .ln 9 .ln)) : Spt Nat),sptIsEmpty ((.bn (.bs (.ls 7) 9 (.ls 7)) (.bs .ln 9 .ln)) : Spt Nat)) = (false,false) := by rfl
-- sw_tree_99
example : (sptWf ((.bn (.bs (.ls 7) 9 (.ls 7)) (.bs .ln 9 (.ls 7))) : Spt Nat),sptIsEmpty ((.bn (.bs (.ls 7) 9 (.ls 7)) (.bs .ln 9 (.ls 7))) : Spt Nat)) = (true,false) := by rfl
-- sw_tree_100
example : (sptWf ((.bn (.bs (.ls 7) 9 (.ls 7)) (.bs (.ls 7) 9 .ln)) : Spt Nat),sptIsEmpty ((.bn (.bs (.ls 7) 9 (.ls 7)) (.bs (.ls 7) 9 .ln)) : Spt Nat)) = (true,false) := by rfl
-- sw_tree_101
example : (sptWf ((.bn (.bs (.ls 7) 9 (.ls 7)) (.bs (.ls 7) 9 (.ls 7))) : Spt Nat),sptIsEmpty ((.bn (.bs (.ls 7) 9 (.ls 7)) (.bs (.ls 7) 9 (.ls 7))) : Spt Nat)) = (true,false) := by rfl
-- sw_tree_102
example : (sptWf ((.bs .ln 9 .ln) : Spt Nat),sptIsEmpty ((.bs .ln 9 .ln) : Spt Nat)) = (false,false) := by rfl
-- sw_tree_103
example : (sptWf ((.bs .ln 9 (.ls 7)) : Spt Nat),sptIsEmpty ((.bs .ln 9 (.ls 7)) : Spt Nat)) = (true,false) := by rfl
-- sw_tree_104
example : (sptWf ((.bs .ln 9 (.bn .ln .ln)) : Spt Nat),sptIsEmpty ((.bs .ln 9 (.bn .ln .ln)) : Spt Nat)) = (false,false) := by rfl
-- sw_tree_105
example : (sptWf ((.bs .ln 9 (.bn .ln (.ls 7))) : Spt Nat),sptIsEmpty ((.bs .ln 9 (.bn .ln (.ls 7))) : Spt Nat)) = (true,false) := by rfl
-- sw_tree_106
example : (sptWf ((.bs .ln 9 (.bn (.ls 7) .ln)) : Spt Nat),sptIsEmpty ((.bs .ln 9 (.bn (.ls 7) .ln)) : Spt Nat)) = (true,false) := by rfl
-- sw_tree_107
example : (sptWf ((.bs .ln 9 (.bn (.ls 7) (.ls 7))) : Spt Nat),sptIsEmpty ((.bs .ln 9 (.bn (.ls 7) (.ls 7))) : Spt Nat)) = (true,false) := by rfl
-- sw_tree_108
example : (sptWf ((.bs .ln 9 (.bs .ln 9 .ln)) : Spt Nat),sptIsEmpty ((.bs .ln 9 (.bs .ln 9 .ln)) : Spt Nat)) = (false,false) := by rfl
-- sw_tree_109
example : (sptWf ((.bs .ln 9 (.bs .ln 9 (.ls 7))) : Spt Nat),sptIsEmpty ((.bs .ln 9 (.bs .ln 9 (.ls 7))) : Spt Nat)) = (true,false) := by rfl
-- sw_tree_110
example : (sptWf ((.bs .ln 9 (.bs (.ls 7) 9 .ln)) : Spt Nat),sptIsEmpty ((.bs .ln 9 (.bs (.ls 7) 9 .ln)) : Spt Nat)) = (true,false) := by rfl
-- sw_tree_111
example : (sptWf ((.bs .ln 9 (.bs (.ls 7) 9 (.ls 7))) : Spt Nat),sptIsEmpty ((.bs .ln 9 (.bs (.ls 7) 9 (.ls 7))) : Spt Nat)) = (true,false) := by rfl
-- sw_tree_112
example : (sptWf ((.bs (.ls 7) 9 .ln) : Spt Nat),sptIsEmpty ((.bs (.ls 7) 9 .ln) : Spt Nat)) = (true,false) := by rfl
-- sw_tree_113
example : (sptWf ((.bs (.ls 7) 9 (.ls 7)) : Spt Nat),sptIsEmpty ((.bs (.ls 7) 9 (.ls 7)) : Spt Nat)) = (true,false) := by rfl
-- sw_tree_114
example : (sptWf ((.bs (.ls 7) 9 (.bn .ln .ln)) : Spt Nat),sptIsEmpty ((.bs (.ls 7) 9 (.bn .ln .ln)) : Spt Nat)) = (false,false) := by rfl
-- sw_tree_115
example : (sptWf ((.bs (.ls 7) 9 (.bn .ln (.ls 7))) : Spt Nat),sptIsEmpty ((.bs (.ls 7) 9 (.bn .ln (.ls 7))) : Spt Nat)) = (true,false) := by rfl
-- sw_tree_116
example : (sptWf ((.bs (.ls 7) 9 (.bn (.ls 7) .ln)) : Spt Nat),sptIsEmpty ((.bs (.ls 7) 9 (.bn (.ls 7) .ln)) : Spt Nat)) = (true,false) := by rfl
-- sw_tree_117
example : (sptWf ((.bs (.ls 7) 9 (.bn (.ls 7) (.ls 7))) : Spt Nat),sptIsEmpty ((.bs (.ls 7) 9 (.bn (.ls 7) (.ls 7))) : Spt Nat)) = (true,false) := by rfl
-- sw_tree_118
example : (sptWf ((.bs (.ls 7) 9 (.bs .ln 9 .ln)) : Spt Nat),sptIsEmpty ((.bs (.ls 7) 9 (.bs .ln 9 .ln)) : Spt Nat)) = (false,false) := by rfl
-- sw_tree_119
example : (sptWf ((.bs (.ls 7) 9 (.bs .ln 9 (.ls 7))) : Spt Nat),sptIsEmpty ((.bs (.ls 7) 9 (.bs .ln 9 (.ls 7))) : Spt Nat)) = (true,false) := by rfl
-- sw_tree_120
example : (sptWf ((.bs (.ls 7) 9 (.bs (.ls 7) 9 .ln)) : Spt Nat),sptIsEmpty ((.bs (.ls 7) 9 (.bs (.ls 7) 9 .ln)) : Spt Nat)) = (true,false) := by rfl
-- sw_tree_121
example : (sptWf ((.bs (.ls 7) 9 (.bs (.ls 7) 9 (.ls 7))) : Spt Nat),sptIsEmpty ((.bs (.ls 7) 9 (.bs (.ls 7) 9 (.ls 7))) : Spt Nat)) = (true,false) := by rfl
-- sw_tree_122
example : (sptWf ((.bs (.bn .ln .ln) 9 .ln) : Spt Nat),sptIsEmpty ((.bs (.bn .ln .ln) 9 .ln) : Spt Nat)) = (false,false) := by rfl
-- sw_tree_123
example : (sptWf ((.bs (.bn .ln .ln) 9 (.ls 7)) : Spt Nat),sptIsEmpty ((.bs (.bn .ln .ln) 9 (.ls 7)) : Spt Nat)) = (false,false) := by rfl
-- sw_tree_124
example : (sptWf ((.bs (.bn .ln .ln) 9 (.bn .ln .ln)) : Spt Nat),sptIsEmpty ((.bs (.bn .ln .ln) 9 (.bn .ln .ln)) : Spt Nat)) = (false,false) := by rfl
-- sw_tree_125
example : (sptWf ((.bs (.bn .ln .ln) 9 (.bn .ln (.ls 7))) : Spt Nat),sptIsEmpty ((.bs (.bn .ln .ln) 9 (.bn .ln (.ls 7))) : Spt Nat)) = (false,false) := by rfl
-- sw_tree_126
example : (sptWf ((.bs (.bn .ln .ln) 9 (.bn (.ls 7) .ln)) : Spt Nat),sptIsEmpty ((.bs (.bn .ln .ln) 9 (.bn (.ls 7) .ln)) : Spt Nat)) = (false,false) := by rfl
-- sw_tree_127
example : (sptWf ((.bs (.bn .ln .ln) 9 (.bn (.ls 7) (.ls 7))) : Spt Nat),sptIsEmpty ((.bs (.bn .ln .ln) 9 (.bn (.ls 7) (.ls 7))) : Spt Nat)) = (false,false) := by rfl
-- sw_tree_128
example : (sptWf ((.bs (.bn .ln .ln) 9 (.bs .ln 9 .ln)) : Spt Nat),sptIsEmpty ((.bs (.bn .ln .ln) 9 (.bs .ln 9 .ln)) : Spt Nat)) = (false,false) := by rfl
-- sw_tree_129
example : (sptWf ((.bs (.bn .ln .ln) 9 (.bs .ln 9 (.ls 7))) : Spt Nat),sptIsEmpty ((.bs (.bn .ln .ln) 9 (.bs .ln 9 (.ls 7))) : Spt Nat)) = (false,false) := by rfl
-- sw_tree_130
example : (sptWf ((.bs (.bn .ln .ln) 9 (.bs (.ls 7) 9 .ln)) : Spt Nat),sptIsEmpty ((.bs (.bn .ln .ln) 9 (.bs (.ls 7) 9 .ln)) : Spt Nat)) = (false,false) := by rfl
-- sw_tree_131
example : (sptWf ((.bs (.bn .ln .ln) 9 (.bs (.ls 7) 9 (.ls 7))) : Spt Nat),sptIsEmpty ((.bs (.bn .ln .ln) 9 (.bs (.ls 7) 9 (.ls 7))) : Spt Nat)) = (false,false) := by rfl
-- sw_tree_132
example : (sptWf ((.bs (.bn .ln (.ls 7)) 9 .ln) : Spt Nat),sptIsEmpty ((.bs (.bn .ln (.ls 7)) 9 .ln) : Spt Nat)) = (true,false) := by rfl
-- sw_tree_133
example : (sptWf ((.bs (.bn .ln (.ls 7)) 9 (.ls 7)) : Spt Nat),sptIsEmpty ((.bs (.bn .ln (.ls 7)) 9 (.ls 7)) : Spt Nat)) = (true,false) := by rfl
-- sw_tree_134
example : (sptWf ((.bs (.bn .ln (.ls 7)) 9 (.bn .ln .ln)) : Spt Nat),sptIsEmpty ((.bs (.bn .ln (.ls 7)) 9 (.bn .ln .ln)) : Spt Nat)) = (false,false) := by rfl
-- sw_tree_135
example : (sptWf ((.bs (.bn .ln (.ls 7)) 9 (.bn .ln (.ls 7))) : Spt Nat),sptIsEmpty ((.bs (.bn .ln (.ls 7)) 9 (.bn .ln (.ls 7))) : Spt Nat)) = (true,false) := by rfl
-- sw_tree_136
example : (sptWf ((.bs (.bn .ln (.ls 7)) 9 (.bn (.ls 7) .ln)) : Spt Nat),sptIsEmpty ((.bs (.bn .ln (.ls 7)) 9 (.bn (.ls 7) .ln)) : Spt Nat)) = (true,false) := by rfl
-- sw_tree_137
example : (sptWf ((.bs (.bn .ln (.ls 7)) 9 (.bn (.ls 7) (.ls 7))) : Spt Nat),sptIsEmpty ((.bs (.bn .ln (.ls 7)) 9 (.bn (.ls 7) (.ls 7))) : Spt Nat)) = (true,false) := by rfl
-- sw_tree_138
example : (sptWf ((.bs (.bn .ln (.ls 7)) 9 (.bs .ln 9 .ln)) : Spt Nat),sptIsEmpty ((.bs (.bn .ln (.ls 7)) 9 (.bs .ln 9 .ln)) : Spt Nat)) = (false,false) := by rfl
-- sw_tree_139
example : (sptWf ((.bs (.bn .ln (.ls 7)) 9 (.bs .ln 9 (.ls 7))) : Spt Nat),sptIsEmpty ((.bs (.bn .ln (.ls 7)) 9 (.bs .ln 9 (.ls 7))) : Spt Nat)) = (true,false) := by rfl
-- sw_tree_140
example : (sptWf ((.bs (.bn .ln (.ls 7)) 9 (.bs (.ls 7) 9 .ln)) : Spt Nat),sptIsEmpty ((.bs (.bn .ln (.ls 7)) 9 (.bs (.ls 7) 9 .ln)) : Spt Nat)) = (true,false) := by rfl
-- sw_tree_141
example : (sptWf ((.bs (.bn .ln (.ls 7)) 9 (.bs (.ls 7) 9 (.ls 7))) : Spt Nat),sptIsEmpty ((.bs (.bn .ln (.ls 7)) 9 (.bs (.ls 7) 9 (.ls 7))) : Spt Nat)) = (true,false) := by rfl
-- sw_tree_142
example : (sptWf ((.bs (.bn (.ls 7) .ln) 9 .ln) : Spt Nat),sptIsEmpty ((.bs (.bn (.ls 7) .ln) 9 .ln) : Spt Nat)) = (true,false) := by rfl
-- sw_tree_143
example : (sptWf ((.bs (.bn (.ls 7) .ln) 9 (.ls 7)) : Spt Nat),sptIsEmpty ((.bs (.bn (.ls 7) .ln) 9 (.ls 7)) : Spt Nat)) = (true,false) := by rfl
-- sw_tree_144
example : (sptWf ((.bs (.bn (.ls 7) .ln) 9 (.bn .ln .ln)) : Spt Nat),sptIsEmpty ((.bs (.bn (.ls 7) .ln) 9 (.bn .ln .ln)) : Spt Nat)) = (false,false) := by rfl
-- sw_tree_145
example : (sptWf ((.bs (.bn (.ls 7) .ln) 9 (.bn .ln (.ls 7))) : Spt Nat),sptIsEmpty ((.bs (.bn (.ls 7) .ln) 9 (.bn .ln (.ls 7))) : Spt Nat)) = (true,false) := by rfl
-- sw_tree_146
example : (sptWf ((.bs (.bn (.ls 7) .ln) 9 (.bn (.ls 7) .ln)) : Spt Nat),sptIsEmpty ((.bs (.bn (.ls 7) .ln) 9 (.bn (.ls 7) .ln)) : Spt Nat)) = (true,false) := by rfl
-- sw_tree_147
example : (sptWf ((.bs (.bn (.ls 7) .ln) 9 (.bn (.ls 7) (.ls 7))) : Spt Nat),sptIsEmpty ((.bs (.bn (.ls 7) .ln) 9 (.bn (.ls 7) (.ls 7))) : Spt Nat)) = (true,false) := by rfl
-- sw_tree_148
example : (sptWf ((.bs (.bn (.ls 7) .ln) 9 (.bs .ln 9 .ln)) : Spt Nat),sptIsEmpty ((.bs (.bn (.ls 7) .ln) 9 (.bs .ln 9 .ln)) : Spt Nat)) = (false,false) := by rfl
-- sw_tree_149
example : (sptWf ((.bs (.bn (.ls 7) .ln) 9 (.bs .ln 9 (.ls 7))) : Spt Nat),sptIsEmpty ((.bs (.bn (.ls 7) .ln) 9 (.bs .ln 9 (.ls 7))) : Spt Nat)) = (true,false) := by rfl
-- sw_tree_150
example : (sptWf ((.bs (.bn (.ls 7) .ln) 9 (.bs (.ls 7) 9 .ln)) : Spt Nat),sptIsEmpty ((.bs (.bn (.ls 7) .ln) 9 (.bs (.ls 7) 9 .ln)) : Spt Nat)) = (true,false) := by rfl
-- sw_tree_151
example : (sptWf ((.bs (.bn (.ls 7) .ln) 9 (.bs (.ls 7) 9 (.ls 7))) : Spt Nat),sptIsEmpty ((.bs (.bn (.ls 7) .ln) 9 (.bs (.ls 7) 9 (.ls 7))) : Spt Nat)) = (true,false) := by rfl
-- sw_tree_152
example : (sptWf ((.bs (.bn (.ls 7) (.ls 7)) 9 .ln) : Spt Nat),sptIsEmpty ((.bs (.bn (.ls 7) (.ls 7)) 9 .ln) : Spt Nat)) = (true,false) := by rfl
-- sw_tree_153
example : (sptWf ((.bs (.bn (.ls 7) (.ls 7)) 9 (.ls 7)) : Spt Nat),sptIsEmpty ((.bs (.bn (.ls 7) (.ls 7)) 9 (.ls 7)) : Spt Nat)) = (true,false) := by rfl
-- sw_tree_154
example : (sptWf ((.bs (.bn (.ls 7) (.ls 7)) 9 (.bn .ln .ln)) : Spt Nat),sptIsEmpty ((.bs (.bn (.ls 7) (.ls 7)) 9 (.bn .ln .ln)) : Spt Nat)) = (false,false) := by rfl
-- sw_tree_155
example : (sptWf ((.bs (.bn (.ls 7) (.ls 7)) 9 (.bn .ln (.ls 7))) : Spt Nat),sptIsEmpty ((.bs (.bn (.ls 7) (.ls 7)) 9 (.bn .ln (.ls 7))) : Spt Nat)) = (true,false) := by rfl
-- sw_tree_156
example : (sptWf ((.bs (.bn (.ls 7) (.ls 7)) 9 (.bn (.ls 7) .ln)) : Spt Nat),sptIsEmpty ((.bs (.bn (.ls 7) (.ls 7)) 9 (.bn (.ls 7) .ln)) : Spt Nat)) = (true,false) := by rfl
-- sw_tree_157
example : (sptWf ((.bs (.bn (.ls 7) (.ls 7)) 9 (.bn (.ls 7) (.ls 7))) : Spt Nat),sptIsEmpty ((.bs (.bn (.ls 7) (.ls 7)) 9 (.bn (.ls 7) (.ls 7))) : Spt Nat)) = (true,false) := by rfl
-- sw_tree_158
example : (sptWf ((.bs (.bn (.ls 7) (.ls 7)) 9 (.bs .ln 9 .ln)) : Spt Nat),sptIsEmpty ((.bs (.bn (.ls 7) (.ls 7)) 9 (.bs .ln 9 .ln)) : Spt Nat)) = (false,false) := by rfl
-- sw_tree_159
example : (sptWf ((.bs (.bn (.ls 7) (.ls 7)) 9 (.bs .ln 9 (.ls 7))) : Spt Nat),sptIsEmpty ((.bs (.bn (.ls 7) (.ls 7)) 9 (.bs .ln 9 (.ls 7))) : Spt Nat)) = (true,false) := by rfl
-- sw_tree_160
example : (sptWf ((.bs (.bn (.ls 7) (.ls 7)) 9 (.bs (.ls 7) 9 .ln)) : Spt Nat),sptIsEmpty ((.bs (.bn (.ls 7) (.ls 7)) 9 (.bs (.ls 7) 9 .ln)) : Spt Nat)) = (true,false) := by rfl
-- sw_tree_161
example : (sptWf ((.bs (.bn (.ls 7) (.ls 7)) 9 (.bs (.ls 7) 9 (.ls 7))) : Spt Nat),sptIsEmpty ((.bs (.bn (.ls 7) (.ls 7)) 9 (.bs (.ls 7) 9 (.ls 7))) : Spt Nat)) = (true,false) := by rfl
-- sw_tree_162
example : (sptWf ((.bs (.bs .ln 9 .ln) 9 .ln) : Spt Nat),sptIsEmpty ((.bs (.bs .ln 9 .ln) 9 .ln) : Spt Nat)) = (false,false) := by rfl
-- sw_tree_163
example : (sptWf ((.bs (.bs .ln 9 .ln) 9 (.ls 7)) : Spt Nat),sptIsEmpty ((.bs (.bs .ln 9 .ln) 9 (.ls 7)) : Spt Nat)) = (false,false) := by rfl
-- sw_tree_164
example : (sptWf ((.bs (.bs .ln 9 .ln) 9 (.bn .ln .ln)) : Spt Nat),sptIsEmpty ((.bs (.bs .ln 9 .ln) 9 (.bn .ln .ln)) : Spt Nat)) = (false,false) := by rfl
-- sw_tree_165
example : (sptWf ((.bs (.bs .ln 9 .ln) 9 (.bn .ln (.ls 7))) : Spt Nat),sptIsEmpty ((.bs (.bs .ln 9 .ln) 9 (.bn .ln (.ls 7))) : Spt Nat)) = (false,false) := by rfl
-- sw_tree_166
example : (sptWf ((.bs (.bs .ln 9 .ln) 9 (.bn (.ls 7) .ln)) : Spt Nat),sptIsEmpty ((.bs (.bs .ln 9 .ln) 9 (.bn (.ls 7) .ln)) : Spt Nat)) = (false,false) := by rfl
-- sw_tree_167
example : (sptWf ((.bs (.bs .ln 9 .ln) 9 (.bn (.ls 7) (.ls 7))) : Spt Nat),sptIsEmpty ((.bs (.bs .ln 9 .ln) 9 (.bn (.ls 7) (.ls 7))) : Spt Nat)) = (false,false) := by rfl
-- sw_tree_168
example : (sptWf ((.bs (.bs .ln 9 .ln) 9 (.bs .ln 9 .ln)) : Spt Nat),sptIsEmpty ((.bs (.bs .ln 9 .ln) 9 (.bs .ln 9 .ln)) : Spt Nat)) = (false,false) := by rfl
-- sw_tree_169
example : (sptWf ((.bs (.bs .ln 9 .ln) 9 (.bs .ln 9 (.ls 7))) : Spt Nat),sptIsEmpty ((.bs (.bs .ln 9 .ln) 9 (.bs .ln 9 (.ls 7))) : Spt Nat)) = (false,false) := by rfl
-- sw_tree_170
example : (sptWf ((.bs (.bs .ln 9 .ln) 9 (.bs (.ls 7) 9 .ln)) : Spt Nat),sptIsEmpty ((.bs (.bs .ln 9 .ln) 9 (.bs (.ls 7) 9 .ln)) : Spt Nat)) = (false,false) := by rfl
-- sw_tree_171
example : (sptWf ((.bs (.bs .ln 9 .ln) 9 (.bs (.ls 7) 9 (.ls 7))) : Spt Nat),sptIsEmpty ((.bs (.bs .ln 9 .ln) 9 (.bs (.ls 7) 9 (.ls 7))) : Spt Nat)) = (false,false) := by rfl
-- sw_tree_172
example : (sptWf ((.bs (.bs .ln 9 (.ls 7)) 9 .ln) : Spt Nat),sptIsEmpty ((.bs (.bs .ln 9 (.ls 7)) 9 .ln) : Spt Nat)) = (true,false) := by rfl
-- sw_tree_173
example : (sptWf ((.bs (.bs .ln 9 (.ls 7)) 9 (.ls 7)) : Spt Nat),sptIsEmpty ((.bs (.bs .ln 9 (.ls 7)) 9 (.ls 7)) : Spt Nat)) = (true,false) := by rfl
-- sw_tree_174
example : (sptWf ((.bs (.bs .ln 9 (.ls 7)) 9 (.bn .ln .ln)) : Spt Nat),sptIsEmpty ((.bs (.bs .ln 9 (.ls 7)) 9 (.bn .ln .ln)) : Spt Nat)) = (false,false) := by rfl
-- sw_tree_175
example : (sptWf ((.bs (.bs .ln 9 (.ls 7)) 9 (.bn .ln (.ls 7))) : Spt Nat),sptIsEmpty ((.bs (.bs .ln 9 (.ls 7)) 9 (.bn .ln (.ls 7))) : Spt Nat)) = (true,false) := by rfl
-- sw_tree_176
example : (sptWf ((.bs (.bs .ln 9 (.ls 7)) 9 (.bn (.ls 7) .ln)) : Spt Nat),sptIsEmpty ((.bs (.bs .ln 9 (.ls 7)) 9 (.bn (.ls 7) .ln)) : Spt Nat)) = (true,false) := by rfl
-- sw_tree_177
example : (sptWf ((.bs (.bs .ln 9 (.ls 7)) 9 (.bn (.ls 7) (.ls 7))) : Spt Nat),sptIsEmpty ((.bs (.bs .ln 9 (.ls 7)) 9 (.bn (.ls 7) (.ls 7))) : Spt Nat)) = (true,false) := by rfl
-- sw_tree_178
example : (sptWf ((.bs (.bs .ln 9 (.ls 7)) 9 (.bs .ln 9 .ln)) : Spt Nat),sptIsEmpty ((.bs (.bs .ln 9 (.ls 7)) 9 (.bs .ln 9 .ln)) : Spt Nat)) = (false,false) := by rfl
-- sw_tree_179
example : (sptWf ((.bs (.bs .ln 9 (.ls 7)) 9 (.bs .ln 9 (.ls 7))) : Spt Nat),sptIsEmpty ((.bs (.bs .ln 9 (.ls 7)) 9 (.bs .ln 9 (.ls 7))) : Spt Nat)) = (true,false) := by rfl
-- sw_tree_180
example : (sptWf ((.bs (.bs .ln 9 (.ls 7)) 9 (.bs (.ls 7) 9 .ln)) : Spt Nat),sptIsEmpty ((.bs (.bs .ln 9 (.ls 7)) 9 (.bs (.ls 7) 9 .ln)) : Spt Nat)) = (true,false) := by rfl
-- sw_tree_181
example : (sptWf ((.bs (.bs .ln 9 (.ls 7)) 9 (.bs (.ls 7) 9 (.ls 7))) : Spt Nat),sptIsEmpty ((.bs (.bs .ln 9 (.ls 7)) 9 (.bs (.ls 7) 9 (.ls 7))) : Spt Nat)) = (true,false) := by rfl
-- sw_tree_182
example : (sptWf ((.bs (.bs (.ls 7) 9 .ln) 9 .ln) : Spt Nat),sptIsEmpty ((.bs (.bs (.ls 7) 9 .ln) 9 .ln) : Spt Nat)) = (true,false) := by rfl
-- sw_tree_183
example : (sptWf ((.bs (.bs (.ls 7) 9 .ln) 9 (.ls 7)) : Spt Nat),sptIsEmpty ((.bs (.bs (.ls 7) 9 .ln) 9 (.ls 7)) : Spt Nat)) = (true,false) := by rfl
-- sw_tree_184
example : (sptWf ((.bs (.bs (.ls 7) 9 .ln) 9 (.bn .ln .ln)) : Spt Nat),sptIsEmpty ((.bs (.bs (.ls 7) 9 .ln) 9 (.bn .ln .ln)) : Spt Nat)) = (false,false) := by rfl
-- sw_tree_185
example : (sptWf ((.bs (.bs (.ls 7) 9 .ln) 9 (.bn .ln (.ls 7))) : Spt Nat),sptIsEmpty ((.bs (.bs (.ls 7) 9 .ln) 9 (.bn .ln (.ls 7))) : Spt Nat)) = (true,false) := by rfl
-- sw_tree_186
example : (sptWf ((.bs (.bs (.ls 7) 9 .ln) 9 (.bn (.ls 7) .ln)) : Spt Nat),sptIsEmpty ((.bs (.bs (.ls 7) 9 .ln) 9 (.bn (.ls 7) .ln)) : Spt Nat)) = (true,false) := by rfl
-- sw_tree_187
example : (sptWf ((.bs (.bs (.ls 7) 9 .ln) 9 (.bn (.ls 7) (.ls 7))) : Spt Nat),sptIsEmpty ((.bs (.bs (.ls 7) 9 .ln) 9 (.bn (.ls 7) (.ls 7))) : Spt Nat)) = (true,false) := by rfl
-- sw_tree_188
example : (sptWf ((.bs (.bs (.ls 7) 9 .ln) 9 (.bs .ln 9 .ln)) : Spt Nat),sptIsEmpty ((.bs (.bs (.ls 7) 9 .ln) 9 (.bs .ln 9 .ln)) : Spt Nat)) = (false,false) := by rfl
-- sw_tree_189
example : (sptWf ((.bs (.bs (.ls 7) 9 .ln) 9 (.bs .ln 9 (.ls 7))) : Spt Nat),sptIsEmpty ((.bs (.bs (.ls 7) 9 .ln) 9 (.bs .ln 9 (.ls 7))) : Spt Nat)) = (true,false) := by rfl
-- sw_tree_190
example : (sptWf ((.bs (.bs (.ls 7) 9 .ln) 9 (.bs (.ls 7) 9 .ln)) : Spt Nat),sptIsEmpty ((.bs (.bs (.ls 7) 9 .ln) 9 (.bs (.ls 7) 9 .ln)) : Spt Nat)) = (true,false) := by rfl
-- sw_tree_191
example : (sptWf ((.bs (.bs (.ls 7) 9 .ln) 9 (.bs (.ls 7) 9 (.ls 7))) : Spt Nat),sptIsEmpty ((.bs (.bs (.ls 7) 9 .ln) 9 (.bs (.ls 7) 9 (.ls 7))) : Spt Nat)) = (true,false) := by rfl
-- sw_tree_192
example : (sptWf ((.bs (.bs (.ls 7) 9 (.ls 7)) 9 .ln) : Spt Nat),sptIsEmpty ((.bs (.bs (.ls 7) 9 (.ls 7)) 9 .ln) : Spt Nat)) = (true,false) := by rfl
-- sw_tree_193
example : (sptWf ((.bs (.bs (.ls 7) 9 (.ls 7)) 9 (.ls 7)) : Spt Nat),sptIsEmpty ((.bs (.bs (.ls 7) 9 (.ls 7)) 9 (.ls 7)) : Spt Nat)) = (true,false) := by rfl
-- sw_tree_194
example : (sptWf ((.bs (.bs (.ls 7) 9 (.ls 7)) 9 (.bn .ln .ln)) : Spt Nat),sptIsEmpty ((.bs (.bs (.ls 7) 9 (.ls 7)) 9 (.bn .ln .ln)) : Spt Nat)) = (false,false) := by rfl
-- sw_tree_195
example : (sptWf ((.bs (.bs (.ls 7) 9 (.ls 7)) 9 (.bn .ln (.ls 7))) : Spt Nat),sptIsEmpty ((.bs (.bs (.ls 7) 9 (.ls 7)) 9 (.bn .ln (.ls 7))) : Spt Nat)) = (true,false) := by rfl
-- sw_tree_196
example : (sptWf ((.bs (.bs (.ls 7) 9 (.ls 7)) 9 (.bn (.ls 7) .ln)) : Spt Nat),sptIsEmpty ((.bs (.bs (.ls 7) 9 (.ls 7)) 9 (.bn (.ls 7) .ln)) : Spt Nat)) = (true,false) := by rfl
-- sw_tree_197
example : (sptWf ((.bs (.bs (.ls 7) 9 (.ls 7)) 9 (.bn (.ls 7) (.ls 7))) : Spt Nat),sptIsEmpty ((.bs (.bs (.ls 7) 9 (.ls 7)) 9 (.bn (.ls 7) (.ls 7))) : Spt Nat)) = (true,false) := by rfl
-- sw_tree_198
example : (sptWf ((.bs (.bs (.ls 7) 9 (.ls 7)) 9 (.bs .ln 9 .ln)) : Spt Nat),sptIsEmpty ((.bs (.bs (.ls 7) 9 (.ls 7)) 9 (.bs .ln 9 .ln)) : Spt Nat)) = (false,false) := by rfl
-- sw_tree_199
example : (sptWf ((.bs (.bs (.ls 7) 9 (.ls 7)) 9 (.bs .ln 9 (.ls 7))) : Spt Nat),sptIsEmpty ((.bs (.bs (.ls 7) 9 (.ls 7)) 9 (.bs .ln 9 (.ls 7))) : Spt Nat)) = (true,false) := by rfl
-- sw_tree_200
example : (sptWf ((.bs (.bs (.ls 7) 9 (.ls 7)) 9 (.bs (.ls 7) 9 .ln)) : Spt Nat),sptIsEmpty ((.bs (.bs (.ls 7) 9 (.ls 7)) 9 (.bs (.ls 7) 9 .ln)) : Spt Nat)) = (true,false) := by rfl
-- sw_tree_201
example : (sptWf ((.bs (.bs (.ls 7) 9 (.ls 7)) 9 (.bs (.ls 7) 9 (.ls 7))) : Spt Nat),sptIsEmpty ((.bs (.bs (.ls 7) 9 (.ls 7)) 9 (.bs (.ls 7) 9 (.ls 7))) : Spt Nat)) = (true,false) := by rfl
-- sw_tree_202
example : (sptWf ((.bn (.ls 7) .ln) : Spt Nat),sptIsEmpty ((.bn (.ls 7) .ln) : Spt Nat)) = (true,false) := by rfl
-- sw_tree_203
example : (sptWf ((.bs .ln 7 (.bs .ln 9 .ln)) : Spt Nat),sptIsEmpty ((.bs .ln 7 (.bs .ln 9 .ln)) : Spt Nat)) = (false,false) := by rfl
-- sw_tree_204
example : (sptWf ((.bs .ln 7 (.bn (.ls 7) .ln)) : Spt Nat),sptIsEmpty ((.bs .ln 7 (.bn (.ls 7) .ln)) : Spt Nat)) = (true,false) := by rfl
-- sw_tree_205
example : (sptWf ((.bn (.bs .ln 7 (.bs .ln 9 .ln)) (.ls 7)) : Spt Nat),sptIsEmpty ((.bn (.bs .ln 7 (.bs .ln 9 .ln)) (.ls 7)) : Spt Nat)) = (false,false) := by rfl
-- sw_tree_206
example : (sptWf ((.bn (.bs .ln 7 (.bn (.ls 7) .ln)) .ln) : Spt Nat),sptIsEmpty ((.bn (.bs .ln 7 (.bn (.ls 7) .ln)) .ln) : Spt Nat)) = (true,false) := by rfl
-- sw_tree_207
example : (sptWf ((.bs .ln 7 (.bn (.bs .ln 7 (.bs .ln 9 .ln)) (.ls 7))) : Spt Nat),sptIsEmpty ((.bs .ln 7 (.bn (.bs .ln 7 (.bs .ln 9 .ln)) (.ls 7))) : Spt Nat)) = (false,false) := by rfl
-- sw_tree_208
example : (sptWf ((.bs .ln 7 (.bn (.bs .ln 7 (.bn (.ls 7) .ln)) .ln)) : Spt Nat),sptIsEmpty ((.bs .ln 7 (.bn (.bs .ln 7 (.bn (.ls 7) .ln)) .ln)) : Spt Nat)) = (true,false) := by rfl
-- sw_tree_209
example : (sptWf ((.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bs .ln 9 .ln)) (.ls 7))) (.ls 7)) : Spt Nat),sptIsEmpty ((.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bs .ln 9 .ln)) (.ls 7))) (.ls 7)) : Spt Nat)) = (false,false) := by rfl
-- sw_tree_210
example : (sptWf ((.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.ls 7) .ln)) .ln)) .ln) : Spt Nat),sptIsEmpty ((.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.ls 7) .ln)) .ln)) .ln) : Spt Nat)) = (true,false) := by rfl
-- sw_tree_211
example : (sptWf ((.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bs .ln 9 .ln)) (.ls 7))) (.ls 7))) : Spt Nat),sptIsEmpty ((.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bs .ln 9 .ln)) (.ls 7))) (.ls 7))) : Spt Nat)) = (false,false) := by rfl
-- sw_tree_212
example : (sptWf ((.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.ls 7) .ln)) .ln)) .ln)) : Spt Nat),sptIsEmpty ((.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.ls 7) .ln)) .ln)) .ln)) : Spt Nat)) = (true,false) := by rfl
-- sw_tree_213
example : (sptWf ((.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bs .ln 9 .ln)) (.ls 7))) (.ls 7))) (.ls 7)) : Spt Nat),sptIsEmpty ((.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bs .ln 9 .ln)) (.ls 7))) (.ls 7))) (.ls 7)) : Spt Nat)) = (false,false) := by rfl
-- sw_tree_214
example : (sptWf ((.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.ls 7) .ln)) .ln)) .ln)) .ln) : Spt Nat),sptIsEmpty ((.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.ls 7) .ln)) .ln)) .ln)) .ln) : Spt Nat)) = (true,false) := by rfl
-- sw_tree_215
example : (sptWf ((.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bs .ln 9 .ln)) (.ls 7))) (.ls 7))) (.ls 7))) : Spt Nat),sptIsEmpty ((.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bs .ln 9 .ln)) (.ls 7))) (.ls 7))) (.ls 7))) : Spt Nat)) = (false,false) := by rfl
-- sw_tree_216
example : (sptWf ((.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.ls 7) .ln)) .ln)) .ln)) .ln)) : Spt Nat),sptIsEmpty ((.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.ls 7) .ln)) .ln)) .ln)) .ln)) : Spt Nat)) = (true,false) := by rfl
-- sw_tree_217
example : (sptWf ((.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bs .ln 9 .ln)) (.ls 7))) (.ls 7))) (.ls 7))) (.ls 7)) : Spt Nat),sptIsEmpty ((.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bs .ln 9 .ln)) (.ls 7))) (.ls 7))) (.ls 7))) (.ls 7)) : Spt Nat)) = (false,false) := by rfl
-- sw_tree_218
example : (sptWf ((.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.ls 7) .ln)) .ln)) .ln)) .ln)) .ln) : Spt Nat),sptIsEmpty ((.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.ls 7) .ln)) .ln)) .ln)) .ln)) .ln) : Spt Nat)) = (true,false) := by rfl
-- sw_tree_219
example : (sptWf ((.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bs .ln 9 .ln)) (.ls 7))) (.ls 7))) (.ls 7))) (.ls 7))) : Spt Nat),sptIsEmpty ((.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bs .ln 9 .ln)) (.ls 7))) (.ls 7))) (.ls 7))) (.ls 7))) : Spt Nat)) = (false,false) := by rfl
-- sw_tree_220
example : (sptWf ((.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.ls 7) .ln)) .ln)) .ln)) .ln)) .ln)) : Spt Nat),sptIsEmpty ((.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.ls 7) .ln)) .ln)) .ln)) .ln)) .ln)) : Spt Nat)) = (true,false) := by rfl
-- sw_tree_221
example : (sptWf ((.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bs .ln 9 .ln)) (.ls 7))) (.ls 7))) (.ls 7))) (.ls 7))) (.ls 7)) : Spt Nat),sptIsEmpty ((.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bs .ln 9 .ln)) (.ls 7))) (.ls 7))) (.ls 7))) (.ls 7))) (.ls 7)) : Spt Nat)) = (false,false) := by rfl
-- sw_tree_222
example : (sptWf ((.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.ls 7) .ln)) .ln)) .ln)) .ln)) .ln)) .ln) : Spt Nat),sptIsEmpty ((.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.ls 7) .ln)) .ln)) .ln)) .ln)) .ln)) .ln) : Spt Nat)) = (true,false) := by rfl
-- sw_tree_223
example : (sptWf ((.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bs .ln 9 .ln)) (.ls 7))) (.ls 7))) (.ls 7))) (.ls 7))) (.ls 7))) : Spt Nat),sptIsEmpty ((.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bs .ln 9 .ln)) (.ls 7))) (.ls 7))) (.ls 7))) (.ls 7))) (.ls 7))) : Spt Nat)) = (false,false) := by rfl
-- sw_tree_224
example : (sptWf ((.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.ls 7) .ln)) .ln)) .ln)) .ln)) .ln)) .ln)) : Spt Nat),sptIsEmpty ((.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.ls 7) .ln)) .ln)) .ln)) .ln)) .ln)) .ln)) : Spt Nat)) = (true,false) := by rfl
-- sw_tree_225
example : (sptWf ((.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bs .ln 9 .ln)) (.ls 7))) (.ls 7))) (.ls 7))) (.ls 7))) (.ls 7))) (.ls 7)) : Spt Nat),sptIsEmpty ((.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bs .ln 9 .ln)) (.ls 7))) (.ls 7))) (.ls 7))) (.ls 7))) (.ls 7))) (.ls 7)) : Spt Nat)) = (false,false) := by rfl
-- sw_tree_226
example : (sptWf ((.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.ls 7) .ln)) .ln)) .ln)) .ln)) .ln)) .ln)) .ln) : Spt Nat),sptIsEmpty ((.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.ls 7) .ln)) .ln)) .ln)) .ln)) .ln)) .ln)) .ln) : Spt Nat)) = (true,false) := by rfl
-- sw_tree_227
example : (sptWf ((.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bs .ln 9 .ln)) (.ls 7))) (.ls 7))) (.ls 7))) (.ls 7))) (.ls 7))) (.ls 7))) : Spt Nat),sptIsEmpty ((.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bs .ln 9 .ln)) (.ls 7))) (.ls 7))) (.ls 7))) (.ls 7))) (.ls 7))) (.ls 7))) : Spt Nat)) = (false,false) := by rfl
-- sw_tree_228
example : (sptWf ((.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.ls 7) .ln)) .ln)) .ln)) .ln)) .ln)) .ln)) .ln)) : Spt Nat),sptIsEmpty ((.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.ls 7) .ln)) .ln)) .ln)) .ln)) .ln)) .ln)) .ln)) : Spt Nat)) = (true,false) := by rfl
-- sw_tree_229
example : (sptWf ((.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bs .ln 9 .ln)) (.ls 7))) (.ls 7))) (.ls 7))) (.ls 7))) (.ls 7))) (.ls 7))) (.ls 7)) : Spt Nat),sptIsEmpty ((.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bs .ln 9 .ln)) (.ls 7))) (.ls 7))) (.ls 7))) (.ls 7))) (.ls 7))) (.ls 7))) (.ls 7)) : Spt Nat)) = (false,false) := by rfl
-- sw_tree_230
example : (sptWf ((.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.ls 7) .ln)) .ln)) .ln)) .ln)) .ln)) .ln)) .ln)) .ln) : Spt Nat),sptIsEmpty ((.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.ls 7) .ln)) .ln)) .ln)) .ln)) .ln)) .ln)) .ln)) .ln) : Spt Nat)) = (true,false) := by rfl
-- sw_tree_231
example : (sptWf ((.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bs .ln 9 .ln)) (.ls 7))) (.ls 7))) (.ls 7))) (.ls 7))) (.ls 7))) (.ls 7))) (.ls 7))) : Spt Nat),sptIsEmpty ((.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bs .ln 9 .ln)) (.ls 7))) (.ls 7))) (.ls 7))) (.ls 7))) (.ls 7))) (.ls 7))) (.ls 7))) : Spt Nat)) = (false,false) := by rfl
-- sw_tree_232
example : (sptWf ((.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.ls 7) .ln)) .ln)) .ln)) .ln)) .ln)) .ln)) .ln)) .ln)) : Spt Nat),sptIsEmpty ((.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.ls 7) .ln)) .ln)) .ln)) .ln)) .ln)) .ln)) .ln)) .ln)) : Spt Nat)) = (true,false) := by rfl
-- sw_tree_233
example : (sptWf ((.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bs .ln 9 .ln)) (.ls 7))) (.ls 7))) (.ls 7))) (.ls 7))) (.ls 7))) (.ls 7))) (.ls 7))) (.ls 7)) : Spt Nat),sptIsEmpty ((.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bs .ln 9 .ln)) (.ls 7))) (.ls 7))) (.ls 7))) (.ls 7))) (.ls 7))) (.ls 7))) (.ls 7))) (.ls 7)) : Spt Nat)) = (false,false) := by rfl
-- sw_tree_234
example : (sptWf ((.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.ls 7) .ln)) .ln)) .ln)) .ln)) .ln)) .ln)) .ln)) .ln)) .ln) : Spt Nat),sptIsEmpty ((.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.ls 7) .ln)) .ln)) .ln)) .ln)) .ln)) .ln)) .ln)) .ln)) .ln) : Spt Nat)) = (true,false) := by rfl
-- sw_tree_235
example : (sptWf ((.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bs .ln 9 .ln)) (.ls 7))) (.ls 7))) (.ls 7))) (.ls 7))) (.ls 7))) (.ls 7))) (.ls 7))) (.ls 7))) : Spt Nat),sptIsEmpty ((.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bs .ln 9 .ln)) (.ls 7))) (.ls 7))) (.ls 7))) (.ls 7))) (.ls 7))) (.ls 7))) (.ls 7))) (.ls 7))) : Spt Nat)) = (false,false) := by rfl
-- sw_tree_236
example : (sptWf ((.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.ls 7) .ln)) .ln)) .ln)) .ln)) .ln)) .ln)) .ln)) .ln)) .ln)) : Spt Nat),sptIsEmpty ((.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.ls 7) .ln)) .ln)) .ln)) .ln)) .ln)) .ln)) .ln)) .ln)) .ln)) : Spt Nat)) = (true,false) := by rfl
-- sw_tree_237
example : (sptWf ((.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bs .ln 9 .ln)) (.ls 7))) (.ls 7))) (.ls 7))) (.ls 7))) (.ls 7))) (.ls 7))) (.ls 7))) (.ls 7))) (.ls 7)) : Spt Nat),sptIsEmpty ((.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bs .ln 9 .ln)) (.ls 7))) (.ls 7))) (.ls 7))) (.ls 7))) (.ls 7))) (.ls 7))) (.ls 7))) (.ls 7))) (.ls 7)) : Spt Nat)) = (false,false) := by rfl
-- sw_tree_238
example : (sptWf ((.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.ls 7) .ln)) .ln)) .ln)) .ln)) .ln)) .ln)) .ln)) .ln)) .ln)) .ln) : Spt Nat),sptIsEmpty ((.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.ls 7) .ln)) .ln)) .ln)) .ln)) .ln)) .ln)) .ln)) .ln)) .ln)) .ln) : Spt Nat)) = (true,false) := by rfl
-- sw_tree_239
example : (sptWf ((.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bs .ln 9 .ln)) (.ls 7))) (.ls 7))) (.ls 7))) (.ls 7))) (.ls 7))) (.ls 7))) (.ls 7))) (.ls 7))) (.ls 7))) : Spt Nat),sptIsEmpty ((.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bs .ln 9 .ln)) (.ls 7))) (.ls 7))) (.ls 7))) (.ls 7))) (.ls 7))) (.ls 7))) (.ls 7))) (.ls 7))) (.ls 7))) : Spt Nat)) = (false,false) := by rfl
-- sw_tree_240
example : (sptWf ((.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.ls 7) .ln)) .ln)) .ln)) .ln)) .ln)) .ln)) .ln)) .ln)) .ln)) .ln)) : Spt Nat),sptIsEmpty ((.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.ls 7) .ln)) .ln)) .ln)) .ln)) .ln)) .ln)) .ln)) .ln)) .ln)) .ln)) : Spt Nat)) = (true,false) := by rfl
-- sw_tree_241
example : (sptWf ((.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bs .ln 9 .ln)) (.ls 7))) (.ls 7))) (.ls 7))) (.ls 7))) (.ls 7))) (.ls 7))) (.ls 7))) (.ls 7))) (.ls 7))) (.ls 7)) : Spt Nat),sptIsEmpty ((.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bs .ln 9 .ln)) (.ls 7))) (.ls 7))) (.ls 7))) (.ls 7))) (.ls 7))) (.ls 7))) (.ls 7))) (.ls 7))) (.ls 7))) (.ls 7)) : Spt Nat)) = (false,false) := by rfl
-- sw_tree_242
example : (sptWf ((.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.ls 7) .ln)) .ln)) .ln)) .ln)) .ln)) .ln)) .ln)) .ln)) .ln)) .ln)) .ln) : Spt Nat),sptIsEmpty ((.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.ls 7) .ln)) .ln)) .ln)) .ln)) .ln)) .ln)) .ln)) .ln)) .ln)) .ln)) .ln) : Spt Nat)) = (true,false) := by rfl
-- sw_tree_243
example : (sptWf ((.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bs .ln 9 .ln)) (.ls 7))) (.ls 7))) (.ls 7))) (.ls 7))) (.ls 7))) (.ls 7))) (.ls 7))) (.ls 7))) (.ls 7))) (.ls 7))) : Spt Nat),sptIsEmpty ((.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bs .ln 9 .ln)) (.ls 7))) (.ls 7))) (.ls 7))) (.ls 7))) (.ls 7))) (.ls 7))) (.ls 7))) (.ls 7))) (.ls 7))) (.ls 7))) : Spt Nat)) = (false,false) := by rfl
-- sw_tree_244
example : (sptWf ((.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.ls 7) .ln)) .ln)) .ln)) .ln)) .ln)) .ln)) .ln)) .ln)) .ln)) .ln)) .ln)) : Spt Nat),sptIsEmpty ((.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.ls 7) .ln)) .ln)) .ln)) .ln)) .ln)) .ln)) .ln)) .ln)) .ln)) .ln)) .ln)) : Spt Nat)) = (true,false) := by rfl
-- sw_tree_245
example : (sptWf ((.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bs .ln 9 .ln)) (.ls 7))) (.ls 7))) (.ls 7))) (.ls 7))) (.ls 7))) (.ls 7))) (.ls 7))) (.ls 7))) (.ls 7))) (.ls 7))) (.ls 7)) : Spt Nat),sptIsEmpty ((.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bs .ln 9 .ln)) (.ls 7))) (.ls 7))) (.ls 7))) (.ls 7))) (.ls 7))) (.ls 7))) (.ls 7))) (.ls 7))) (.ls 7))) (.ls 7))) (.ls 7)) : Spt Nat)) = (false,false) := by rfl
-- sw_tree_246
example : (sptWf ((.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.ls 7) .ln)) .ln)) .ln)) .ln)) .ln)) .ln)) .ln)) .ln)) .ln)) .ln)) .ln)) .ln) : Spt Nat),sptIsEmpty ((.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.ls 7) .ln)) .ln)) .ln)) .ln)) .ln)) .ln)) .ln)) .ln)) .ln)) .ln)) .ln)) .ln) : Spt Nat)) = (true,false) := by rfl
-- sw_tree_247
example : (sptWf ((.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bs .ln 9 .ln)) (.ls 7))) (.ls 7))) (.ls 7))) (.ls 7))) (.ls 7))) (.ls 7))) (.ls 7))) (.ls 7))) (.ls 7))) (.ls 7))) (.ls 7))) : Spt Nat),sptIsEmpty ((.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bs .ln 9 .ln)) (.ls 7))) (.ls 7))) (.ls 7))) (.ls 7))) (.ls 7))) (.ls 7))) (.ls 7))) (.ls 7))) (.ls 7))) (.ls 7))) (.ls 7))) : Spt Nat)) = (false,false) := by rfl
-- sw_tree_248
example : (sptWf ((.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.ls 7) .ln)) .ln)) .ln)) .ln)) .ln)) .ln)) .ln)) .ln)) .ln)) .ln)) .ln)) .ln)) : Spt Nat),sptIsEmpty ((.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.ls 7) .ln)) .ln)) .ln)) .ln)) .ln)) .ln)) .ln)) .ln)) .ln)) .ln)) .ln)) .ln)) : Spt Nat)) = (true,false) := by rfl
-- sw_tree_249
example : (sptWf ((.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bs .ln 9 .ln)) (.ls 7))) (.ls 7))) (.ls 7))) (.ls 7))) (.ls 7))) (.ls 7))) (.ls 7))) (.ls 7))) (.ls 7))) (.ls 7))) (.ls 7))) (.ls 7)) : Spt Nat),sptIsEmpty ((.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bs .ln 9 .ln)) (.ls 7))) (.ls 7))) (.ls 7))) (.ls 7))) (.ls 7))) (.ls 7))) (.ls 7))) (.ls 7))) (.ls 7))) (.ls 7))) (.ls 7))) (.ls 7)) : Spt Nat)) = (false,false) := by rfl
-- sw_function_0
example : (sptWf (.ln : Spt (Nat → Nat)),sptIsEmpty (.ln : Spt (Nat → Nat))) = (true,true) := by rfl
-- sw_function_1
example : (sptWf ((.ls (fun n : Nat => n+1)) : Spt (Nat → Nat)),sptIsEmpty ((.ls (fun n : Nat => n+1)) : Spt (Nat → Nat))) = (true,false) := by rfl
-- sw_function_2
example : (sptWf ((.bn (.ls (fun n : Nat => n+1)) .ln) : Spt (Nat → Nat)),sptIsEmpty ((.bn (.ls (fun n : Nat => n+1)) .ln) : Spt (Nat → Nat))) = (true,false) := by rfl
-- sw_function_3
example : (sptWf ((.bs .ln (fun n : Nat => n+1) .ln) : Spt (Nat → Nat)),sptIsEmpty ((.bs .ln (fun n : Nat => n+1) .ln) : Spt (Nat → Nat))) = (false,false) := by rfl

-- The entire four-clause witness is unconditional for arbitrary payloads.
example {α : Type} :
    sptWf (.ln : Spt α) = true ∧
    (∀ a : α, sptWf (.ls a) = true) ∧
    (∀ l r : Spt α, sptWf (.bn l r) = true ↔
      sptWf l = true ∧ sptWf r = true ∧ ¬ (l = .ln ∧ r = .ln)) ∧
    (∀ (l : Spt α) (a : α) (r : Spt α), sptWf (.bs l a r) = true ↔
      sptWf l = true ∧ sptWf r = true ∧ ¬ (l = .ln ∧ r = .ln)) := sptWfClauses
#print axioms sptWfClauses

private def check (label : String) (actual expected : Bool × Bool) : IO Bool := do
  if actual = expected then pure true else
    IO.eprintln s!"FAIL original sptree wf {label}"
    pure false

def runChecks : IO Bool := do
  let results ← List.mapM (fun action => action) [
    check "sw_tree_0" (sptWf (.ln : Spt Nat),sptIsEmpty (.ln : Spt Nat)) (true,true),
    check "sw_tree_1" (sptWf ((.ls 7) : Spt Nat),sptIsEmpty ((.ls 7) : Spt Nat)) (true,false),
    check "sw_tree_2" (sptWf ((.bn .ln .ln) : Spt Nat),sptIsEmpty ((.bn .ln .ln) : Spt Nat)) (false,false),
    check "sw_tree_3" (sptWf ((.bn .ln (.ls 7)) : Spt Nat),sptIsEmpty ((.bn .ln (.ls 7)) : Spt Nat)) (true,false),
    check "sw_tree_4" (sptWf ((.bn .ln (.bn .ln .ln)) : Spt Nat),sptIsEmpty ((.bn .ln (.bn .ln .ln)) : Spt Nat)) (false,false),
    check "sw_tree_5" (sptWf ((.bn .ln (.bn .ln (.ls 7))) : Spt Nat),sptIsEmpty ((.bn .ln (.bn .ln (.ls 7))) : Spt Nat)) (true,false),
    check "sw_tree_6" (sptWf ((.bn .ln (.bn (.ls 7) .ln)) : Spt Nat),sptIsEmpty ((.bn .ln (.bn (.ls 7) .ln)) : Spt Nat)) (true,false),
    check "sw_tree_7" (sptWf ((.bn .ln (.bn (.ls 7) (.ls 7))) : Spt Nat),sptIsEmpty ((.bn .ln (.bn (.ls 7) (.ls 7))) : Spt Nat)) (true,false),
    check "sw_tree_8" (sptWf ((.bn .ln (.bs .ln 9 .ln)) : Spt Nat),sptIsEmpty ((.bn .ln (.bs .ln 9 .ln)) : Spt Nat)) (false,false),
    check "sw_tree_9" (sptWf ((.bn .ln (.bs .ln 9 (.ls 7))) : Spt Nat),sptIsEmpty ((.bn .ln (.bs .ln 9 (.ls 7))) : Spt Nat)) (true,false),
    check "sw_tree_10" (sptWf ((.bn .ln (.bs (.ls 7) 9 .ln)) : Spt Nat),sptIsEmpty ((.bn .ln (.bs (.ls 7) 9 .ln)) : Spt Nat)) (true,false),
    check "sw_tree_11" (sptWf ((.bn .ln (.bs (.ls 7) 9 (.ls 7))) : Spt Nat),sptIsEmpty ((.bn .ln (.bs (.ls 7) 9 (.ls 7))) : Spt Nat)) (true,false),
    check "sw_tree_12" (sptWf ((.bn (.ls 7) .ln) : Spt Nat),sptIsEmpty ((.bn (.ls 7) .ln) : Spt Nat)) (true,false),
    check "sw_tree_13" (sptWf ((.bn (.ls 7) (.ls 7)) : Spt Nat),sptIsEmpty ((.bn (.ls 7) (.ls 7)) : Spt Nat)) (true,false),
    check "sw_tree_14" (sptWf ((.bn (.ls 7) (.bn .ln .ln)) : Spt Nat),sptIsEmpty ((.bn (.ls 7) (.bn .ln .ln)) : Spt Nat)) (false,false),
    check "sw_tree_15" (sptWf ((.bn (.ls 7) (.bn .ln (.ls 7))) : Spt Nat),sptIsEmpty ((.bn (.ls 7) (.bn .ln (.ls 7))) : Spt Nat)) (true,false),
    check "sw_tree_16" (sptWf ((.bn (.ls 7) (.bn (.ls 7) .ln)) : Spt Nat),sptIsEmpty ((.bn (.ls 7) (.bn (.ls 7) .ln)) : Spt Nat)) (true,false),
    check "sw_tree_17" (sptWf ((.bn (.ls 7) (.bn (.ls 7) (.ls 7))) : Spt Nat),sptIsEmpty ((.bn (.ls 7) (.bn (.ls 7) (.ls 7))) : Spt Nat)) (true,false),
    check "sw_tree_18" (sptWf ((.bn (.ls 7) (.bs .ln 9 .ln)) : Spt Nat),sptIsEmpty ((.bn (.ls 7) (.bs .ln 9 .ln)) : Spt Nat)) (false,false),
    check "sw_tree_19" (sptWf ((.bn (.ls 7) (.bs .ln 9 (.ls 7))) : Spt Nat),sptIsEmpty ((.bn (.ls 7) (.bs .ln 9 (.ls 7))) : Spt Nat)) (true,false),
    check "sw_tree_20" (sptWf ((.bn (.ls 7) (.bs (.ls 7) 9 .ln)) : Spt Nat),sptIsEmpty ((.bn (.ls 7) (.bs (.ls 7) 9 .ln)) : Spt Nat)) (true,false),
    check "sw_tree_21" (sptWf ((.bn (.ls 7) (.bs (.ls 7) 9 (.ls 7))) : Spt Nat),sptIsEmpty ((.bn (.ls 7) (.bs (.ls 7) 9 (.ls 7))) : Spt Nat)) (true,false),
    check "sw_tree_22" (sptWf ((.bn (.bn .ln .ln) .ln) : Spt Nat),sptIsEmpty ((.bn (.bn .ln .ln) .ln) : Spt Nat)) (false,false),
    check "sw_tree_23" (sptWf ((.bn (.bn .ln .ln) (.ls 7)) : Spt Nat),sptIsEmpty ((.bn (.bn .ln .ln) (.ls 7)) : Spt Nat)) (false,false),
    check "sw_tree_24" (sptWf ((.bn (.bn .ln .ln) (.bn .ln .ln)) : Spt Nat),sptIsEmpty ((.bn (.bn .ln .ln) (.bn .ln .ln)) : Spt Nat)) (false,false),
    check "sw_tree_25" (sptWf ((.bn (.bn .ln .ln) (.bn .ln (.ls 7))) : Spt Nat),sptIsEmpty ((.bn (.bn .ln .ln) (.bn .ln (.ls 7))) : Spt Nat)) (false,false),
    check "sw_tree_26" (sptWf ((.bn (.bn .ln .ln) (.bn (.ls 7) .ln)) : Spt Nat),sptIsEmpty ((.bn (.bn .ln .ln) (.bn (.ls 7) .ln)) : Spt Nat)) (false,false),
    check "sw_tree_27" (sptWf ((.bn (.bn .ln .ln) (.bn (.ls 7) (.ls 7))) : Spt Nat),sptIsEmpty ((.bn (.bn .ln .ln) (.bn (.ls 7) (.ls 7))) : Spt Nat)) (false,false),
    check "sw_tree_28" (sptWf ((.bn (.bn .ln .ln) (.bs .ln 9 .ln)) : Spt Nat),sptIsEmpty ((.bn (.bn .ln .ln) (.bs .ln 9 .ln)) : Spt Nat)) (false,false),
    check "sw_tree_29" (sptWf ((.bn (.bn .ln .ln) (.bs .ln 9 (.ls 7))) : Spt Nat),sptIsEmpty ((.bn (.bn .ln .ln) (.bs .ln 9 (.ls 7))) : Spt Nat)) (false,false),
    check "sw_tree_30" (sptWf ((.bn (.bn .ln .ln) (.bs (.ls 7) 9 .ln)) : Spt Nat),sptIsEmpty ((.bn (.bn .ln .ln) (.bs (.ls 7) 9 .ln)) : Spt Nat)) (false,false),
    check "sw_tree_31" (sptWf ((.bn (.bn .ln .ln) (.bs (.ls 7) 9 (.ls 7))) : Spt Nat),sptIsEmpty ((.bn (.bn .ln .ln) (.bs (.ls 7) 9 (.ls 7))) : Spt Nat)) (false,false),
    check "sw_tree_32" (sptWf ((.bn (.bn .ln (.ls 7)) .ln) : Spt Nat),sptIsEmpty ((.bn (.bn .ln (.ls 7)) .ln) : Spt Nat)) (true,false),
    check "sw_tree_33" (sptWf ((.bn (.bn .ln (.ls 7)) (.ls 7)) : Spt Nat),sptIsEmpty ((.bn (.bn .ln (.ls 7)) (.ls 7)) : Spt Nat)) (true,false),
    check "sw_tree_34" (sptWf ((.bn (.bn .ln (.ls 7)) (.bn .ln .ln)) : Spt Nat),sptIsEmpty ((.bn (.bn .ln (.ls 7)) (.bn .ln .ln)) : Spt Nat)) (false,false),
    check "sw_tree_35" (sptWf ((.bn (.bn .ln (.ls 7)) (.bn .ln (.ls 7))) : Spt Nat),sptIsEmpty ((.bn (.bn .ln (.ls 7)) (.bn .ln (.ls 7))) : Spt Nat)) (true,false),
    check "sw_tree_36" (sptWf ((.bn (.bn .ln (.ls 7)) (.bn (.ls 7) .ln)) : Spt Nat),sptIsEmpty ((.bn (.bn .ln (.ls 7)) (.bn (.ls 7) .ln)) : Spt Nat)) (true,false),
    check "sw_tree_37" (sptWf ((.bn (.bn .ln (.ls 7)) (.bn (.ls 7) (.ls 7))) : Spt Nat),sptIsEmpty ((.bn (.bn .ln (.ls 7)) (.bn (.ls 7) (.ls 7))) : Spt Nat)) (true,false),
    check "sw_tree_38" (sptWf ((.bn (.bn .ln (.ls 7)) (.bs .ln 9 .ln)) : Spt Nat),sptIsEmpty ((.bn (.bn .ln (.ls 7)) (.bs .ln 9 .ln)) : Spt Nat)) (false,false),
    check "sw_tree_39" (sptWf ((.bn (.bn .ln (.ls 7)) (.bs .ln 9 (.ls 7))) : Spt Nat),sptIsEmpty ((.bn (.bn .ln (.ls 7)) (.bs .ln 9 (.ls 7))) : Spt Nat)) (true,false),
    check "sw_tree_40" (sptWf ((.bn (.bn .ln (.ls 7)) (.bs (.ls 7) 9 .ln)) : Spt Nat),sptIsEmpty ((.bn (.bn .ln (.ls 7)) (.bs (.ls 7) 9 .ln)) : Spt Nat)) (true,false),
    check "sw_tree_41" (sptWf ((.bn (.bn .ln (.ls 7)) (.bs (.ls 7) 9 (.ls 7))) : Spt Nat),sptIsEmpty ((.bn (.bn .ln (.ls 7)) (.bs (.ls 7) 9 (.ls 7))) : Spt Nat)) (true,false),
    check "sw_tree_42" (sptWf ((.bn (.bn (.ls 7) .ln) .ln) : Spt Nat),sptIsEmpty ((.bn (.bn (.ls 7) .ln) .ln) : Spt Nat)) (true,false),
    check "sw_tree_43" (sptWf ((.bn (.bn (.ls 7) .ln) (.ls 7)) : Spt Nat),sptIsEmpty ((.bn (.bn (.ls 7) .ln) (.ls 7)) : Spt Nat)) (true,false),
    check "sw_tree_44" (sptWf ((.bn (.bn (.ls 7) .ln) (.bn .ln .ln)) : Spt Nat),sptIsEmpty ((.bn (.bn (.ls 7) .ln) (.bn .ln .ln)) : Spt Nat)) (false,false),
    check "sw_tree_45" (sptWf ((.bn (.bn (.ls 7) .ln) (.bn .ln (.ls 7))) : Spt Nat),sptIsEmpty ((.bn (.bn (.ls 7) .ln) (.bn .ln (.ls 7))) : Spt Nat)) (true,false),
    check "sw_tree_46" (sptWf ((.bn (.bn (.ls 7) .ln) (.bn (.ls 7) .ln)) : Spt Nat),sptIsEmpty ((.bn (.bn (.ls 7) .ln) (.bn (.ls 7) .ln)) : Spt Nat)) (true,false),
    check "sw_tree_47" (sptWf ((.bn (.bn (.ls 7) .ln) (.bn (.ls 7) (.ls 7))) : Spt Nat),sptIsEmpty ((.bn (.bn (.ls 7) .ln) (.bn (.ls 7) (.ls 7))) : Spt Nat)) (true,false),
    check "sw_tree_48" (sptWf ((.bn (.bn (.ls 7) .ln) (.bs .ln 9 .ln)) : Spt Nat),sptIsEmpty ((.bn (.bn (.ls 7) .ln) (.bs .ln 9 .ln)) : Spt Nat)) (false,false),
    check "sw_tree_49" (sptWf ((.bn (.bn (.ls 7) .ln) (.bs .ln 9 (.ls 7))) : Spt Nat),sptIsEmpty ((.bn (.bn (.ls 7) .ln) (.bs .ln 9 (.ls 7))) : Spt Nat)) (true,false),
    check "sw_tree_50" (sptWf ((.bn (.bn (.ls 7) .ln) (.bs (.ls 7) 9 .ln)) : Spt Nat),sptIsEmpty ((.bn (.bn (.ls 7) .ln) (.bs (.ls 7) 9 .ln)) : Spt Nat)) (true,false),
    check "sw_tree_51" (sptWf ((.bn (.bn (.ls 7) .ln) (.bs (.ls 7) 9 (.ls 7))) : Spt Nat),sptIsEmpty ((.bn (.bn (.ls 7) .ln) (.bs (.ls 7) 9 (.ls 7))) : Spt Nat)) (true,false),
    check "sw_tree_52" (sptWf ((.bn (.bn (.ls 7) (.ls 7)) .ln) : Spt Nat),sptIsEmpty ((.bn (.bn (.ls 7) (.ls 7)) .ln) : Spt Nat)) (true,false),
    check "sw_tree_53" (sptWf ((.bn (.bn (.ls 7) (.ls 7)) (.ls 7)) : Spt Nat),sptIsEmpty ((.bn (.bn (.ls 7) (.ls 7)) (.ls 7)) : Spt Nat)) (true,false),
    check "sw_tree_54" (sptWf ((.bn (.bn (.ls 7) (.ls 7)) (.bn .ln .ln)) : Spt Nat),sptIsEmpty ((.bn (.bn (.ls 7) (.ls 7)) (.bn .ln .ln)) : Spt Nat)) (false,false),
    check "sw_tree_55" (sptWf ((.bn (.bn (.ls 7) (.ls 7)) (.bn .ln (.ls 7))) : Spt Nat),sptIsEmpty ((.bn (.bn (.ls 7) (.ls 7)) (.bn .ln (.ls 7))) : Spt Nat)) (true,false),
    check "sw_tree_56" (sptWf ((.bn (.bn (.ls 7) (.ls 7)) (.bn (.ls 7) .ln)) : Spt Nat),sptIsEmpty ((.bn (.bn (.ls 7) (.ls 7)) (.bn (.ls 7) .ln)) : Spt Nat)) (true,false),
    check "sw_tree_57" (sptWf ((.bn (.bn (.ls 7) (.ls 7)) (.bn (.ls 7) (.ls 7))) : Spt Nat),sptIsEmpty ((.bn (.bn (.ls 7) (.ls 7)) (.bn (.ls 7) (.ls 7))) : Spt Nat)) (true,false),
    check "sw_tree_58" (sptWf ((.bn (.bn (.ls 7) (.ls 7)) (.bs .ln 9 .ln)) : Spt Nat),sptIsEmpty ((.bn (.bn (.ls 7) (.ls 7)) (.bs .ln 9 .ln)) : Spt Nat)) (false,false),
    check "sw_tree_59" (sptWf ((.bn (.bn (.ls 7) (.ls 7)) (.bs .ln 9 (.ls 7))) : Spt Nat),sptIsEmpty ((.bn (.bn (.ls 7) (.ls 7)) (.bs .ln 9 (.ls 7))) : Spt Nat)) (true,false),
    check "sw_tree_60" (sptWf ((.bn (.bn (.ls 7) (.ls 7)) (.bs (.ls 7) 9 .ln)) : Spt Nat),sptIsEmpty ((.bn (.bn (.ls 7) (.ls 7)) (.bs (.ls 7) 9 .ln)) : Spt Nat)) (true,false),
    check "sw_tree_61" (sptWf ((.bn (.bn (.ls 7) (.ls 7)) (.bs (.ls 7) 9 (.ls 7))) : Spt Nat),sptIsEmpty ((.bn (.bn (.ls 7) (.ls 7)) (.bs (.ls 7) 9 (.ls 7))) : Spt Nat)) (true,false),
    check "sw_tree_62" (sptWf ((.bn (.bs .ln 9 .ln) .ln) : Spt Nat),sptIsEmpty ((.bn (.bs .ln 9 .ln) .ln) : Spt Nat)) (false,false),
    check "sw_tree_63" (sptWf ((.bn (.bs .ln 9 .ln) (.ls 7)) : Spt Nat),sptIsEmpty ((.bn (.bs .ln 9 .ln) (.ls 7)) : Spt Nat)) (false,false),
    check "sw_tree_64" (sptWf ((.bn (.bs .ln 9 .ln) (.bn .ln .ln)) : Spt Nat),sptIsEmpty ((.bn (.bs .ln 9 .ln) (.bn .ln .ln)) : Spt Nat)) (false,false),
    check "sw_tree_65" (sptWf ((.bn (.bs .ln 9 .ln) (.bn .ln (.ls 7))) : Spt Nat),sptIsEmpty ((.bn (.bs .ln 9 .ln) (.bn .ln (.ls 7))) : Spt Nat)) (false,false),
    check "sw_tree_66" (sptWf ((.bn (.bs .ln 9 .ln) (.bn (.ls 7) .ln)) : Spt Nat),sptIsEmpty ((.bn (.bs .ln 9 .ln) (.bn (.ls 7) .ln)) : Spt Nat)) (false,false),
    check "sw_tree_67" (sptWf ((.bn (.bs .ln 9 .ln) (.bn (.ls 7) (.ls 7))) : Spt Nat),sptIsEmpty ((.bn (.bs .ln 9 .ln) (.bn (.ls 7) (.ls 7))) : Spt Nat)) (false,false),
    check "sw_tree_68" (sptWf ((.bn (.bs .ln 9 .ln) (.bs .ln 9 .ln)) : Spt Nat),sptIsEmpty ((.bn (.bs .ln 9 .ln) (.bs .ln 9 .ln)) : Spt Nat)) (false,false),
    check "sw_tree_69" (sptWf ((.bn (.bs .ln 9 .ln) (.bs .ln 9 (.ls 7))) : Spt Nat),sptIsEmpty ((.bn (.bs .ln 9 .ln) (.bs .ln 9 (.ls 7))) : Spt Nat)) (false,false),
    check "sw_tree_70" (sptWf ((.bn (.bs .ln 9 .ln) (.bs (.ls 7) 9 .ln)) : Spt Nat),sptIsEmpty ((.bn (.bs .ln 9 .ln) (.bs (.ls 7) 9 .ln)) : Spt Nat)) (false,false),
    check "sw_tree_71" (sptWf ((.bn (.bs .ln 9 .ln) (.bs (.ls 7) 9 (.ls 7))) : Spt Nat),sptIsEmpty ((.bn (.bs .ln 9 .ln) (.bs (.ls 7) 9 (.ls 7))) : Spt Nat)) (false,false),
    check "sw_tree_72" (sptWf ((.bn (.bs .ln 9 (.ls 7)) .ln) : Spt Nat),sptIsEmpty ((.bn (.bs .ln 9 (.ls 7)) .ln) : Spt Nat)) (true,false),
    check "sw_tree_73" (sptWf ((.bn (.bs .ln 9 (.ls 7)) (.ls 7)) : Spt Nat),sptIsEmpty ((.bn (.bs .ln 9 (.ls 7)) (.ls 7)) : Spt Nat)) (true,false),
    check "sw_tree_74" (sptWf ((.bn (.bs .ln 9 (.ls 7)) (.bn .ln .ln)) : Spt Nat),sptIsEmpty ((.bn (.bs .ln 9 (.ls 7)) (.bn .ln .ln)) : Spt Nat)) (false,false),
    check "sw_tree_75" (sptWf ((.bn (.bs .ln 9 (.ls 7)) (.bn .ln (.ls 7))) : Spt Nat),sptIsEmpty ((.bn (.bs .ln 9 (.ls 7)) (.bn .ln (.ls 7))) : Spt Nat)) (true,false),
    check "sw_tree_76" (sptWf ((.bn (.bs .ln 9 (.ls 7)) (.bn (.ls 7) .ln)) : Spt Nat),sptIsEmpty ((.bn (.bs .ln 9 (.ls 7)) (.bn (.ls 7) .ln)) : Spt Nat)) (true,false),
    check "sw_tree_77" (sptWf ((.bn (.bs .ln 9 (.ls 7)) (.bn (.ls 7) (.ls 7))) : Spt Nat),sptIsEmpty ((.bn (.bs .ln 9 (.ls 7)) (.bn (.ls 7) (.ls 7))) : Spt Nat)) (true,false),
    check "sw_tree_78" (sptWf ((.bn (.bs .ln 9 (.ls 7)) (.bs .ln 9 .ln)) : Spt Nat),sptIsEmpty ((.bn (.bs .ln 9 (.ls 7)) (.bs .ln 9 .ln)) : Spt Nat)) (false,false),
    check "sw_tree_79" (sptWf ((.bn (.bs .ln 9 (.ls 7)) (.bs .ln 9 (.ls 7))) : Spt Nat),sptIsEmpty ((.bn (.bs .ln 9 (.ls 7)) (.bs .ln 9 (.ls 7))) : Spt Nat)) (true,false),
    check "sw_tree_80" (sptWf ((.bn (.bs .ln 9 (.ls 7)) (.bs (.ls 7) 9 .ln)) : Spt Nat),sptIsEmpty ((.bn (.bs .ln 9 (.ls 7)) (.bs (.ls 7) 9 .ln)) : Spt Nat)) (true,false),
    check "sw_tree_81" (sptWf ((.bn (.bs .ln 9 (.ls 7)) (.bs (.ls 7) 9 (.ls 7))) : Spt Nat),sptIsEmpty ((.bn (.bs .ln 9 (.ls 7)) (.bs (.ls 7) 9 (.ls 7))) : Spt Nat)) (true,false),
    check "sw_tree_82" (sptWf ((.bn (.bs (.ls 7) 9 .ln) .ln) : Spt Nat),sptIsEmpty ((.bn (.bs (.ls 7) 9 .ln) .ln) : Spt Nat)) (true,false),
    check "sw_tree_83" (sptWf ((.bn (.bs (.ls 7) 9 .ln) (.ls 7)) : Spt Nat),sptIsEmpty ((.bn (.bs (.ls 7) 9 .ln) (.ls 7)) : Spt Nat)) (true,false),
    check "sw_tree_84" (sptWf ((.bn (.bs (.ls 7) 9 .ln) (.bn .ln .ln)) : Spt Nat),sptIsEmpty ((.bn (.bs (.ls 7) 9 .ln) (.bn .ln .ln)) : Spt Nat)) (false,false),
    check "sw_tree_85" (sptWf ((.bn (.bs (.ls 7) 9 .ln) (.bn .ln (.ls 7))) : Spt Nat),sptIsEmpty ((.bn (.bs (.ls 7) 9 .ln) (.bn .ln (.ls 7))) : Spt Nat)) (true,false),
    check "sw_tree_86" (sptWf ((.bn (.bs (.ls 7) 9 .ln) (.bn (.ls 7) .ln)) : Spt Nat),sptIsEmpty ((.bn (.bs (.ls 7) 9 .ln) (.bn (.ls 7) .ln)) : Spt Nat)) (true,false),
    check "sw_tree_87" (sptWf ((.bn (.bs (.ls 7) 9 .ln) (.bn (.ls 7) (.ls 7))) : Spt Nat),sptIsEmpty ((.bn (.bs (.ls 7) 9 .ln) (.bn (.ls 7) (.ls 7))) : Spt Nat)) (true,false),
    check "sw_tree_88" (sptWf ((.bn (.bs (.ls 7) 9 .ln) (.bs .ln 9 .ln)) : Spt Nat),sptIsEmpty ((.bn (.bs (.ls 7) 9 .ln) (.bs .ln 9 .ln)) : Spt Nat)) (false,false),
    check "sw_tree_89" (sptWf ((.bn (.bs (.ls 7) 9 .ln) (.bs .ln 9 (.ls 7))) : Spt Nat),sptIsEmpty ((.bn (.bs (.ls 7) 9 .ln) (.bs .ln 9 (.ls 7))) : Spt Nat)) (true,false),
    check "sw_tree_90" (sptWf ((.bn (.bs (.ls 7) 9 .ln) (.bs (.ls 7) 9 .ln)) : Spt Nat),sptIsEmpty ((.bn (.bs (.ls 7) 9 .ln) (.bs (.ls 7) 9 .ln)) : Spt Nat)) (true,false),
    check "sw_tree_91" (sptWf ((.bn (.bs (.ls 7) 9 .ln) (.bs (.ls 7) 9 (.ls 7))) : Spt Nat),sptIsEmpty ((.bn (.bs (.ls 7) 9 .ln) (.bs (.ls 7) 9 (.ls 7))) : Spt Nat)) (true,false),
    check "sw_tree_92" (sptWf ((.bn (.bs (.ls 7) 9 (.ls 7)) .ln) : Spt Nat),sptIsEmpty ((.bn (.bs (.ls 7) 9 (.ls 7)) .ln) : Spt Nat)) (true,false),
    check "sw_tree_93" (sptWf ((.bn (.bs (.ls 7) 9 (.ls 7)) (.ls 7)) : Spt Nat),sptIsEmpty ((.bn (.bs (.ls 7) 9 (.ls 7)) (.ls 7)) : Spt Nat)) (true,false),
    check "sw_tree_94" (sptWf ((.bn (.bs (.ls 7) 9 (.ls 7)) (.bn .ln .ln)) : Spt Nat),sptIsEmpty ((.bn (.bs (.ls 7) 9 (.ls 7)) (.bn .ln .ln)) : Spt Nat)) (false,false),
    check "sw_tree_95" (sptWf ((.bn (.bs (.ls 7) 9 (.ls 7)) (.bn .ln (.ls 7))) : Spt Nat),sptIsEmpty ((.bn (.bs (.ls 7) 9 (.ls 7)) (.bn .ln (.ls 7))) : Spt Nat)) (true,false),
    check "sw_tree_96" (sptWf ((.bn (.bs (.ls 7) 9 (.ls 7)) (.bn (.ls 7) .ln)) : Spt Nat),sptIsEmpty ((.bn (.bs (.ls 7) 9 (.ls 7)) (.bn (.ls 7) .ln)) : Spt Nat)) (true,false),
    check "sw_tree_97" (sptWf ((.bn (.bs (.ls 7) 9 (.ls 7)) (.bn (.ls 7) (.ls 7))) : Spt Nat),sptIsEmpty ((.bn (.bs (.ls 7) 9 (.ls 7)) (.bn (.ls 7) (.ls 7))) : Spt Nat)) (true,false),
    check "sw_tree_98" (sptWf ((.bn (.bs (.ls 7) 9 (.ls 7)) (.bs .ln 9 .ln)) : Spt Nat),sptIsEmpty ((.bn (.bs (.ls 7) 9 (.ls 7)) (.bs .ln 9 .ln)) : Spt Nat)) (false,false),
    check "sw_tree_99" (sptWf ((.bn (.bs (.ls 7) 9 (.ls 7)) (.bs .ln 9 (.ls 7))) : Spt Nat),sptIsEmpty ((.bn (.bs (.ls 7) 9 (.ls 7)) (.bs .ln 9 (.ls 7))) : Spt Nat)) (true,false),
    check "sw_tree_100" (sptWf ((.bn (.bs (.ls 7) 9 (.ls 7)) (.bs (.ls 7) 9 .ln)) : Spt Nat),sptIsEmpty ((.bn (.bs (.ls 7) 9 (.ls 7)) (.bs (.ls 7) 9 .ln)) : Spt Nat)) (true,false),
    check "sw_tree_101" (sptWf ((.bn (.bs (.ls 7) 9 (.ls 7)) (.bs (.ls 7) 9 (.ls 7))) : Spt Nat),sptIsEmpty ((.bn (.bs (.ls 7) 9 (.ls 7)) (.bs (.ls 7) 9 (.ls 7))) : Spt Nat)) (true,false),
    check "sw_tree_102" (sptWf ((.bs .ln 9 .ln) : Spt Nat),sptIsEmpty ((.bs .ln 9 .ln) : Spt Nat)) (false,false),
    check "sw_tree_103" (sptWf ((.bs .ln 9 (.ls 7)) : Spt Nat),sptIsEmpty ((.bs .ln 9 (.ls 7)) : Spt Nat)) (true,false),
    check "sw_tree_104" (sptWf ((.bs .ln 9 (.bn .ln .ln)) : Spt Nat),sptIsEmpty ((.bs .ln 9 (.bn .ln .ln)) : Spt Nat)) (false,false),
    check "sw_tree_105" (sptWf ((.bs .ln 9 (.bn .ln (.ls 7))) : Spt Nat),sptIsEmpty ((.bs .ln 9 (.bn .ln (.ls 7))) : Spt Nat)) (true,false),
    check "sw_tree_106" (sptWf ((.bs .ln 9 (.bn (.ls 7) .ln)) : Spt Nat),sptIsEmpty ((.bs .ln 9 (.bn (.ls 7) .ln)) : Spt Nat)) (true,false),
    check "sw_tree_107" (sptWf ((.bs .ln 9 (.bn (.ls 7) (.ls 7))) : Spt Nat),sptIsEmpty ((.bs .ln 9 (.bn (.ls 7) (.ls 7))) : Spt Nat)) (true,false),
    check "sw_tree_108" (sptWf ((.bs .ln 9 (.bs .ln 9 .ln)) : Spt Nat),sptIsEmpty ((.bs .ln 9 (.bs .ln 9 .ln)) : Spt Nat)) (false,false),
    check "sw_tree_109" (sptWf ((.bs .ln 9 (.bs .ln 9 (.ls 7))) : Spt Nat),sptIsEmpty ((.bs .ln 9 (.bs .ln 9 (.ls 7))) : Spt Nat)) (true,false),
    check "sw_tree_110" (sptWf ((.bs .ln 9 (.bs (.ls 7) 9 .ln)) : Spt Nat),sptIsEmpty ((.bs .ln 9 (.bs (.ls 7) 9 .ln)) : Spt Nat)) (true,false),
    check "sw_tree_111" (sptWf ((.bs .ln 9 (.bs (.ls 7) 9 (.ls 7))) : Spt Nat),sptIsEmpty ((.bs .ln 9 (.bs (.ls 7) 9 (.ls 7))) : Spt Nat)) (true,false),
    check "sw_tree_112" (sptWf ((.bs (.ls 7) 9 .ln) : Spt Nat),sptIsEmpty ((.bs (.ls 7) 9 .ln) : Spt Nat)) (true,false),
    check "sw_tree_113" (sptWf ((.bs (.ls 7) 9 (.ls 7)) : Spt Nat),sptIsEmpty ((.bs (.ls 7) 9 (.ls 7)) : Spt Nat)) (true,false),
    check "sw_tree_114" (sptWf ((.bs (.ls 7) 9 (.bn .ln .ln)) : Spt Nat),sptIsEmpty ((.bs (.ls 7) 9 (.bn .ln .ln)) : Spt Nat)) (false,false),
    check "sw_tree_115" (sptWf ((.bs (.ls 7) 9 (.bn .ln (.ls 7))) : Spt Nat),sptIsEmpty ((.bs (.ls 7) 9 (.bn .ln (.ls 7))) : Spt Nat)) (true,false),
    check "sw_tree_116" (sptWf ((.bs (.ls 7) 9 (.bn (.ls 7) .ln)) : Spt Nat),sptIsEmpty ((.bs (.ls 7) 9 (.bn (.ls 7) .ln)) : Spt Nat)) (true,false),
    check "sw_tree_117" (sptWf ((.bs (.ls 7) 9 (.bn (.ls 7) (.ls 7))) : Spt Nat),sptIsEmpty ((.bs (.ls 7) 9 (.bn (.ls 7) (.ls 7))) : Spt Nat)) (true,false),
    check "sw_tree_118" (sptWf ((.bs (.ls 7) 9 (.bs .ln 9 .ln)) : Spt Nat),sptIsEmpty ((.bs (.ls 7) 9 (.bs .ln 9 .ln)) : Spt Nat)) (false,false),
    check "sw_tree_119" (sptWf ((.bs (.ls 7) 9 (.bs .ln 9 (.ls 7))) : Spt Nat),sptIsEmpty ((.bs (.ls 7) 9 (.bs .ln 9 (.ls 7))) : Spt Nat)) (true,false),
    check "sw_tree_120" (sptWf ((.bs (.ls 7) 9 (.bs (.ls 7) 9 .ln)) : Spt Nat),sptIsEmpty ((.bs (.ls 7) 9 (.bs (.ls 7) 9 .ln)) : Spt Nat)) (true,false),
    check "sw_tree_121" (sptWf ((.bs (.ls 7) 9 (.bs (.ls 7) 9 (.ls 7))) : Spt Nat),sptIsEmpty ((.bs (.ls 7) 9 (.bs (.ls 7) 9 (.ls 7))) : Spt Nat)) (true,false),
    check "sw_tree_122" (sptWf ((.bs (.bn .ln .ln) 9 .ln) : Spt Nat),sptIsEmpty ((.bs (.bn .ln .ln) 9 .ln) : Spt Nat)) (false,false),
    check "sw_tree_123" (sptWf ((.bs (.bn .ln .ln) 9 (.ls 7)) : Spt Nat),sptIsEmpty ((.bs (.bn .ln .ln) 9 (.ls 7)) : Spt Nat)) (false,false),
    check "sw_tree_124" (sptWf ((.bs (.bn .ln .ln) 9 (.bn .ln .ln)) : Spt Nat),sptIsEmpty ((.bs (.bn .ln .ln) 9 (.bn .ln .ln)) : Spt Nat)) (false,false),
    check "sw_tree_125" (sptWf ((.bs (.bn .ln .ln) 9 (.bn .ln (.ls 7))) : Spt Nat),sptIsEmpty ((.bs (.bn .ln .ln) 9 (.bn .ln (.ls 7))) : Spt Nat)) (false,false),
    check "sw_tree_126" (sptWf ((.bs (.bn .ln .ln) 9 (.bn (.ls 7) .ln)) : Spt Nat),sptIsEmpty ((.bs (.bn .ln .ln) 9 (.bn (.ls 7) .ln)) : Spt Nat)) (false,false),
    check "sw_tree_127" (sptWf ((.bs (.bn .ln .ln) 9 (.bn (.ls 7) (.ls 7))) : Spt Nat),sptIsEmpty ((.bs (.bn .ln .ln) 9 (.bn (.ls 7) (.ls 7))) : Spt Nat)) (false,false),
    check "sw_tree_128" (sptWf ((.bs (.bn .ln .ln) 9 (.bs .ln 9 .ln)) : Spt Nat),sptIsEmpty ((.bs (.bn .ln .ln) 9 (.bs .ln 9 .ln)) : Spt Nat)) (false,false),
    check "sw_tree_129" (sptWf ((.bs (.bn .ln .ln) 9 (.bs .ln 9 (.ls 7))) : Spt Nat),sptIsEmpty ((.bs (.bn .ln .ln) 9 (.bs .ln 9 (.ls 7))) : Spt Nat)) (false,false),
    check "sw_tree_130" (sptWf ((.bs (.bn .ln .ln) 9 (.bs (.ls 7) 9 .ln)) : Spt Nat),sptIsEmpty ((.bs (.bn .ln .ln) 9 (.bs (.ls 7) 9 .ln)) : Spt Nat)) (false,false),
    check "sw_tree_131" (sptWf ((.bs (.bn .ln .ln) 9 (.bs (.ls 7) 9 (.ls 7))) : Spt Nat),sptIsEmpty ((.bs (.bn .ln .ln) 9 (.bs (.ls 7) 9 (.ls 7))) : Spt Nat)) (false,false),
    check "sw_tree_132" (sptWf ((.bs (.bn .ln (.ls 7)) 9 .ln) : Spt Nat),sptIsEmpty ((.bs (.bn .ln (.ls 7)) 9 .ln) : Spt Nat)) (true,false),
    check "sw_tree_133" (sptWf ((.bs (.bn .ln (.ls 7)) 9 (.ls 7)) : Spt Nat),sptIsEmpty ((.bs (.bn .ln (.ls 7)) 9 (.ls 7)) : Spt Nat)) (true,false),
    check "sw_tree_134" (sptWf ((.bs (.bn .ln (.ls 7)) 9 (.bn .ln .ln)) : Spt Nat),sptIsEmpty ((.bs (.bn .ln (.ls 7)) 9 (.bn .ln .ln)) : Spt Nat)) (false,false),
    check "sw_tree_135" (sptWf ((.bs (.bn .ln (.ls 7)) 9 (.bn .ln (.ls 7))) : Spt Nat),sptIsEmpty ((.bs (.bn .ln (.ls 7)) 9 (.bn .ln (.ls 7))) : Spt Nat)) (true,false),
    check "sw_tree_136" (sptWf ((.bs (.bn .ln (.ls 7)) 9 (.bn (.ls 7) .ln)) : Spt Nat),sptIsEmpty ((.bs (.bn .ln (.ls 7)) 9 (.bn (.ls 7) .ln)) : Spt Nat)) (true,false),
    check "sw_tree_137" (sptWf ((.bs (.bn .ln (.ls 7)) 9 (.bn (.ls 7) (.ls 7))) : Spt Nat),sptIsEmpty ((.bs (.bn .ln (.ls 7)) 9 (.bn (.ls 7) (.ls 7))) : Spt Nat)) (true,false),
    check "sw_tree_138" (sptWf ((.bs (.bn .ln (.ls 7)) 9 (.bs .ln 9 .ln)) : Spt Nat),sptIsEmpty ((.bs (.bn .ln (.ls 7)) 9 (.bs .ln 9 .ln)) : Spt Nat)) (false,false),
    check "sw_tree_139" (sptWf ((.bs (.bn .ln (.ls 7)) 9 (.bs .ln 9 (.ls 7))) : Spt Nat),sptIsEmpty ((.bs (.bn .ln (.ls 7)) 9 (.bs .ln 9 (.ls 7))) : Spt Nat)) (true,false),
    check "sw_tree_140" (sptWf ((.bs (.bn .ln (.ls 7)) 9 (.bs (.ls 7) 9 .ln)) : Spt Nat),sptIsEmpty ((.bs (.bn .ln (.ls 7)) 9 (.bs (.ls 7) 9 .ln)) : Spt Nat)) (true,false),
    check "sw_tree_141" (sptWf ((.bs (.bn .ln (.ls 7)) 9 (.bs (.ls 7) 9 (.ls 7))) : Spt Nat),sptIsEmpty ((.bs (.bn .ln (.ls 7)) 9 (.bs (.ls 7) 9 (.ls 7))) : Spt Nat)) (true,false),
    check "sw_tree_142" (sptWf ((.bs (.bn (.ls 7) .ln) 9 .ln) : Spt Nat),sptIsEmpty ((.bs (.bn (.ls 7) .ln) 9 .ln) : Spt Nat)) (true,false),
    check "sw_tree_143" (sptWf ((.bs (.bn (.ls 7) .ln) 9 (.ls 7)) : Spt Nat),sptIsEmpty ((.bs (.bn (.ls 7) .ln) 9 (.ls 7)) : Spt Nat)) (true,false),
    check "sw_tree_144" (sptWf ((.bs (.bn (.ls 7) .ln) 9 (.bn .ln .ln)) : Spt Nat),sptIsEmpty ((.bs (.bn (.ls 7) .ln) 9 (.bn .ln .ln)) : Spt Nat)) (false,false),
    check "sw_tree_145" (sptWf ((.bs (.bn (.ls 7) .ln) 9 (.bn .ln (.ls 7))) : Spt Nat),sptIsEmpty ((.bs (.bn (.ls 7) .ln) 9 (.bn .ln (.ls 7))) : Spt Nat)) (true,false),
    check "sw_tree_146" (sptWf ((.bs (.bn (.ls 7) .ln) 9 (.bn (.ls 7) .ln)) : Spt Nat),sptIsEmpty ((.bs (.bn (.ls 7) .ln) 9 (.bn (.ls 7) .ln)) : Spt Nat)) (true,false),
    check "sw_tree_147" (sptWf ((.bs (.bn (.ls 7) .ln) 9 (.bn (.ls 7) (.ls 7))) : Spt Nat),sptIsEmpty ((.bs (.bn (.ls 7) .ln) 9 (.bn (.ls 7) (.ls 7))) : Spt Nat)) (true,false),
    check "sw_tree_148" (sptWf ((.bs (.bn (.ls 7) .ln) 9 (.bs .ln 9 .ln)) : Spt Nat),sptIsEmpty ((.bs (.bn (.ls 7) .ln) 9 (.bs .ln 9 .ln)) : Spt Nat)) (false,false),
    check "sw_tree_149" (sptWf ((.bs (.bn (.ls 7) .ln) 9 (.bs .ln 9 (.ls 7))) : Spt Nat),sptIsEmpty ((.bs (.bn (.ls 7) .ln) 9 (.bs .ln 9 (.ls 7))) : Spt Nat)) (true,false),
    check "sw_tree_150" (sptWf ((.bs (.bn (.ls 7) .ln) 9 (.bs (.ls 7) 9 .ln)) : Spt Nat),sptIsEmpty ((.bs (.bn (.ls 7) .ln) 9 (.bs (.ls 7) 9 .ln)) : Spt Nat)) (true,false),
    check "sw_tree_151" (sptWf ((.bs (.bn (.ls 7) .ln) 9 (.bs (.ls 7) 9 (.ls 7))) : Spt Nat),sptIsEmpty ((.bs (.bn (.ls 7) .ln) 9 (.bs (.ls 7) 9 (.ls 7))) : Spt Nat)) (true,false),
    check "sw_tree_152" (sptWf ((.bs (.bn (.ls 7) (.ls 7)) 9 .ln) : Spt Nat),sptIsEmpty ((.bs (.bn (.ls 7) (.ls 7)) 9 .ln) : Spt Nat)) (true,false),
    check "sw_tree_153" (sptWf ((.bs (.bn (.ls 7) (.ls 7)) 9 (.ls 7)) : Spt Nat),sptIsEmpty ((.bs (.bn (.ls 7) (.ls 7)) 9 (.ls 7)) : Spt Nat)) (true,false),
    check "sw_tree_154" (sptWf ((.bs (.bn (.ls 7) (.ls 7)) 9 (.bn .ln .ln)) : Spt Nat),sptIsEmpty ((.bs (.bn (.ls 7) (.ls 7)) 9 (.bn .ln .ln)) : Spt Nat)) (false,false),
    check "sw_tree_155" (sptWf ((.bs (.bn (.ls 7) (.ls 7)) 9 (.bn .ln (.ls 7))) : Spt Nat),sptIsEmpty ((.bs (.bn (.ls 7) (.ls 7)) 9 (.bn .ln (.ls 7))) : Spt Nat)) (true,false),
    check "sw_tree_156" (sptWf ((.bs (.bn (.ls 7) (.ls 7)) 9 (.bn (.ls 7) .ln)) : Spt Nat),sptIsEmpty ((.bs (.bn (.ls 7) (.ls 7)) 9 (.bn (.ls 7) .ln)) : Spt Nat)) (true,false),
    check "sw_tree_157" (sptWf ((.bs (.bn (.ls 7) (.ls 7)) 9 (.bn (.ls 7) (.ls 7))) : Spt Nat),sptIsEmpty ((.bs (.bn (.ls 7) (.ls 7)) 9 (.bn (.ls 7) (.ls 7))) : Spt Nat)) (true,false),
    check "sw_tree_158" (sptWf ((.bs (.bn (.ls 7) (.ls 7)) 9 (.bs .ln 9 .ln)) : Spt Nat),sptIsEmpty ((.bs (.bn (.ls 7) (.ls 7)) 9 (.bs .ln 9 .ln)) : Spt Nat)) (false,false),
    check "sw_tree_159" (sptWf ((.bs (.bn (.ls 7) (.ls 7)) 9 (.bs .ln 9 (.ls 7))) : Spt Nat),sptIsEmpty ((.bs (.bn (.ls 7) (.ls 7)) 9 (.bs .ln 9 (.ls 7))) : Spt Nat)) (true,false),
    check "sw_tree_160" (sptWf ((.bs (.bn (.ls 7) (.ls 7)) 9 (.bs (.ls 7) 9 .ln)) : Spt Nat),sptIsEmpty ((.bs (.bn (.ls 7) (.ls 7)) 9 (.bs (.ls 7) 9 .ln)) : Spt Nat)) (true,false),
    check "sw_tree_161" (sptWf ((.bs (.bn (.ls 7) (.ls 7)) 9 (.bs (.ls 7) 9 (.ls 7))) : Spt Nat),sptIsEmpty ((.bs (.bn (.ls 7) (.ls 7)) 9 (.bs (.ls 7) 9 (.ls 7))) : Spt Nat)) (true,false),
    check "sw_tree_162" (sptWf ((.bs (.bs .ln 9 .ln) 9 .ln) : Spt Nat),sptIsEmpty ((.bs (.bs .ln 9 .ln) 9 .ln) : Spt Nat)) (false,false),
    check "sw_tree_163" (sptWf ((.bs (.bs .ln 9 .ln) 9 (.ls 7)) : Spt Nat),sptIsEmpty ((.bs (.bs .ln 9 .ln) 9 (.ls 7)) : Spt Nat)) (false,false),
    check "sw_tree_164" (sptWf ((.bs (.bs .ln 9 .ln) 9 (.bn .ln .ln)) : Spt Nat),sptIsEmpty ((.bs (.bs .ln 9 .ln) 9 (.bn .ln .ln)) : Spt Nat)) (false,false),
    check "sw_tree_165" (sptWf ((.bs (.bs .ln 9 .ln) 9 (.bn .ln (.ls 7))) : Spt Nat),sptIsEmpty ((.bs (.bs .ln 9 .ln) 9 (.bn .ln (.ls 7))) : Spt Nat)) (false,false),
    check "sw_tree_166" (sptWf ((.bs (.bs .ln 9 .ln) 9 (.bn (.ls 7) .ln)) : Spt Nat),sptIsEmpty ((.bs (.bs .ln 9 .ln) 9 (.bn (.ls 7) .ln)) : Spt Nat)) (false,false),
    check "sw_tree_167" (sptWf ((.bs (.bs .ln 9 .ln) 9 (.bn (.ls 7) (.ls 7))) : Spt Nat),sptIsEmpty ((.bs (.bs .ln 9 .ln) 9 (.bn (.ls 7) (.ls 7))) : Spt Nat)) (false,false),
    check "sw_tree_168" (sptWf ((.bs (.bs .ln 9 .ln) 9 (.bs .ln 9 .ln)) : Spt Nat),sptIsEmpty ((.bs (.bs .ln 9 .ln) 9 (.bs .ln 9 .ln)) : Spt Nat)) (false,false),
    check "sw_tree_169" (sptWf ((.bs (.bs .ln 9 .ln) 9 (.bs .ln 9 (.ls 7))) : Spt Nat),sptIsEmpty ((.bs (.bs .ln 9 .ln) 9 (.bs .ln 9 (.ls 7))) : Spt Nat)) (false,false),
    check "sw_tree_170" (sptWf ((.bs (.bs .ln 9 .ln) 9 (.bs (.ls 7) 9 .ln)) : Spt Nat),sptIsEmpty ((.bs (.bs .ln 9 .ln) 9 (.bs (.ls 7) 9 .ln)) : Spt Nat)) (false,false),
    check "sw_tree_171" (sptWf ((.bs (.bs .ln 9 .ln) 9 (.bs (.ls 7) 9 (.ls 7))) : Spt Nat),sptIsEmpty ((.bs (.bs .ln 9 .ln) 9 (.bs (.ls 7) 9 (.ls 7))) : Spt Nat)) (false,false),
    check "sw_tree_172" (sptWf ((.bs (.bs .ln 9 (.ls 7)) 9 .ln) : Spt Nat),sptIsEmpty ((.bs (.bs .ln 9 (.ls 7)) 9 .ln) : Spt Nat)) (true,false),
    check "sw_tree_173" (sptWf ((.bs (.bs .ln 9 (.ls 7)) 9 (.ls 7)) : Spt Nat),sptIsEmpty ((.bs (.bs .ln 9 (.ls 7)) 9 (.ls 7)) : Spt Nat)) (true,false),
    check "sw_tree_174" (sptWf ((.bs (.bs .ln 9 (.ls 7)) 9 (.bn .ln .ln)) : Spt Nat),sptIsEmpty ((.bs (.bs .ln 9 (.ls 7)) 9 (.bn .ln .ln)) : Spt Nat)) (false,false),
    check "sw_tree_175" (sptWf ((.bs (.bs .ln 9 (.ls 7)) 9 (.bn .ln (.ls 7))) : Spt Nat),sptIsEmpty ((.bs (.bs .ln 9 (.ls 7)) 9 (.bn .ln (.ls 7))) : Spt Nat)) (true,false),
    check "sw_tree_176" (sptWf ((.bs (.bs .ln 9 (.ls 7)) 9 (.bn (.ls 7) .ln)) : Spt Nat),sptIsEmpty ((.bs (.bs .ln 9 (.ls 7)) 9 (.bn (.ls 7) .ln)) : Spt Nat)) (true,false),
    check "sw_tree_177" (sptWf ((.bs (.bs .ln 9 (.ls 7)) 9 (.bn (.ls 7) (.ls 7))) : Spt Nat),sptIsEmpty ((.bs (.bs .ln 9 (.ls 7)) 9 (.bn (.ls 7) (.ls 7))) : Spt Nat)) (true,false),
    check "sw_tree_178" (sptWf ((.bs (.bs .ln 9 (.ls 7)) 9 (.bs .ln 9 .ln)) : Spt Nat),sptIsEmpty ((.bs (.bs .ln 9 (.ls 7)) 9 (.bs .ln 9 .ln)) : Spt Nat)) (false,false),
    check "sw_tree_179" (sptWf ((.bs (.bs .ln 9 (.ls 7)) 9 (.bs .ln 9 (.ls 7))) : Spt Nat),sptIsEmpty ((.bs (.bs .ln 9 (.ls 7)) 9 (.bs .ln 9 (.ls 7))) : Spt Nat)) (true,false),
    check "sw_tree_180" (sptWf ((.bs (.bs .ln 9 (.ls 7)) 9 (.bs (.ls 7) 9 .ln)) : Spt Nat),sptIsEmpty ((.bs (.bs .ln 9 (.ls 7)) 9 (.bs (.ls 7) 9 .ln)) : Spt Nat)) (true,false),
    check "sw_tree_181" (sptWf ((.bs (.bs .ln 9 (.ls 7)) 9 (.bs (.ls 7) 9 (.ls 7))) : Spt Nat),sptIsEmpty ((.bs (.bs .ln 9 (.ls 7)) 9 (.bs (.ls 7) 9 (.ls 7))) : Spt Nat)) (true,false),
    check "sw_tree_182" (sptWf ((.bs (.bs (.ls 7) 9 .ln) 9 .ln) : Spt Nat),sptIsEmpty ((.bs (.bs (.ls 7) 9 .ln) 9 .ln) : Spt Nat)) (true,false),
    check "sw_tree_183" (sptWf ((.bs (.bs (.ls 7) 9 .ln) 9 (.ls 7)) : Spt Nat),sptIsEmpty ((.bs (.bs (.ls 7) 9 .ln) 9 (.ls 7)) : Spt Nat)) (true,false),
    check "sw_tree_184" (sptWf ((.bs (.bs (.ls 7) 9 .ln) 9 (.bn .ln .ln)) : Spt Nat),sptIsEmpty ((.bs (.bs (.ls 7) 9 .ln) 9 (.bn .ln .ln)) : Spt Nat)) (false,false),
    check "sw_tree_185" (sptWf ((.bs (.bs (.ls 7) 9 .ln) 9 (.bn .ln (.ls 7))) : Spt Nat),sptIsEmpty ((.bs (.bs (.ls 7) 9 .ln) 9 (.bn .ln (.ls 7))) : Spt Nat)) (true,false),
    check "sw_tree_186" (sptWf ((.bs (.bs (.ls 7) 9 .ln) 9 (.bn (.ls 7) .ln)) : Spt Nat),sptIsEmpty ((.bs (.bs (.ls 7) 9 .ln) 9 (.bn (.ls 7) .ln)) : Spt Nat)) (true,false),
    check "sw_tree_187" (sptWf ((.bs (.bs (.ls 7) 9 .ln) 9 (.bn (.ls 7) (.ls 7))) : Spt Nat),sptIsEmpty ((.bs (.bs (.ls 7) 9 .ln) 9 (.bn (.ls 7) (.ls 7))) : Spt Nat)) (true,false),
    check "sw_tree_188" (sptWf ((.bs (.bs (.ls 7) 9 .ln) 9 (.bs .ln 9 .ln)) : Spt Nat),sptIsEmpty ((.bs (.bs (.ls 7) 9 .ln) 9 (.bs .ln 9 .ln)) : Spt Nat)) (false,false),
    check "sw_tree_189" (sptWf ((.bs (.bs (.ls 7) 9 .ln) 9 (.bs .ln 9 (.ls 7))) : Spt Nat),sptIsEmpty ((.bs (.bs (.ls 7) 9 .ln) 9 (.bs .ln 9 (.ls 7))) : Spt Nat)) (true,false),
    check "sw_tree_190" (sptWf ((.bs (.bs (.ls 7) 9 .ln) 9 (.bs (.ls 7) 9 .ln)) : Spt Nat),sptIsEmpty ((.bs (.bs (.ls 7) 9 .ln) 9 (.bs (.ls 7) 9 .ln)) : Spt Nat)) (true,false),
    check "sw_tree_191" (sptWf ((.bs (.bs (.ls 7) 9 .ln) 9 (.bs (.ls 7) 9 (.ls 7))) : Spt Nat),sptIsEmpty ((.bs (.bs (.ls 7) 9 .ln) 9 (.bs (.ls 7) 9 (.ls 7))) : Spt Nat)) (true,false),
    check "sw_tree_192" (sptWf ((.bs (.bs (.ls 7) 9 (.ls 7)) 9 .ln) : Spt Nat),sptIsEmpty ((.bs (.bs (.ls 7) 9 (.ls 7)) 9 .ln) : Spt Nat)) (true,false),
    check "sw_tree_193" (sptWf ((.bs (.bs (.ls 7) 9 (.ls 7)) 9 (.ls 7)) : Spt Nat),sptIsEmpty ((.bs (.bs (.ls 7) 9 (.ls 7)) 9 (.ls 7)) : Spt Nat)) (true,false),
    check "sw_tree_194" (sptWf ((.bs (.bs (.ls 7) 9 (.ls 7)) 9 (.bn .ln .ln)) : Spt Nat),sptIsEmpty ((.bs (.bs (.ls 7) 9 (.ls 7)) 9 (.bn .ln .ln)) : Spt Nat)) (false,false),
    check "sw_tree_195" (sptWf ((.bs (.bs (.ls 7) 9 (.ls 7)) 9 (.bn .ln (.ls 7))) : Spt Nat),sptIsEmpty ((.bs (.bs (.ls 7) 9 (.ls 7)) 9 (.bn .ln (.ls 7))) : Spt Nat)) (true,false),
    check "sw_tree_196" (sptWf ((.bs (.bs (.ls 7) 9 (.ls 7)) 9 (.bn (.ls 7) .ln)) : Spt Nat),sptIsEmpty ((.bs (.bs (.ls 7) 9 (.ls 7)) 9 (.bn (.ls 7) .ln)) : Spt Nat)) (true,false),
    check "sw_tree_197" (sptWf ((.bs (.bs (.ls 7) 9 (.ls 7)) 9 (.bn (.ls 7) (.ls 7))) : Spt Nat),sptIsEmpty ((.bs (.bs (.ls 7) 9 (.ls 7)) 9 (.bn (.ls 7) (.ls 7))) : Spt Nat)) (true,false),
    check "sw_tree_198" (sptWf ((.bs (.bs (.ls 7) 9 (.ls 7)) 9 (.bs .ln 9 .ln)) : Spt Nat),sptIsEmpty ((.bs (.bs (.ls 7) 9 (.ls 7)) 9 (.bs .ln 9 .ln)) : Spt Nat)) (false,false),
    check "sw_tree_199" (sptWf ((.bs (.bs (.ls 7) 9 (.ls 7)) 9 (.bs .ln 9 (.ls 7))) : Spt Nat),sptIsEmpty ((.bs (.bs (.ls 7) 9 (.ls 7)) 9 (.bs .ln 9 (.ls 7))) : Spt Nat)) (true,false),
    check "sw_tree_200" (sptWf ((.bs (.bs (.ls 7) 9 (.ls 7)) 9 (.bs (.ls 7) 9 .ln)) : Spt Nat),sptIsEmpty ((.bs (.bs (.ls 7) 9 (.ls 7)) 9 (.bs (.ls 7) 9 .ln)) : Spt Nat)) (true,false),
    check "sw_tree_201" (sptWf ((.bs (.bs (.ls 7) 9 (.ls 7)) 9 (.bs (.ls 7) 9 (.ls 7))) : Spt Nat),sptIsEmpty ((.bs (.bs (.ls 7) 9 (.ls 7)) 9 (.bs (.ls 7) 9 (.ls 7))) : Spt Nat)) (true,false),
    check "sw_tree_202" (sptWf ((.bn (.ls 7) .ln) : Spt Nat),sptIsEmpty ((.bn (.ls 7) .ln) : Spt Nat)) (true,false),
    check "sw_tree_203" (sptWf ((.bs .ln 7 (.bs .ln 9 .ln)) : Spt Nat),sptIsEmpty ((.bs .ln 7 (.bs .ln 9 .ln)) : Spt Nat)) (false,false),
    check "sw_tree_204" (sptWf ((.bs .ln 7 (.bn (.ls 7) .ln)) : Spt Nat),sptIsEmpty ((.bs .ln 7 (.bn (.ls 7) .ln)) : Spt Nat)) (true,false),
    check "sw_tree_205" (sptWf ((.bn (.bs .ln 7 (.bs .ln 9 .ln)) (.ls 7)) : Spt Nat),sptIsEmpty ((.bn (.bs .ln 7 (.bs .ln 9 .ln)) (.ls 7)) : Spt Nat)) (false,false),
    check "sw_tree_206" (sptWf ((.bn (.bs .ln 7 (.bn (.ls 7) .ln)) .ln) : Spt Nat),sptIsEmpty ((.bn (.bs .ln 7 (.bn (.ls 7) .ln)) .ln) : Spt Nat)) (true,false),
    check "sw_tree_207" (sptWf ((.bs .ln 7 (.bn (.bs .ln 7 (.bs .ln 9 .ln)) (.ls 7))) : Spt Nat),sptIsEmpty ((.bs .ln 7 (.bn (.bs .ln 7 (.bs .ln 9 .ln)) (.ls 7))) : Spt Nat)) (false,false),
    check "sw_tree_208" (sptWf ((.bs .ln 7 (.bn (.bs .ln 7 (.bn (.ls 7) .ln)) .ln)) : Spt Nat),sptIsEmpty ((.bs .ln 7 (.bn (.bs .ln 7 (.bn (.ls 7) .ln)) .ln)) : Spt Nat)) (true,false),
    check "sw_tree_209" (sptWf ((.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bs .ln 9 .ln)) (.ls 7))) (.ls 7)) : Spt Nat),sptIsEmpty ((.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bs .ln 9 .ln)) (.ls 7))) (.ls 7)) : Spt Nat)) (false,false),
    check "sw_tree_210" (sptWf ((.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.ls 7) .ln)) .ln)) .ln) : Spt Nat),sptIsEmpty ((.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.ls 7) .ln)) .ln)) .ln) : Spt Nat)) (true,false),
    check "sw_tree_211" (sptWf ((.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bs .ln 9 .ln)) (.ls 7))) (.ls 7))) : Spt Nat),sptIsEmpty ((.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bs .ln 9 .ln)) (.ls 7))) (.ls 7))) : Spt Nat)) (false,false),
    check "sw_tree_212" (sptWf ((.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.ls 7) .ln)) .ln)) .ln)) : Spt Nat),sptIsEmpty ((.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.ls 7) .ln)) .ln)) .ln)) : Spt Nat)) (true,false),
    check "sw_tree_213" (sptWf ((.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bs .ln 9 .ln)) (.ls 7))) (.ls 7))) (.ls 7)) : Spt Nat),sptIsEmpty ((.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bs .ln 9 .ln)) (.ls 7))) (.ls 7))) (.ls 7)) : Spt Nat)) (false,false),
    check "sw_tree_214" (sptWf ((.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.ls 7) .ln)) .ln)) .ln)) .ln) : Spt Nat),sptIsEmpty ((.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.ls 7) .ln)) .ln)) .ln)) .ln) : Spt Nat)) (true,false),
    check "sw_tree_215" (sptWf ((.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bs .ln 9 .ln)) (.ls 7))) (.ls 7))) (.ls 7))) : Spt Nat),sptIsEmpty ((.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bs .ln 9 .ln)) (.ls 7))) (.ls 7))) (.ls 7))) : Spt Nat)) (false,false),
    check "sw_tree_216" (sptWf ((.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.ls 7) .ln)) .ln)) .ln)) .ln)) : Spt Nat),sptIsEmpty ((.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.ls 7) .ln)) .ln)) .ln)) .ln)) : Spt Nat)) (true,false),
    check "sw_tree_217" (sptWf ((.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bs .ln 9 .ln)) (.ls 7))) (.ls 7))) (.ls 7))) (.ls 7)) : Spt Nat),sptIsEmpty ((.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bs .ln 9 .ln)) (.ls 7))) (.ls 7))) (.ls 7))) (.ls 7)) : Spt Nat)) (false,false),
    check "sw_tree_218" (sptWf ((.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.ls 7) .ln)) .ln)) .ln)) .ln)) .ln) : Spt Nat),sptIsEmpty ((.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.ls 7) .ln)) .ln)) .ln)) .ln)) .ln) : Spt Nat)) (true,false),
    check "sw_tree_219" (sptWf ((.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bs .ln 9 .ln)) (.ls 7))) (.ls 7))) (.ls 7))) (.ls 7))) : Spt Nat),sptIsEmpty ((.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bs .ln 9 .ln)) (.ls 7))) (.ls 7))) (.ls 7))) (.ls 7))) : Spt Nat)) (false,false),
    check "sw_tree_220" (sptWf ((.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.ls 7) .ln)) .ln)) .ln)) .ln)) .ln)) : Spt Nat),sptIsEmpty ((.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.ls 7) .ln)) .ln)) .ln)) .ln)) .ln)) : Spt Nat)) (true,false),
    check "sw_tree_221" (sptWf ((.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bs .ln 9 .ln)) (.ls 7))) (.ls 7))) (.ls 7))) (.ls 7))) (.ls 7)) : Spt Nat),sptIsEmpty ((.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bs .ln 9 .ln)) (.ls 7))) (.ls 7))) (.ls 7))) (.ls 7))) (.ls 7)) : Spt Nat)) (false,false),
    check "sw_tree_222" (sptWf ((.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.ls 7) .ln)) .ln)) .ln)) .ln)) .ln)) .ln) : Spt Nat),sptIsEmpty ((.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.ls 7) .ln)) .ln)) .ln)) .ln)) .ln)) .ln) : Spt Nat)) (true,false),
    check "sw_tree_223" (sptWf ((.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bs .ln 9 .ln)) (.ls 7))) (.ls 7))) (.ls 7))) (.ls 7))) (.ls 7))) : Spt Nat),sptIsEmpty ((.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bs .ln 9 .ln)) (.ls 7))) (.ls 7))) (.ls 7))) (.ls 7))) (.ls 7))) : Spt Nat)) (false,false),
    check "sw_tree_224" (sptWf ((.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.ls 7) .ln)) .ln)) .ln)) .ln)) .ln)) .ln)) : Spt Nat),sptIsEmpty ((.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.ls 7) .ln)) .ln)) .ln)) .ln)) .ln)) .ln)) : Spt Nat)) (true,false),
    check "sw_tree_225" (sptWf ((.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bs .ln 9 .ln)) (.ls 7))) (.ls 7))) (.ls 7))) (.ls 7))) (.ls 7))) (.ls 7)) : Spt Nat),sptIsEmpty ((.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bs .ln 9 .ln)) (.ls 7))) (.ls 7))) (.ls 7))) (.ls 7))) (.ls 7))) (.ls 7)) : Spt Nat)) (false,false),
    check "sw_tree_226" (sptWf ((.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.ls 7) .ln)) .ln)) .ln)) .ln)) .ln)) .ln)) .ln) : Spt Nat),sptIsEmpty ((.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.ls 7) .ln)) .ln)) .ln)) .ln)) .ln)) .ln)) .ln) : Spt Nat)) (true,false),
    check "sw_tree_227" (sptWf ((.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bs .ln 9 .ln)) (.ls 7))) (.ls 7))) (.ls 7))) (.ls 7))) (.ls 7))) (.ls 7))) : Spt Nat),sptIsEmpty ((.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bs .ln 9 .ln)) (.ls 7))) (.ls 7))) (.ls 7))) (.ls 7))) (.ls 7))) (.ls 7))) : Spt Nat)) (false,false),
    check "sw_tree_228" (sptWf ((.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.ls 7) .ln)) .ln)) .ln)) .ln)) .ln)) .ln)) .ln)) : Spt Nat),sptIsEmpty ((.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.ls 7) .ln)) .ln)) .ln)) .ln)) .ln)) .ln)) .ln)) : Spt Nat)) (true,false),
    check "sw_tree_229" (sptWf ((.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bs .ln 9 .ln)) (.ls 7))) (.ls 7))) (.ls 7))) (.ls 7))) (.ls 7))) (.ls 7))) (.ls 7)) : Spt Nat),sptIsEmpty ((.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bs .ln 9 .ln)) (.ls 7))) (.ls 7))) (.ls 7))) (.ls 7))) (.ls 7))) (.ls 7))) (.ls 7)) : Spt Nat)) (false,false),
    check "sw_tree_230" (sptWf ((.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.ls 7) .ln)) .ln)) .ln)) .ln)) .ln)) .ln)) .ln)) .ln) : Spt Nat),sptIsEmpty ((.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.ls 7) .ln)) .ln)) .ln)) .ln)) .ln)) .ln)) .ln)) .ln) : Spt Nat)) (true,false),
    check "sw_tree_231" (sptWf ((.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bs .ln 9 .ln)) (.ls 7))) (.ls 7))) (.ls 7))) (.ls 7))) (.ls 7))) (.ls 7))) (.ls 7))) : Spt Nat),sptIsEmpty ((.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bs .ln 9 .ln)) (.ls 7))) (.ls 7))) (.ls 7))) (.ls 7))) (.ls 7))) (.ls 7))) (.ls 7))) : Spt Nat)) (false,false),
    check "sw_tree_232" (sptWf ((.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.ls 7) .ln)) .ln)) .ln)) .ln)) .ln)) .ln)) .ln)) .ln)) : Spt Nat),sptIsEmpty ((.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.ls 7) .ln)) .ln)) .ln)) .ln)) .ln)) .ln)) .ln)) .ln)) : Spt Nat)) (true,false),
    check "sw_tree_233" (sptWf ((.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bs .ln 9 .ln)) (.ls 7))) (.ls 7))) (.ls 7))) (.ls 7))) (.ls 7))) (.ls 7))) (.ls 7))) (.ls 7)) : Spt Nat),sptIsEmpty ((.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bs .ln 9 .ln)) (.ls 7))) (.ls 7))) (.ls 7))) (.ls 7))) (.ls 7))) (.ls 7))) (.ls 7))) (.ls 7)) : Spt Nat)) (false,false),
    check "sw_tree_234" (sptWf ((.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.ls 7) .ln)) .ln)) .ln)) .ln)) .ln)) .ln)) .ln)) .ln)) .ln) : Spt Nat),sptIsEmpty ((.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.ls 7) .ln)) .ln)) .ln)) .ln)) .ln)) .ln)) .ln)) .ln)) .ln) : Spt Nat)) (true,false),
    check "sw_tree_235" (sptWf ((.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bs .ln 9 .ln)) (.ls 7))) (.ls 7))) (.ls 7))) (.ls 7))) (.ls 7))) (.ls 7))) (.ls 7))) (.ls 7))) : Spt Nat),sptIsEmpty ((.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bs .ln 9 .ln)) (.ls 7))) (.ls 7))) (.ls 7))) (.ls 7))) (.ls 7))) (.ls 7))) (.ls 7))) (.ls 7))) : Spt Nat)) (false,false),
    check "sw_tree_236" (sptWf ((.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.ls 7) .ln)) .ln)) .ln)) .ln)) .ln)) .ln)) .ln)) .ln)) .ln)) : Spt Nat),sptIsEmpty ((.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.ls 7) .ln)) .ln)) .ln)) .ln)) .ln)) .ln)) .ln)) .ln)) .ln)) : Spt Nat)) (true,false),
    check "sw_tree_237" (sptWf ((.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bs .ln 9 .ln)) (.ls 7))) (.ls 7))) (.ls 7))) (.ls 7))) (.ls 7))) (.ls 7))) (.ls 7))) (.ls 7))) (.ls 7)) : Spt Nat),sptIsEmpty ((.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bs .ln 9 .ln)) (.ls 7))) (.ls 7))) (.ls 7))) (.ls 7))) (.ls 7))) (.ls 7))) (.ls 7))) (.ls 7))) (.ls 7)) : Spt Nat)) (false,false),
    check "sw_tree_238" (sptWf ((.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.ls 7) .ln)) .ln)) .ln)) .ln)) .ln)) .ln)) .ln)) .ln)) .ln)) .ln) : Spt Nat),sptIsEmpty ((.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.ls 7) .ln)) .ln)) .ln)) .ln)) .ln)) .ln)) .ln)) .ln)) .ln)) .ln) : Spt Nat)) (true,false),
    check "sw_tree_239" (sptWf ((.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bs .ln 9 .ln)) (.ls 7))) (.ls 7))) (.ls 7))) (.ls 7))) (.ls 7))) (.ls 7))) (.ls 7))) (.ls 7))) (.ls 7))) : Spt Nat),sptIsEmpty ((.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bs .ln 9 .ln)) (.ls 7))) (.ls 7))) (.ls 7))) (.ls 7))) (.ls 7))) (.ls 7))) (.ls 7))) (.ls 7))) (.ls 7))) : Spt Nat)) (false,false),
    check "sw_tree_240" (sptWf ((.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.ls 7) .ln)) .ln)) .ln)) .ln)) .ln)) .ln)) .ln)) .ln)) .ln)) .ln)) : Spt Nat),sptIsEmpty ((.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.ls 7) .ln)) .ln)) .ln)) .ln)) .ln)) .ln)) .ln)) .ln)) .ln)) .ln)) : Spt Nat)) (true,false),
    check "sw_tree_241" (sptWf ((.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bs .ln 9 .ln)) (.ls 7))) (.ls 7))) (.ls 7))) (.ls 7))) (.ls 7))) (.ls 7))) (.ls 7))) (.ls 7))) (.ls 7))) (.ls 7)) : Spt Nat),sptIsEmpty ((.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bs .ln 9 .ln)) (.ls 7))) (.ls 7))) (.ls 7))) (.ls 7))) (.ls 7))) (.ls 7))) (.ls 7))) (.ls 7))) (.ls 7))) (.ls 7)) : Spt Nat)) (false,false),
    check "sw_tree_242" (sptWf ((.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.ls 7) .ln)) .ln)) .ln)) .ln)) .ln)) .ln)) .ln)) .ln)) .ln)) .ln)) .ln) : Spt Nat),sptIsEmpty ((.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.ls 7) .ln)) .ln)) .ln)) .ln)) .ln)) .ln)) .ln)) .ln)) .ln)) .ln)) .ln) : Spt Nat)) (true,false),
    check "sw_tree_243" (sptWf ((.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bs .ln 9 .ln)) (.ls 7))) (.ls 7))) (.ls 7))) (.ls 7))) (.ls 7))) (.ls 7))) (.ls 7))) (.ls 7))) (.ls 7))) (.ls 7))) : Spt Nat),sptIsEmpty ((.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bs .ln 9 .ln)) (.ls 7))) (.ls 7))) (.ls 7))) (.ls 7))) (.ls 7))) (.ls 7))) (.ls 7))) (.ls 7))) (.ls 7))) (.ls 7))) : Spt Nat)) (false,false),
    check "sw_tree_244" (sptWf ((.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.ls 7) .ln)) .ln)) .ln)) .ln)) .ln)) .ln)) .ln)) .ln)) .ln)) .ln)) .ln)) : Spt Nat),sptIsEmpty ((.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.ls 7) .ln)) .ln)) .ln)) .ln)) .ln)) .ln)) .ln)) .ln)) .ln)) .ln)) .ln)) : Spt Nat)) (true,false),
    check "sw_tree_245" (sptWf ((.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bs .ln 9 .ln)) (.ls 7))) (.ls 7))) (.ls 7))) (.ls 7))) (.ls 7))) (.ls 7))) (.ls 7))) (.ls 7))) (.ls 7))) (.ls 7))) (.ls 7)) : Spt Nat),sptIsEmpty ((.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bs .ln 9 .ln)) (.ls 7))) (.ls 7))) (.ls 7))) (.ls 7))) (.ls 7))) (.ls 7))) (.ls 7))) (.ls 7))) (.ls 7))) (.ls 7))) (.ls 7)) : Spt Nat)) (false,false),
    check "sw_tree_246" (sptWf ((.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.ls 7) .ln)) .ln)) .ln)) .ln)) .ln)) .ln)) .ln)) .ln)) .ln)) .ln)) .ln)) .ln) : Spt Nat),sptIsEmpty ((.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.ls 7) .ln)) .ln)) .ln)) .ln)) .ln)) .ln)) .ln)) .ln)) .ln)) .ln)) .ln)) .ln) : Spt Nat)) (true,false),
    check "sw_tree_247" (sptWf ((.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bs .ln 9 .ln)) (.ls 7))) (.ls 7))) (.ls 7))) (.ls 7))) (.ls 7))) (.ls 7))) (.ls 7))) (.ls 7))) (.ls 7))) (.ls 7))) (.ls 7))) : Spt Nat),sptIsEmpty ((.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bs .ln 9 .ln)) (.ls 7))) (.ls 7))) (.ls 7))) (.ls 7))) (.ls 7))) (.ls 7))) (.ls 7))) (.ls 7))) (.ls 7))) (.ls 7))) (.ls 7))) : Spt Nat)) (false,false),
    check "sw_tree_248" (sptWf ((.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.ls 7) .ln)) .ln)) .ln)) .ln)) .ln)) .ln)) .ln)) .ln)) .ln)) .ln)) .ln)) .ln)) : Spt Nat),sptIsEmpty ((.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.ls 7) .ln)) .ln)) .ln)) .ln)) .ln)) .ln)) .ln)) .ln)) .ln)) .ln)) .ln)) .ln)) : Spt Nat)) (true,false),
    check "sw_tree_249" (sptWf ((.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bs .ln 9 .ln)) (.ls 7))) (.ls 7))) (.ls 7))) (.ls 7))) (.ls 7))) (.ls 7))) (.ls 7))) (.ls 7))) (.ls 7))) (.ls 7))) (.ls 7))) (.ls 7)) : Spt Nat),sptIsEmpty ((.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bn (.bs .ln 7 (.bs .ln 9 .ln)) (.ls 7))) (.ls 7))) (.ls 7))) (.ls 7))) (.ls 7))) (.ls 7))) (.ls 7))) (.ls 7))) (.ls 7))) (.ls 7))) (.ls 7))) (.ls 7)) : Spt Nat)) (false,false),
    check "sw_function_0" (sptWf (.ln : Spt (Nat → Nat)),sptIsEmpty (.ln : Spt (Nat → Nat))) (true,true),
    check "sw_function_1" (sptWf ((.ls (fun n : Nat => n+1)) : Spt (Nat → Nat)),sptIsEmpty ((.ls (fun n : Nat => n+1)) : Spt (Nat → Nat))) (true,false),
    check "sw_function_2" (sptWf ((.bn (.ls (fun n : Nat => n+1)) .ln) : Spt (Nat → Nat)),sptIsEmpty ((.bn (.ls (fun n : Nat => n+1)) .ln) : Spt (Nat → Nat))) (true,false),
    check "sw_function_3" (sptWf ((.bs .ln (fun n : Nat => n+1) .ln) : Spt (Nat → Nat)),sptIsEmpty ((.bs .ln (fun n : Nat => n+1) .ln) : Spt (Nat → Nat))) (false,false)
  ]
  if results.all id then
    IO.println "PASS original sptree wf complete outputs (254)"
    pure true
  else pure false

end Flapjack.Test.SptreeWfDefinitionParity
