import Flapjack.Compiler.Backend.WordAlloc.GetPrefs
namespace Flapjack.Test.WordAllocGetPrefsParity
open Flapjack Flapjack.WordAlloc
abbrev P := WordLangProgHOL (BitVec 64)
private def m1 : P := .move 2 [(1,3)]
private def m2 : P := .move 4 [(5,7)]
private def acc : List (Nat × Nat × Nat) := [(9,8,7)]

-- prefs_skip=T
example : getPrefs (.skip : P) [(9,8,7)] = [(9,8,7)] := by rfl

-- prefs_empty=T
example : getPrefs (.move 0 [] : P) [(9,8,7)] = [(9,8,7)] := by rfl

-- prefs_move=T
example : getPrefs (.move 2 [(1,3),(4,5)] : P) [(9,8,7)] = [(2,1,3),(2,4,5),(9,8,7)] := by rfl

-- prefs_duplicate=T
example : getPrefs (.move 2 [(1,3),(1,3)] : P) [] = [(2,1,3),(2,1,3)] := by rfl

-- prefs_self=T
example : getPrefs (.move 0 [(3,3)] : P) [] = [(0,3,3)] := by rfl

-- prefs_seq=T
example : getPrefs (.seq m1 m2 : P) acc = [(2,1,3),(4,5,7),(9,8,7)] := by rfl

-- prefs_if_reg=T
example : getPrefs (.ite .equal 0 (.reg 1) m1 m2 : P) acc = [(2,1,3),(4,5,7),(9,8,7)] := by rfl

-- prefs_if_imm=T
example : getPrefs (.ite .less 99 (.imm 0) m1 m2 : P) acc = [(2,1,3),(4,5,7),(9,8,7)] := by rfl

-- prefs_must=T
example : getPrefs (.mustTerminate m1 : P) acc = [(2,1,3),(9,8,7)] := by rfl

-- prefs_loop=T
example : getPrefs (.loop .ln m1 (.ls ()) : P) acc = [(2,1,3),(9,8,7)] := by rfl

-- prefs_tail=T
example : getPrefs (.call none (some 123) [1,2] none : P) acc = acc := by rfl

-- prefs_tail_handler=T
example : getPrefs (.call none none [] (some (1,m2,11,13)) : P) acc = acc := by rfl

-- prefs_return=T
example : getPrefs (.call (some ([1],(.ln,.ln),m1,17,19)) none [] none : P) acc = [(2,1,3),(9,8,7)] := by rfl

-- prefs_both=T
example : getPrefs (.call (some ([1],(.ln,.ln),m1,17,19)) none [] (some (1,m2,11,13)) : P) acc = [(4,5,7),(2,1,3),(9,8,7)] := by rfl

-- prefs_nested=T
example : getPrefs (.seq (.mustTerminate m1) (.loop .ln m2 .ln) : P) acc = [(2,1,3),(4,5,7),(9,8,7)] := by rfl

-- prefs_ignored=T
example : getPrefs (.return 3 [1,2,3] : P) acc = acc := by rfl

-- prefs_large=T
example : getPrefs (.move 18446744073709551616 [(18446744073709551617,18446744073709551619)] : P) [] = [(18446744073709551616,18446744073709551617,18446744073709551619)] := by rfl

end Flapjack.Test.WordAllocGetPrefsParity
