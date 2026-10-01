import Flapjack.Pancake.WordConvs.NoInstall

namespace Flapjack.Test.WordConvsNoInstallDefParity
open Flapjack
private def cuts : WordLangCutsetsHOL := (.ln,.ln)
private def bad {width : Nat} [NeZero width] : WordLangProgHOL (BitVec width) := .install 1 2 3 4 cuts
/-- A complete source-conjunction instance with failing recursive bodies and
nonempty real payloads; no individual desired clause is supplied as a premise. -/
private theorem sourceInstance {width : Nat} [NeZero width]
    (r : Option (List Nat × WordLangCutsetsHOL × WordLangProgHOL (BitVec width) × Nat × Nat))
    (h : Option (Nat × WordLangProgHOL (BitVec width) × Nat × Nat)) :
    (noInstallSubprogsHOL (width := width) (.mustTerminate (bad)) = noInstallSubprogsHOL (width := width) (bad)) ∧
    (noInstallSubprogsHOL (width := width) (.seq (bad) (.skip)) = (noInstallSubprogsHOL (width := width) (bad) && noInstallSubprogsHOL (width := width) (.skip))) ∧
    (noInstallSubprogsHOL (width := width) (.loop (.ln) (bad) (.ln)) = noInstallSubprogsHOL (width := width) (bad)) ∧
    (noInstallSubprogsHOL (width := width) (.ite (.equal) (2) ((.reg 3)) (bad) (.skip)) = (noInstallSubprogsHOL (width := width) (bad) && noInstallSubprogsHOL (width := width) (.skip))) ∧
    (noInstallSubprogsHOL (width := width) (.call (r) (none) ([1,2]) (h)) =
      ((match (r) with | none => true | some (_,_,body,_,_) => noInstallSubprogsHOL (width := width) body) &&
       (match (h) with | none => true | some (_,body,_,_) => noInstallSubprogsHOL (width := width) body))) ∧
    noInstallSubprogsHOL (width := width) (.alloc (3) (cuts)) = true ∧
    noInstallSubprogsHOL (width := width) (.locValue (2) (3)) = true ∧
    noInstallSubprogsHOL (width := width) (.shareInst (.load) (8) ((.var 9))) = true ∧
    noInstallSubprogsHOL (width := width) (.install (1) (2) (3) (4) (cuts)) = false ∧
    noInstallSubprogsHOL (width := width) .skip = true ∧
    noInstallSubprogsHOL (width := width) (.move (5) ([(1,2),(2,3)])) = true ∧
    noInstallSubprogsHOL (width := width) (.inst ((.const 2 7))) = true ∧
    noInstallSubprogsHOL (width := width) (.assign (2) ((.const 7))) = true ∧
    noInstallSubprogsHOL (width := width) (.get (2) (.currHeap)) = true ∧
    noInstallSubprogsHOL (width := width) (.set (.currHeap) ((.const 7))) = true ∧
    noInstallSubprogsHOL (width := width) (.store ((.var 2)) (3)) = true ∧
    noInstallSubprogsHOL (width := width) (.storeConsts (2) (3) (4) (5) ([(true,7),(false,8)])) = true ∧
    noInstallSubprogsHOL (width := width) (.raise (3)) = true ∧
    noInstallSubprogsHOL (width := width) (.return (4) ([5,6])) = true ∧
    noInstallSubprogsHOL (width := width) (.break (7)) = true ∧
    noInstallSubprogsHOL (width := width) (.continue (8)) = true ∧
    noInstallSubprogsHOL (width := width) .tick = true ∧
    noInstallSubprogsHOL (width := width) (.opCurrHeap (.add) (2) (3)) = true ∧
    noInstallSubprogsHOL (width := width) (.codeBufferWrite (2) (3)) = true ∧
    noInstallSubprogsHOL (width := width) (.dataBufferWrite (4) (5)) = true ∧
    noInstallSubprogsHOL (width := width) (.ffi ((.implode [105,111])) (2) (3) (4) (5) (cuts)) = true := noInstallDef (width := width)
      bad bad .skip bad .ln .ln .equal 2 (.reg 3)
      r none [1,2] h
      3 cuts 2 3 .load 8 (.var 9) 1 2 3 4 cuts
      5 [(1,2),(2,3)] (.const 2 7) 2 (.const 7) 2 .currHeap .currHeap
      (.const 7) (.var 2) 3 2 3 4 5 [(true,7),(false,8)]
      3 4 [5,6] 7 8 .add 2 3 2 3 4 5 (.implode [105,111]) 2 3 4 5 cuts

-- wcni_01_mt: (F,T)
example : noInstallSubprogsHOL (.mustTerminate bad : WordLangProgHOL (BitVec 64)) = false := by
  have clause := (sourceInstance (width := 64) none (some (7,bad,8,9))).1
  rw [clause]
  rfl

-- wcni_02_seq: (F,T)
example : noInstallSubprogsHOL (.seq bad .skip : WordLangProgHOL (BitVec 64)) = false := by
  have clause := (sourceInstance (width := 64) none (some (7,bad,8,9))).2.1
  rw [clause]
  rfl

-- wcni_03_loop: (F,T)
example : noInstallSubprogsHOL (.loop .ln bad .ln : WordLangProgHOL (BitVec 64)) = false := by
  have clause := (sourceInstance (width := 64) none (some (7,bad,8,9))).2.2.1
  rw [clause]
  rfl

-- wcni_04_if: (F,T)
example : noInstallSubprogsHOL (.ite .equal 2 (.reg 3) bad .skip : WordLangProgHOL (BitVec 64)) = false := by
  have clause := (sourceInstance (width := 64) none (some (7,bad,8,9))).2.2.2.1
  rw [clause]
  rfl

-- wcni_05_call: (F,T)
example : noInstallSubprogsHOL (.call none none [1,2] (some (7,bad,8,9)) : WordLangProgHOL (BitVec 64)) = false := by
  have clause := (sourceInstance (width := 64) none (some (7,bad,8,9))).2.2.2.2.1
  rw [clause]
  rfl

-- wcni_06_alloc: (T,T)
example : noInstallSubprogsHOL (.alloc 3 cuts : WordLangProgHOL (BitVec 64)) = true := by
  have clause := (sourceInstance (width := 64) none (some (7,bad,8,9))).2.2.2.2.2.1
  exact clause

-- wcni_07_loc: (T,T)
example : noInstallSubprogsHOL (.locValue 2 3 : WordLangProgHOL (BitVec 64)) = true := by
  have clause := (sourceInstance (width := 64) none (some (7,bad,8,9))).2.2.2.2.2.2.1
  exact clause

-- wcni_08_share: (T,T)
example : noInstallSubprogsHOL (.shareInst .load 8 (.var 9) : WordLangProgHOL (BitVec 64)) = true := by
  have clause := (sourceInstance (width := 64) none (some (7,bad,8,9))).2.2.2.2.2.2.2.1
  exact clause

-- wcni_09_install: (F,T)
example : noInstallSubprogsHOL (.install 1 2 3 4 cuts : WordLangProgHOL (BitVec 64)) = false := by
  have clause := (sourceInstance (width := 64) none (some (7,bad,8,9))).2.2.2.2.2.2.2.2.1
  exact clause

-- wcni_10_skip: (T,T)
example : noInstallSubprogsHOL (.skip : WordLangProgHOL (BitVec 64)) = true := by
  have clause := (sourceInstance (width := 64) none (some (7,bad,8,9))).2.2.2.2.2.2.2.2.2.1
  exact clause

-- wcni_11_move: (T,T)
example : noInstallSubprogsHOL (.move 5 [(1,2),(2,3)] : WordLangProgHOL (BitVec 64)) = true := by
  have clause := (sourceInstance (width := 64) none (some (7,bad,8,9))).2.2.2.2.2.2.2.2.2.2.1
  exact clause

-- wcni_12_inst: (T,T)
example : noInstallSubprogsHOL (.inst (.const 2 7) : WordLangProgHOL (BitVec 64)) = true := by
  have clause := (sourceInstance (width := 64) none (some (7,bad,8,9))).2.2.2.2.2.2.2.2.2.2.2.1
  exact clause

-- wcni_13_assign: (T,T)
example : noInstallSubprogsHOL (.assign 2 (.const 7) : WordLangProgHOL (BitVec 64)) = true := by
  have clause := (sourceInstance (width := 64) none (some (7,bad,8,9))).2.2.2.2.2.2.2.2.2.2.2.2.1
  exact clause

-- wcni_14_get: (T,T)
example : noInstallSubprogsHOL (.get 2 .currHeap : WordLangProgHOL (BitVec 64)) = true := by
  have clause := (sourceInstance (width := 64) none (some (7,bad,8,9))).2.2.2.2.2.2.2.2.2.2.2.2.2.1
  exact clause

-- wcni_15_set: (T,T)
example : noInstallSubprogsHOL (.set .currHeap (.const 7) : WordLangProgHOL (BitVec 64)) = true := by
  have clause := (sourceInstance (width := 64) none (some (7,bad,8,9))).2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  exact clause

-- wcni_16_store: (T,T)
example : noInstallSubprogsHOL (.store (.var 2) 3 : WordLangProgHOL (BitVec 64)) = true := by
  have clause := (sourceInstance (width := 64) none (some (7,bad,8,9))).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  exact clause

-- wcni_17_consts: (T,T)
example : noInstallSubprogsHOL (.storeConsts 2 3 4 5 [(true,7),(false,8)] : WordLangProgHOL (BitVec 64)) = true := by
  have clause := (sourceInstance (width := 64) none (some (7,bad,8,9))).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  exact clause

-- wcni_18_raise: (T,T)
example : noInstallSubprogsHOL (.raise 3 : WordLangProgHOL (BitVec 64)) = true := by
  have clause := (sourceInstance (width := 64) none (some (7,bad,8,9))).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  exact clause

-- wcni_19_return: (T,T)
example : noInstallSubprogsHOL (.return 4 [5,6] : WordLangProgHOL (BitVec 64)) = true := by
  have clause := (sourceInstance (width := 64) none (some (7,bad,8,9))).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  exact clause

-- wcni_20_break: (T,T)
example : noInstallSubprogsHOL (.break 7 : WordLangProgHOL (BitVec 64)) = true := by
  have clause := (sourceInstance (width := 64) none (some (7,bad,8,9))).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  exact clause

-- wcni_21_continue: (T,T)
example : noInstallSubprogsHOL (.continue 8 : WordLangProgHOL (BitVec 64)) = true := by
  have clause := (sourceInstance (width := 64) none (some (7,bad,8,9))).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  exact clause

-- wcni_22_tick: (T,T)
example : noInstallSubprogsHOL (.tick : WordLangProgHOL (BitVec 64)) = true := by
  have clause := (sourceInstance (width := 64) none (some (7,bad,8,9))).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  exact clause

-- wcni_23_heap: (T,T)
example : noInstallSubprogsHOL (.opCurrHeap .add 2 3 : WordLangProgHOL (BitVec 64)) = true := by
  have clause := (sourceInstance (width := 64) none (some (7,bad,8,9))).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  exact clause

-- wcni_24_code: (T,T)
example : noInstallSubprogsHOL (.codeBufferWrite 2 3 : WordLangProgHOL (BitVec 64)) = true := by
  have clause := (sourceInstance (width := 64) none (some (7,bad,8,9))).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  exact clause

-- wcni_25_data: (T,T)
example : noInstallSubprogsHOL (.dataBufferWrite 4 5 : WordLangProgHOL (BitVec 64)) = true := by
  have clause := (sourceInstance (width := 64) none (some (7,bad,8,9))).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  exact clause

-- wcni_26_ffi: (T,T)
example : noInstallSubprogsHOL (.ffi (.implode [105,111]) 2 3 4 5 cuts : WordLangProgHOL (BitVec 64)) = true := by
  have clause := (sourceInstance (width := 64) none (some (7,bad,8,9))).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  exact clause

-- wcni_call_none_none_width1
example : noInstallSubprogsHOL (.call none none [1,2] none : WordLangProgHOL (BitVec 1)) = true := by
  have clause := (sourceInstance (width := 1) none none).2.2.2.2.1
  rw [clause]
  rfl

-- wcni_call_return_only_width1
example : noInstallSubprogsHOL (.call (some ([1,2],cuts,bad,8,9)) none [1,2] none : WordLangProgHOL (BitVec 1)) = false := by
  have clause := (sourceInstance (width := 1) (some ([1,2],cuts,bad,8,9)) none).2.2.2.2.1
  rw [clause]
  rfl

-- wcni_call_both_present_width1
example : noInstallSubprogsHOL (.call (some ([1,2],cuts,.skip,8,9)) none [1,2] (some (7,bad,8,9)) : WordLangProgHOL (BitVec 1)) = false := by
  have clause := (sourceInstance (width := 1) (some ([1,2],cuts,.skip,8,9)) (some (7,bad,8,9))).2.2.2.2.1
  rw [clause]
  rfl

end Flapjack.Test.WordConvsNoInstallDefParity
