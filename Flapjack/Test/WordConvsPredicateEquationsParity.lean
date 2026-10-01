import Flapjack.Pancake.WordConvs.PredicateEquations

namespace Flapjack.Test.WordConvsNoAllocDefParity
open Flapjack
private def cuts : WordLangCutsetsHOL := (.ln,.ln)
private def bad {width : Nat} [NeZero width] : WordLangProgHOL (BitVec width) := .alloc 1 cuts
/-- A complete source-conjunction instance with failing recursive bodies and
nonempty real payloads; no individual desired clause is supplied as a premise. -/
private theorem sourceInstance {width : Nat} [NeZero width]
    (r : Option (List Nat × WordLangCutsetsHOL × WordLangProgHOL (BitVec width) × Nat × Nat))
    (h : Option (Nat × WordLangProgHOL (BitVec width) × Nat × Nat)) :
    (noAllocSubprogsHOL (width := width) (.mustTerminate (bad)) = noAllocSubprogsHOL (width := width) (bad)) ∧
    (noAllocSubprogsHOL (width := width) (.seq (bad) (.skip)) = (noAllocSubprogsHOL (width := width) (bad) && noAllocSubprogsHOL (width := width) (.skip))) ∧
    (noAllocSubprogsHOL (width := width) (.loop (.ln) (bad) (.ln)) = noAllocSubprogsHOL (width := width) (bad)) ∧
    (noAllocSubprogsHOL (width := width) (.ite (.equal) (2) ((.reg 3)) (bad) (.skip)) = (noAllocSubprogsHOL (width := width) (bad) && noAllocSubprogsHOL (width := width) (.skip))) ∧
    (noAllocSubprogsHOL (width := width) (.call (r) (none) ([1,2]) (h)) =
      ((match (r) with | none => true | some (_,_,body,_,_) => noAllocSubprogsHOL (width := width) body) &&
       (match (h) with | none => true | some (_,body,_,_) => noAllocSubprogsHOL (width := width) body))) ∧
    noAllocSubprogsHOL (width := width) (.alloc (3) (cuts)) = false ∧
    noAllocSubprogsHOL (width := width) (.locValue (2) (3)) = true ∧
    noAllocSubprogsHOL (width := width) (.shareInst (.load) (8) ((.var 9))) = true ∧
    noAllocSubprogsHOL (width := width) (.install (1) (2) (3) (4) (cuts)) = true ∧
    noAllocSubprogsHOL (width := width) .skip = true ∧
    noAllocSubprogsHOL (width := width) (.move (5) ([(1,2),(2,3)])) = true ∧
    noAllocSubprogsHOL (width := width) (.inst ((.const 2 7))) = true ∧
    noAllocSubprogsHOL (width := width) (.assign (2) ((.const 7))) = true ∧
    noAllocSubprogsHOL (width := width) (.get (2) (.currHeap)) = true ∧
    noAllocSubprogsHOL (width := width) (.set (.currHeap) ((.const 7))) = true ∧
    noAllocSubprogsHOL (width := width) (.store ((.var 2)) (3)) = true ∧
    noAllocSubprogsHOL (width := width) (.storeConsts (2) (3) (4) (5) ([(true,7),(false,8)])) = true ∧
    noAllocSubprogsHOL (width := width) (.raise (3)) = true ∧
    noAllocSubprogsHOL (width := width) (.return (4) ([5,6])) = true ∧
    noAllocSubprogsHOL (width := width) (.break (7)) = true ∧
    noAllocSubprogsHOL (width := width) (.continue (8)) = true ∧
    noAllocSubprogsHOL (width := width) .tick = true ∧
    noAllocSubprogsHOL (width := width) (.opCurrHeap (.add) (2) (3)) = true ∧
    noAllocSubprogsHOL (width := width) (.codeBufferWrite (2) (3)) = true ∧
    noAllocSubprogsHOL (width := width) (.dataBufferWrite (4) (5)) = true ∧
    noAllocSubprogsHOL (width := width) (.ffi ((.implode [105,111])) (2) (3) (4) (5) (cuts)) = true := noAllocDef (width := width)
      bad bad .skip bad .ln .ln .equal 2 (.reg 3)
      r none [1,2] h
      3 cuts 2 3 .load 8 (.var 9) 1 2 3 4 cuts
      5 [(1,2),(2,3)] (.const 2 7) 2 (.const 7) 2 .currHeap .currHeap
      (.const 7) (.var 2) 3 2 3 4 5 [(true,7),(false,8)]
      3 4 [5,6] 7 8 .add 2 3 2 3 4 5 (.implode [105,111]) 2 3 4 5 cuts

-- wcna_01_mt: (F,T)
example : noAllocSubprogsHOL (.mustTerminate bad : WordLangProgHOL (BitVec 64)) = false := by
  have clause := (sourceInstance (width := 64) none (some (7,bad,8,9))).1
  rw [clause]
  rfl

-- wcna_02_seq: (F,T)
example : noAllocSubprogsHOL (.seq bad .skip : WordLangProgHOL (BitVec 64)) = false := by
  have clause := (sourceInstance (width := 64) none (some (7,bad,8,9))).2.1
  rw [clause]
  rfl

-- wcna_03_loop: (F,T)
example : noAllocSubprogsHOL (.loop .ln bad .ln : WordLangProgHOL (BitVec 64)) = false := by
  have clause := (sourceInstance (width := 64) none (some (7,bad,8,9))).2.2.1
  rw [clause]
  rfl

-- wcna_04_if: (F,T)
example : noAllocSubprogsHOL (.ite .equal 2 (.reg 3) bad .skip : WordLangProgHOL (BitVec 64)) = false := by
  have clause := (sourceInstance (width := 64) none (some (7,bad,8,9))).2.2.2.1
  rw [clause]
  rfl

-- wcna_05_call: (F,T)
example : noAllocSubprogsHOL (.call none none [1,2] (some (7,bad,8,9)) : WordLangProgHOL (BitVec 64)) = false := by
  have clause := (sourceInstance (width := 64) none (some (7,bad,8,9))).2.2.2.2.1
  rw [clause]
  rfl

-- wcna_06_alloc: (F,T)
example : noAllocSubprogsHOL (.alloc 3 cuts : WordLangProgHOL (BitVec 64)) = false := by
  have clause := (sourceInstance (width := 64) none (some (7,bad,8,9))).2.2.2.2.2.1
  exact clause

-- wcna_07_loc: (T,T)
example : noAllocSubprogsHOL (.locValue 2 3 : WordLangProgHOL (BitVec 64)) = true := by
  have clause := (sourceInstance (width := 64) none (some (7,bad,8,9))).2.2.2.2.2.2.1
  exact clause

-- wcna_08_share: (T,T)
example : noAllocSubprogsHOL (.shareInst .load 8 (.var 9) : WordLangProgHOL (BitVec 64)) = true := by
  have clause := (sourceInstance (width := 64) none (some (7,bad,8,9))).2.2.2.2.2.2.2.1
  exact clause

-- wcna_09_install: (T,T)
example : noAllocSubprogsHOL (.install 1 2 3 4 cuts : WordLangProgHOL (BitVec 64)) = true := by
  have clause := (sourceInstance (width := 64) none (some (7,bad,8,9))).2.2.2.2.2.2.2.2.1
  exact clause

-- wcna_10_skip: (T,T)
example : noAllocSubprogsHOL (.skip : WordLangProgHOL (BitVec 64)) = true := by
  have clause := (sourceInstance (width := 64) none (some (7,bad,8,9))).2.2.2.2.2.2.2.2.2.1
  exact clause

-- wcna_11_move: (T,T)
example : noAllocSubprogsHOL (.move 5 [(1,2),(2,3)] : WordLangProgHOL (BitVec 64)) = true := by
  have clause := (sourceInstance (width := 64) none (some (7,bad,8,9))).2.2.2.2.2.2.2.2.2.2.1
  exact clause

-- wcna_12_inst: (T,T)
example : noAllocSubprogsHOL (.inst (.const 2 7) : WordLangProgHOL (BitVec 64)) = true := by
  have clause := (sourceInstance (width := 64) none (some (7,bad,8,9))).2.2.2.2.2.2.2.2.2.2.2.1
  exact clause

-- wcna_13_assign: (T,T)
example : noAllocSubprogsHOL (.assign 2 (.const 7) : WordLangProgHOL (BitVec 64)) = true := by
  have clause := (sourceInstance (width := 64) none (some (7,bad,8,9))).2.2.2.2.2.2.2.2.2.2.2.2.1
  exact clause

-- wcna_14_get: (T,T)
example : noAllocSubprogsHOL (.get 2 .currHeap : WordLangProgHOL (BitVec 64)) = true := by
  have clause := (sourceInstance (width := 64) none (some (7,bad,8,9))).2.2.2.2.2.2.2.2.2.2.2.2.2.1
  exact clause

-- wcna_15_set: (T,T)
example : noAllocSubprogsHOL (.set .currHeap (.const 7) : WordLangProgHOL (BitVec 64)) = true := by
  have clause := (sourceInstance (width := 64) none (some (7,bad,8,9))).2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  exact clause

-- wcna_16_store: (T,T)
example : noAllocSubprogsHOL (.store (.var 2) 3 : WordLangProgHOL (BitVec 64)) = true := by
  have clause := (sourceInstance (width := 64) none (some (7,bad,8,9))).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  exact clause

-- wcna_17_consts: (T,T)
example : noAllocSubprogsHOL (.storeConsts 2 3 4 5 [(true,7),(false,8)] : WordLangProgHOL (BitVec 64)) = true := by
  have clause := (sourceInstance (width := 64) none (some (7,bad,8,9))).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  exact clause

-- wcna_18_raise: (T,T)
example : noAllocSubprogsHOL (.raise 3 : WordLangProgHOL (BitVec 64)) = true := by
  have clause := (sourceInstance (width := 64) none (some (7,bad,8,9))).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  exact clause

-- wcna_19_return: (T,T)
example : noAllocSubprogsHOL (.return 4 [5,6] : WordLangProgHOL (BitVec 64)) = true := by
  have clause := (sourceInstance (width := 64) none (some (7,bad,8,9))).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  exact clause

-- wcna_20_break: (T,T)
example : noAllocSubprogsHOL (.break 7 : WordLangProgHOL (BitVec 64)) = true := by
  have clause := (sourceInstance (width := 64) none (some (7,bad,8,9))).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  exact clause

-- wcna_21_continue: (T,T)
example : noAllocSubprogsHOL (.continue 8 : WordLangProgHOL (BitVec 64)) = true := by
  have clause := (sourceInstance (width := 64) none (some (7,bad,8,9))).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  exact clause

-- wcna_22_tick: (T,T)
example : noAllocSubprogsHOL (.tick : WordLangProgHOL (BitVec 64)) = true := by
  have clause := (sourceInstance (width := 64) none (some (7,bad,8,9))).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  exact clause

-- wcna_23_heap: (T,T)
example : noAllocSubprogsHOL (.opCurrHeap .add 2 3 : WordLangProgHOL (BitVec 64)) = true := by
  have clause := (sourceInstance (width := 64) none (some (7,bad,8,9))).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  exact clause

-- wcna_24_code: (T,T)
example : noAllocSubprogsHOL (.codeBufferWrite 2 3 : WordLangProgHOL (BitVec 64)) = true := by
  have clause := (sourceInstance (width := 64) none (some (7,bad,8,9))).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  exact clause

-- wcna_25_data: (T,T)
example : noAllocSubprogsHOL (.dataBufferWrite 4 5 : WordLangProgHOL (BitVec 64)) = true := by
  have clause := (sourceInstance (width := 64) none (some (7,bad,8,9))).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  exact clause

-- wcna_26_ffi: (T,T)
example : noAllocSubprogsHOL (.ffi (.implode [105,111]) 2 3 4 5 cuts : WordLangProgHOL (BitVec 64)) = true := by
  have clause := (sourceInstance (width := 64) none (some (7,bad,8,9))).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  exact clause

-- wcna_call_none_none_width1
example : noAllocSubprogsHOL (.call none none [1,2] none : WordLangProgHOL (BitVec 1)) = true := by
  have clause := (sourceInstance (width := 1) none none).2.2.2.2.1
  rw [clause]
  rfl

-- wcna_call_return_only_width1
example : noAllocSubprogsHOL (.call (some ([1,2],cuts,bad,8,9)) none [1,2] none : WordLangProgHOL (BitVec 1)) = false := by
  have clause := (sourceInstance (width := 1) (some ([1,2],cuts,bad,8,9)) none).2.2.2.2.1
  rw [clause]
  rfl

-- wcna_call_both_present_width1
example : noAllocSubprogsHOL (.call (some ([1,2],cuts,.skip,8,9)) none [1,2] (some (7,bad,8,9)) : WordLangProgHOL (BitVec 1)) = false := by
  have clause := (sourceInstance (width := 1) (some ([1,2],cuts,.skip,8,9)) (some (7,bad,8,9))).2.2.2.2.1
  rw [clause]
  rfl

end Flapjack.Test.WordConvsNoAllocDefParity

namespace Flapjack.Test.WordConvsNoMtDefParity
open Flapjack
private def cuts : WordLangCutsetsHOL := (.ln,.ln)
private def bad {width : Nat} [NeZero width] : WordLangProgHOL (BitVec width) := .mustTerminate .skip
/-- A complete source-conjunction instance with failing recursive bodies and
nonempty real payloads; no individual desired clause is supplied as a premise. -/
private theorem sourceInstance {width : Nat} [NeZero width]
    (r : Option (List Nat × WordLangCutsetsHOL × WordLangProgHOL (BitVec width) × Nat × Nat))
    (h : Option (Nat × WordLangProgHOL (BitVec width) × Nat × Nat)) :
    (noMtSubprogsHOL (width := width) (.mustTerminate (bad)) = false) ∧
    (noMtSubprogsHOL (width := width) (.seq (bad) (.skip)) = (noMtSubprogsHOL (width := width) (bad) && noMtSubprogsHOL (width := width) (.skip))) ∧
    (noMtSubprogsHOL (width := width) (.loop (.ln) (bad) (.ln)) = noMtSubprogsHOL (width := width) (bad)) ∧
    (noMtSubprogsHOL (width := width) (.ite (.equal) (2) ((.reg 3)) (bad) (.skip)) = (noMtSubprogsHOL (width := width) (bad) && noMtSubprogsHOL (width := width) (.skip))) ∧
    (noMtSubprogsHOL (width := width) (.call (r) (none) ([1,2]) (h)) =
      ((match (r) with | none => true | some (_,_,body,_,_) => noMtSubprogsHOL (width := width) body) &&
       (match (h) with | none => true | some (_,body,_,_) => noMtSubprogsHOL (width := width) body))) ∧
    noMtSubprogsHOL (width := width) (.alloc (3) (cuts)) = true ∧
    noMtSubprogsHOL (width := width) (.locValue (2) (3)) = true ∧
    noMtSubprogsHOL (width := width) (.shareInst (.load) (8) ((.var 9))) = true ∧
    noMtSubprogsHOL (width := width) (.install (1) (2) (3) (4) (cuts)) = true ∧
    noMtSubprogsHOL (width := width) .skip = true ∧
    noMtSubprogsHOL (width := width) (.move (5) ([(1,2),(2,3)])) = true ∧
    noMtSubprogsHOL (width := width) (.inst ((.const 2 7))) = true ∧
    noMtSubprogsHOL (width := width) (.assign (2) ((.const 7))) = true ∧
    noMtSubprogsHOL (width := width) (.get (2) (.currHeap)) = true ∧
    noMtSubprogsHOL (width := width) (.set (.currHeap) ((.const 7))) = true ∧
    noMtSubprogsHOL (width := width) (.store ((.var 2)) (3)) = true ∧
    noMtSubprogsHOL (width := width) (.storeConsts (2) (3) (4) (5) ([(true,7),(false,8)])) = true ∧
    noMtSubprogsHOL (width := width) (.raise (3)) = true ∧
    noMtSubprogsHOL (width := width) (.return (4) ([5,6])) = true ∧
    noMtSubprogsHOL (width := width) (.break (7)) = true ∧
    noMtSubprogsHOL (width := width) (.continue (8)) = true ∧
    noMtSubprogsHOL (width := width) .tick = true ∧
    noMtSubprogsHOL (width := width) (.opCurrHeap (.add) (2) (3)) = true ∧
    noMtSubprogsHOL (width := width) (.codeBufferWrite (2) (3)) = true ∧
    noMtSubprogsHOL (width := width) (.dataBufferWrite (4) (5)) = true ∧
    noMtSubprogsHOL (width := width) (.ffi ((.implode [105,111])) (2) (3) (4) (5) (cuts)) = true := noMtDef (width := width)
      bad bad .skip bad .ln .ln .equal 2 (.reg 3)
      r none [1,2] h
      3 cuts 2 3 .load 8 (.var 9) 1 2 3 4 cuts
      5 [(1,2),(2,3)] (.const 2 7) 2 (.const 7) 2 .currHeap .currHeap
      (.const 7) (.var 2) 3 2 3 4 5 [(true,7),(false,8)]
      3 4 [5,6] 7 8 .add 2 3 2 3 4 5 (.implode [105,111]) 2 3 4 5 cuts

-- wcnm_01_mt: (F,T)
example : noMtSubprogsHOL (.mustTerminate bad : WordLangProgHOL (BitVec 64)) = false := by
  have clause := (sourceInstance (width := 64) none (some (7,bad,8,9))).1
  rw [clause]

-- wcnm_02_seq: (F,T)
example : noMtSubprogsHOL (.seq bad .skip : WordLangProgHOL (BitVec 64)) = false := by
  have clause := (sourceInstance (width := 64) none (some (7,bad,8,9))).2.1
  rw [clause]
  rfl

-- wcnm_03_loop: (F,T)
example : noMtSubprogsHOL (.loop .ln bad .ln : WordLangProgHOL (BitVec 64)) = false := by
  have clause := (sourceInstance (width := 64) none (some (7,bad,8,9))).2.2.1
  rw [clause]
  rfl

-- wcnm_04_if: (F,T)
example : noMtSubprogsHOL (.ite .equal 2 (.reg 3) bad .skip : WordLangProgHOL (BitVec 64)) = false := by
  have clause := (sourceInstance (width := 64) none (some (7,bad,8,9))).2.2.2.1
  rw [clause]
  rfl

-- wcnm_05_call: (F,T)
example : noMtSubprogsHOL (.call none none [1,2] (some (7,bad,8,9)) : WordLangProgHOL (BitVec 64)) = false := by
  have clause := (sourceInstance (width := 64) none (some (7,bad,8,9))).2.2.2.2.1
  rw [clause]
  rfl

-- wcnm_06_alloc: (T,T)
example : noMtSubprogsHOL (.alloc 3 cuts : WordLangProgHOL (BitVec 64)) = true := by
  have clause := (sourceInstance (width := 64) none (some (7,bad,8,9))).2.2.2.2.2.1
  exact clause

-- wcnm_07_loc: (T,T)
example : noMtSubprogsHOL (.locValue 2 3 : WordLangProgHOL (BitVec 64)) = true := by
  have clause := (sourceInstance (width := 64) none (some (7,bad,8,9))).2.2.2.2.2.2.1
  exact clause

-- wcnm_08_share: (T,T)
example : noMtSubprogsHOL (.shareInst .load 8 (.var 9) : WordLangProgHOL (BitVec 64)) = true := by
  have clause := (sourceInstance (width := 64) none (some (7,bad,8,9))).2.2.2.2.2.2.2.1
  exact clause

-- wcnm_09_install: (T,T)
example : noMtSubprogsHOL (.install 1 2 3 4 cuts : WordLangProgHOL (BitVec 64)) = true := by
  have clause := (sourceInstance (width := 64) none (some (7,bad,8,9))).2.2.2.2.2.2.2.2.1
  exact clause

-- wcnm_10_skip: (T,T)
example : noMtSubprogsHOL (.skip : WordLangProgHOL (BitVec 64)) = true := by
  have clause := (sourceInstance (width := 64) none (some (7,bad,8,9))).2.2.2.2.2.2.2.2.2.1
  exact clause

-- wcnm_11_move: (T,T)
example : noMtSubprogsHOL (.move 5 [(1,2),(2,3)] : WordLangProgHOL (BitVec 64)) = true := by
  have clause := (sourceInstance (width := 64) none (some (7,bad,8,9))).2.2.2.2.2.2.2.2.2.2.1
  exact clause

-- wcnm_12_inst: (T,T)
example : noMtSubprogsHOL (.inst (.const 2 7) : WordLangProgHOL (BitVec 64)) = true := by
  have clause := (sourceInstance (width := 64) none (some (7,bad,8,9))).2.2.2.2.2.2.2.2.2.2.2.1
  exact clause

-- wcnm_13_assign: (T,T)
example : noMtSubprogsHOL (.assign 2 (.const 7) : WordLangProgHOL (BitVec 64)) = true := by
  have clause := (sourceInstance (width := 64) none (some (7,bad,8,9))).2.2.2.2.2.2.2.2.2.2.2.2.1
  exact clause

-- wcnm_14_get: (T,T)
example : noMtSubprogsHOL (.get 2 .currHeap : WordLangProgHOL (BitVec 64)) = true := by
  have clause := (sourceInstance (width := 64) none (some (7,bad,8,9))).2.2.2.2.2.2.2.2.2.2.2.2.2.1
  exact clause

-- wcnm_15_set: (T,T)
example : noMtSubprogsHOL (.set .currHeap (.const 7) : WordLangProgHOL (BitVec 64)) = true := by
  have clause := (sourceInstance (width := 64) none (some (7,bad,8,9))).2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  exact clause

-- wcnm_16_store: (T,T)
example : noMtSubprogsHOL (.store (.var 2) 3 : WordLangProgHOL (BitVec 64)) = true := by
  have clause := (sourceInstance (width := 64) none (some (7,bad,8,9))).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  exact clause

-- wcnm_17_consts: (T,T)
example : noMtSubprogsHOL (.storeConsts 2 3 4 5 [(true,7),(false,8)] : WordLangProgHOL (BitVec 64)) = true := by
  have clause := (sourceInstance (width := 64) none (some (7,bad,8,9))).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  exact clause

-- wcnm_18_raise: (T,T)
example : noMtSubprogsHOL (.raise 3 : WordLangProgHOL (BitVec 64)) = true := by
  have clause := (sourceInstance (width := 64) none (some (7,bad,8,9))).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  exact clause

-- wcnm_19_return: (T,T)
example : noMtSubprogsHOL (.return 4 [5,6] : WordLangProgHOL (BitVec 64)) = true := by
  have clause := (sourceInstance (width := 64) none (some (7,bad,8,9))).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  exact clause

-- wcnm_20_break: (T,T)
example : noMtSubprogsHOL (.break 7 : WordLangProgHOL (BitVec 64)) = true := by
  have clause := (sourceInstance (width := 64) none (some (7,bad,8,9))).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  exact clause

-- wcnm_21_continue: (T,T)
example : noMtSubprogsHOL (.continue 8 : WordLangProgHOL (BitVec 64)) = true := by
  have clause := (sourceInstance (width := 64) none (some (7,bad,8,9))).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  exact clause

-- wcnm_22_tick: (T,T)
example : noMtSubprogsHOL (.tick : WordLangProgHOL (BitVec 64)) = true := by
  have clause := (sourceInstance (width := 64) none (some (7,bad,8,9))).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  exact clause

-- wcnm_23_heap: (T,T)
example : noMtSubprogsHOL (.opCurrHeap .add 2 3 : WordLangProgHOL (BitVec 64)) = true := by
  have clause := (sourceInstance (width := 64) none (some (7,bad,8,9))).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  exact clause

-- wcnm_24_code: (T,T)
example : noMtSubprogsHOL (.codeBufferWrite 2 3 : WordLangProgHOL (BitVec 64)) = true := by
  have clause := (sourceInstance (width := 64) none (some (7,bad,8,9))).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  exact clause

-- wcnm_25_data: (T,T)
example : noMtSubprogsHOL (.dataBufferWrite 4 5 : WordLangProgHOL (BitVec 64)) = true := by
  have clause := (sourceInstance (width := 64) none (some (7,bad,8,9))).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  exact clause

-- wcnm_26_ffi: (T,T)
example : noMtSubprogsHOL (.ffi (.implode [105,111]) 2 3 4 5 cuts : WordLangProgHOL (BitVec 64)) = true := by
  have clause := (sourceInstance (width := 64) none (some (7,bad,8,9))).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  exact clause

-- wcnm_call_none_none_width1
example : noMtSubprogsHOL (.call none none [1,2] none : WordLangProgHOL (BitVec 1)) = true := by
  have clause := (sourceInstance (width := 1) none none).2.2.2.2.1
  rw [clause]
  rfl

-- wcnm_call_return_only_width1
example : noMtSubprogsHOL (.call (some ([1,2],cuts,bad,8,9)) none [1,2] none : WordLangProgHOL (BitVec 1)) = false := by
  have clause := (sourceInstance (width := 1) (some ([1,2],cuts,bad,8,9)) none).2.2.2.2.1
  rw [clause]
  rfl

-- wcnm_call_both_present_width1
example : noMtSubprogsHOL (.call (some ([1,2],cuts,.skip,8,9)) none [1,2] (some (7,bad,8,9)) : WordLangProgHOL (BitVec 1)) = false := by
  have clause := (sourceInstance (width := 1) (some ([1,2],cuts,.skip,8,9)) (some (7,bad,8,9))).2.2.2.2.1
  rw [clause]
  rfl

end Flapjack.Test.WordConvsNoMtDefParity

namespace Flapjack.Test.WordConvsNoShareInstDefParity
open Flapjack
private def cuts : WordLangCutsetsHOL := (.ln,.ln)
private def bad {width : Nat} [NeZero width] : WordLangProgHOL (BitVec width) := .shareInst .load 8 (.var 9)
/-- A complete source-conjunction instance with failing recursive bodies and
nonempty real payloads; no individual desired clause is supplied as a premise. -/
private theorem sourceInstance {width : Nat} [NeZero width]
    (r : Option (List Nat × WordLangCutsetsHOL × WordLangProgHOL (BitVec width) × Nat × Nat))
    (h : Option (Nat × WordLangProgHOL (BitVec width) × Nat × Nat)) :
    (noShareInstSubprogsHOL (width := width) (.mustTerminate (bad)) = noShareInstSubprogsHOL (width := width) (bad)) ∧
    (noShareInstSubprogsHOL (width := width) (.seq (bad) (.skip)) = (noShareInstSubprogsHOL (width := width) (bad) && noShareInstSubprogsHOL (width := width) (.skip))) ∧
    (noShareInstSubprogsHOL (width := width) (.loop (.ln) (bad) (.ln)) = noShareInstSubprogsHOL (width := width) (bad)) ∧
    (noShareInstSubprogsHOL (width := width) (.ite (.equal) (2) ((.reg 3)) (bad) (.skip)) = (noShareInstSubprogsHOL (width := width) (bad) && noShareInstSubprogsHOL (width := width) (.skip))) ∧
    (noShareInstSubprogsHOL (width := width) (.call (r) (none) ([1,2]) (h)) =
      ((match (r) with | none => true | some (_,_,body,_,_) => noShareInstSubprogsHOL (width := width) body) &&
       (match (h) with | none => true | some (_,body,_,_) => noShareInstSubprogsHOL (width := width) body))) ∧
    noShareInstSubprogsHOL (width := width) (.alloc (3) (cuts)) = true ∧
    noShareInstSubprogsHOL (width := width) (.locValue (2) (3)) = true ∧
    noShareInstSubprogsHOL (width := width) (.shareInst (.load) (8) ((.var 9))) = false ∧
    noShareInstSubprogsHOL (width := width) (.install (1) (2) (3) (4) (cuts)) = true ∧
    noShareInstSubprogsHOL (width := width) .skip = true ∧
    noShareInstSubprogsHOL (width := width) (.move (5) ([(1,2),(2,3)])) = true ∧
    noShareInstSubprogsHOL (width := width) (.inst ((.const 2 7))) = true ∧
    noShareInstSubprogsHOL (width := width) (.assign (2) ((.const 7))) = true ∧
    noShareInstSubprogsHOL (width := width) (.get (2) (.currHeap)) = true ∧
    noShareInstSubprogsHOL (width := width) (.set (.currHeap) ((.const 7))) = true ∧
    noShareInstSubprogsHOL (width := width) (.store ((.var 2)) (3)) = true ∧
    noShareInstSubprogsHOL (width := width) (.storeConsts (2) (3) (4) (5) ([(true,7),(false,8)])) = true ∧
    noShareInstSubprogsHOL (width := width) (.raise (3)) = true ∧
    noShareInstSubprogsHOL (width := width) (.return (4) ([5,6])) = true ∧
    noShareInstSubprogsHOL (width := width) (.break (7)) = true ∧
    noShareInstSubprogsHOL (width := width) (.continue (8)) = true ∧
    noShareInstSubprogsHOL (width := width) .tick = true ∧
    noShareInstSubprogsHOL (width := width) (.opCurrHeap (.add) (2) (3)) = true ∧
    noShareInstSubprogsHOL (width := width) (.codeBufferWrite (2) (3)) = true ∧
    noShareInstSubprogsHOL (width := width) (.dataBufferWrite (4) (5)) = true ∧
    noShareInstSubprogsHOL (width := width) (.ffi ((.implode [105,111])) (2) (3) (4) (5) (cuts)) = true := noShareInstDef (width := width)
      bad bad .skip bad .ln .ln .equal 2 (.reg 3)
      r none [1,2] h
      3 cuts 2 3 .load 8 (.var 9) 1 2 3 4 cuts
      5 [(1,2),(2,3)] (.const 2 7) 2 (.const 7) 2 .currHeap .currHeap
      (.const 7) (.var 2) 3 2 3 4 5 [(true,7),(false,8)]
      3 4 [5,6] 7 8 .add 2 3 2 3 4 5 (.implode [105,111]) 2 3 4 5 cuts

-- wcns_01_mt: (F,T)
example : noShareInstSubprogsHOL (.mustTerminate bad : WordLangProgHOL (BitVec 64)) = false := by
  have clause := (sourceInstance (width := 64) none (some (7,bad,8,9))).1
  rw [clause]
  rfl

-- wcns_02_seq: (F,T)
example : noShareInstSubprogsHOL (.seq bad .skip : WordLangProgHOL (BitVec 64)) = false := by
  have clause := (sourceInstance (width := 64) none (some (7,bad,8,9))).2.1
  rw [clause]
  rfl

-- wcns_03_loop: (F,T)
example : noShareInstSubprogsHOL (.loop .ln bad .ln : WordLangProgHOL (BitVec 64)) = false := by
  have clause := (sourceInstance (width := 64) none (some (7,bad,8,9))).2.2.1
  rw [clause]
  rfl

-- wcns_04_if: (F,T)
example : noShareInstSubprogsHOL (.ite .equal 2 (.reg 3) bad .skip : WordLangProgHOL (BitVec 64)) = false := by
  have clause := (sourceInstance (width := 64) none (some (7,bad,8,9))).2.2.2.1
  rw [clause]
  rfl

-- wcns_05_call: (F,T)
example : noShareInstSubprogsHOL (.call none none [1,2] (some (7,bad,8,9)) : WordLangProgHOL (BitVec 64)) = false := by
  have clause := (sourceInstance (width := 64) none (some (7,bad,8,9))).2.2.2.2.1
  rw [clause]
  rfl

-- wcns_06_alloc: (T,T)
example : noShareInstSubprogsHOL (.alloc 3 cuts : WordLangProgHOL (BitVec 64)) = true := by
  have clause := (sourceInstance (width := 64) none (some (7,bad,8,9))).2.2.2.2.2.1
  exact clause

-- wcns_07_loc: (T,T)
example : noShareInstSubprogsHOL (.locValue 2 3 : WordLangProgHOL (BitVec 64)) = true := by
  have clause := (sourceInstance (width := 64) none (some (7,bad,8,9))).2.2.2.2.2.2.1
  exact clause

-- wcns_08_share: (F,T)
example : noShareInstSubprogsHOL (.shareInst .load 8 (.var 9) : WordLangProgHOL (BitVec 64)) = false := by
  have clause := (sourceInstance (width := 64) none (some (7,bad,8,9))).2.2.2.2.2.2.2.1
  exact clause

-- wcns_09_install: (T,T)
example : noShareInstSubprogsHOL (.install 1 2 3 4 cuts : WordLangProgHOL (BitVec 64)) = true := by
  have clause := (sourceInstance (width := 64) none (some (7,bad,8,9))).2.2.2.2.2.2.2.2.1
  exact clause

-- wcns_10_skip: (T,T)
example : noShareInstSubprogsHOL (.skip : WordLangProgHOL (BitVec 64)) = true := by
  have clause := (sourceInstance (width := 64) none (some (7,bad,8,9))).2.2.2.2.2.2.2.2.2.1
  exact clause

-- wcns_11_move: (T,T)
example : noShareInstSubprogsHOL (.move 5 [(1,2),(2,3)] : WordLangProgHOL (BitVec 64)) = true := by
  have clause := (sourceInstance (width := 64) none (some (7,bad,8,9))).2.2.2.2.2.2.2.2.2.2.1
  exact clause

-- wcns_12_inst: (T,T)
example : noShareInstSubprogsHOL (.inst (.const 2 7) : WordLangProgHOL (BitVec 64)) = true := by
  have clause := (sourceInstance (width := 64) none (some (7,bad,8,9))).2.2.2.2.2.2.2.2.2.2.2.1
  exact clause

-- wcns_13_assign: (T,T)
example : noShareInstSubprogsHOL (.assign 2 (.const 7) : WordLangProgHOL (BitVec 64)) = true := by
  have clause := (sourceInstance (width := 64) none (some (7,bad,8,9))).2.2.2.2.2.2.2.2.2.2.2.2.1
  exact clause

-- wcns_14_get: (T,T)
example : noShareInstSubprogsHOL (.get 2 .currHeap : WordLangProgHOL (BitVec 64)) = true := by
  have clause := (sourceInstance (width := 64) none (some (7,bad,8,9))).2.2.2.2.2.2.2.2.2.2.2.2.2.1
  exact clause

-- wcns_15_set: (T,T)
example : noShareInstSubprogsHOL (.set .currHeap (.const 7) : WordLangProgHOL (BitVec 64)) = true := by
  have clause := (sourceInstance (width := 64) none (some (7,bad,8,9))).2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  exact clause

-- wcns_16_store: (T,T)
example : noShareInstSubprogsHOL (.store (.var 2) 3 : WordLangProgHOL (BitVec 64)) = true := by
  have clause := (sourceInstance (width := 64) none (some (7,bad,8,9))).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  exact clause

-- wcns_17_consts: (T,T)
example : noShareInstSubprogsHOL (.storeConsts 2 3 4 5 [(true,7),(false,8)] : WordLangProgHOL (BitVec 64)) = true := by
  have clause := (sourceInstance (width := 64) none (some (7,bad,8,9))).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  exact clause

-- wcns_18_raise: (T,T)
example : noShareInstSubprogsHOL (.raise 3 : WordLangProgHOL (BitVec 64)) = true := by
  have clause := (sourceInstance (width := 64) none (some (7,bad,8,9))).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  exact clause

-- wcns_19_return: (T,T)
example : noShareInstSubprogsHOL (.return 4 [5,6] : WordLangProgHOL (BitVec 64)) = true := by
  have clause := (sourceInstance (width := 64) none (some (7,bad,8,9))).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  exact clause

-- wcns_20_break: (T,T)
example : noShareInstSubprogsHOL (.break 7 : WordLangProgHOL (BitVec 64)) = true := by
  have clause := (sourceInstance (width := 64) none (some (7,bad,8,9))).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  exact clause

-- wcns_21_continue: (T,T)
example : noShareInstSubprogsHOL (.continue 8 : WordLangProgHOL (BitVec 64)) = true := by
  have clause := (sourceInstance (width := 64) none (some (7,bad,8,9))).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  exact clause

-- wcns_22_tick: (T,T)
example : noShareInstSubprogsHOL (.tick : WordLangProgHOL (BitVec 64)) = true := by
  have clause := (sourceInstance (width := 64) none (some (7,bad,8,9))).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  exact clause

-- wcns_23_heap: (T,T)
example : noShareInstSubprogsHOL (.opCurrHeap .add 2 3 : WordLangProgHOL (BitVec 64)) = true := by
  have clause := (sourceInstance (width := 64) none (some (7,bad,8,9))).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  exact clause

-- wcns_24_code: (T,T)
example : noShareInstSubprogsHOL (.codeBufferWrite 2 3 : WordLangProgHOL (BitVec 64)) = true := by
  have clause := (sourceInstance (width := 64) none (some (7,bad,8,9))).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  exact clause

-- wcns_25_data: (T,T)
example : noShareInstSubprogsHOL (.dataBufferWrite 4 5 : WordLangProgHOL (BitVec 64)) = true := by
  have clause := (sourceInstance (width := 64) none (some (7,bad,8,9))).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  exact clause

-- wcns_26_ffi: (T,T)
example : noShareInstSubprogsHOL (.ffi (.implode [105,111]) 2 3 4 5 cuts : WordLangProgHOL (BitVec 64)) = true := by
  have clause := (sourceInstance (width := 64) none (some (7,bad,8,9))).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  exact clause

-- wcns_call_none_none_width1
example : noShareInstSubprogsHOL (.call none none [1,2] none : WordLangProgHOL (BitVec 1)) = true := by
  have clause := (sourceInstance (width := 1) none none).2.2.2.2.1
  rw [clause]
  rfl

-- wcns_call_return_only_width1
example : noShareInstSubprogsHOL (.call (some ([1,2],cuts,bad,8,9)) none [1,2] none : WordLangProgHOL (BitVec 1)) = false := by
  have clause := (sourceInstance (width := 1) (some ([1,2],cuts,bad,8,9)) none).2.2.2.2.1
  rw [clause]
  rfl

-- wcns_call_both_present_width1
example : noShareInstSubprogsHOL (.call (some ([1,2],cuts,.skip,8,9)) none [1,2] (some (7,bad,8,9)) : WordLangProgHOL (BitVec 1)) = false := by
  have clause := (sourceInstance (width := 1) (some ([1,2],cuts,.skip,8,9)) (some (7,bad,8,9))).2.2.2.2.1
  rw [clause]
  rfl

end Flapjack.Test.WordConvsNoShareInstDefParity
