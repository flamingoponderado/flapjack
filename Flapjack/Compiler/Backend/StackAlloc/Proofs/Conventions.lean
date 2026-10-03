import Flapjack.Compiler.Backend.StackAlloc.Compile
import Flapjack.Compiler.Backend.StackProps.ProgramNames
import Flapjack.Compiler.Backend.StackProps.RemoveNames
import Flapjack.Compiler.Backend.StackProps.RegisterBounds
import Flapjack.Compiler.Backend.StackProps.CallArgs

/-!
# `stack_allocProof` syntactic convention lemmas

`stack_alloc_comp_stack_asm_name`, `stack_alloc_reg_bound` and
`stack_alloc_call_args` of
`cakeml/compiler/backend/proofs/stack_allocProofScript.sml` (6217-6331): `comp`
preserves the naming, register-bound and call-argument conventions, and the GC
stub satisfies the latter two.
-/

namespace Flapjack.Compiler.Backend.StackAlloc

open Flapjack Flapjack.Compiler.Backend.StackLang Flapjack.Compiler.Backend.StackProps
open Flapjack.Compiler.Encoders.Asm

/-- Exact HOL `stack_alloc_comp_stack_asm_name`
(`stack_allocProofScript.sml:6217-6237`). HOL's free `c` is implicit; its
`'a asm_config` shares the word dimension of the program, as in the source. -/
@[hol "cakeml/compiler/backend/proofs/stack_allocProofScript.sml"
  "stack_alloc_comp_stack_asm_name" (words_as_type_indexed_bitvec)]
theorem stack_alloc_comp_stack_asm_name {width : Nat} [NeZero width] {c : AsmConfigExact width} :
    ∀ (n m : Nat) (p : HolProg width),
      stackAsmName c p ∧ stackAsmRemove c p →
      stackAsmName c (comp n m p).1 ∧ stackAsmRemove c (comp n m p).1
  | n, m, .seq a b, ⟨h1, h2⟩ => by
      simp only [stackAsmName, stackAsmRemove] at h1 h2
      have ha := stack_alloc_comp_stack_asm_name n m a ⟨h1.1, h2.1⟩
      have hb := stack_alloc_comp_stack_asm_name n (comp n m a).2 b ⟨h1.2, h2.2⟩
      simp only [comp, stackAsmName, stackAsmRemove]
      exact ⟨⟨ha.1, hb.1⟩, ha.2, hb.2⟩
  | n, m, .ite cmp r ri a b, ⟨h1, h2⟩ => by
      simp only [stackAsmName, stackAsmRemove] at h1 h2
      have ha := stack_alloc_comp_stack_asm_name n m a ⟨h1.1, h2.1⟩
      have hb := stack_alloc_comp_stack_asm_name n (comp n m a).2 b ⟨h1.2, h2.2⟩
      simp only [comp, stackAsmName, stackAsmRemove]
      exact ⟨⟨ha.1, hb.1⟩, ha.2, hb.2⟩
  | n, m, .loop body, ⟨h1, h2⟩ => by
      simp only [stackAsmName, stackAsmRemove] at h1 h2
      have hb := stack_alloc_comp_stack_asm_name n m body ⟨h1, h2⟩
      simp only [comp, stackAsmName, stackAsmRemove]
      exact hb
  | n, m, .call none dest handler, ⟨h1, h2⟩ => by
      simp only [stackAsmName] at h1
      simp only [comp, stackAsmName, stackAsmRemove, and_true]
      exact h1.1
  | n, m, .call (some (rp, lr, l1, l2)) dest none, ⟨h1, h2⟩ => by
      simp only [stackAsmName, stackAsmRemove, and_true] at h1 h2
      have hr := stack_alloc_comp_stack_asm_name n m rp ⟨h1.2, h2⟩
      simp only [comp, stackAsmName, stackAsmRemove, and_true]
      exact ⟨⟨h1.1, hr.1⟩, hr.2⟩
  | n, m, .call (some (rp, lr, l1, l2)) dest (some (hp, k1, k2)), ⟨h1, h2⟩ => by
      simp only [stackAsmName, stackAsmRemove] at h1 h2
      have hr := stack_alloc_comp_stack_asm_name n m rp ⟨h1.2.1, h2.1⟩
      have hh := stack_alloc_comp_stack_asm_name n (comp n m rp).2 hp ⟨h1.2.2, h2.2⟩
      simp only [comp, stackAsmName, stackAsmRemove]
      exact ⟨⟨h1.1, hr.1, hh.1⟩, hr.2, hh.2⟩
  | n, m, .alloc k, _ => by
      simp [comp, stackAsmName, stackAsmRemove]
  | n, m, .storeConsts t1 t2 (some loc), _ => by
      simp [comp, stackAsmName, stackAsmRemove]
  | _, _, .storeConsts _ _ none, h | _, _, .skip, h | _, _, .halt _, h | _, _, .tick, h
  | _, _, .ret _, h | _, _, .raise _, h | _, _, .break _, h | _, _, .continue _, h
  | _, _, .inst _, h | _, _, .get _ _, h | _, _, .set _ _, h | _, _, .opCurrHeap _ _ _, h
  | _, _, .jumpLower _ _ _, h | _, _, .rawCall _, h | _, _, .install _ _ _ _ _, h
  | _, _, .shMemOp _ _ _, h | _, _, .codeBufferWrite _ _, h | _, _, .dataBufferWrite _ _, h
  | _, _, .ffi _ _ _ _ _ _, h | _, _, .locValue _ _ _, h | _, _, .stackAlloc _, h
  | _, _, .stackFree _, h | _, _, .stackLoad _ _, h | _, _, .stackLoadAny _ _, h
  | _, _, .stackStore _ _, h | _, _, .stackStoreAny _ _, h | _, _, .stackGetSize _, h
  | _, _, .stackSetSize _, h | _, _, .bitmapLoad _ _, h => by
      simp only [comp]; exact h
termination_by _ _ p => sizeOf p
decreasing_by all_goals simp_wf <;> omega

namespace ConventionSupport

/-- `comp` preserves `reg_bound` when the bound is at least 10 (the inner
`comp_ind` induction of HOL's `stack_alloc_reg_bound`). -/
theorem comp_regBound {width : Nat} [NeZero width] {sp : Nat} (hsp : 10 ≤ sp) :
    ∀ (n m : Nat) (p : HolProg width), regBound p sp → regBound (comp n m p).1 sp
  | n, m, .seq a b, h => by
      simp only [regBound] at h
      simp only [comp, regBound]
      exact ⟨comp_regBound hsp n m a h.1, comp_regBound hsp n _ b h.2⟩
  | n, m, .ite cmp r ri a b, h => by
      simp only [regBound] at h
      simp only [comp, regBound]
      exact ⟨h.1, h.2.1, comp_regBound hsp n m a h.2.2.1, comp_regBound hsp n _ b h.2.2.2⟩
  | n, m, .loop body, h => by
      simp only [regBound] at h
      simp only [comp, regBound]
      exact comp_regBound hsp n m body h
  | n, m, .call none dest handler, h => by
      simp only [regBound] at h
      simp only [comp, regBound, and_true]
      exact h.1
  | n, m, .call (some (rp, lr, l1, l2)) dest none, h => by
      simp only [regBound, and_true] at h
      simp only [comp, regBound, and_true]
      exact ⟨h.1, comp_regBound hsp n m rp h.2.1, h.2.2⟩
  | n, m, .call (some (rp, lr, l1, l2)) dest (some (hp, k1, k2)), h => by
      simp only [regBound] at h
      simp only [comp, regBound]
      exact ⟨h.1, comp_regBound hsp n m rp h.2.1, h.2.2.1, comp_regBound hsp n _ hp h.2.2.2⟩
  | n, m, .alloc k, _ => by
      simp only [comp, regBound]; exact ⟨trivial, trivial, by omega, trivial⟩
  | n, m, .storeConsts t1 t2 (some loc), _ => by
      simp only [comp, regBound]; exact ⟨trivial, trivial, by omega, trivial⟩
  | _, _, .storeConsts _ _ none, h | _, _, .skip, h | _, _, .halt _, h | _, _, .tick, h
  | _, _, .ret _, h | _, _, .raise _, h | _, _, .break _, h | _, _, .continue _, h
  | _, _, .inst _, h | _, _, .get _ _, h | _, _, .set _ _, h | _, _, .opCurrHeap _ _ _, h
  | _, _, .jumpLower _ _ _, h | _, _, .rawCall _, h | _, _, .install _ _ _ _ _, h
  | _, _, .shMemOp _ _ _, h | _, _, .codeBufferWrite _ _, h | _, _, .dataBufferWrite _ _, h
  | _, _, .ffi _ _ _ _ _ _, h | _, _, .locValue _ _ _, h | _, _, .stackAlloc _, h
  | _, _, .stackFree _, h | _, _, .stackLoad _ _, h | _, _, .stackLoadAny _ _, h
  | _, _, .stackStore _ _, h | _, _, .stackStoreAny _ _, h | _, _, .stackGetSize _, h
  | _, _, .stackSetSize _, h | _, _, .bitmapLoad _ _, h => by
      simp only [comp]; exact h
termination_by _ _ p => sizeOf p
decreasing_by all_goals simp_wf <;> omega

/-- `comp` preserves `call_args p 1 2 3 4 0` (the inner `comp_ind` induction of
HOL's `stack_alloc_call_args`). -/
theorem comp_callArgs {width : Nat} [NeZero width] :
    ∀ (n m : Nat) (p : HolProg width), callArgs p 1 2 3 4 0 → callArgs (comp n m p).1 1 2 3 4 0
  | n, m, .seq a b, h => by
      simp only [callArgs] at h
      simp only [comp, callArgs]
      exact ⟨comp_callArgs n m a h.1, comp_callArgs n _ b h.2⟩
  | n, m, .ite cmp r ri a b, h => by
      simp only [callArgs] at h
      simp only [comp, callArgs]
      exact ⟨comp_callArgs n m a h.1, comp_callArgs n _ b h.2⟩
  | n, m, .loop body, h => by
      simp only [callArgs] at h
      simp only [comp, callArgs]
      exact comp_callArgs n m body h
  | n, m, .call none dest handler, h => by
      simp only [comp, callArgs]
  | n, m, .call (some (rp, lr, l1, l2)) dest none, h => by
      simp only [callArgs, and_true] at h
      simp only [comp, callArgs, and_true]
      exact ⟨comp_callArgs n m rp h.1, h.2⟩
  | n, m, .call (some (rp, lr, l1, l2)) dest (some (hp, k1, k2)), h => by
      simp only [callArgs] at h
      simp only [comp, callArgs]
      exact ⟨comp_callArgs n m rp h.1, h.2.1, comp_callArgs n _ hp h.2.2⟩
  | n, m, .alloc k, _ => by
      simp [comp, callArgs]
  | n, m, .storeConsts t1 t2 (some loc), _ => by
      simp [comp, callArgs]
  | _, _, .storeConsts _ _ none, h | _, _, .skip, h | _, _, .halt _, h | _, _, .tick, h
  | _, _, .ret _, h | _, _, .raise _, h | _, _, .break _, h | _, _, .continue _, h
  | _, _, .inst _, h | _, _, .get _ _, h | _, _, .set _ _, h | _, _, .opCurrHeap _ _ _, h
  | _, _, .jumpLower _ _ _, h | _, _, .rawCall _, h | _, _, .install _ _ _ _ _, h
  | _, _, .shMemOp _ _ _, h | _, _, .codeBufferWrite _ _, h | _, _, .dataBufferWrite _ _, h
  | _, _, .ffi _ _ _ _ _ _, h | _, _, .locValue _ _ _, h | _, _, .stackAlloc _, h
  | _, _, .stackFree _, h | _, _, .stackLoad _ _, h | _, _, .stackLoadAny _ _, h
  | _, _, .stackStore _ _, h | _, _, .stackStoreAny _ _, h | _, _, .stackGetSize _, h
  | _, _, .stackSetSize _, h | _, _, .bitmapLoad _ _, h => by
      simp only [comp]; exact h
termination_by _ _ p => sizeOf p
decreasing_by all_goals simp_wf <;> omega

set_option linter.unusedSimpArgs false in
/-- The GC stub is register-bounded by any bound of at least 10 (the
`EVAL_TAC` step of HOL's `stack_alloc_reg_bound`). -/
theorem stub_regBound {width : Nat} [NeZero width] (dc : DataToWord.Config) (sp : Nat)
    (hsp : 10 ≤ sp) : regBound (wordGcCode dc : HolProg width) sp := by
  unfold wordGcCode
  rcases dc.gcKind with _ | _ | gs
  · simp [memcpyCode, clearTopInst, wordGcMoveCode, wordGcMoveListCode, wordGcMoveLoopCode, wordGcMoveBitmapCode, wordGcMoveBitmapsCode, wordGcMoveRootsBitmapsCode, wordGenGcMoveCode, wordGenGcPartialMoveCode, wordGenGcMoveBitmapCode, wordGenGcPartialMoveBitmapCode, wordGenGcMoveBitmapsCode, wordGenGcPartialMoveBitmapsCode, wordGenGcMoveRootsBitmapsCode, wordGenGcPartialMoveRootsBitmapsCode, wordGenGcMoveListCode, wordGenGcPartialMoveListCode, wordGenGcMoveDataCode, wordGenGcPartialMoveRefListCode, wordGenGcPartialMoveDataCode, wordGenGcMoveRefsCode, wordGenGcMoveLoopCode, wordGcPartialOrFull, setNewTrigger, listSeqHOL, whileHOL, moveHOL, sub1Inst, subInst, addInst, andInst, xorInst, add1Inst, orInst, addBytesInWordInst, div2Inst, StackRemove.leftShiftInst, StackRemove.rightShiftInst, StackRemove.constInst, StackRemove.loadInst, StackRemove.storeInst, regBound, regBoundInst]; omega
  · simp [memcpyCode, clearTopInst, wordGcMoveCode, wordGcMoveListCode, wordGcMoveLoopCode, wordGcMoveBitmapCode, wordGcMoveBitmapsCode, wordGcMoveRootsBitmapsCode, wordGenGcMoveCode, wordGenGcPartialMoveCode, wordGenGcMoveBitmapCode, wordGenGcPartialMoveBitmapCode, wordGenGcMoveBitmapsCode, wordGenGcPartialMoveBitmapsCode, wordGenGcMoveRootsBitmapsCode, wordGenGcPartialMoveRootsBitmapsCode, wordGenGcMoveListCode, wordGenGcPartialMoveListCode, wordGenGcMoveDataCode, wordGenGcPartialMoveRefListCode, wordGenGcPartialMoveDataCode, wordGenGcMoveRefsCode, wordGenGcMoveLoopCode, wordGcPartialOrFull, setNewTrigger, listSeqHOL, whileHOL, moveHOL, sub1Inst, subInst, addInst, andInst, xorInst, add1Inst, orInst, addBytesInWordInst, div2Inst, StackRemove.leftShiftInst, StackRemove.rightShiftInst, StackRemove.constInst, StackRemove.loadInst, StackRemove.storeInst, regBound, regBoundInst]; omega
  · rcases gs with _ | ⟨g, gs⟩
    · simp [memcpyCode, clearTopInst, wordGcMoveCode, wordGcMoveListCode, wordGcMoveLoopCode, wordGcMoveBitmapCode, wordGcMoveBitmapsCode, wordGcMoveRootsBitmapsCode, wordGenGcMoveCode, wordGenGcPartialMoveCode, wordGenGcMoveBitmapCode, wordGenGcPartialMoveBitmapCode, wordGenGcMoveBitmapsCode, wordGenGcPartialMoveBitmapsCode, wordGenGcMoveRootsBitmapsCode, wordGenGcPartialMoveRootsBitmapsCode, wordGenGcMoveListCode, wordGenGcPartialMoveListCode, wordGenGcMoveDataCode, wordGenGcPartialMoveRefListCode, wordGenGcPartialMoveDataCode, wordGenGcMoveRefsCode, wordGenGcMoveLoopCode, wordGcPartialOrFull, setNewTrigger, listSeqHOL, whileHOL, moveHOL, sub1Inst, subInst, addInst, andInst, xorInst, add1Inst, orInst, addBytesInWordInst, div2Inst, StackRemove.leftShiftInst, StackRemove.rightShiftInst, StackRemove.constInst, StackRemove.loadInst, StackRemove.storeInst, regBound, regBoundInst]; omega
    · simp [memcpyCode, clearTopInst, wordGcMoveCode, wordGcMoveListCode, wordGcMoveLoopCode, wordGcMoveBitmapCode, wordGcMoveBitmapsCode, wordGcMoveRootsBitmapsCode, wordGenGcMoveCode, wordGenGcPartialMoveCode, wordGenGcMoveBitmapCode, wordGenGcPartialMoveBitmapCode, wordGenGcMoveBitmapsCode, wordGenGcPartialMoveBitmapsCode, wordGenGcMoveRootsBitmapsCode, wordGenGcPartialMoveRootsBitmapsCode, wordGenGcMoveListCode, wordGenGcPartialMoveListCode, wordGenGcMoveDataCode, wordGenGcPartialMoveRefListCode, wordGenGcPartialMoveDataCode, wordGenGcMoveRefsCode, wordGenGcMoveLoopCode, wordGcPartialOrFull, setNewTrigger, listSeqHOL, whileHOL, moveHOL, sub1Inst, subInst, addInst, andInst, xorInst, add1Inst, orInst, addBytesInWordInst, div2Inst, StackRemove.leftShiftInst, StackRemove.rightShiftInst, StackRemove.constInst, StackRemove.loadInst, StackRemove.storeInst, regBound, regBoundInst]; omega

set_option linter.unusedSimpArgs false in
/-- The GC stub satisfies `call_args _ 1 2 3 4 0` (the `EVAL_TAC` step of HOL's
`stack_alloc_call_args`). -/
theorem stub_callArgs {width : Nat} [NeZero width] (dc : DataToWord.Config) :
    callArgs (wordGcCode dc : HolProg width) 1 2 3 4 0 := by
  unfold wordGcCode
  rcases dc.gcKind with _ | _ | gs
  · simp [memcpyCode, clearTopInst, wordGcMoveCode, wordGcMoveListCode, wordGcMoveLoopCode, wordGcMoveBitmapCode, wordGcMoveBitmapsCode, wordGcMoveRootsBitmapsCode, wordGenGcMoveCode, wordGenGcPartialMoveCode, wordGenGcMoveBitmapCode, wordGenGcPartialMoveBitmapCode, wordGenGcMoveBitmapsCode, wordGenGcPartialMoveBitmapsCode, wordGenGcMoveRootsBitmapsCode, wordGenGcPartialMoveRootsBitmapsCode, wordGenGcMoveListCode, wordGenGcPartialMoveListCode, wordGenGcMoveDataCode, wordGenGcPartialMoveRefListCode, wordGenGcPartialMoveDataCode, wordGenGcMoveRefsCode, wordGenGcMoveLoopCode, wordGcPartialOrFull, setNewTrigger, listSeqHOL, whileHOL, moveHOL, sub1Inst, subInst, addInst, andInst, xorInst, add1Inst, orInst, addBytesInWordInst, div2Inst, StackRemove.leftShiftInst, StackRemove.rightShiftInst, StackRemove.constInst, StackRemove.loadInst, StackRemove.storeInst, callArgs]
  · simp [memcpyCode, clearTopInst, wordGcMoveCode, wordGcMoveListCode, wordGcMoveLoopCode, wordGcMoveBitmapCode, wordGcMoveBitmapsCode, wordGcMoveRootsBitmapsCode, wordGenGcMoveCode, wordGenGcPartialMoveCode, wordGenGcMoveBitmapCode, wordGenGcPartialMoveBitmapCode, wordGenGcMoveBitmapsCode, wordGenGcPartialMoveBitmapsCode, wordGenGcMoveRootsBitmapsCode, wordGenGcPartialMoveRootsBitmapsCode, wordGenGcMoveListCode, wordGenGcPartialMoveListCode, wordGenGcMoveDataCode, wordGenGcPartialMoveRefListCode, wordGenGcPartialMoveDataCode, wordGenGcMoveRefsCode, wordGenGcMoveLoopCode, wordGcPartialOrFull, setNewTrigger, listSeqHOL, whileHOL, moveHOL, sub1Inst, subInst, addInst, andInst, xorInst, add1Inst, orInst, addBytesInWordInst, div2Inst, StackRemove.leftShiftInst, StackRemove.rightShiftInst, StackRemove.constInst, StackRemove.loadInst, StackRemove.storeInst, callArgs]
  · rcases gs with _ | ⟨g, gs⟩
    · simp [memcpyCode, clearTopInst, wordGcMoveCode, wordGcMoveListCode, wordGcMoveLoopCode, wordGcMoveBitmapCode, wordGcMoveBitmapsCode, wordGcMoveRootsBitmapsCode, wordGenGcMoveCode, wordGenGcPartialMoveCode, wordGenGcMoveBitmapCode, wordGenGcPartialMoveBitmapCode, wordGenGcMoveBitmapsCode, wordGenGcPartialMoveBitmapsCode, wordGenGcMoveRootsBitmapsCode, wordGenGcPartialMoveRootsBitmapsCode, wordGenGcMoveListCode, wordGenGcPartialMoveListCode, wordGenGcMoveDataCode, wordGenGcPartialMoveRefListCode, wordGenGcPartialMoveDataCode, wordGenGcMoveRefsCode, wordGenGcMoveLoopCode, wordGcPartialOrFull, setNewTrigger, listSeqHOL, whileHOL, moveHOL, sub1Inst, subInst, addInst, andInst, xorInst, add1Inst, orInst, addBytesInWordInst, div2Inst, StackRemove.leftShiftInst, StackRemove.rightShiftInst, StackRemove.constInst, StackRemove.loadInst, StackRemove.storeInst, callArgs]
    · simp [memcpyCode, clearTopInst, wordGcMoveCode, wordGcMoveListCode, wordGcMoveLoopCode, wordGcMoveBitmapCode, wordGcMoveBitmapsCode, wordGcMoveRootsBitmapsCode, wordGenGcMoveCode, wordGenGcPartialMoveCode, wordGenGcMoveBitmapCode, wordGenGcPartialMoveBitmapCode, wordGenGcMoveBitmapsCode, wordGenGcPartialMoveBitmapsCode, wordGenGcMoveRootsBitmapsCode, wordGenGcPartialMoveRootsBitmapsCode, wordGenGcMoveListCode, wordGenGcPartialMoveListCode, wordGenGcMoveDataCode, wordGenGcPartialMoveRefListCode, wordGenGcPartialMoveDataCode, wordGenGcMoveRefsCode, wordGenGcMoveLoopCode, wordGcPartialOrFull, setNewTrigger, listSeqHOL, whileHOL, moveHOL, sub1Inst, subInst, addInst, andInst, xorInst, add1Inst, orInst, addBytesInWordInst, div2Inst, StackRemove.leftShiftInst, StackRemove.rightShiftInst, StackRemove.constInst, StackRemove.loadInst, StackRemove.storeInst, callArgs]

end ConventionSupport

open ConventionSupport in
/-- Exact HOL `stack_alloc_reg_bound` (`stack_allocProofScript.sml:6270-6302`).
HOL's free `sp prog1 dc` are implicit; `EVERY P (MAP SND l)` is bounded
quantification over `l.map Prod.snd`. -/
@[hol "cakeml/compiler/backend/proofs/stack_allocProofScript.sml" "stack_alloc_reg_bound"
  (words_as_type_indexed_bitvec)]
theorem stack_alloc_reg_bound {width : Nat} [NeZero width] {sp : Nat}
    {prog1 : List (Nat × HolProg width)} {dc : DataToWord.Config} :
    10 ≤ sp ∧ (∀ p ∈ prog1.map Prod.snd, regBound p sp) →
    ∀ p ∈ (compile dc prog1).map Prod.snd, regBound p sp := by
  rintro ⟨hsp, h⟩ p hp
  simp only [compile, stubs, List.map_append, List.map_cons, List.map_nil, List.map_map,
    List.mem_append, List.mem_singleton, List.mem_map, Function.comp] at hp
  rcases hp with rfl | ⟨⟨k, q⟩, hq, rfl⟩
  · simp only [regBound]
    exact ⟨stub_regBound dc sp hsp, by omega⟩
  · exact comp_regBound hsp _ _ q (h q (List.mem_map.2 ⟨(k, q), hq, rfl⟩))

open ConventionSupport in
/-- Exact HOL `stack_alloc_call_args` (`stack_allocProofScript.sml:6304-6331`).
HOL's free `prog1 dc` are implicit. -/
@[hol "cakeml/compiler/backend/proofs/stack_allocProofScript.sml" "stack_alloc_call_args"
  (words_as_type_indexed_bitvec)]
theorem stack_alloc_call_args {width : Nat} [NeZero width]
    {prog1 : List (Nat × HolProg width)} {dc : DataToWord.Config} :
    (∀ p ∈ prog1.map Prod.snd, callArgs p 1 2 3 4 0) →
    ∀ p ∈ (compile dc prog1).map Prod.snd, callArgs p 1 2 3 4 0 := by
  intro h p hp
  simp only [compile, stubs, List.map_append, List.map_cons, List.map_nil, List.map_map,
    List.mem_append, List.mem_singleton, List.mem_map, Function.comp] at hp
  rcases hp with rfl | ⟨⟨k, q⟩, hq, rfl⟩
  · simp only [callArgs, and_true]
    exact stub_callArgs dc
  · exact comp_callArgs _ _ q (h q (List.mem_map.2 ⟨(k, q), hq, rfl⟩))

/-- Exact HOL `compile_has_fp_ops` (`stack_allocProofScript.sml:6333-6360`):
the GC stub, and hence `compile`, ignores the FP-capability flags of the
configuration. HOL's free `dconf b1 b2 code` are implicit. -/
@[hol "cakeml/compiler/backend/proofs/stack_allocProofScript.sml" "compile_has_fp_ops"
  (words_as_type_indexed_bitvec)]
theorem compile_has_fp_ops {width : Nat} [NeZero width] {dconf : DataToWord.Config}
    {b1 b2 : Bool} {code : List (Nat × HolProg width)} :
    compile { dconf with hasFpOps := b1, hasFpTern := b2 } code = compile dconf code := rfl

end Flapjack.Compiler.Backend.StackAlloc
