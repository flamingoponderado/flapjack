import Flapjack.Compiler.Backend.WordToStack.NativePrograms
import Flapjack.Misc.Sptree

/-! backendProofScript.sml `compile_word_to_stack_sfs_aux` (2788-2809): the
frame sizes returned by `compile_word_to_stack` agree with those of compiling
each program separately from empty bitmaps. HOL `fromAList` is the external
HOL-library rendering `sptFromAList`; `Nil` is `AppList.nil`. -/
namespace Flapjack.Compiler.Backend.BackendProof

open Flapjack Flapjack.Compiler.Backend.WordToStack.Native
open Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Backend.StackLang

/-- The frame size computed by `compile_prog` does not depend on the incoming
bitmaps (Flapjack infrastructure for the theorem below). -/
theorem compileProgNative_frame_bitmaps {width : Nat} [NeZero width]
    (ac : AsmConfigExact width) (perf : Bool) (prog : WordLangProgHOL (BitVec width))
    (argCount k : Nat) (bm bm' : AppList (BitVec width) × Nat) :
    (compileProgNative ac perf prog argCount k bm).2.1 =
      (compileProgNative ac perf prog argCount k bm').2.1 := by
  simp only [compileProgNative]

/-- Full original `compile_word_to_stack_sfs_aux`:
`compile_word_to_stack ac perf k p bm = (progs',fs',bitmaps) ∧ perf = F ⇒
fromAList (MAP (λkv. (FST kv, (λ(arg_count,prog). FST (SND (compile_prog ac perf
prog arg_count k (Nil,0)))) (SND kv))) p) =
fromAList (MAP (λ((i,_),n). (i,n)) (ZIP (progs',fs')))`. The identifiers are
`num`, as HOL infers from `fromAList`. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem compileWordToStackSfsAux {width : Nat} [NeZero width] :
    ∀ (ac : AsmConfigExact width) (perf : Bool) (k : Nat)
      (p : List (Nat × Nat × WordLangProgHOL (BitVec width)))
      (bm : AppList (BitVec width) × Nat) (progs' : List (Nat × HolProg width))
      (fs' : List Nat) (bitmaps : AppList (BitVec width) × Nat),
      compileWordToStackNative ac perf k p bm = (progs', fs', bitmaps) ∧ perf = false →
      sptFromAList (p.map fun kv =>
          (kv.1, (compileProgNative ac perf kv.2.2 kv.2.1 k (.nil, 0)).2.1)) =
        sptFromAList ((progs'.zip fs').map fun x => (x.1.1, x.2)) := by
  intro ac perf k p
  induction p with
  | nil =>
      intro bm progs' fs' bitmaps ⟨h, _⟩
      simp only [compileWordToStackNative, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, -⟩ := h
      rfl
  | cons hd tl ih =>
      intro bm progs' fs' bitmaps ⟨h, hperf⟩
      obtain ⟨i, n, prog⟩ := hd
      simp only [compileWordToStackNative] at h
      generalize hc : compileProgNative ac perf prog n k bm = c at h
      obtain ⟨body, frame, bm1⟩ := c
      generalize hr : compileWordToStackNative ac perf k tl bm1 = r at h
      obtain ⟨bodies, frames, bm2⟩ := r
      simp only [Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, -⟩ := h
      have hf : (compileProgNative ac perf prog n k (.nil, 0)).2.1 = frame := by
        rw [compileProgNative_frame_bitmaps ac perf prog n k (.nil, 0) bm, hc]
      simp only [List.map_cons, List.zip_cons_cons, sptFromAList, hf]
      rw [ih bm1 bodies frames bm2 ⟨hr, hperf⟩]

end Flapjack.Compiler.Backend.BackendProof
