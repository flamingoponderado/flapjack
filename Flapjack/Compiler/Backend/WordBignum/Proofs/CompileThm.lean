module

public import Flapjack.Compiler.Backend.WordBignum.Proofs.CompileThmCases

@[expose] public section

/-! HOL `compile_thm` of `cakeml/compiler/backend/proofs/word_bignumProofScript.sml`:
the mini-language compiler is correct with respect to the `wordSem`
evaluator. The proof is HOL's induction over the `Eval` rules; each rule's case
is a Flapjack-only lemma of `CompileThmCases`. -/

namespace Flapjack.Compiler.Backend.WordBignum

open Flapjack
open Flapjack.Compiler.Backend.WordBignum.CompileThmSupport

namespace CompileThmWitness

/-- Same-module canonical roundtrip witness for the mini-language state
carrier, required by the relation qualifier on `compile_thm`. -/
theorem holFmapAsFiniteSupportRelationWitness_MiniState {width : Nat} [NeZero width] :
    (∀ s : MiniStateBroad width, (MiniState.ofBroad s).toBroad = s) ∧
      (∀ s : MiniState width, MiniState.ofBroad s.toBroad = s) :=
  Flapjack.Compiler.Backend.WordBignum.holFmapAsFiniteSupportWitness

/-- Same-module canonical roundtrip witness for the `wordSem` state carrier,
required by the relation qualifier on `compile_thm`. -/
theorem holFmapAsFiniteSupportRelationWitness_WordSemStateFiniteExact {width : Nat}
    [NeZero width] {C : Type} {F : Type} :
    (∀ (state : WordSemStateBroad width C F) (h : state.FiniteSupport),
        (WordSemStateBroad.ofBroad state h).toBroad = state) ∧
      (∀ state : WordSemStateFiniteExact width C F,
        WordSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  WordSemStateExact.holFmapAsFiniteSupportWitness

end CompileThmWitness

/-- HOL `compile_thm` (`word_bignumProofScript.sml:682`): if the mini program
`prog` evaluates under `Eval rec` from `s1` to `s2`, then its compiled word
program `p1`, run from a related `wordSem` state `t1` and followed by any `p9`,
behaves like `p9` (for a finished `INR` result) or like the tail call back to
the enclosing loop (for a `Continue`, `INL` result) from a related state `t2`
with the same stack, return location and code. HOL's free variables `t0` and
`frame` are explicit parameters; the type variables of `cs2`'s first component
and of the `wordSem` compiler-configuration and FFI types are `β`, `C`, `F`.
HOL's premise is one conjunction, kept as one hypothesis. -/
@[hol "cakeml/compiler/backend/proofs/word_bignumProofScript.sml" "compile_thm"
  (fmap_as_finite_support_relation :=
    [MiniState.regs, WordSemStateFiniteExact.fpRegs, WordSemStateFiniteExact.store])
  (words_as_type_indexed_bitvec)]
theorem compile_thm {width : Nat} [NeZero width] {β C F : Type}
    (t0 : WordSemStateFiniteExact width C F)
    (frame : ((BitVec width × WordLocW width) → Prop) → Prop) :
    ∀ (rec : Option (Mini (BitVec width))) (s1 : MiniState width) (prog : Mini (BitVec width))
      (s2 : Sum (MiniState width) (MiniState width)),
      Eval rec s1 prog s2 →
      ∀ (n l i : Nat)
        (cs : Nat × List (Mini (BitVec width) × Nat × WordLangProgHOL (BitVec width)))
        (p1 : WordLangProgHOL (BitVec width)) (l1 i1 : Nat)
        (cs1 : Nat × List (Mini (BitVec width) × Nat × WordLangProgHOL (BitVec width)))
        (cs2 : β × List (Mini (BitVec width) × Nat × WordLangProgHOL (BitVec width)))
        (t1 : WordSemStateFiniteExact width C F) (retVal : WordLocW width)
        (p9 : WordLangProgHOL (BitVec width)),
        compile n l i cs prog = (p1, l1, i1, cs1) ∧ stateRel s1 t1 cs2 t0 frame ∧ 0 < i ∧
          syntaxOk prog ∧ codeSubset cs1 cs2 ∧
          (∀ body, rec = some body →
            ∃ (l i : Nat)
              (cs : Nat × List (Mini (BitVec width) × Nat × WordLangProgHOL (BitVec width)))
              (p1 : WordLangProgHOL (BitVec width)) (l1 i1 : Nat)
              (cs1 : Nat × List (Mini (BitVec width) × Nat × WordLangProgHOL (BitVec width))),
              compile n l i cs body = (p1, l1, i1, cs1) ∧ 0 < i ∧ syntaxOkAux body ∧
                codeSubset cs1 cs2 ∧ sptLookup n t1.code = some (1, .seq p1 (.return 0 [0]))) ∧
          (∀ body, prog = .loopBody body →
            p9 = .return 0 [0] ∧ sptLookup n t1.code = some (1, .seq p1 (.return 0 [0]))) ∧
          WordSemStateFiniteExact.getVar 0 t1 = some retVal ∧ goodDimindex width →
        ∃ (t2 : WordSemStateFiniteExact width C F)
          (res : Option (WordSemResult width) × WordSemStateFiniteExact width C F),
          WordSemStateFiniteExact.evaluate (.seq p1 p9) t1 = res ∧
            match s2 with
            | .inl s =>
                res = WordSemStateFiniteExact.evaluate (.call none (some n) [0] none) t2 ∧
                  0 < i1 ∧ t2.stack = t1.stack ∧
                  WordSemStateFiniteExact.getVar 0 t2 = some retVal ∧
                  stateRel s t2 cs2 t0 frame ∧ t2.code = t1.code
            | .inr s =>
                res = WordSemStateFiniteExact.evaluate p9 t2 ∧ 0 < i1 ∧
                  t2.stack = t1.stack ∧ WordSemStateFiniteExact.getVar 0 t2 = some retVal ∧
                  stateRel s t2 cs2 t0 frame ∧ t2.code = t1.code := by
  intro rec s1 prog s2 h
  show CompileGoal t0 frame β rec s1 prog s2
  induction h with
  | skip r s => exact case_skip t0 frame r s
  | «continue» r s => exact case_continue t0 frame r s
  | delete r vs s => exact case_delete t0 frame r vs s
  | assign r s x n hpre => exact case_assign t0 frame r s x n hpre
  | seq r s1 s2 s3 p1 p2 _ _ ih1 ih2 => exact case_seq t0 frame r s1 s2 s3 p1 p2 ih1 ih2
  | ite rec s1 c r ri p1 p2 s2 hreg hri _ ih => exact case_ite t0 frame rec s1 c r ri p1 p2 s2 hreg hri ih
  | load rec s r i a w h => exact case_load t0 frame rec s r i a w h
  | store rec s r i w wr h => exact case_store t0 frame rec s r i w wr h
  | swap r s => exact case_swap t0 frame r s
  | add n1 n2 n3 n4 n5 r s r1 r2 h => exact case_add t0 frame n1 n2 n3 n4 n5 r s r1 r2 h
  | sub r s n1 n2 n3 n4 n5 r1 r2 h => exact case_sub t0 frame r s n1 n2 n3 n4 n5 r1 r2 h
  | mul r s n1 n2 n3 n4 h => exact case_mul t0 frame r s n1 n2 n3 n4 h
  | div r s n1 n2 n3 n4 n5 h => exact case_div t0 frame r s n1 n2 n3 n4 n5 h
  | loop r s1 p vs s2 rec _ hclock ih => exact case_loop t0 frame r s1 p vs s2 rec hclock ih
  | recurse s1 save vs p s2 s3 _ hcopy hclock ih =>
    exact case_recurse t0 frame s1 save vs p s2 s3 hcopy hclock ih
  | loopBodyReturn r s1 p s2 _ ih => exact case_loopBodyReturn t0 frame r s1 p s2 ih
  | loopBodyContinue r s1 s2 s3 p _ hclock _ ih1 ih2 =>
    exact case_loopBodyContinue t0 frame r s1 s2 s3 p hclock ih1 ih2

end Flapjack.Compiler.Backend.WordBignum
