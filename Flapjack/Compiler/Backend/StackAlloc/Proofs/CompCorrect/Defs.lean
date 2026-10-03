import Flapjack.Compiler.Backend.StackAlloc.Proofs.AllocCorrect
import Flapjack.Compiler.Backend.StackAlloc.Proofs.InstCorrect
import Flapjack.Compiler.Backend.StackProps.AllocArg
import Flapjack.Compiler.Backend.StackProps.ClockSupport
import Flapjack.Compiler.Backend.StackProps.EvaluateAddClock
import Flapjack.Compiler.Backend.StackProps.EvaluateCodeBitmaps
import Flapjack.Compiler.Backend.StackProps.EvaluateConsts
import Flapjack.Compiler.Backend.Semantics.StackSem.EvaluateClock

/-!
# `stack_allocProof` `comp_correct`: statement infrastructure

Flapjack infrastructure for the case split of `comp_correct`
(`cakeml/compiler/backend/proofs/stack_allocProofScript.sml:5297-5894`). `Tgt`
and `Res` spell out the source's two record overrides of the target state,
`Pre` the source's premises other than the evaluation, `Post` its conclusions
other than the target evaluation, and `Goal` the whole statement for one program
and state. None of these is a HOL declaration; the tagged theorem states the
source shape literally.
-/

namespace Flapjack.Compiler.Backend.StackAlloc.CompCorrect

open Flapjack Flapjack.StackSemStateOps Flapjack.Compiler.Backend.StackLang
open Flapjack.StackSemEvaluate Flapjack.Compiler.Backend.StackProps
open Flapjack.Compiler.Backend.DataToWord Flapjack.Compiler.Backend.WordGcFunctions

/-- Canonical codec for the imported owning StackSem state carrier. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : StackSemStateBroad width C F) (h : state.FiniteSupport),
        (StackSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : StackSemStateFiniteExact width C F,
        StackSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  StackSemStateOps.holFmapAsFiniteSupportWitness

variable {width : Nat} [NeZero width] {C F : Type}

/-- The compiler configuration type of the StackSem state. -/
abbrev CompileFn (width : Nat) [NeZero width] (C : Type) : Type :=
  C → List (Nat × HolProg width) → Option (List (BitVec 8) × C)

/-- HOL `(I ## MAP prog_comp ## I)`. -/
abbrev oracleMap : C × List (Nat × HolProg width) × List (BitVec width) →
    C × List (Nat × HolProg width) × List (BitVec width) :=
  Prod.map id (Prod.map (List.map progComp) id)

/-- The source's result-side override of a StackSem state. -/
abbrev Res (anything : WordSemGcFun width) (cr : CompileFn width C) (c : DataToWord.Config)
    (t : StackSemStateFiniteExact width C F) (regs1 : HolFiniteMapExact Nat (WordLocW width)) :
    StackSemStateFiniteExact width C F :=
  { t with
    useStore := true, useStack := true, useAlloc := false
    regs := regs1, gcFun := anything
    compileOracle := oracleMap ∘ t.compileOracle
    compile := cr
    code := sptFromAList (compile c (sptToAList t.code)) }

/-- The source's input-side override: `Res` with the clock raised by `ck`. -/
abbrev Tgt (anything : WordSemGcFun width) (cr : CompileFn width C) (c : DataToWord.Config)
    (s : StackSemStateFiniteExact width C F) (ck : Nat)
    (regs : HolFiniteMapExact Nat (WordLocW width)) : StackSemStateFiniteExact width C F :=
  { s with
    useStore := true, useStack := true, useAlloc := false
    clock := s.clock + ck, regs := regs, gcFun := anything
    compileOracle := oracleMap ∘ s.compileOracle
    compile := cr
    code := sptFromAList (compile c (sptToAList s.code)) }

/-- The data-buffer bound of the source. -/
abbrev BufBound (s : StackSemStateFiniteExact width C F) : Prop :=
  s.bitmaps.length + s.dataBuffer.buffer.length + s.dataBuffer.spaceLeft < 2 ^ width - 1

/-- The stack-byte bound of the source. -/
abbrev StackBound (s : StackSemStateFiniteExact width C F) : Prop :=
  s.stack.length * (width / 8) < 2 ^ width

/-- The source's premises on the state, other than the evaluation, the
`r <> SOME Error` and the `alloc_arg p` premises. -/
structure Pre (cr : CompileFn width C) (c : DataToWord.Config)
    (s : StackSemStateFiniteExact width C F) (regs : HolFiniteMapExact Nat (WordLocW width)) :
    Prop where
  code : ∀ k prog, sptLookup k s.code = some prog → k ≠ gcStubLocation ∧ StackProps.allocArg prog
  oracle : ∀ n k p, (k, p) ∈ (s.compileOracle n).2.1 → k ≠ gcStubLocation ∧ StackProps.allocArg p
  gcFun : s.gcFun = wordGcFun c
  useAlloc : s.useAlloc = true
  stack : StackBound s
  regs : s.regs.submap regs
  useStack : s.useStack = true
  buf : BufBound s
  compile : s.compile = fun cfg => cr cfg ∘ List.map progComp

/-- The source's conclusions other than the target evaluation. -/
abbrev Post (r : Option (StackSemResult width)) (t : StackSemStateFiniteExact width C F)
    (regs1 : HolFiniteMapExact Nat (WordLocW width)) : Prop :=
  t.regs.submap regs1 ∧ BufBound t ∧ ((∀ w, r ≠ some (.halt w)) → StackBound t)

/-- The whole `comp_correct` statement for one program and state. -/
def Goal (anything : WordSemGcFun width) (cr : CompileFn width C)
    (p : HolProg width) (s : StackSemStateFiniteExact width C F) : Prop :=
  ∀ (r : Option (StackSemResult width)) (t : StackSemStateFiniteExact width C F)
    (m n : Nat) (c : DataToWord.Config) (regs : HolFiniteMapExact Nat (WordLocW width)),
    evaluate (p, s) = (r, t) → r ≠ some .error → StackProps.allocArg p → Pre cr c s regs →
    ∃ ck regs1,
      evaluate ((comp n m p).1, Tgt anything cr c s ck regs) = (r, Res anything cr c t regs1) ∧
      Post r t regs1

theorem tgt_zero (anything : WordSemGcFun width) (cr : CompileFn width C) (c : DataToWord.Config)
    (s : StackSemStateFiniteExact width C F) (regs : HolFiniteMapExact Nat (WordLocW width)) :
    Tgt anything cr c s 0 regs = Res anything cr c s regs := rfl

theorem tgt_eq (anything : WordSemGcFun width) (cr : CompileFn width C) (c : DataToWord.Config)
    (s : StackSemStateFiniteExact width C F) (ck : Nat)
    (regs : HolFiniteMapExact Nat (WordLocW width)) :
    Tgt anything cr c s ck regs = { Res anything cr c s regs with clock := s.clock + ck } := rfl

/-! Commutation of the override with the state operations. -/

theorem res_setVar (anything : WordSemGcFun width) (cr : CompileFn width C) (c : DataToWord.Config)
    (s : StackSemStateFiniteExact width C F) (regs : HolFiniteMapExact Nat (WordLocW width))
    (r : Nat) (v : WordLocW width) :
    setVar r v (Res anything cr c s regs) = Res anything cr c (setVar r v s) (regs.updateEq (r, v)) :=
  rfl

theorem res_emptyEnv (anything : WordSemGcFun width) (cr : CompileFn width C)
    (c : DataToWord.Config) (s : StackSemStateFiniteExact width C F)
    (regs : HolFiniteMapExact Nat (WordLocW width)) :
    emptyEnv (Res anything cr c s regs) = Res anything cr c (emptyEnv s) HolFiniteMapExact.empty :=
  rfl

theorem res_decClock (anything : WordSemGcFun width) (cr : CompileFn width C)
    (c : DataToWord.Config) (s : StackSemStateFiniteExact width C F)
    (regs : HolFiniteMapExact Nat (WordLocW width)) :
    decClock (Res anything cr c s regs) = Res anything cr c (decClock s) regs := rfl

theorem getVar_res (anything : WordSemGcFun width) (cr : CompileFn width C) (c : DataToWord.Config)
    (s : StackSemStateFiniteExact width C F) (regs : HolFiniteMapExact Nat (WordLocW width))
    (hsub : s.regs.submap regs) {r : Nat} {v : WordLocW width} (h : getVar r s = some v) :
    getVar r (Res anything cr c s regs) = some v := hsub _ _ h

theorem submap_empty (m : HolFiniteMapExact Nat (WordLocW width)) :
    (HolFiniteMapExact.empty : HolFiniteMapExact Nat (WordLocW width)).submap m := by
  intro k v h; simp [HolFiniteMapExact.empty] at h

/-! Lookups in a left fold of unions, HOL `lookup_FOLDL_union` with
`FOLDL_OPTION_CHOICE_EQ_SOME_IMP_MEM`. -/

theorem sptLookup_foldl_sptUnion {α : Type} (k : Nat) (v : α) :
    ∀ (trees : List (Spt α)) (init : Spt α),
      sptLookup k (trees.foldl sptUnion init) = some v →
      sptLookup k init = some v ∨ ∃ t ∈ trees, sptLookup k t = some v
  | [], init, h => Or.inl h
  | t :: ts, init, h => by
      rcases sptLookup_foldl_sptUnion k v ts (sptUnion init t) h with h1 | ⟨t', ht', h2⟩
      · rw [sptLookup_sptUnion] at h1
        split at h1
        · rename_i v' hv
          simp only [Option.some.injEq] at h1
          subst h1
          exact Or.inl hv
        · exact Or.inr ⟨t, List.mem_cons_self, h1⟩
      · exact Or.inr ⟨t', List.mem_cons_of_mem _ ht', h2⟩

/-- The source premises survive an evaluation, given the conclusions the source
proves for it (HOL's `evaluate_consts` and `evaluate_code_bitmaps` steps). -/
theorem Pre.of_evaluate {cr : CompileFn width C} {c : DataToWord.Config}
    {p : HolProg width} {s t : StackSemStateFiniteExact width C F}
    {r : Option (StackSemResult width)} {regs regs1 : HolFiniteMapExact Nat (WordLocW width)}
    (h : evaluate (p, s) = (r, t)) (hpre : Pre cr c s regs) (hsub : t.regs.submap regs1)
    (hbuf : BufBound t) (hst : StackBound t) : Pre cr c t regs1 := by
  obtain ⟨hA, -, hK, -, hG, -, -, hC⟩ := evaluateConsts p s r t h
  obtain ⟨k, ho, hcode, -⟩ := EvaluateCodeBitmaps.evaluateCodeBitmaps p s r t h
  refine ⟨?_, ?_, hG ▸ hpre.gcFun, hA ▸ hpre.useAlloc, hst, hsub, hK ▸ hpre.useStack, hbuf,
    hC ▸ hpre.compile⟩
  · intro key prog hl
    rw [hcode] at hl
    rcases sptLookup_foldl_sptUnion _ _ _ _ hl with hl | ⟨tr, htr, hl⟩
    · exact hpre.code key prog hl
    · obtain ⟨i, -, rfl⟩ := List.mem_map.1 htr
      rw [sptLookup_sptFromAList] at hl
      exact hpre.oracle i key prog (sptAListLookup_mem _ _ _ hl)
  · intro n key prog hm
    rw [ho] at hm
    exact hpre.oracle (n + k) key prog hm

end Flapjack.Compiler.Backend.StackAlloc.CompCorrect
