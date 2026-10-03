import Flapjack.Compiler.Backend.StackAlloc.Proofs.CompileSemantics

/-!
# `stack_allocProof` `make_init_def`, `prog_comp_lambda` and `make_init_semantics`

`make_init_def`, `prog_comp_lambda` and `make_init_semantics` of
`cakeml/compiler/backend/proofs/stack_allocProofScript.sml` (6068-6109): the
initial state for the `stack_alloc` source program, and the semantics
equivalence between the compiled initial state and it, from `compile_semantics`.
-/

namespace Flapjack.Compiler.Backend.StackAlloc

open Flapjack Flapjack.StackSemStateOps Flapjack.Compiler.Backend.StackLang
open Flapjack.StackSemEvaluate Flapjack.Compiler.Backend.StackProps
open Flapjack.Compiler.Backend.DataToWord Flapjack.Compiler.Backend.WordGcFunctions
open ProgCompSupport

namespace MakeInitSupport

/-- Canonical codec for the imported owning StackSem state carrier. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : StackSemStateBroad width C F) (h : state.FiniteSupport),
        (StackSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : StackSemStateFiniteExact width C F,
        StackSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  StackSemStateOps.holFmapAsFiniteSupportWitness

end MakeInitSupport

/-- Exact HOL `make_init_def` (`stack_allocProofScript.sml:6068-6073`): the
source-side initial state, with the given code and oracle, the collector of `c`,
allocation and stack enabled, and the compiler that first runs `prog_comp`. -/
@[hol "cakeml/compiler/backend/proofs/stack_allocProofScript.sml" "make_init_def"
  (fmap_as_finite_support := [regs, fpRegs, store]) (words_as_type_indexed_bitvec)]
noncomputable def makeInit {width : Nat} [NeZero width] {C F : Type} (c : DataToWord.Config)
    (code : Spt (HolProg width))
    (oracle : Nat → C × List (Nat × HolProg width) × List (BitVec width))
    (s : StackSemStateFiniteExact width C F) : StackSemStateFiniteExact width C F :=
  { s with
    code := code, useAlloc := true, useStack := true, gcFun := wordGcFun c
    compile := fun cfg => s.compile cfg ∘ List.map progComp
    compileOracle := oracle }

/-- Exact HOL `prog_comp_lambda` (`stack_allocProofScript.sml:6075-6079`): the
paired-lambda form of `prog_comp_def`. -/
@[hol "cakeml/compiler/backend/proofs/stack_allocProofScript.sml" "prog_comp_lambda"
  (words_as_type_indexed_bitvec)]
theorem prog_comp_lambda {width : Nat} [NeZero width] :
    (progComp : Nat × HolProg width → Nat × HolProg width) =
      fun np => (np.1, (comp np.1 (nextLabHOL np.2 2) np.2).1) :=
  prog_comp_lemma

/-- Exact HOL `make_init_semantics` (`stack_allocProofScript.sml:6081-6109`).
HOL's free `code oracle s c start` are implicit; `ALOOKUP` is `sptAListLookup`,
`ALL_DISTINCT (MAP FST code)` is `List.Nodup`, and `(I ## MAP prog_comp ## I) o
oracle` is `Prod.map id (Prod.map (List.map progComp) id) ∘ oracle`. All ten
premises are kept; as in HOL, `ALL_DISTINCT` is not needed by the proof. The
native evaluator inherits the `reals_as_rational_cuts` limit (`docs/SOUNDNESS.md`
item 8). -/
@[hol "cakeml/compiler/backend/proofs/stack_allocProofScript.sml" "make_init_semantics"
  (fmap_as_finite_support := [regs, fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem make_init_semantics {width : Nat} [NeZero width] {C F : Type}
    {code : List (Nat × HolProg width)}
    {oracle : Nat → C × List (Nat × HolProg width) × List (BitVec width)}
    {s : StackSemStateFiniteExact width C F} {c : DataToWord.Config} {start : Nat} :
    (∀ k prog, sptAListLookup k code = some prog →
      k ≠ gcStubLocation ∧ StackProps.allocArg prog) ∧
    (∀ (i k : Nat) (q : HolProg width), (k, q) ∈ (oracle i).2.1 →
      k ≠ gcStubLocation ∧ StackProps.allocArg q) ∧
    s.useStack = true ∧ s.useStore = true ∧ ¬ s.useAlloc = true ∧
    s.code = sptFromAList (compile c code) ∧
    s.compileOracle = Prod.map id (Prod.map (List.map progComp) id) ∘ oracle ∧
    s.bitmaps.length + s.dataBuffer.buffer.length + s.dataBuffer.spaceLeft < 2 ^ width - 1 ∧
    s.stack.length * (width / 8) < 2 ^ width ∧
    (code.map Prod.fst).Nodup ∧
    semantics start (makeInit c (sptFromAList code) oracle s) ≠ .fail →
    semantics start s = semantics start (makeInit c (sptFromAList code) oracle s) := by
  rintro ⟨hcode, horacle, hK, hS, hA, hc, hor, hbuf, hst, -, hsem⟩
  have h := compile_semantics (s := makeInit c (sptFromAList code) oracle s) (c := c)
    (compile_rest := s.compile) (start := start) (anything := s.gcFun)
    ⟨fun k prog hk => hcode k prog (by
      change sptLookup k (sptFromAList code) = some prog at hk
      rwa [sptLookup_sptFromAList] at hk), horacle, rfl, hbuf,
      hst, rfl, rfl, rfl, hsem⟩
  rw [← h]
  congr 1
  have hcc : sptFromAList (compile c (sptToAList (sptFromAList code))) = s.code := by
    rw [hc]
    refine (sptEqThm _ _ ⟨sptWfFromAList _, sptWfFromAList _⟩).mpr fun n => ?_
    rw [CompCorrect.sptLookup_compile, CompCorrect.sptLookup_compile,
      sptAListLookup_sptToAList, sptLookup_sptFromAList]
  cases s
  simp only [makeInit] at hcc hor hS hK hA ⊢
  simp only [Bool.not_eq_true] at hA
  subst hS hK hA
  rw [hcc, hor]
