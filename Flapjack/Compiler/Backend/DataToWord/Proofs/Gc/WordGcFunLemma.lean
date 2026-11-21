module

public import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.CombinedStore

@[expose] public section

/-! The store-level collector lemma `word_gc_fun_lemma` of
`data_to_word_gcProofScript.sml`. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.WordGcFunctions
open Flapjack.Compiler.Backend.DataToWord.Proofs.Memory Flapjack.Compiler.Backend.GcCombined

namespace WordGcFunLemmaWitnesses
/-- Canonical finite-map roundtrip for the word-semantics state. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : WordSemStateBroad width C F) (h : state.FiniteSupport),
      (WordSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : WordSemStateFiniteExact width C F,
      WordSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  WordSemStateExact.holFmapAsFiniteSupportWitness
end WordGcFunLemmaWitnesses

/-- HOL types are inhabited: a word-semantics state exists whenever its compiler
state and FFI state types are inhabited. HOL's record literal `<| store := s1 |>`
is `ARB with store := s1`, rendered through `holArb` with this global derived
instance. Flapjack infrastructure. -/
instance wordSemStateFiniteExactNonempty {width : Nat} [NeZero width] {C F : Type}
    [Nonempty C] [Nonempty F] : Nonempty (WordSemStateFiniteExact width C F) := by
  obtain ⟨c⟩ := ‹Nonempty C›
  obtain ⟨f⟩ := ‹Nonempty F›
  exact ⟨{
    locals := .ln
    localsSize := none
    fpRegs := HolFiniteMapExact.empty
    store := HolFiniteMapExact.empty
    stack := []
    stackLimit := 0
    stackMax := none
    stackSize := .ln
    memory := fun _ => .loc 0 0
    mdomain := fun _ => false
    shMdomain := fun _ => false
    permute := fun _ _ => 0
    compile := fun _ _ => none
    compileOracle := fun _ => (c, [])
    codeBuffer := ⟨0, [], 0⟩
    dataBuffer := ⟨0, [], 0⟩
    gcFun := fun _ => none
    handler := 0
    clock := 0
    termdep := 0
    code := .ln
    be := false
    ffi := ⟨fun _ s _ _ => .ret s [], f, []⟩ }⟩

/-- Exact HOL `word_gc_fun_lemma` (`data_to_word_gcProofScript.sml:4045-4328`), in the
exported form (the source's `Q.prove` simplified with `LET_DEF`, `PULL_EXISTS` and
conjunction associativity): the free `k` and the HOL free variables are universally
quantified, and the record literal `<| store := s1 |>` is
`{ holArb (WordSemStateFiniteExact width C F) with store := s1 }` at the free
compiler and FFI state types `C`/`F`. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_gcProofScript.sml" "word_gc_fun_lemma"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)
  (total_function_inhabitants := [C, F])]
theorem word_gc_fun_lemma {width : Nat} [NeZero width] {C F : Type} [Nonempty C] [Nonempty F]
    {c : Config} {v : DataSem.Value} {stack : List (DataSem.Value × WordLocW width)}
    {refs : Spt (BvlSem.Ref DataSem.Value)} {v' : HeapAddress (WordLocW width)}
    {xs : List (HeapAddress (WordLocW width))}
    {heap : List (HeapElement (WordLocW width) (HeapTag × List (WordLocW width)))}
    {be : Bool} {a sp sp1 : Nat} {gens : GenState} {limit ts : Nat}
    {s : HolFiniteMapExact WordStoreHOL (WordLocW width)}
    {m : BitVec width → WordLocW width} {dm : BitVec width → Bool}
    {roots2 : List (HeapAddress (WordLocW width))}
    {heap2 : List (HeapElement (WordLocW width) (HeapTag × List (WordLocW width)))}
    {a2 n2 : Nat} {gens2 : GenState} {k : Nat} :
    absMlInv c (v :: stack.map Prod.fst) refs (v' :: xs, heap, be, a, sp, sp1, gens) limit ts ∧
        goodDimindex width ∧ heapInMemoryStore heap a sp sp1 gens c s m dm limit ∧
        wordAddr c v' = holFapply s .globals ∧
        List.Forall₂ (fun v w => wordAddr c v = w) xs (stack.map Prod.snd) ∧
        gcCombined (makeGcConf (α := List (WordLocW width)) limit) c.gcKind
          (v' :: xs, heap, gens, a + sp + sp1, doPartial c s) =
          (roots2, heap2, a2, n2, gens2, true) →
      ∃ (stack1 : List (WordLocW width)) (m1 : BitVec width → WordLocW width)
        (s1 : HolFiniteMapExact WordStoreHOL (WordLocW width)) (k2 k3 : Nat)
        (v : HeapAddress (WordLocW width)) (xs : List (HeapAddress (WordLocW width))),
        wordGcFun c (stack.map Prod.snd, m, dm, s) = some (stack1, m1, s1) ∧
        heapInMemoryStore heap2 a2 k2 k3 gens2 c s1 m1 dm limit ∧ k2 + k3 = n2 ∧
        (∀ l : List Nat, s.lookup .allocSize = some (.word (gcAllocSize k)) ∧
            c.gcKind = .generational l ∧ wordGenGcCanDoPartial l s →
          WordSemStateFiniteExact.hasSpace (.word (gcAllocSize k : BitVec width))
            { holArb (WordSemStateFiniteExact width C F) with store := s1 } = some true) ∧
        ((c.gcKind = .none ∨ c.gcKind = .simple) → k3 = 0) ∧
        (∀ (l : List Nat) (k : Nat), s.lookup .allocSize = some (.word (gcAllocSize k)) ∧
            c.gcKind = .generational l ∧ ¬ wordGenGcCanDoPartial l s ∧ k ≤ n2 → k ≤ k2) ∧
        roots2 = v :: xs ∧ wordAddr c v = holFapply s1 .globals ∧
        List.Forall₂ (fun v w => wordAddr c v = w) xs
          (((stack.map Prod.fst).zip stack1).map Prod.snd) ∧
        stack1.length = stack.length := by
  rintro ⟨source, good, heapMem, global, related, run⟩
  obtain ⟨stack1, outMemory, outStore, k2, k3, root1, rest, execution, invariant, sum, zero,
    rootsOut, globalOut, stackOut, length, _, space, allocation⟩ :=
    combinedGc_stack_correct c v stack refs v' xs roots2 heap heap2 be a sp sp1 limit ts a2 n2
      gens gens2 s m dm source good heapMem global related run
  refine ⟨stack1, outMemory, outStore, k2, k3, root1, rest, execution, invariant, sum, ?_, zero,
    ?_, rootsOut, globalOut, stackOut, length⟩
  · rintro l ⟨alloc, kind, partialOk⟩
    exact space l _ kind partialOk alloc (holArb (WordSemStateFiniteExact width C F))
  · rintro l requested ⟨alloc, kind, full, bound⟩
    exact allocation l requested kind full (by simpa [gcAllocSize] using alloc) bound

end Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
