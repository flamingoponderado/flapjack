import Flapjack.Compiler.Backend.ClosToBvl.SourceInc
import Flapjack.Compiler.Backend.Semantics.ClosProps.FnAnnotations
import Flapjack.Compiler.Backend.Semantics.ClosSem.State
import Flapjack.Compiler.Backend.Semantics.BvlSem.State
import Flapjack.Compiler.Backend.BackendProps.Pure
import Flapjack.Compiler.Backend.ClosToBvl.Proofs.ExpsEquivalence

/-! Future code and compilation-oracle conditions used by the pass simulation. -/
namespace Flapjack.Compiler.Backend.ClosToBvl
open Flapjack.Compiler.Backend.ClosProps Flapjack.Compiler.Backend.BackendProps

/-- The checked program converter produces the same incremental result as the
source-shaped definition. This is Flapjack infrastructure connecting the two
compilation interfaces. -/
theorem compileInc_checked_eq (maxApp : Nat) (program : ClosSem.Program) :
    (let (start, expressions) := extractName program.1
     compileProg? maxApp (chainExps start expressions ++ program.2)) =
      some (compileInc maxApp program) := by
  cases h : extractName program.1 with
  | mk start expressions =>
      simpa [compileInc, h] using
        compileProg_checked_eq_original maxApp (chainExps start expressions ++ program.2)

/-- Accumulate the code installed by the first `n` future oracle entries. -/
@[hol "cakeml/compiler/backend/proofs/clos_to_bvlProofScript.sml" "nth_code_def"]
def nthCode {C A : Type} (oracle : Nat → C × List (Nat × A)) : Nat → Spt A
  | 0 => .ln
  | n + 1 => sptUnion (sptFromAList (oracle 0).2) (nthCode (fun i => oracle (i + 1)) n)

/-- Every location accumulated from the first `count` oracle entries came
from an entry strictly before `count`. -/
theorem nthCode_location_before {C A : Type} (oracle : Nat → C × List (Nat × A))
    (count location : Nat) (member : sptMem location (nthCode oracle count)) :
    ∃ index, index < count ∧ location ∈ ((oracle index).2.map Prod.fst) := by
  induction count generalizing oracle with
  | zero =>
    obtain ⟨value, found⟩ := (sptMem_iff_lookup _ _).1 member
    simp [nthCode] at found
  | succ count ih =>
    simp only [nthCode, sptMem_sptUnion] at member
    cases member with
    | inl first =>
      obtain ⟨value, found⟩ := (sptMem_iff_lookup _ _).1 first
      rw [sptLookup_sptFromAList] at found
      have inList := sptAListLookup_mem location (oracle 0).2 value found
      exact ⟨0, by omega, List.mem_map.mpr ⟨(location, value), inList, rfl⟩⟩
    | inr later =>
      obtain ⟨index, bound, found⟩ := ih (fun n => oracle (n + 1)) later
      exact ⟨index + 1, by omega, found⟩

/-- Freshness against both initial code and every earlier oracle entry implies
freshness against the accumulated target-code tree. -/
theorem nthCode_fresh_of_pairwise {C A : Type} (oracle : Nat → C × List (Nat × A))
    (code : Spt A)
    (initialFresh : ∀ index location, sptMem location code → location ∉ (oracle index).2.map Prod.fst)
    (pairwiseFresh : ∀ earlier later location, earlier < later →
      location ∈ (oracle earlier).2.map Prod.fst → location ∉ (oracle later).2.map Prod.fst) :
    ∀ index location, sptMem location (sptUnion code (nthCode oracle index)) →
      location ∉ (oracle index).2.map Prod.fst := by
  intro index location member
  cases (sptMem_sptUnion _ _ _).1 member with
  | inl initial => exact initialFresh index location initial
  | inr accumulated =>
    obtain ⟨earlier, earlierBound, found⟩ := nthCode_location_before oracle index location accumulated
    exact pairwiseFresh earlier index location earlierBound found

/-- Disjoint ordered label intervals for successive oracle entries establish
the freshness condition for all accumulated code, including the initial tree. -/
theorem nthCode_fresh_of_boundaries {C A : Type} (oracle : Nat → C × List (Nat × A))
    (code : Spt A) (boundary : Nat → Nat)
    (monotone : ∀ {i j}, i ≤ j → boundary i ≤ boundary j)
    (initialBelow : ∀ location, sptMem location code → location < boundary 0)
    (ranges : ∀ index location, location ∈ (oracle index).2.map Prod.fst →
      boundary index ≤ location ∧ location < boundary (index + 1)) :
    ∀ index location, sptMem location (sptUnion code (nthCode oracle index)) →
      location ∉ (oracle index).2.map Prod.fst := by
  apply nthCode_fresh_of_pairwise oracle code
  · intro index location initial future
    have below := initialBelow location initial
    have order := monotone (Nat.zero_le index)
    have lower := (ranges index location future).1
    omega
  · intro earlier later location indexBound old future
    have upper := (ranges earlier location old).2
    have lower := (ranges later location future).1
    have order := monotone (show earlier + 1 ≤ later by omega)
    omega

/-- The compiler and oracle agree with incremental conversion, with fresh
future labels and the source annotations required by closure conversion. -/
@[hol "cakeml/compiler/backend/proofs/clos_to_bvlProofScript.sml" "compile_oracle_inv_def" 1069]
def compileOracleInv {CC OC Result S : Type} (maxApp : Nat) (_sourceCode : S)
    (sourceCompiler : CC → ClosSem.Program → Result)
    (sourceOracle : ClosSem.CompileOracle OC)
    (targetCode : Spt (Nat × Bvl.Exp))
    (targetCompiler : CC → List (Nat × Nat × Bvl.Exp) → Result)
    (targetOracle : BvlSem.CompileOracle OC) : Prop :=
  sourceCompiler = pureCc (compileInc maxApp) targetCompiler ∧
  targetOracle = pureCo (compileInc maxApp) ∘ sourceOracle ∧
  (∀ n, ((targetOracle n).2.map Prod.fst).Nodup) ∧
  (∀ n p, sptMem p (sptUnion targetCode (nthCode targetOracle n)) →
    p ∉ (targetOracle n).2.map Prod.fst) ∧
  ∀ n, everyFnLocationSome (sourceOracle n).2.1 ∧
    everyFnVarsSome (sourceOracle n).2.1 ∧
    (∀ entry ∈ (sourceOracle n).2.2, everyFnLocationSome [entry.2.2]) ∧
    (∀ entry ∈ (sourceOracle n).2.2, everyFnVarsSome [entry.2.2])

/-- The explicit compiler and oracle transformations, annotation checks,
distinct future labels and ordered label intervals establish the candidate
compiler-oracle invariant used by the evaluation simulation. -/
theorem compileOracleInv_of_boundaries {C : Type} (maxApp : Nat)
    (sourceCode : HolFiniteMapExact Nat (Nat × ClosLang.Exp))
    (sourceOracle : ClosSem.CompileOracle C) (targetCode : Spt (Nat × Bvl.Exp))
    (targetCompiler : BvlSem.Compiler C) (boundary : Nat → Nat)
    (monotone : ∀ {i j}, i ≤ j → boundary i ≤ boundary j)
    (initialBelow : ∀ location, sptMem location targetCode → location < boundary 0)
    (distinct : ∀ index, ((compileInc maxApp (sourceOracle index).2).map Prod.fst).Nodup)
    (ranges : ∀ index location, location ∈ (compileInc maxApp (sourceOracle index).2).map Prod.fst →
      boundary index ≤ location ∧ location < boundary (index + 1))
    (annotations : ∀ index, everyFnLocationSome (sourceOracle index).2.1 ∧
      everyFnVarsSome (sourceOracle index).2.1 ∧
      (∀ entry ∈ (sourceOracle index).2.2, everyFnLocationSome [entry.2.2]) ∧
      (∀ entry ∈ (sourceOracle index).2.2, everyFnVarsSome [entry.2.2])) :
    compileOracleInv maxApp sourceCode (pureCc (compileInc maxApp) targetCompiler) sourceOracle targetCode
      targetCompiler (pureCo (compileInc maxApp) ∘ sourceOracle) := by
  refine ⟨rfl, rfl, ?_, ?_, annotations⟩
  · simpa [Function.comp_def, pureCo] using distinct
  · apply nthCode_fresh_of_boundaries (pureCo (compileInc maxApp) ∘ sourceOracle) targetCode boundary
      monotone initialBelow
    simpa [Function.comp_def, pureCo] using ranges

/-- The next target oracle entry is the incremental compilation of the
source entry, with fresh and distinct labels and the corresponding callback. -/
theorem compileOracleInv_head {CC OC Result S : Type} (maxApp : Nat) (sourceCode : S)
    (sourceCompiler : CC → ClosSem.Program → Result) (sourceOracle : ClosSem.CompileOracle OC)
    (targetCode : Spt (Nat × Bvl.Exp)) (targetCompiler : CC → List (Nat × Nat × Bvl.Exp) → Result)
    (targetOracle : BvlSem.CompileOracle OC)
    (invariant : compileOracleInv maxApp sourceCode sourceCompiler sourceOracle targetCode targetCompiler targetOracle) :
    targetOracle 0 = pureCo (compileInc maxApp) (sourceOracle 0) ∧
      (∀ config program, sourceCompiler config program = targetCompiler config (compileInc maxApp program)) ∧
      ((targetOracle 0).2.map Prod.fst).Nodup ∧
      ∀ entry ∈ (targetOracle 0).2, sptLookup entry.1 targetCode = none := by
  obtain ⟨compilerEq, oracleEq, nodup, fresh, _⟩ := invariant
  refine ⟨congrFun oracleEq 0, ?_, nodup 0, ?_⟩
  · intro config program
    rw [compilerEq]
    rfl
  · intro entry member
    cases lookup : sptLookup entry.1 targetCode with
    | none => rfl
    | some value =>
      have mem : sptMem entry.1 targetCode := (sptMem_iff_lookup _ _).2 ⟨value, lookup⟩
      have excluded := fresh 0 entry.1 ((sptMem_sptUnion _ _ _).2 (Or.inl mem))
      exact False.elim (excluded (List.mem_map.mpr ⟨entry, member, rfl⟩))

/-- Consuming the first future compilation entry preserves the oracle
invariant when its code is added to the target code tree. The source-code
parameter is observationally irrelevant to this invariant. -/
theorem compileOracleInv_shift {CC OC Result S : Type} (maxApp : Nat) (sourceCode sourceCode' : S)
    (sourceCompiler : CC → ClosSem.Program → Result) (sourceOracle : ClosSem.CompileOracle OC)
    (targetCode : Spt (Nat × Bvl.Exp)) (targetCompiler : CC → List (Nat × Nat × Bvl.Exp) → Result)
    (targetOracle : BvlSem.CompileOracle OC)
    (invariant : compileOracleInv maxApp sourceCode sourceCompiler sourceOracle targetCode targetCompiler targetOracle) :
    compileOracleInv maxApp sourceCode' sourceCompiler (fun n => sourceOracle (n + 1))
      (sptUnion targetCode (sptFromAList (targetOracle 0).2)) targetCompiler (fun n => targetOracle (n + 1)) := by
  obtain ⟨compilerEq, oracleEq, nodup, fresh, annotations⟩ := invariant
  refine ⟨compilerEq, ?_, ?_, ?_, ?_⟩
  · funext n
    exact congrFun oracleEq (n + 1)
  · intro n
    exact nodup (n + 1)
  · intro n p member
    apply fresh (n + 1) p
    simp only [nthCode, sptMem_sptUnion] at member ⊢
    exact member.elim (fun first => first.elim Or.inl (fun h => Or.inr (Or.inl h)))
      (fun h => Or.inr (Or.inr h))
  · intro n
    exact annotations (n + 1)

end Flapjack.Compiler.Backend.ClosToBvl
