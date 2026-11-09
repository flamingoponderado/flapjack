module

public import Flapjack.Compiler.Backend.ClosToBvl.SourceInc
public import Flapjack.Compiler.Backend.Semantics.ClosProps.FnAnnotations
public import Flapjack.Compiler.Backend.Semantics.ClosSem.State
public import Flapjack.Compiler.Backend.Semantics.BvlSem.State
public import Flapjack.Compiler.Backend.BackendProps.Pure
public import Flapjack.Compiler.Backend.ClosToBvl.Proofs.ExpsEquivalence

@[expose] public section

/-! Future code and compilation-oracle conditions used by the pass simulation. -/
namespace Flapjack.Compiler.Backend.ClosToBvl
open Flapjack.Compiler.Backend.ClosProps Flapjack.Compiler.Backend.BackendProps

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
