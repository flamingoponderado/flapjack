import Flapjack.Compiler.Backend.SourceToFlat.ToWord
import Flapjack.Compiler.Backend.BviToData.Proofs.CompileAgreement

/-! Executed data and word stages for the configured source pipeline. -/
namespace Flapjack.Compiler.Backend.SourceToFlat
open Flapjack

/-- The fused executable traversal first produces the same data program as
the total BVI-to-data compiler, then runs the checked data-to-word compiler. -/
theorem configured_word_lowering_factors (fuel : Nat) (config : DataToWord.Config)
    (program : List (Nat × Nat × Bvi.Exp)) :
    (program.mapM fun (name, args, body) => do
      let body ← BviToData.compileExpBounded fuel args body
      let (body, _) ← DataToWord.compileControl? (width := 64) config name 2 body
      pure (name, args + 1, body)) =
    ((BviToData.compileProg program).mapM fun (name, args, body) => do
      let (body, _) ← DataToWord.compileControl? (width := 64) config name 2 body
      pure (name, args + 1, body)) := by
  induction program with
  | nil => rfl
  | cons part rest ih =>
    obtain ⟨name, args, body⟩ := part
    change _ = (BviToData.compilePart (name, args, body) :: BviToData.compileProg rest).mapM _
    simp only [List.mapM_cons, BviToData.compilePart]
    rw [ih]
    simp [BviToData.compileExpBounded_agrees_all]

/-- A successful configured source-to-word run contains the actual BVI run
and checked lowering of its complete data program, followed by both stub
groups. This is a pipeline decomposition, not data-to-word correctness. -/
theorem configured_word_stage_witnesses (fuel : Nat) (source : Config)
    (closure : ClosToBvl.Config) (bvlConfig : BvlToBvi.Config) (wordConfig : DataToWord.Config)
    (decls : List AstHOL.Dec) (resultSource : Config) (resultClosure : ClosToBvl.Config)
    (resultConfig : BvlToBvi.Config) (output : List (Nat × Nat × WordLangProgHOL (BitVec 64)))
    (names : Spt Basis.Pure.MlString.MlString)
    (run : compileCakeToWord64ConfiguredFuel fuel source closure bvlConfig wordConfig decls =
      some (resultSource, resultClosure, resultConfig, output, names)) :
    ∃ bviCode lowered fixed bignum,
      compileCakeToBviConfiguredFuel fuel source closure bvlConfig decls =
        some (resultSource, resultClosure, resultConfig, bviCode, names) ∧
      ((BviToData.compileProg bviCode).mapM fun (name, args, body) => do
        let (body, _) ← DataToWord.compileControl? (width := 64) wordConfig name 2 body
        pure (name, args + 1, body)) = some lowered ∧
      DataToWord.fixedStubs? wordConfig = some fixed ∧
      WordBignum.generateStubs 64 DataToWord.bignumLocation = some bignum ∧
      output = fixed ++ bignum ++ lowered := by
  unfold compileCakeToWord64ConfiguredFuel at run
  cases first : compileCakeToBviConfiguredFuel fuel source closure bvlConfig decls with
  | none => simp [first] at run
  | some firstResult =>
    obtain ⟨source', closure', config', bviCode, names'⟩ := firstResult
    rw [first] at run
    change (do
      let code ← bviCode.mapM fun (name, args, body) => do
        let body ← BviToData.compileExpBounded fuel args body
        let (body, _) ← DataToWord.compileControl? (width := 64) wordConfig name 2 body
        pure (name, args + 1, body)
      let fixed ← DataToWord.fixedStubs? wordConfig
      let bignum ← WordBignum.generateStubs 64 DataToWord.bignumLocation
      pure (source', closure', config', fixed ++ bignum ++ code, names')) =
        some (resultSource, resultClosure, resultConfig, output, names) at run
    rw [configured_word_lowering_factors] at run
    cases second : (BviToData.compileProg bviCode).mapM (fun (name, args, body) => do
        let (body, _) ← DataToWord.compileControl? (width := 64) wordConfig name 2 body
        pure (name, args + 1, body)) with
    | none => rw [second] at run; contradiction
    | some lowered =>
      rw [second] at run
      change (do
        let fixed ← DataToWord.fixedStubs? wordConfig
        let bignum ← WordBignum.generateStubs 64 DataToWord.bignumLocation
        pure (source', closure', config', fixed ++ bignum ++ lowered, names')) =
          some (resultSource, resultClosure, resultConfig, output, names) at run
      cases third : DataToWord.fixedStubs? (width := 64) wordConfig with
      | none => simp [third] at run
      | some fixed =>
        cases fourth : WordBignum.generateStubs 64 DataToWord.bignumLocation with
        | none => simp [third, fourth] at run
        | some bignum =>
          simp [third, fourth] at run
          obtain ⟨sourceEq, closureEq, configEq, outputEq, namesEq⟩ := run
          subst resultSource
          subst resultClosure
          subst resultConfig
          subst names
          refine ⟨bviCode, lowered, fixed, bignum, ?_⟩
          simp_all

end Flapjack.Compiler.Backend.SourceToFlat
