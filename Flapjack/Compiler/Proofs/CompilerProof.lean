module

public import Flapjack.Compiler.Inference.InferProps
public import Flapjack.Compiler.Repl.ReplTypes

@[expose] public section

/-! Prerequisites for CakeML's top-level compiler correctness theorem. -/
namespace Flapjack.Compiler.Proofs.CompilerProof
open Flapjack.NamespaceHOL Flapjack.Compiler.Inference.InferProps
  Flapjack.Compiler.Inference.Infer Flapjack.PrimTypesHOL Flapjack.TypeSystemHOL

/-- Inference-side well-formedness needed to establish the initial environment
relation. This supports `type_config_ok`; it is not a separate HOL theorem. -/
theorem primitiveInferenceWellFormed : ienvOk (fun _ => False) initConfig := by
  have declarative := Flapjack.Compiler.Repl.ReplTypes.tenvOkPrimTenv
  refine ⟨?_, declarative.2.1, declarative.2.2⟩
  intro id v h
  cases id <;> simp [initConfig, nsEmpty, nsLookup] at h

/-- The identifier-set conjunct needed for `type_config_ok`. This is a
supporting fact, not a separate HOL theorem or the complete conjunction. -/
theorem primitiveInferenceIds : infSetTidsIenv primTypeIds initConfig := by
  unfold infSetTidsIenv initConfig
  simp only [nsAll, primTenv, alistToNs, nsEmpty]
  constructor
  · intro id v h
    cases id with
    | long m id => simp [nsLookup] at h
    | short name =>
      simp only [nsLookup, List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append] at h
      simp only [List.lookup] at h
      repeat' (split at h <;> simp_all)
      all_goals subst v
      all_goals simp_all [infSetTidsSubset, unconvertT, unconvertTList, infSetTids,
        infSetTidsList, primTypeIds, primTypeNums, TarrayNum, TcharNum, TexnNum,
        TfnNum, TintNum, TrefNum, TstringNum, TtupNum, TvectorNum, Tword64Num,
        Tword8Num, Tword8arrayNum, TdoubleNum]
  · constructor
    · intro id v h
      cases id with
      | long m id => simp [nsLookup] at h
      | short name =>
        simp only [nsLookup, List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append] at h
        simp only [List.lookup] at h
        repeat' (split at h <;> simp_all)
        all_goals subst v
        all_goals simp_all [infSetTidsSubset, unconvertT, unconvertTList, infSetTids,
          infSetTidsList, primTypeIds, primTypeNums, TarrayNum, TcharNum, TexnNum,
          TfnNum, TintNum, TrefNum, TstringNum, TtupNum, TvectorNum, Tword64Num,
          Tword8Num, Tword8arrayNum, TdoubleNum]
    · intro id v h
      cases id <;> simp [nsLookup] at h

end Flapjack.Compiler.Proofs.CompilerProof
