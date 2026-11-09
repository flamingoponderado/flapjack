module

public import Flapjack.Compiler.Backend.BviToData.Proofs.Value
public import Flapjack.Compiler.Backend.Semantics.DataSem.Word
public import Flapjack.Compiler.Backend.Semantics.BvlSem.Word
public import Mathlib.Tactic.CasesM

@[expose] public section

/-! Word operations under the BVI-to-data value projection. -/
namespace Flapjack.Compiler.Backend.BviToData
set_option linter.unusedSimpArgs false

private theorem intCmp_lt_leq (a b : Int) :
    Flapjack.SemanticPrimitivesHOL.intCmp .lt a b = decide (a < b) ∧
    Flapjack.SemanticPrimitivesHOL.intCmp .leq a b = decide (a ≤ b) := by
  cases h : compare a b with
  | lt =>
    have hab : a < b := Int.compare_eq_lt.mp h
    simp only [Flapjack.SemanticPrimitivesHOL.intCmp, h]
    change true = decide (a < b) ∧ true = decide (a ≤ b)
    simp [hab, show a ≤ b by omega]
  | eq =>
    have hab : a = b := Int.compare_eq_eq.mp h
    subst b
    simp only [Flapjack.SemanticPrimitivesHOL.intCmp, h]
    change false = decide (a < a) ∧ true = decide (a ≤ a)
    simp
  | gt =>
    have hab : b < a := Int.compare_eq_gt.mp h
    simp only [Flapjack.SemanticPrimitivesHOL.intCmp, h]
    change false = decide (a < b) ∧ false = decide (a ≤ b)
    simp [show ¬a < b by omega, show ¬a ≤ b by omega]

/-- Successful data-language word operations agree after timestamps are erased.
The converse is not true without restrictions: BVI accepts some byte
comparisons that data rejects. This is Flapjack proof infrastructure, not the
original pass-correctness result, which also relates the complete primitive
dispatchers and their states. -/
theorem doWordApp_projection (op : ClosLang.WordOp) (args : List DataSem.Value)
    (result : DataSem.Value) (run : DataSem.doWordApp op args = some result) :
    BvlSem.doWordApp op (args.map dataToBviValue) = some (dataToBviValue result) := by
  cases args with
  | nil =>
    cases op <;> simp_all [DataSem.doWordApp, DataSem.doWordAppIntegral]
  | cons a rest =>
    cases rest with
    | nil =>
      cases a <;> cases op
      all_goals try (cases_type AstHOL.WordSize)
      all_goals try (cases_type AstHOL.Test)
      all_goals try (cases_type Flapjack.Opb)
      all_goals try (cases_type Bool)
      all_goals simp_all [DataSem.doWordApp, BvlSem.doWordApp, DataSem.doWordAppIntegral,
        BvlSem.doWordAppIntegral, dataToBviValue, DataSem.boolValue, BvlSem.boolValue]
      all_goals try (simp only [Option.bind] at run ⊢)
      all_goals try (split at run <;> simp_all [dataToBviValue])
      all_goals try (subst result; simp [dataToBviValue])
    | cons b rest =>
      cases rest with
      | nil =>
        cases a <;> cases b <;> cases op
        all_goals try (cases_type AstHOL.WordSize)
        all_goals try (cases_type AstHOL.Test)
        all_goals try (cases_type Flapjack.Opb)
        all_goals try (cases_type Bool)
        all_goals simp_all [DataSem.doWordApp, BvlSem.doWordApp, DataSem.doWordAppIntegral,
          BvlSem.doWordAppIntegral, dataToBviValue, DataSem.boolValue, BvlSem.boolValue]
        all_goals try (simp only [Option.bind] at run ⊢)
        all_goals try (split at run <;> simp_all [dataToBviValue])
        all_goals try (split at run <;> simp_all [dataToBviValue])
        all_goals try (subst result; simp [dataToBviValue])
        all_goals try (rcases run with ⟨_, rfl⟩; simp [dataToBviValue, (intCmp_lt_leq _ _).1, (intCmp_lt_leq _ _).2])
      | cons c rest =>
        cases rest with
        | nil =>
          cases op <;> simp_all [DataSem.doWordApp, DataSem.doWordAppIntegral]
          all_goals cases a <;> cases b <;> cases c <;>
            simp_all [DataSem.doWordApp, BvlSem.doWordApp, DataSem.doWordAppIntegral,
              BvlSem.doWordAppIntegral, dataToBviValue, DataSem.boolValue, BvlSem.boolValue]
          all_goals try (subst result; simp [dataToBviValue])
        | cons d rest =>
          cases op <;> simp_all [DataSem.doWordApp, DataSem.doWordAppIntegral]


/-- If the BVI operation succeeds on projected inputs, its data-language
counterpart succeeds and projects to the same result, except for the two
byte-comparison operations excluded by the source pass proof. -/
theorem doWordApp_bvi_success (op : ClosLang.WordOp) (args : List DataSem.Value)
    (result : BvlSem.Value)
    (notGt : op ≠ .wordTest .w8 (.compare .gt))
    (notGeq : op ≠ .wordTest .w8 (.compare .geq))
    (run : BvlSem.doWordApp op (args.map dataToBviValue) = some result) :
    ∃ dataResult, DataSem.doWordApp op args = some dataResult ∧ dataToBviValue dataResult = result := by
  cases args with
  | nil =>
    cases op <;> simp_all [BvlSem.doWordApp, BvlSem.doWordAppIntegral]
  | cons a rest =>
    cases rest with
    | nil =>
      cases a <;> cases op
      all_goals try (cases_type AstHOL.WordSize)
      all_goals try (cases_type AstHOL.Test)
      all_goals try (cases_type Flapjack.Opb)
      all_goals try (cases_type Bool)
      all_goals simp_all [DataSem.doWordApp, BvlSem.doWordApp, DataSem.doWordAppIntegral,
        BvlSem.doWordAppIntegral, dataToBviValue, DataSem.boolValue, BvlSem.boolValue]
      all_goals try (simp only [Option.bind] at run ⊢)
      all_goals try (split at run <;> simp_all [dataToBviValue])
    | cons b rest =>
      cases rest with
      | nil =>
        cases a <;> cases b <;> cases op
        all_goals try (cases_type AstHOL.WordSize)
        all_goals try (cases_type AstHOL.Test)
        all_goals try (cases_type Flapjack.Opb)
        all_goals try (cases_type Bool)
        all_goals simp_all [DataSem.doWordApp, BvlSem.doWordApp, DataSem.doWordAppIntegral,
          BvlSem.doWordAppIntegral, dataToBviValue, DataSem.boolValue, BvlSem.boolValue,
          (intCmp_lt_leq _ _).1, (intCmp_lt_leq _ _).2]
        all_goals try (simp only [Option.bind] at run ⊢)
        all_goals try (split at run <;> simp_all [dataToBviValue])
        all_goals try (split at run <;> simp_all [dataToBviValue])
      | cons c rest =>
        cases rest with
        | nil =>
          cases op <;> simp_all [BvlSem.doWordApp, BvlSem.doWordAppIntegral]
          all_goals cases a <;> cases b <;> cases c <;>
            simp_all [DataSem.doWordApp, BvlSem.doWordApp, DataSem.doWordAppIntegral,
              BvlSem.doWordAppIntegral, dataToBviValue, DataSem.boolValue, BvlSem.boolValue]
        | cons d rest =>
          cases op <;> simp_all [BvlSem.doWordApp, BvlSem.doWordAppIntegral]


end Flapjack.Compiler.Backend.BviToData
