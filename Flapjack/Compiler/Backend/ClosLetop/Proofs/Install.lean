import Flapjack.Compiler.Backend.ClosLetop.Proofs.Primitive
import Flapjack.Compiler.Backend.Semantics.ClosProps.DecodeRelations
import Flapjack.Compiler.Backend.Semantics.ClosSem.Install
import Flapjack.Misc.ShiftSeq

/-! Dynamic-installation prerequisites for let-operation cleanup. -/
namespace Flapjack.Compiler.Backend.ClosLetop
open Flapjack.Compiler.Backend.ClosSem Flapjack.Compiler.Backend.ClosProps
open Flapjack.Compiler.Backend.BackendProps

/-- Let-operation-related values decode to the same byte sequence. -/
@[hol "cakeml/compiler/backend/proofs/clos_letopProofScript.sml" "v_rel_IMP_v_to_bytes"]
theorem valueRel_bytes (x y : Value) (related : ValueRel x y) : valueToBytes y = valueToBytes x :=
  (simpleValRel_valueToBytes ValueRel x y ⟨valueRelSimple, related⟩).symm

/-- Let-operation-related values decode to the same word sequence. -/
@[hol "cakeml/compiler/backend/proofs/clos_letopProofScript.sml" "v_rel_IMP_v_to_words"]
theorem valueRel_words (x y : Value) (related : ValueRel x y) : valueToWords y = valueToWords x :=
  (simpleValRel_valueToWords x y ValueRel ⟨valueRelSimple, related⟩).symm

/-- Shifting related compiler oracles equally and setting equal clocks
preserves the let-operation state relation. This is Flapjack infrastructure
for the installation proof. -/
theorem stateRel_shift {C F : Type} (s t : State C F) (shift clock : Nat) (related : StateRel s t) :
    StateRel { s with clock := clock, compileOracle := Flapjack.holShiftSeq shift s.compileOracle }
      { t with clock := clock, compileOracle := Flapjack.holShiftSeq shift t.compileOracle } := by
  obtain ⟨aux, codeS, codeT, maxApp, positive, _, ffi, globals, refs, compiler, oracle⟩ := related
  refine ⟨?_, codeS, codeT, maxApp, positive, rfl, ffi, globals, refs, compiler, ?_⟩
  · intro n; exact aux (n + shift)
  · rw [oracle]
    funext n
    rfl

/-- Let-operation cleanup preserves whether an installed program is empty. This is
Flapjack infrastructure for the installation proof. -/
theorem compile_nonempty (program : List ClosLang.Exp) : compileList program ≠ [] ↔ program ≠ [] := by
  constructor
  · intro nonempty empty
    subst program
    exact nonempty rfl
  · intro nonempty empty
    have lengths : (compileList program).length = program.length := by simp [compileList_eq_map]
    rw [empty] at lengths
    exact nonempty (List.eq_nil_of_length_eq_zero lengths.symm)

/-- Corresponding oracle entries share their compiler configuration and
transform the program while leaving the auxiliary component empty. This is
Flapjack infrastructure for the installation proof. -/
theorem oracle_entry {C F : Type} (s t : State C F) (related : StateRel s t) (n : Nat) :
    ∃ config program, s.compileOracle n = (config, program, []) ∧
      t.compileOracle n = (config, compileList program, []) := by
  have aux := related.1 n
  have oracle := related.2.2.2.2.2.2.2.2.2.2
  cases entry : s.compileOracle n with
  | mk config rest =>
    rcases rest with ⟨program, auxiliary⟩
    have empty : auxiliary = [] := by simpa [entry] using aux
    subst auxiliary
    refine ⟨config, program, rfl, ?_⟩
    rw [oracle]
    simp [pureCo, compileInc, entry]

/-- Related compiler callbacks receive the same transformed program. This is
Flapjack infrastructure for the installation proof. -/
theorem compiler_callback {C F : Type} (s t : State C F) (related : StateRel s t)
    (config : C) (program : List ClosLang.Exp) :
    s.compile config (program, []) = t.compile config (compileList program, []) := by
  rw [related.2.2.2.2.2.2.2.2.2.1]
  rfl

/-- Corresponding shifted oracles have the same compiler configuration. This
is Flapjack infrastructure for the installation proof. -/
theorem shifted_config {C F : Type} (s t : State C F) (related : StateRel s t) :
    (Flapjack.holShiftSeq 1 s.compileOracle 0).1 =
      (Flapjack.holShiftSeq 1 t.compileOracle 0).1 := by
  obtain ⟨config, program, left, right⟩ := oracle_entry s t related 1
  simp [Flapjack.holShiftSeq, left, right]

/-- Installation outcomes preserve exceptions or relate nonempty programs,
along with their resulting states. This is Flapjack infrastructure for the
installation proof. -/
def InstallRel {C F : Type} :
    (Flapjack.SemanticPrimitivesHOL.Result (List ClosLang.Exp) Value × State C F) →
    (Flapjack.SemanticPrimitivesHOL.Result (List ClosLang.Exp) Value × State C F) → Prop
  | (.err e, s), (.err f, t) => Flapjack.SemanticPrimitivesProps.excRel ValueRel e f ∧ StateRel s t
  | (.val xs, s), (.val ys, t) => xs ≠ [] ∧ CodeRel xs ys ∧ StateRel s t
  | _, _ => False

/-- A pair of related installation payloads yields related installation
outcomes, including invalid payloads and the clock-zero timeout update. This
is Flapjack infrastructure for the installation proof. -/
theorem install_pair_related {C F : Type} (s t : State C F)
    (a b x y : Value) (states : StateRel s t) (bytesRel : ValueRel a x) (wordsRel : ValueRel b y) :
    InstallRel (doInstall [a, b] s) (doInstall [x, y] t) := by
  classical
  have bytesEq := valueRel_bytes a x bytesRel
  have wordsEq := valueRel_words b y wordsRel
  have clocks : t.clock = s.clock := states.2.2.2.2.2.1
  have shifted := stateRel_shift s t 1 (s.clock - 1) states
  have sourceNoUpdate : s.code.updateListEq ([] : List (Nat × Nat × ClosLang.Exp)) = s.code := by
    simp [HolFiniteMapExact.updateListEq]
  have targetNoUpdate : t.code.updateListEq ([] : List (Nat × Nat × ClosLang.Exp)) = t.code := by
    simp [HolFiniteMapExact.updateListEq]
  obtain ⟨config, program, sourceOracle, targetOracle⟩ := oracle_entry s t states 0
  have callback := compiler_callback s t states config program
  have configs := shifted_config s t states
  cases bytesRun : valueToBytes a with
  | none =>
    have targetBytes : valueToBytes x = none := bytesEq.trans bytesRun
    simp [doInstall, bytesRun, targetBytes, InstallRel, Flapjack.SemanticPrimitivesProps.excRel, states]
  | some bytes =>
    have targetBytes : valueToBytes x = some bytes := bytesEq.trans bytesRun
    cases wordsRun : valueToWords b with
    | none =>
      have targetWords : valueToWords y = none := wordsEq.trans wordsRun
      simp [doInstall, bytesRun, targetBytes, wordsRun, targetWords, InstallRel,
        Flapjack.SemanticPrimitivesProps.excRel, states]
    | some words =>
      have targetWords : valueToWords y = some words := wordsEq.trans wordsRun
      cases compiled : t.compile config (compileList program, []) with
      | none =>
        have sourceCompiled : s.compile config (program, []) = none := callback.trans compiled
        simp [doInstall, bytesRun, targetBytes, wordsRun, targetWords, sourceOracle, targetOracle,
          sourceCompiled, compiled, InstallRel, Flapjack.SemanticPrimitivesProps.excRel, states]
      | some output =>
        rcases output with ⟨compiledBytes, compiledWords, nextConfig⟩
        have sourceCompiled : s.compile config (program, []) = some (compiledBytes, compiledWords, nextConfig) :=
          callback.trans compiled
        by_cases checks : bytes = compiledBytes ∧ words = compiledWords ∧
            (Flapjack.holShiftSeq 1 s.compileOracle 0).1 = nextConfig ∧ program ≠ []
        · have targetChecks : bytes = compiledBytes ∧ words = compiledWords ∧
              (Flapjack.holShiftSeq 1 t.compileOracle 0).1 = nextConfig ∧ compileList program ≠ [] := by
            simpa [← configs, compile_nonempty] using checks
          by_cases zero : s.clock = 0
          · simp [doInstall, bytesRun, targetBytes, wordsRun, targetWords, sourceOracle, targetOracle,
              sourceCompiled, compiled, checks, targetChecks, zero, clocks, InstallRel,
              Flapjack.SemanticPrimitivesProps.excRel, sourceNoUpdate, targetNoUpdate]
            simpa [zero] using shifted
          · simp [doInstall, bytesRun, targetBytes, wordsRun, targetWords, sourceOracle, targetOracle,
              sourceCompiled, compiled, checks, targetChecks, zero, clocks, InstallRel,
              CodeRel, sourceNoUpdate, targetNoUpdate, shifted]
        · have targetChecks : ¬ (bytes = compiledBytes ∧ words = compiledWords ∧
              (Flapjack.holShiftSeq 1 t.compileOracle 0).1 = nextConfig ∧ compileList program ≠ []) := by
            simpa [← configs, compile_nonempty] using checks
          simp [doInstall, bytesRun, targetBytes, wordsRun, targetWords, sourceOracle, targetOracle,
            sourceCompiled, compiled, checks, targetChecks, InstallRel,
            Flapjack.SemanticPrimitivesProps.excRel, states]

/-- All related installation payload lists yield related outcomes. This is
Flapjack infrastructure for the installation proof. -/
theorem install_related {C F : Type} (s t : State C F) (xs ys : List Value)
    (states : StateRel s t) (values : List.Forall₂ ValueRel xs ys) :
    InstallRel (doInstall xs s) (doInstall ys t) := by
  by_cases arity : xs.length = 2
  · cases values with
    | nil => simp at arity
    | @cons a x rest nextRest first tail =>
      cases tail with
      | nil => simp at arity
      | @cons b y rest nextRest second tail =>
        cases tail with
        | nil => exact install_pair_related s t a b x y states first second
        | cons third tail => simp at arity
  · have targetArity : ys.length ≠ 2 := by simpa [← values.length_eq] using arity
    rw [doInstall_wrongArity xs s arity, doInstall_wrongArity ys t targetArity]
    exact ⟨rfl, states⟩

namespace InstallPort
/-- The closure state uses canonical finite-map fields. -/
theorem holFmapAsFiniteSupportWitness {C F : Type} :
    (∀ s : StateBroad C F, (State.ofBroad s).toBroad = s) ∧
      (∀ s : State C F, State.ofBroad s.toBroad = s) :=
  ClosSem.holFmapAsFiniteSupportWitness

/-- Installation preserves the let-operation state relation and produces
related programs or related exceptions. -/
@[hol "cakeml/compiler/backend/proofs/clos_letopProofScript.sml" "do_install_lemma"
  (fmap_as_finite_support := [refs, code])]
theorem doInstallLemma {C F : Type} (s t : State C F) (xs ys : List Value)
    (related : StateRel s t ∧ List.Forall₂ ValueRel xs ys) :
    match doInstall xs s with
    | (.err err1, s1) => ∃ err2 t1, doInstall ys t = (.err err2, t1) ∧
        Flapjack.SemanticPrimitivesProps.excRel ValueRel err1 err2 ∧ StateRel s1 t1
    | (.val exps1, s1) => ∃ exps2 t1, StateRel s1 t1 ∧ exps1 ≠ [] ∧ CodeRel exps1 exps2 ∧
        doInstall ys t = (.val exps2, t1) := by
  have both := install_related s t xs ys related.1 related.2
  cases sourceRun : doInstall xs s with
  | mk sourceResult sourceNext =>
    cases targetRun : doInstall ys t with
    | mk targetResult targetNext =>
      rw [sourceRun, targetRun] at both
      cases sourceResult with
      | err error =>
        cases targetResult with
        | val values => simp [InstallRel] at both
        | err targetError =>
          exact ⟨targetError, targetNext, rfl, both.1, both.2⟩
      | val program =>
        cases targetResult with
        | err error => simp [InstallRel] at both
        | val targetProgram =>
          exact ⟨targetProgram, targetNext, both.2.2, both.1, both.2.1, rfl⟩
end InstallPort

end Flapjack.Compiler.Backend.ClosLetop
