module

public import Flapjack.Compiler.Backend.ClosLetop.Proofs.Primitive
public import Flapjack.Compiler.Backend.Semantics.ClosProps.DecodeRelations
public import Flapjack.Compiler.Backend.Semantics.ClosSem.Install
public import Flapjack.Compiler.Backend.Semantics.ClosProps.InstallStep
public import Flapjack.Misc.ShiftSeq

@[expose] public section

/-! Dynamic-installation prerequisites for let-operation cleanup. -/
namespace Flapjack.Compiler.Backend.ClosLetop
open Flapjack.Compiler.Backend.ClosSem Flapjack.Compiler.Backend.ClosProps
open Flapjack.Compiler.Backend.BackendProps

/-- Let-operation-related values decode to the same byte sequence. -/
@[hol "cakeml/compiler/backend/proofs/clos_letopProofScript.sml" "v_rel_IMP_v_to_bytes"]
theorem valueRel_bytes (x y : Value) (related : ValueRel x y) : valueToBytes y = valueToBytes x :=
  (simpleValRel_valueToBytes ValueRel x y ⟨valueRelSimple, related⟩).symm

/-- Related values agree on whether they encode any given byte list. -/
@[hol "cakeml/compiler/backend/proofs/clos_letopProofScript.sml" "v_rel_IMP_v_to_bytes_lemma"]
theorem valueRel_bytes_list (x y : Value) (related : ValueRel x y) (bytes : List (BitVec 8)) :
    (valueToList x = some (bytes.map (fun b => Value.number b.toNat))) ↔
      (valueToList y = some (bytes.map (fun b => Value.number b.toNat))) := by
  rw [← valueToBytes_eq_some, ← valueToBytes_eq_some, valueRel_bytes x y related]

/-- Let-operation-related values decode to the same word sequence. -/
@[hol "cakeml/compiler/backend/proofs/clos_letopProofScript.sml" "v_rel_IMP_v_to_words"]
theorem valueRel_words (x y : Value) (related : ValueRel x y) : valueToWords y = valueToWords x :=
  (simpleValRel_valueToWords x y ValueRel ⟨valueRelSimple, related⟩).symm

/-- Related values agree on whether they encode any given word list. -/
@[hol "cakeml/compiler/backend/proofs/clos_letopProofScript.sml" "v_rel_IMP_v_to_words_lemma"]
theorem valueRel_words_list (x y : Value) (related : ValueRel x y) (words : List (BitVec 64)) :
    (valueToList x = some (words.map Value.word64)) ↔
      (valueToList y = some (words.map Value.word64)) := by
  rw [← valueToWords_eq_some, ← valueToWords_eq_some, valueRel_words x y related]

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
  rw [related.2.2.2.2.2.2.2.2.2.1, compileIncSource_eq]
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
  have clocks : t.clock = s.clock := (state_rel_clocks_eqs s t states).symm
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
            simpa [← configs, compileList_eq_map] using checks
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
            simpa [← configs, compileList_eq_map] using checks
          simp [doInstall, bytesRun, targetBytes, wordsRun, targetWords, sourceOracle, targetOracle,
            sourceCompiled, compiled, checks, targetChecks, InstallRel,
            Flapjack.SemanticPrimitivesProps.excRel, states]

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
        doInstall ys t = (.val exps2, t1) :=
  ClosProps.doInstallLemmaOf (CodeRel := CodeRel) (InstallRel := InstallRel)
    (by
      intro r1 r2 u v
      cases r1 <;> cases r2 <;> simp [InstallRel])
    s t xs ys (ClosProps.install_related install_pair_related
      (fun s t st => ⟨rfl, st⟩) s t xs ys related.1 related.2)
end InstallPort

end Flapjack.Compiler.Backend.ClosLetop
