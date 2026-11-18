module

public import Flapjack.Compiler.Backend.DataToWord.Proofs.Correct.Move
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation.SmallNumber

@[expose] public section

/-! State preservation for the constant-assignment proof. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Assign
open Flapjack Flapjack.Compiler.Backend.DataToWord.Proofs
open Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
open Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
open Flapjack.Compiler.Backend.BackendProps

/-- Data stack accounting preserves the relation to an unchanged word state.
This is an intermediate step of the HOL assignment proof, with no standalone
HOL declaration. -/
theorem stateRel_doStack {width : Nat} [NeZero width] {C F : Type}
    (conf : Config) (l1 l2 : Nat) (source : DataSem.State C F)
    (target : WordSemStateFiniteExact width C F) (locs : List (Nat × Nat))
    (op : ClosLang.Op) (values : List DataSem.Value)
    (related : stateRel conf l1 l2 source target none locs) :
    stateRel conf l1 l2 (DataSem.doStack op values source) target none locs := by
  rcases related with ⟨hffi, hclock, hhandler, hgc, hcode, horacle, hgood, hshift,
    htstamp, hglobal, hzero, hpresent, hstack, hlocs, hacc, hmax, hsizes, hlocals, hlim, hmem⟩
  refine ⟨hffi, hclock, hhandler, hgc, hcode, horacle, hgood, hshift, htstamp, hglobal,
    hzero, hpresent, hstack, hlocs, hacc, ?_, hsizes, hlocals, hlim, hmem⟩
  exact (optionLe_max_right _ _ _).mpr (Or.inl hmax)

/-- Updating data-space safety alone preserves the relation. This is an
intermediate step of HOL's assignment proof, not a separate HOL theorem. -/
theorem stateRel_doLimSafe {width : Nat} [NeZero width] {C F : Type}
    (conf : Config) (l1 l2 : Nat) (source : DataSem.State C F)
    (target : WordSemStateFiniteExact width C F) (locs : List (Nat × Nat))
    (op : ClosLang.Op) (values : List DataSem.Value)
    (related : stateRel conf l1 l2 source target none locs) :
    stateRel conf l1 l2 (DataSem.doLimSafe source op values) target none locs := by
  exact related

/-- Updating corresponding locals with a compiler-sized integer preserves
the complete state relation. This factors the state update in HOL's
constant-assignment proof; it has no standalone HOL declaration. -/
theorem stateRel_setConst {width : Nat} [NeZero width] {C F : Type}
    (conf : Config) (l1 l2 : Nat) (source : DataSem.State C F)
    (target : WordSemStateFiniteExact width C F) (locs : List (Nat × Nat))
    (dest : Nat) (i : Int)
    (related : stateRel conf l1 l2 source target none locs)
    (small : BackendCommon.smallEnoughInt i) :
    stateRel conf l1 l2 (DataSem.setVar dest (.number i) source)
      (WordSemStateFiniteExact.setVar (adjustVar dest) (.word (smallnum i)) target) none locs := by
  apply stateRel_insertRoot conf l1 l2 source target locs dest (.number i) (.word (smallnum i)) related
  rcases related with ⟨_, _, _, _, _, _, good, _, _, _, _, _, _, _, _, _, _, _, _, hmem⟩
  have smallWord : smallInt width i := by
    rcases good with h | h <;> subst width <;>
      simp [smallInt, BackendCommon.smallEnoughInt] at small ⊢ <;> omega
  exact impMemoryRel_number conf target.be (holThe source.tstamps) source.refs source.space
    target.store target.memory target.mdomain _ i ⟨good, smallWord, hmem⟩

/-- The source constant operation preserves the state relation after its
successful result is assigned. This factors the corresponding reasoning in
HOL's constant-assignment case and is not a standalone HOL theorem. -/
theorem stateRel_afterConst {width : Nat} [NeZero width] {C F : Type}
    (conf : Config) (l1 l2 : Nat) (source resultState : DataSem.State C F)
    (target : WordSemStateFiniteExact width C F) (locs : List (Nat × Nat))
    (dest : Nat) (i : Int) (values : List DataSem.Value) (result : DataSem.Value)
    (related : stateRel conf l1 l2 source target none locs)
    (run : DataSem.doApp (.intOp (.const i)) values source = .val (result, resultState)) :
    stateRel conf l1 l2 (DataSem.setVar dest result resultState)
      (WordSemStateFiniteExact.setVar (adjustVar dest) (.word (smallnum i)) target) none locs := by
  cases values with
  | nil =>
    by_cases small : BackendCommon.smallEnoughInt i
    · simp [DataSem.doApp, DataSem.doSpace, DataLang.opSpaceReset, DataSpace.opSpaceReq,
        DataSem.doAppAux, DataSem.applyNonFfi, DataSem.doIntApp, small] at run
      obtain ⟨rfl, rfl⟩ := run
      apply stateRel_setConst conf l1 l2 _ target locs dest i
      · exact stateRel_doStack conf l1 l2 _ target locs _ _
          (stateRel_doLimSafe conf l1 l2 source target locs _ _ related)
      · exact small
    · simp [DataSem.doApp, DataSem.doSpace, DataLang.opSpaceReset, DataSpace.opSpaceReq,
        DataSem.doAppAux, DataSem.applyNonFfi, DataSem.doIntApp, small] at run
  | cons head tail =>
    simp [DataSem.doApp, DataSem.doSpace, DataLang.opSpaceReset, DataSpace.opSpaceReq,
      DataSem.doAppAux, DataSem.applyNonFfi, DataSem.doIntApp] at run

/-- The constant-assignment case of the source assignment simulation. The
compiler is expressed through the executed control traversal; its correspondence
to HOL's assignment compiler and the state relation still require review before
this result can carry a HOL reference. -/
theorem assignConst_correct {width : Nat} [NeZero width] {C F : Type}
    (conf : Config) (n l l1 l2 dest : Nat) (op : ClosLang.Op)
    (args : List Nat) (names : Option NumSet) (source cut resultState : DataSem.State C F)
    (target : WordSemStateFiniteExact width C F) (locs : List (Nat × Nat))
    (values : List DataSem.Value) (result : DataSem.Value)
    (constant : ∃ i, op = .intOp (.const i))
    (related : stateRel conf l1 l2 source target none locs)
    (validNames : DataLang.opRequiresNames op ≠ names.isNone)
    (cutEq : DataSem.cutStateOpt names source = some cut)
    (_argsEq : DataSem.getVars args source.locals = some values)
    (_depth : target.termdep > 1)
    (run : DataSem.doApp op values cut = .val (result, resultState)) :
    ∃ q r,
      WordSemStateFiniteExact.evaluate (compileControl conf n l (.assign dest op args names)).1 target = (q, r) ∧
      (q = some .notEnoughSpace → r.ffi = target.ffi ∧ optionLe r.stackMax resultState.stackMax ∧
        (conf.gcKind ≠ .none → resultState.safeForSpace = false)) ∧
      (q ≠ some .notEnoughSpace →
        stateRel conf l1 l2 (DataSem.setVar dest result resultState) r none locs ∧ q = none) := by
  obtain ⟨i, rfl⟩ := constant
  cases names with
  | some names => simp [DataLang.opRequiresNames, DataLang.opSpaceReset] at validNames
  | none =>
    have cutIsSource : cut = source := by simpa [DataSem.cutStateOpt] using cutEq.symm
    subst cut
    have updated := stateRel_afterConst conf l1 l2 source resultState target locs dest i values result related run
    have compiled : compileControl (width := width) conf n l (.assign dest (.intOp (.const i)) args none) =
        (.assign (adjustVar dest) (.const (smallnum i)), l) := by
      have h := compileControl_option (width := width) conf n l (.assign dest (.intOp (.const i)) args none)
      by_cases neg : i < 0 <;> simpa [compileControl?, assignConst, smallnum, neg] using h.symm
    refine ⟨none, WordSemStateFiniteExact.setVar (adjustVar dest) (.word (smallnum i)) target, ?_, ?_, ?_⟩
    · simp [compiled, WordSemStateFiniteExact.evaluate, WordSemStateFiniteExact.wordExp]
    · simp
    · simp [updated]

end Flapjack.Compiler.Backend.DataToWord.Proofs.Assign
