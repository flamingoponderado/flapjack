module

public import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.StateRelation
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.MkLoc
public import Flapjack.Compiler.Backend.Semantics.DataSem.Evaluate
public import Flapjack.Compiler.Backend.Semantics.WordSem.Evaluate
public import Flapjack.Compiler.Backend.Semantics.WordSem.Env

public import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.MemoryRelation
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation.Rearrange

@[expose] public section

/-! The `Return` case of the data-to-word evaluator simulation. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
open Flapjack Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
/-- Derive the post-return relation from the source reads in the HOL Return case. -/
private theorem returnStateRel {width : Nat} [NeZero width] {C F : Type}
    (c : Config) (l1 l2 : Nat) (s : Flapjack.Compiler.Backend.DataSem.State C F)
    (t : WordSemStateFiniteExact width C F) (locs : List (Nat × Nat))
    (ns : List Nat) (values : List Flapjack.Compiler.Backend.DataSem.Value) (words : List (WordLocW width))
    (rel : stateRel c l1 l2 s t none locs)
    (sourceRead : DataSem.getVars ns s.locals = some values)
    (targetRead : WordSemStateFiniteExact.getVars (ns.map adjustVar) t = some words) :
    stateRel c l1 l2 (DataSem.flushState false s) (WordSemStateFiniteExact.flushState false t)
      (some (values.zip words)) locs := by
  rcases rel with ⟨hffi, hclock, hhandler, hgc, hcode, horacle, hgood, hshift,
    htstamp, hglobal, hzero, hpresent, hstack, hlocs, hacc, hmax, hsizes, hlocals, hlim, hmem⟩
  have memory := memoryRel_getVars c t.be (holThe s.tstamps) s s.space t.store t.memory t.mdomain t
    ([(theGlobal s.global, holFapply t.store .globals)] ++ flatStack s.stack t.stack)
    ns values words ⟨by simpa [List.append_assoc] using hmem, sourceRead, targetRead⟩
  have newMemory : memoryRel c t.be (holThe s.tstamps) s.refs s.space t.store t.memory t.mdomain
      (values.zip words ++ [(theGlobal s.global, holFapply t.store .globals)] ++ flatStack s.stack t.stack) := by
    apply memoryRel_rearrange c t.be (holThe s.tstamps) s.refs s.space t.store t.memory t.mdomain _ _ ?_ memory
    intro pair member
    simp only [List.mem_append] at member ⊢
    tauto
  have newBound : BackendProps.optionLe
      (Option.map₂ (fun x y => x + y) (wordSemStackSize t.stack) (some 0)) t.stackMax := by
    cases hsize : wordSemStackSize t.stack <;> cases hlocal : t.localsSize <;> cases hmax' : t.stackMax
    all_goals simp [hsize, hlocal, hmax', BackendProps.optionLe] at hacc ⊢
    all_goals omega
  simp only [stateRel, DataSem.flushState, Bool.false_eq_true, ↓reduceIte,
    WordSemStateFiniteExact.flushState]
  refine ⟨hffi, hclock, hhandler, hgc, hcode, horacle, hgood, hshift, htstamp,
    hglobal, ?_, ?_, hstack, hlocs, newBound, hmax, hsizes, trivial, hlim, ?_⟩
  · simp
  · simp [sptLookup]
  · simpa [sptInter, sptToAList, sptFoldi, joinEnv_nil, List.append_assoc] using newMemory
end Flapjack.Compiler.Backend.DataToWord.Proofs.Gc


namespace Flapjack.Compiler.Backend.DataToWord.Proofs
open Flapjack Flapjack.SemanticPrimitivesHOL
open Flapjack.Compiler.Backend.BackendProps
open Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
namespace reviewedDataCompileCorrect_returnMap
/-- Canonical roundtrip for the target state used by this HOL port. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : WordSemStateBroad width C F) (h : state.FiniteSupport),
      (WordSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : WordSemStateFiniteExact width C F,
      WordSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  WordSemStateExact.holFmapAsFiniteSupportWitness
end reviewedDataCompileCorrect_returnMap

/-- The `Return` case retains the complete conclusion of `data_compile_correct`.
The word evaluator inherits the real-model assumption documented in
`docs/SOUNDNESS.md` item 8. The full theorem still requires assembly of all cases. -/
@[hol "cakeml/compiler/backend/proofs/data_to_wordProofScript.sml" "data_compile_correct"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem dataCompileCorrect_return {width : Nat} [NeZero width] {C F : Type}
    (source : Flapjack.Compiler.Backend.DataSem.State C F) (conf : Flapjack.Compiler.Backend.DataToWord.Config) (n l l1 l2 : Nat)
    (res : Option (Result (List Flapjack.Compiler.Backend.DataSem.Value) Flapjack.Compiler.Backend.DataSem.Value)) (source1 : Flapjack.Compiler.Backend.DataSem.State C F)
    (target : WordSemStateFiniteExact width C F) (locs : List (Nat × Nat))
    (names : List Nat)
    (run : DataSem.evaluate (.return names) source = (res, source1))
    (notTypeError : res ≠ some (.err (.abort .typeError)))
    (related : stateRel conf l1 l2 source target none locs)
    (_depth : target.termdep > 1) :
    ∃ target1 res1,
      WordSemStateFiniteExact.evaluate (compileControl conf n l (.return names)).1 target = (res1, target1) ∧
      optionLe target1.stackMax source1.stackMax ∧
      (res1 = some .notEnoughSpace →
        target1.ffi.ioEvents.IsPrefix source1.ffi.ioEvents ∧
        (conf.gcKind ≠ .none → source1.safeForSpace = false)) ∧
      (res1 ≠ some .notEnoughSpace →
        match res with
        | none => stateRel conf l1 l2 source1 target1 none locs ∧ res1 = none
        | some (.val values) =>
            ∃ words, words.length = values.length ∧
              stateRel conf l1 l2 source1 target1 (some (values.zip words)) locs ∧
              res1 = some (.result (.loc l1 l2) words)
        | some (.err (.raise value)) =>
            target1.ffi = source1.ffi ∧
            ∃ word l5 l6 rest,
              res1 = some (.exception (mkLoc (WordSemStateFiniteExact.jumpExc target)) word) ∧
              (WordSemStateFiniteExact.jumpExc target ≠ none →
                wordSemLastN (source1.stack.length + 1) locs = (l5, l6) :: rest ∧
                ∀ i, stateRel conf l5 l6 (DataSem.setVar i value source1)
                  (WordSemStateFiniteExact.setVar (adjustVar i) word target1) none rest)
        | some (.err (.abort (.ffiError event))) =>
            res1 = some (.finalFfi event) ∧ target1.ffi = source1.ffi
        | some (.err (.abort _)) => res1 = some .timeOut ∧ target1.ffi = source1.ffi) := by
  have compiled : compileControl (width := width) conf n l (.return names) =
      (.return 0 (names.map adjustVar), l) := by
    have h := compileControl_option (width := width) conf n l (.return names)
    simpa [compileControl?] using h.symm
  have bound : optionLe target.stackMax source.stackMax := related.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  cases dataRead : DataSem.getVars names source.locals with
  | none =>
    have bad : res = some (.err (.abort .typeError)) := by
      have h := congrArg Prod.fst run
      simpa [DataSem.evaluate, dataRead, DataSem.typeError] using h.symm
    exact (notTypeError bad).elim
  | some values =>
    have sourceEq : res = some (.val values) ∧ source1 = DataSem.flushState false source := by
      simpa [DataSem.evaluate, dataRead] using run.symm
    rcases sourceEq with ⟨resEq, stateEq⟩
    subst res
    subst source1
    obtain ⟨words, wordRead, lengths⟩ := stateRel_getVars conf l1 l2 source target locs names values related dataRead
    have zero := related.2.2.2.2.2.2.2.2.2.2.1 rfl
    have post := returnStateRel conf l1 l2 source target locs names values words related dataRead wordRead
    refine ⟨WordSemStateFiniteExact.flushState false target, some (.result (.loc l1 l2) words), ?_, ?_, ?_, ?_⟩
    · simp [compiled, WordSemStateFiniteExact.evaluate, WordSemStateFiniteExact.getVar, zero, wordRead]
    · simpa [WordSemStateFiniteExact.flushState, DataSem.flushState] using bound
    · simp
    · intro _
      exact ⟨words, lengths.symm, post, rfl⟩
end Flapjack.Compiler.Backend.DataToWord.Proofs
