module

public import Flapjack.Compiler.Backend.DataToWord.Proofs.Correct.CallHandler

@[expose] public section

/-! The `Call` case of the data-to-word evaluator simulation
(`data_to_wordProofScript.sml` lines 934-1152). -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs
open Flapjack Flapjack.SemanticPrimitivesHOL
open Flapjack.Compiler.Backend.BackendProps
open Flapjack.Compiler.Backend.DataToWord.Proofs.Gc

namespace reviewedDataCompileCorrect_callMap
/-- Canonical roundtrip for the target state used by this HOL port. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : WordSemStateBroad width C F) (h : state.FiniteSupport),
      (WordSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : WordSemStateFiniteExact width C F,
      WordSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  WordSemStateExact.holFmapAsFiniteSupportWitness
end reviewedDataCompileCorrect_callMap

/-- The `Call` case retains the complete conclusion of `data_compile_correct`.
Its three hypotheses are the `Call` clause's evaluator induction hypotheses:
the handler body after a raising callee, the callee of a returning call, and
the callee of a tail call. HOL's auxiliary pattern variables for the found
code triple, the return pair, the callee result and the handler pair are bound
here as the corresponding tuple patterns. The word evaluator inherits the
real-model assumption documented in `docs/SOUNDNESS.md` item 8. The full
theorem still requires assembly of all cases. -/
@[hol "cakeml/compiler/backend/proofs/data_to_wordProofScript.sml" "data_compile_correct"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem dataCompileCorrect_call {width : Nat} [NeZero width] {C F : Type}
    (source : Flapjack.Compiler.Backend.DataSem.State C F) (conf : Flapjack.Compiler.Backend.DataToWord.Config) (n l l1 l2 : Nat)
    (res : Option (Result (List Flapjack.Compiler.Backend.DataSem.Value) Flapjack.Compiler.Backend.DataSem.Value)) (source1 : Flapjack.Compiler.Backend.DataSem.State C F)
    (target : WordSemStateFiniteExact width C F) (locs : List (Nat × Nat))
    (ret : Option (List Nat × NumSet)) (dest : Option Nat) (args : List Nat)
    (handler : Option (Nat × Flapjack.Compiler.Backend.DataLang.Prog))
    (ihHandler : ∀ xs args1 prog ss ns names env s1 r s2 x hn h,
      DataSem.getVars args source.locals = some xs ∧
      DataSem.findCode dest xs source.code source.stackFrameSizes = some (args1, prog, ss) ∧
      ret = some (ns, names) ∧ ns.Nodup ∧ DataSem.cutEnv names source.locals = some env ∧
      s1 = DataSem.callEnv args1 ss (DataSem.pushEnv env handler.isSome (DataSem.decClock source)) ∧
      source.clock ≠ 0 ∧ DataSem.evaluate prog s1 = (r, s2) ∧ r = some (.err (.raise x)) ∧
      handler = some (hn, h) →
      dataCompileCorrectInduction (width := width) h (DataSem.setVar hn x s2))
    (ihCall : ∀ xs args1 prog ss ns names env s1,
      DataSem.getVars args source.locals = some xs ∧
      DataSem.findCode dest xs source.code source.stackFrameSizes = some (args1, prog, ss) ∧
      ret = some (ns, names) ∧ ns.Nodup ∧ DataSem.cutEnv names source.locals = some env ∧
      s1 = DataSem.callEnv args1 ss (DataSem.pushEnv env handler.isSome (DataSem.decClock source)) ∧
      source.clock ≠ 0 →
      dataCompileCorrectInduction (width := width) prog s1)
    (ihTail : ∀ xs args1 prog ss,
      DataSem.getVars args source.locals = some xs ∧
      DataSem.findCode dest xs source.code source.stackFrameSizes = some (args1, prog, ss) ∧
      ret = none ∧ handler = none ∧ source.clock ≠ 0 →
      dataCompileCorrectInduction (width := width) prog
        (DataSem.callEnv args1 ss (DataSem.decClock source)))
    (run : DataSem.evaluate (.call ret dest args handler) source = (res, source1))
    (notTypeError : res ≠ some (.err (.abort .typeError)))
    (related : stateRel conf l1 l2 source target none locs)
    (depth : target.termdep > 1) :
    ∃ target1 res1,
      WordSemStateFiniteExact.evaluate (compileControl conf n l (.call ret dest args handler)).1 target = (res1, target1) ∧
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
  have full : dataCompileCorrectInduction (width := width) (.call ret dest args handler) source := by
    cases ret with
    | none =>
      exact dataCompileCorrect_callTail source dest args handler
        (fun xs args1 prog ss h => ihTail xs args1 prog ss ⟨h.1, h.2.1, rfl, h.2.2⟩)
    | some pair =>
      obtain ⟨ns, names⟩ := pair
      cases handler with
      | none =>
        exact dataCompileCorrect_callReturn source dest args ns names
          (fun xs args1 prog ss env s1 h =>
            ihCall xs args1 prog ss ns names env s1 ⟨h.1, h.2.1, rfl, h.2.2⟩)
      | some hpair =>
        obtain ⟨hn, hprog⟩ := hpair
        exact dataCompileCorrect_callHandler source dest args ns names hn hprog
          (fun xs args1 prog ss env s1 s2 x h =>
            ihHandler xs args1 prog ss ns names env s1 _ s2 x hn hprog
              ⟨h.1, h.2.1, rfl, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2, rfl, rfl⟩)
          (fun xs args1 prog ss env s1 h =>
            ihCall xs args1 prog ss ns names env s1 ⟨h.1, h.2.1, rfl, h.2.2⟩)
  obtain ⟨target1, res1, wordRun, stackBound, space, result⟩ :=
    full conf n l l1 l2 res source1 target locs run notTypeError related depth
  refine ⟨target1, res1, wordRun, stackBound, space, fun hs => ?_⟩
  have h := result hs
  cases res with
  | none => exact h
  | some r =>
    cases r with
    | val values => exact h
    | err err =>
      cases err with
      | raise value => exact h
      | abort err => cases err <;> exact h

end Flapjack.Compiler.Backend.DataToWord.Proofs
