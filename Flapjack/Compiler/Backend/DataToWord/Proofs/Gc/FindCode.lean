module

public import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.PushCallEnv
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.CodePointer
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.GetVarsSnoc
public import Flapjack.Compiler.Backend.Semantics.WordSem.Alloc
public import Flapjack.Compiler.Backend.Semantics.WordSem.CallHelpers

@[expose] public section

/-! Direct and indirect data-to-word code lookup simulation. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
open Flapjack Flapjack.Compiler.Backend

namespace findCodeMap
/-- Canonical target-state roundtrip for code lookup simulation. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : WordSemStateBroad width C F) (h : state.FiniteSupport),
      (WordSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : WordSemStateFiniteExact width C F,
      WordSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  WordSemStateExact.holFmapAsFiniteSupportWitness
end findCodeMap

/-- A nonempty snoc list has the appended element as its last value. -/
private theorem lastSnoc {α : Type} [Nonempty α] (xs : List α) (x : α) :
    holLast (xs ++ [x]) = x := by
  induction xs with
  | nil => simp [holLast]
  | cons a xs ih =>
    cases xs with
    | nil => simp [holLast]
    | cons b xs => simpa [holLast] using ih

/-- A successful data call lookup has a compiled word lookup and related call states. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_gcProofScript.sml" "find_code_thm" 5277
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem findCode_correct {width : Nat} [NeZero width] {C F : Type}
    (conf : Flapjack.Compiler.Backend.DataToWord.Config) (l1 l2 : Nat) (source : Flapjack.Compiler.Backend.DataSem.State C F)
    (target : WordSemStateFiniteExact width C F) (locs : List (Nat × Nat))
    (args : List Nat) (values : List Flapjack.Compiler.Backend.DataSem.Value) (words : List (WordLocW width))
    (dest : Option Nat) (fs : Spt Nat) (result : List Flapjack.Compiler.Backend.DataSem.Value)
    (body : Flapjack.Compiler.Backend.DataLang.Prog)
    (size : Option Nat)
    (premises : stateRel conf l1 l2 source target none locs ∧
      DataSem.getVars args source.locals = some values ∧
      WordSemStateFiniteExact.getVars (0 :: args.map adjustVar) target = some (.loc l1 l2 :: words) ∧
      DataSem.findCode dest values source.code fs = some (result, body, size)) :
    ∃ args1 n1 n2,
      wordSemFindCode dest (.loc l1 l2 :: words) target.code fs =
        some (args1, (compileControl conf n1 n2 body).1, size) ∧
      stateRel conf l1 l2 (DataSem.callEnv result size (DataSem.decClock source))
        (WordSemStateFiniteExact.callEnv args1 size (WordSemStateFiniteExact.decClock target)) none locs := by
  obtain ⟨related, sourceRead, targetRead, found⟩ := premises
  have wordRead : WordSemStateFiniteExact.getVars (args.map adjustVar) target = some words := by
    cases h0 : WordSemStateFiniteExact.getVar 0 target with
    | none => simp [WordSemStateFiniteExact.getVars, h0] at targetRead
    | some v =>
      cases hv : WordSemStateFiniteExact.getVars (args.map adjustVar) target with
      | none => simp [WordSemStateFiniteExact.getVars, h0, hv] at targetRead
      | some vs =>
        simp [WordSemStateFiniteExact.getVars, h0, hv] at targetRead
        exact targetRead.2 ▸ rfl
  have dataLen := getVars_imp_length args values source.locals sourceRead
  have wordLen := wordGetVars_imp_length (args.map adjustVar) words target wordRead
  simp only [List.length_map] at wordLen
  have sameLen : values.length = words.length := dataLen.symm.trans wordLen
  have codeRel := related.2.2.2.2.1
  cases dest with
  | some label =>
    cases code : sptLookup label source.code with
    | none => simp [DataSem.findCode, code] at found
    | some entry =>
      obtain ⟨arity, program⟩ := entry
      by_cases valid : values.length = arity
      · simp [DataSem.findCode, code, valid] at found
        obtain ⟨rfl, rfl, rfl⟩ := found
        have targetCode := codeRel.2.2 label arity program code
        refine ⟨.loc l1 l2 :: words, label, 2, ?_, ?_⟩
        · simp [wordSemFindCode, targetCode, valid, ← sameLen]
        · exact stateRel_callEnv conf l1 l2 l1 l2 source target locs args values words _
            ⟨sourceRead, wordRead, related⟩
      · simp [DataSem.findCode, code, valid] at found
  | none =>
    have valuesNonempty : values ≠ [] := by
      intro empty
      subst values
      simp [DataSem.findCode] at found
    have argsNonempty : args ≠ [] := by
      intro empty
      simp [empty] at dataLen
      exact valuesNonempty (by simpa using dataLen.symm)
    obtain ⟨init, last, argsEq⟩ := (List.eq_nil_or_concat args).resolve_left argsNonempty
    simp only [List.concat_eq_append] at argsEq
    subst args
    obtain ⟨lastValue, prefixValues, valuesEq, lastSource, prefixSource⟩ :=
      dataGetVars_snoc init values last source.locals sourceRead
    obtain ⟨lastWord, prefixWords, wordsEq, lastTarget, prefixTarget⟩ :=
      wordGetVars_snoc (init.map adjustVar) words (adjustVar last) target (by simpa using wordRead)
    subst values
    subst words
    have pointerRel : ∀ label, lastValue = .codePtr label → lastWord = .loc label 0 := by
      intro label hp
      have h := stateRel_codePtr conf l1 l2 source target locs (init ++ [last])
        (prefixValues ++ [lastValue]) (prefixWords ++ [lastWord]) label
        ⟨related, sourceRead, wordRead, by simpa [lastSnoc] using hp, by simp⟩
      simpa [lastSnoc] using h.2
    have hfind : DataSem.findCode none (prefixValues ++ [lastValue]) source.code fs =
        some (result, body, size) := found
    cases lastValue with
    | codePtr label =>
      cases code : sptLookup label source.code with
      | none => simp [DataSem.findCode, lastSnoc, code] at hfind
      | some entry =>
        obtain ⟨arity, program⟩ := entry
        by_cases valid : (prefixValues ++ [Flapjack.Compiler.Backend.DataSem.Value.codePtr label]).length = arity + 1
        · simp [DataSem.findCode, lastSnoc, code, valid] at hfind
          obtain ⟨rfl, rfl, rfl⟩ := hfind
          have targetCode := codeRel.2.2 label arity program code
          have wordEq := pointerRel label rfl
          subst lastWord
          refine ⟨.loc l1 l2 :: prefixWords, label, 2, ?_, ?_⟩
          · have prefixLength : prefixWords.length = arity := by
              simp only [List.length_append, List.length_singleton] at sameLen valid
              omega
            have dropEq : (.loc l1 l2 :: (prefixWords ++ [.loc label 0])).dropLast =
                .loc l1 l2 :: prefixWords := by
              simpa only [List.cons_append] using
                (List.dropLast_concat (l₁ := .loc l1 l2 :: prefixWords) (b := .loc label 0))
            change wordSemFindCode none ((.loc l1 l2 :: prefixWords) ++ [.loc label 0]) target.code fs = _
            simp [wordSemFindCode, targetCode, prefixLength, Nat.add_assoc, dropEq]
          · exact stateRel_callEnv conf l1 l2 l1 l2 source target locs init prefixValues prefixWords _
              ⟨prefixSource, prefixTarget, related⟩
        · simp only [List.length_append, List.length_singleton, Nat.add_right_cancel_iff] at valid
          simp [DataSem.findCode, lastSnoc, code, valid] at hfind
    | number n => simp [DataSem.findCode, lastSnoc] at hfind
    | block x y z => simp [DataSem.findCode, lastSnoc] at hfind
    | refPtr x y => simp [DataSem.findCode, lastSnoc] at hfind
    | word64 x => simp [DataSem.findCode, lastSnoc] at hfind


/-- Shared call lookup reasoning for the returning and handler cases of the
HOL proof. The handler remains arbitrary until each source theorem fixes it. -/
private theorem findCode_pushEnv {width : Nat} [NeZero width] {C F : Type}
    (conf : Flapjack.Compiler.Backend.DataToWord.Config) (l1 l2 q l : Nat) (source : Flapjack.Compiler.Backend.DataSem.State C F)
    (target : WordSemStateFiniteExact width C F) (locs : List (Nat × Nat))
    (args : List Nat) (values : List Flapjack.Compiler.Backend.DataSem.Value) (words : List (WordLocW width))
    (dest : Option Nat) (fs : Spt Nat) (result : List Flapjack.Compiler.Backend.DataSem.Value)
    (body : Flapjack.Compiler.Backend.DataLang.Prog)
    (handler : Option (Nat × WordLangProgHOL (BitVec width) × Nat × Nat))
    (size : Option Nat) (names : NumSet) (cutData : Spt DataSem.Value)
    (cutWords : Spt (WordLocW width) × Spt (WordLocW width))
    (premises : stateRel conf l1 l2 source target none locs ∧
      DataSem.getVars args source.locals = some values ∧
      WordSemStateFiniteExact.getVars (args.map adjustVar) target = some words ∧
      DataSem.findCode dest values source.code fs = some (result, body, size) ∧
      DataSem.cutEnv names source.locals = some cutData ∧
      wordSemCutEnvs (adjustSets names) target.locals = some cutWords) :
    ∃ args1 n1 n2,
      wordSemFindCode dest (.loc q l :: words) target.code fs =
        some (args1, (compileControl conf n1 n2 body).1, size) ∧
      stateRel conf q l (DataSem.callEnv result size (DataSem.pushEnv cutData handler.isSome (DataSem.decClock source)))
        (WordSemStateFiniteExact.callEnv args1 size (WordSemStateFiniteExact.pushEnv cutWords handler (WordSemStateFiniteExact.decClock target))) none ((l1,l2)::locs) := by
  obtain ⟨related, sourceRead, wordRead, found, sourceCut, targetCut⟩ := premises
  have dataLen := getVars_imp_length args values source.locals sourceRead
  have wordLen := wordGetVars_imp_length (args.map adjustVar) words target wordRead
  simp only [List.length_map] at wordLen
  have sameLen : values.length = words.length := dataLen.symm.trans wordLen
  have codeRel := related.2.2.2.2.1
  cases dest with
  | some label =>
    cases code : sptLookup label source.code with
    | none => simp [DataSem.findCode, code] at found
    | some entry =>
      obtain ⟨arity, program⟩ := entry
      by_cases valid : values.length = arity
      · simp [DataSem.findCode, code, valid] at found
        obtain ⟨rfl, rfl, rfl⟩ := found
        have targetCode := codeRel.2.2 label arity program code
        refine ⟨.loc q l :: words, label, 2, ?_, ?_⟩
        · simp [wordSemFindCode, targetCode, valid, ← sameLen]
        · exact stateRel_callEnv_pushEnv conf l1 l2 q l source target locs args values words _ names cutData cutWords handler
            ⟨related, sourceRead, wordRead, sourceCut, targetCut⟩
      · simp [DataSem.findCode, code, valid] at found
  | none =>
    have valuesNonempty : values ≠ [] := by
      intro empty
      subst values
      simp [DataSem.findCode] at found
    have argsNonempty : args ≠ [] := by
      intro empty
      simp [empty] at dataLen
      exact valuesNonempty (by simpa using dataLen.symm)
    obtain ⟨init, last, argsEq⟩ := (List.eq_nil_or_concat args).resolve_left argsNonempty
    simp only [List.concat_eq_append] at argsEq
    subst args
    obtain ⟨lastValue, prefixValues, valuesEq, lastSource, prefixSource⟩ :=
      dataGetVars_snoc init values last source.locals sourceRead
    obtain ⟨lastWord, prefixWords, wordsEq, lastTarget, prefixTarget⟩ :=
      wordGetVars_snoc (init.map adjustVar) words (adjustVar last) target (by simpa using wordRead)
    subst values
    subst words
    have pointerRel : ∀ label, lastValue = .codePtr label → lastWord = .loc label 0 := by
      intro label hp
      have h := stateRel_codePtr conf l1 l2 source target locs (init ++ [last])
        (prefixValues ++ [lastValue]) (prefixWords ++ [lastWord]) label
        ⟨related, sourceRead, wordRead, by simpa [lastSnoc] using hp, by simp⟩
      simpa [lastSnoc] using h.2
    have hfind : DataSem.findCode none (prefixValues ++ [lastValue]) source.code fs =
        some (result, body, size) := found
    cases lastValue with
    | codePtr label =>
      cases code : sptLookup label source.code with
      | none => simp [DataSem.findCode, lastSnoc, code] at hfind
      | some entry =>
        obtain ⟨arity, program⟩ := entry
        by_cases valid : (prefixValues ++ [Flapjack.Compiler.Backend.DataSem.Value.codePtr label]).length = arity + 1
        · simp [DataSem.findCode, lastSnoc, code, valid] at hfind
          obtain ⟨rfl, rfl, rfl⟩ := hfind
          have targetCode := codeRel.2.2 label arity program code
          have wordEq := pointerRel label rfl
          subst lastWord
          refine ⟨.loc q l :: prefixWords, label, 2, ?_, ?_⟩
          · have prefixLength : prefixWords.length = arity := by
              simp only [List.length_append, List.length_singleton] at sameLen valid
              omega
            have dropEq : (.loc q l :: (prefixWords ++ [.loc label 0])).dropLast =
                .loc q l :: prefixWords := by
              simpa only [List.cons_append] using
                (List.dropLast_concat (l₁ := .loc q l :: prefixWords) (b := .loc label 0))
            change wordSemFindCode none ((.loc q l :: prefixWords) ++ [.loc label 0]) target.code fs = _
            simp [wordSemFindCode, targetCode, prefixLength, Nat.add_assoc, dropEq]
          · exact stateRel_callEnv_pushEnv conf l1 l2 q l source target locs init prefixValues prefixWords _ names cutData cutWords handler
              ⟨related, prefixSource, prefixTarget, sourceCut, targetCut⟩
        · simp only [List.length_append, List.length_singleton, Nat.add_right_cancel_iff] at valid
          simp [DataSem.findCode, lastSnoc, code, valid] at hfind
    | number n => simp [DataSem.findCode, lastSnoc] at hfind
    | block x y z => simp [DataSem.findCode, lastSnoc] at hfind
    | refPtr x y => simp [DataSem.findCode, lastSnoc] at hfind
    | word64 x => simp [DataSem.findCode, lastSnoc] at hfind

/-- A successful data lookup for a returning call has a compiled word lookup
and preserves the relation after pushing the caller's environments. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_gcProofScript.sml" "find_code_thm_ret"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem findCode_return {width : Nat} [NeZero width] {C F : Type}
    (conf : Flapjack.Compiler.Backend.DataToWord.Config) (l1 l2 q l : Nat) (source : Flapjack.Compiler.Backend.DataSem.State C F)
    (target : WordSemStateFiniteExact width C F) (locs : List (Nat × Nat))
    (args : List Nat) (values : List Flapjack.Compiler.Backend.DataSem.Value) (words : List (WordLocW width))
    (dest : Option Nat) (fs : Spt Nat) (result : List Flapjack.Compiler.Backend.DataSem.Value)
    (body : Flapjack.Compiler.Backend.DataLang.Prog)
    (size : Option Nat) (names : NumSet) (cutData : Spt Flapjack.Compiler.Backend.DataSem.Value)
    (cutWords : Spt (WordLocW width) × Spt (WordLocW width))
    (premises : stateRel conf l1 l2 source target none locs ∧
      DataSem.getVars args source.locals = some values ∧
      WordSemStateFiniteExact.getVars (args.map adjustVar) target = some words ∧
      DataSem.findCode dest values source.code fs = some (result, body, size) ∧
      DataSem.cutEnv names source.locals = some cutData ∧
      wordSemCutEnvs (adjustSets names) target.locals = some cutWords) :
    ∃ args1 n1 n2,
      wordSemFindCode dest (.loc q l :: words) target.code fs =
        some (args1, (compileControl conf n1 n2 body).1, size) ∧
      stateRel conf q l (DataSem.callEnv result size (DataSem.pushEnv cutData false (DataSem.decClock source)))
        (WordSemStateFiniteExact.callEnv args1 size (WordSemStateFiniteExact.pushEnv cutWords none (WordSemStateFiniteExact.decClock target))) none ((l1,l2)::locs) := by
  simpa using findCode_pushEnv conf l1 l2 q l source target locs args values words dest fs
    result body none size names cutData cutWords premises

/-- A successful handler call lookup preserves the pushed call relation. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_gcProofScript.sml" "find_code_thm_handler"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem findCode_handler {width : Nat} [NeZero width] {C F : Type}
    (conf : Flapjack.Compiler.Backend.DataToWord.Config) (l1 l2 q l : Nat) (source : Flapjack.Compiler.Backend.DataSem.State C F)
    (target : WordSemStateFiniteExact width C F) (locs : List (Nat × Nat))
    (args : List Nat) (values : List Flapjack.Compiler.Backend.DataSem.Value) (words : List (WordLocW width))
    (dest : Option Nat) (fs : Spt Nat) (result : List Flapjack.Compiler.Backend.DataSem.Value)
    (body : Flapjack.Compiler.Backend.DataLang.Prog)
    (x0 nn : Nat) (prog1 : WordLangProgHOL (BitVec width))
    (size : Option Nat) (names : NumSet) (cutData : Spt Flapjack.Compiler.Backend.DataSem.Value)
    (cutWords : Spt (WordLocW width) × Spt (WordLocW width))
    (premises : stateRel conf l1 l2 source target none locs ∧
      DataSem.getVars args source.locals = some values ∧
      WordSemStateFiniteExact.getVars (args.map adjustVar) target = some words ∧
      DataSem.findCode dest values source.code fs = some (result, body, size) ∧
      DataSem.cutEnv names source.locals = some cutData ∧
      wordSemCutEnvs (adjustSets names) target.locals = some cutWords) :
    ∃ args1 n1 n2,
      wordSemFindCode dest (.loc q l :: words) target.code fs =
        some (args1, (compileControl conf n1 n2 body).1, size) ∧
      stateRel conf q l (DataSem.callEnv result size (DataSem.pushEnv cutData true (DataSem.decClock source)))
        (WordSemStateFiniteExact.callEnv args1 size (WordSemStateFiniteExact.pushEnv cutWords (some (adjustVar x0, prog1, nn, l + 1)) (WordSemStateFiniteExact.decClock target))) none ((l1,l2)::locs) := by
  simpa using findCode_pushEnv conf l1 l2 q l source target locs args values words dest fs
    result body (some (adjustVar x0, prog1, nn, l + 1)) size names cutData cutWords premises

/-- A successful data code lookup cannot have an indirect destination with
an empty argument list. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_gcProofScript.sml" "data_find_code"]
theorem dataFindCode {α β : Type} (dest : Option Nat) (xs ys : List DataSem.Value)
    (code : Spt (Nat × α)) (fs : Spt β) (prog : α) (ss : Option β)
    (found : DataSem.findCode dest xs code fs = some (ys, prog, ss)) :
    ¬ wordSemBadDestArgs dest xs = true := by
  cases dest with
  | none =>
    cases xs with
    | nil => simp [DataSem.findCode] at found
    | cons x xs => simp [wordSemBadDestArgs]
  | some n => simp [wordSemBadDestArgs]

end Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
