import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.CallEnv

/-! Source and word lookup for indirect calls through local code pointers. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
open Flapjack

/-- Extending a successful source argument read by one local appends its value. -/
theorem dataGetVars_snoc (names : List Nat) (values : List DataSem.Value) (name : Nat) (value : DataSem.Value)
    (env : Spt DataSem.Value) (prefixRun : DataSem.getVars names env = some values)
    (last : DataSem.getVar name env = some value) :
    DataSem.getVars (names ++ [name]) env = some (values ++ [value]) := by
  induction names generalizing values with
  | nil => simp [DataSem.getVars] at prefixRun; subst values; simp [DataSem.getVars, last]
  | cons n names ih =>
    cases one : DataSem.getVar n env with
    | none => simp [DataSem.getVars, one] at prefixRun
    | some v =>
      cases rest : DataSem.getVars names env with
      | none => simp [DataSem.getVars, one, rest] at prefixRun
      | some vs =>
        simp [DataSem.getVars, one, rest] at prefixRun
        subst values
        simp [DataSem.getVars, one, ih vs rest]

/-- Extending a successful word argument read by one local appends its value. -/
theorem wordGetVars_snoc {C F : Type} (names : List Nat) (values : List (WordLocW 64)) (name : Nat)
    (value : WordLocW 64) (state : WordSemStateFiniteExact 64 C F)
    (prefixRun : WordSemStateFiniteExact.getVars names state = some values)
    (last : WordSemStateFiniteExact.getVar name state = some value) :
    WordSemStateFiniteExact.getVars (names ++ [name]) state = some (values ++ [value]) := by
  induction names generalizing values with
  | nil => simp [WordSemStateFiniteExact.getVars] at prefixRun; subst values; simp [WordSemStateFiniteExact.getVars, last]
  | cons n names ih =>
    cases one : WordSemStateFiniteExact.getVar n state with
    | none => simp [WordSemStateFiniteExact.getVars, one] at prefixRun
    | some v =>
      cases rest : WordSemStateFiniteExact.getVars names state with
      | none => simp [WordSemStateFiniteExact.getVars, one, rest] at prefixRun
      | some vs =>
        simp [WordSemStateFiniteExact.getVars, one, rest] at prefixRun
        subst values
        simp [WordSemStateFiniteExact.getVars, one, ih vs rest]

theorem holLast_snoc {α : Type} [Nonempty α] (xs : List α) (x : α) : holLast (xs ++ [x]) = x := by
  induction xs with
  | nil => simp [holLast]
  | cons a xs ih => cases xs with
    | nil => simp [holLast]
    | cons b xs => simpa [holLast] using ih

/-- Decompose a successful source read ending in a given local. -/
theorem dataGetVars_unsnoc (names : List Nat) (name : Nat) (env : Spt DataSem.Value)
    (values : List DataSem.Value) (run : DataSem.getVars (names ++ [name]) env = some values) :
    ∃ initial final, DataSem.getVars names env = some initial ∧ DataSem.getVar name env = some final ∧
      values = initial ++ [final] := by
  induction names generalizing values with
  | nil =>
    cases found : DataSem.getVar name env with
    | none => simp [DataSem.getVars, found] at run
    | some value =>
      simp [DataSem.getVars, found] at run
      subst values
      exact ⟨[], value, rfl, rfl, rfl⟩
  | cons n names ih =>
    cases found : DataSem.getVar n env with
    | none => simp [DataSem.getVars, found] at run
    | some value =>
      cases rest : DataSem.getVars (names ++ [name]) env with
      | none => simp [DataSem.getVars, found, rest] at run
      | some results =>
        simp [DataSem.getVars, found, rest] at run
        subst values
        obtain ⟨initial, final, initialRun, finalRun, rfl⟩ := ih results rest
        exact ⟨value :: initial, final, by simp [DataSem.getVars, found, initialRun], finalRun, rfl⟩

/-- An indirect call's final code pointer selects the corresponding compiled
body; both evaluators pass only the prefix arguments to the callee. -/
theorem stateRel64_findCode_indirect_callEnv {C F : Type} (conf : Config) (l1 l2 : Nat)
    (source : DataSem.State C F) (target : WordSemStateFiniteExact 64 C F)
    (locs : List (Nat × Nat)) (related : stateRel64 conf l1 l2 source target none locs)
    (label : Nat) (names : List Nat) (lastName : Nat) (values : List DataSem.Value) (body : DataLang.Prog)
    (sourceRun : DataSem.getVars names source.locals = some values)
    (pointer : DataSem.getVar lastName source.locals = some (.codePtr label))
    (lookup : sptLookup label source.code = some (values.length, body)) :
    ∃ words,
      DataSem.getVars (names ++ [lastName]) source.locals = some (values ++ [.codePtr label]) ∧
      WordSemStateFiniteExact.getVars (0 :: (names ++ [lastName]).map adjustVar) target =
        some ((.loc l1 l2 :: words) ++ [.loc label 0]) ∧
      DataSem.findCode none (values ++ [.codePtr label]) source.code source.stackFrameSizes =
        some (values, body, sptLookup label source.stackFrameSizes) ∧
      wordSemFindCode none ((.loc l1 l2 :: words) ++ [.loc label 0]) target.code target.stackSize =
        some (.loc l1 l2 :: words, (compileControl64 conf label 2 body).1, sptLookup label source.stackFrameSizes) ∧
      stateRel64 conf l1 l2 (DataSem.callEnv values (sptLookup label source.stackFrameSizes) (DataSem.decClock source))
        (WordSemStateFiniteExact.callEnv (.loc l1 l2 :: words) (sptLookup label source.stackFrameSizes)
          (WordSemStateFiniteExact.decClock target)) none locs := by
  obtain ⟨words, wordRun, lengths⟩ := stateRel64_getVars conf l1 l2 source target none locs related names values sourceRun
  have codePtr := stateRel64_getCodePtr conf l1 l2 source target locs related lastName label pointer
  have sourceAll := dataGetVars_snoc names values lastName (.codePtr label) source.locals sourceRun pointer
  have wordAll := wordGetVars_snoc (names.map adjustVar) words (adjustVar lastName) (.loc label 0) target wordRun codePtr
  have zero : WordSemStateFiniteExact.getVar 0 target = some (.loc l1 l2) := related.2.2.2.2.2.2.2.2.2.2.1 rfl
  refine ⟨words, sourceAll, ?_, ?_, ?_, stateRel64_callEnv conf l1 l2 l1 l2 source target locs related
    names values words _ sourceRun wordRun⟩
  · simp [List.map_append, WordSemStateFiniteExact.getVars, zero, wordAll]
  · simp [DataSem.findCode, holLast_snoc, lookup]
  · exact stateRel64_findCode_indirect conf l1 l2 source target locs related l1 l2 label values.length body values words lengths rfl lookup

end Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
