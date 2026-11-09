module

public import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.StackRoots

@[expose] public section

/-! The data/word root pairing after decoding collected roots. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
open Flapjack WordSemStackEq
local instance : Nonempty DataSem.Value := ⟨.number 0⟩

private theorem locMerge_filter_of_rel {width : Nat} [NeZero width]
    {before after : List (WordLocW width)}
    (related : List.Forall₂ (fun x y => wordSemIsWordLoc x = wordSemIsWordLoc y ∧
      (wordSemIsWordLoc x = false → x = y)) before after) :
    locMerge before (after.filter wordSemIsWordLoc) = after := by
  induction related with
  | nil => rfl
  | @cons x y xs ys head tail ih =>
    cases x <;> cases y <;> simp_all [List.filter_cons, wordSemIsWordLoc, locMerge]

private theorem encStack_decStack {width : Nat} [NeZero width]
    (before after : List (WordSemStackFrame width)) (roots : List (WordLocW width))
    (decoded : wordSemDecStack roots before = some after) : wordSemEncStack after = roots := by
  induction before generalizing roots after with
  | nil =>
    cases roots <;> simp_all [wordSemDecStack, wordSemEncStack]
  | cons frame before ih =>
    rcases frame with ⟨size, nonGc, gc, handler⟩
    simp only [wordSemDecStack] at decoded
    split at decoded
    · contradiction
    · rename_i enough
      cases tailRun : wordSemDecStack (roots.drop gc.length) before with
      | none => simp [tailRun] at decoded
      | some tail =>
        simp only [tailRun, Option.some.injEq] at decoded
        subst after
        have tailEq := ih tail (roots.drop gc.length) tailRun
        have lengthEq : (roots.take gc.length).length = gc.length := by simp; omega
        simp only [wordSemEncStack, List.map_snd_zip (l₁ := gc.map Prod.fst)
          (l₂ := roots.take gc.length) (by simpa using Nat.le_of_eq lengthEq), tailEq,
          List.take_append_drop]

private theorem joinEnv_keys {width : Nat} [NeZero width] (env : Spt DataSem.Value)
    (before after : List (Nat × WordLocW width)) (keys : before.map Prod.fst = after.map Prod.fst) :
    (joinEnv env before).map Prod.fst = (joinEnv env after).map Prod.fst := by
  induction before generalizing after with
  | nil => cases after <;> simp_all [joinEnv]
  | cons x xs ih =>
    cases after with
    | nil => simp at keys
    | cons y ys =>
      rcases x with ⟨a, x⟩
      rcases y with ⟨b, y⟩
      simp only [List.map_cons, List.cons.injEq] at keys
      rcases keys with ⟨rfl, keys⟩
      have tailEq := ih ys keys
      simp only [joinEnv, List.map_map] at tailEq
      simp only [joinEnv, List.filter_cons]
      split <;> simp_all [List.map_map]

private theorem flatStack_keys {width : Nat} [NeZero width]
    (source : List DataSem.Stack) (before after : List (WordSemStackFrame width))
    (keys : sKeyEq before after) :
    (flatStack source before).map Prod.fst = (flatStack source after).map Prod.fst := by
  induction source generalizing before after with
  | nil => cases before <;> cases after <;> simp_all [flatStack, sKeyEq]
  | cons frame source ih =>
    cases before with
    | nil => cases after <;> simp_all [flatStack, sKeyEq]
    | cons b before =>
      cases after with
      | nil => simp [sKeyEq] at keys
      | cons a after =>
        rcases b with ⟨size, nonGc, gc, handler⟩
        rcases a with ⟨size', nonGc', gc', handler'⟩
        have frameKeys := (sFrameKeyEqDef2 _ _ _ _ _ _ _ _).mp keys.2
        cases frame <;> simp only [flatStack, List.map_append, ih before after keys.1,
          joinEnv_keys _ gc gc' frameKeys.1]

/-- Rebuilding the stack pairs each source root with the collector's
corresponding returned word or unchanged code location. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_gcProofScript.sml" "word_gc_fun_EL_lemma"
  (words_as_type_indexed_bitvec)]
theorem wordGcFun_decStack_flat {width : Nat} [NeZero width]
    (source : List DataSem.Stack) (before after : List (WordSemStackFrame width))
    (roots : List (WordLocW width))
    (afterRel : List.Forall₂ stackRel source after)
    (rootRel : List.Forall₂ (fun x y => wordSemIsWordLoc x = wordSemIsWordLoc y ∧
      (wordSemIsWordLoc x = false → x = y)) (flatStack source before |>.map Prod.snd) roots)
    (decoded : wordSemDecStack (locMerge (wordSemEncStack before) (roots.filter wordSemIsWordLoc)) before = some after)
    (beforeRel : List.Forall₂ stackRel source before) :
    flatStack source after = ((flatStack source before).map Prod.fst).zip roots := by
  have rootEq : locMerge (wordSemEncStack before) (roots.filter wordSemIsWordLoc) = roots := by
    rw [← flatStack_values_eq_encStack source before beforeRel]
    exact locMerge_filter_of_rel rootRel
  rw [rootEq] at decoded
  have values := flatStack_values_eq_encStack source after afterRel
  rw [encStack_decStack before after roots decoded] at values
  have keys := flatStack_keys source before after (decStackStackKeyEq roots before after decoded)
  have pairEq : ∀ {α β : Type} (pairs : List (α × β)), (pairs.map Prod.fst).zip (pairs.map Prod.snd) = pairs := by
    intro α β pairs
    induction pairs with
    | nil => rfl
    | cons pair pairs ih => cases pair; simp [ih]
  rw [keys, ← values, pairEq]

end Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
