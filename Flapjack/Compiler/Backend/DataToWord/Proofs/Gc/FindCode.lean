import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.ReturnRoots
import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation.CodePointer
import Flapjack.Compiler.Backend.Semantics.WordSem.Alloc

/-! Code and argument correspondence for data-to-word calls. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
open Flapjack

/-- A represented code pointer has the exact word-level code location. -/
theorem memoryRel_codePtr_location {width : Nat} [NeZero width] (conf : Config) (be : Bool)
    (next : Nat) (refs : Spt (BvlSem.Ref DataSem.Value)) (space : Nat)
    (store : HolFiniteMapExact WordStoreHOL (WordLocW width)) (memory : BitVec width → WordLocW width)
    (domain : BitVec width → Bool) (label : Nat) (word : WordLocW width)
    (roots : List (DataSem.Value × WordLocW width))
    (rel : Memory.memoryRel conf be next refs space store memory domain ((.codePtr label, word) :: roots)) :
    word = .loc label 0 := by
  obtain ⟨heap, limit, a, sp, sp1, gens, _, hword, _, _⟩ := rel
  obtain ⟨xs, habs, addresses⟩ := hword
  obtain ⟨_, _, _, _, stack⟩ := habs
  obtain ⟨f, tf, _, _, _, _, _, _, _, values, _⟩ := stack
  cases xs with
  | nil => cases values
  | cons x xs =>
    cases values with
    | cons valueInv _ =>
      cases addresses with
      | cons address _ =>
        have eq := (Memory.valueInv_codePtr conf label refs x f tf heap).mp valueInv
        subst x
        simpa [Memory.wordAddr] using address.symm

/-- A code pointer held in a related local is held in the corresponding word
local as the same label and zero offset. -/
theorem stateRel64_getCodePtr {C F : Type} (conf : Config) (l1 l2 : Nat)
    (source : DataSem.State C F) (target : WordSemStateFiniteExact 64 C F)
    (locs : List (Nat × Nat)) (related : stateRel64 conf l1 l2 source target none locs)
    (name label : Nat) (lookup : DataSem.getVar name source.locals = some (.codePtr label)) :
    WordSemStateFiniteExact.getVar (adjustVar name) target = some (.loc label 0) := by
  obtain ⟨word, wordRun⟩ := stateRel64_getVar conf l1 l2 source target none locs related name (.codePtr label) lookup
  have member := localPair_mem_joinEnv source.locals target.locals name (.codePtr label) word lookup wordRun
  rcases related with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, memory⟩
  let roots := joinEnv source.locals (sptToAList (sptInter target.locals (adjustSet source.locals))) ++
    [(theGlobal source.global, holFapply target.store .globals)] ++ flatStack source.stack target.stack
  have focused : Memory.memoryRel conf target.be (holThe source.tstamps) source.refs source.space
      target.store target.memory target.mdomain ((.codePtr label, word) :: roots) := by
    apply Memory.memoryRel_rearrange conf target.be (holThe source.tstamps) source.refs source.space
      target.store target.memory target.mdomain roots
    · intro pair present
      simp only [List.mem_cons] at present
      rcases present with rfl | tail
      · exact List.mem_append_left _ (List.mem_append_left _ member)
      · exact tail
    · simpa [roots] using memory
  have eq := memoryRel_codePtr_location conf target.be (holThe source.tstamps) source.refs source.space
    target.store target.memory target.mdomain label word roots focused
  simpa [eq] using wordRun

/-- Direct call lookup finds the compiled code with the extra return-location
argument and the same optional frame size. -/
theorem stateRel64_findCode_direct {C F : Type} (conf : Config) (l1 l2 : Nat)
    (source : DataSem.State C F) (target : WordSemStateFiniteExact 64 C F)
    (locs : List (Nat × Nat)) (related : stateRel64 conf l1 l2 source target none locs)
    (label : Nat) (args : List DataSem.Value) (words : List (WordLocW 64)) (body : DataLang.Prog)
    (size : Option Nat) (lengths : args.length = words.length)
    (found : DataSem.findCode (some label) args source.code source.stackFrameSizes = some (args, body, size)) :
    wordSemFindCode (some label) (.loc l1 l2 :: words) target.code target.stackSize =
      some (.loc l1 l2 :: words, (compileControl64 conf label 2 body).1, size) := by
  unfold DataSem.findCode at found
  cases lookup : sptLookup label source.code with
  | none => simp [lookup] at found
  | some entry =>
    obtain ⟨arity, prog⟩ := entry
    by_cases arityEq : args.length = arity
    · simp [lookup, arityEq] at found
      obtain ⟨rfl, rfl⟩ := found
      have targetLookup := related.2.2.2.2.1.2.2 label arity prog lookup
      have sizes := related.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      simp [wordSemFindCode, targetLookup, sizes, ← lengths, arityEq]
    · simp [lookup, arityEq] at found

/-- An indirect call ending in a corresponding code location resolves to the
same compiled function and removes the pointer from the argument list. -/
theorem stateRel64_findCode_indirect {C F : Type} (conf : Config) (l1 l2 : Nat)
    (source : DataSem.State C F) (target : WordSemStateFiniteExact 64 C F)
    (locs : List (Nat × Nat)) (related : stateRel64 conf l1 l2 source target none locs)
    (label arity : Nat) (body : DataLang.Prog) (args : List DataSem.Value) (words : List (WordLocW 64))
    (lengths : args.length = words.length) (arityEq : args.length = arity)
    (lookup : sptLookup label source.code = some (arity, body)) :
    wordSemFindCode none ((.loc l1 l2 :: words) ++ [.loc label 0]) target.code target.stackSize =
      some (.loc l1 l2 :: words, (compileControl64 conf label 2 body).1, sptLookup label source.stackFrameSizes) := by
  have targetLookup := related.2.2.2.2.1.2.2 label arity body lookup
  have sizes := related.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have drop : ∀ xs : List (WordLocW 64), (xs ++ [WordLocW.loc label 0]).dropLast = xs := by
    intro xs
    induction xs with
    | nil => rfl
    | cons x xs ih =>
      cases xs with
      | nil => rfl
      | cons y ys => simpa [List.dropLast_cons_cons] using congrArg (List.cons x) ih
  simpa [wordSemFindCode, targetLookup, sizes, ← lengths, arityEq, drop] using
    drop (.loc l1 l2 :: words)

end Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
