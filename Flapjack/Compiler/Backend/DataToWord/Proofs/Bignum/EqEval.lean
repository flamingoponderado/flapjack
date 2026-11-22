module

public import Flapjack.Compiler.Backend.Semantics.WordSem.EvaluateInd

@[expose] public section

/-! The combined evaluation rewrite `eq_eval` of the data-to-word bignum proof. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Bignum
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Encoders.Asm

namespace EqEvalWitness
/-- Canonical finite-map roundtrip for the target word state. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : WordSemStateBroad width C F) (h : state.FiniteSupport),
      (WordSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : WordSemStateFiniteExact width C F,
      WordSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  WordSemStateExact.holFmapAsFiniteSupportWitness
end EqEvalWitness

/-- HOL `eq_eval` (`data_to_word_bignumProofScript.sml:38-45`) is
`LIST_CONJ` of eighteen equation theorems, in this order: wordSem `evaluate_def`
(the rebound one), `get_var_def`, sptree `lookup_insert`, `get_var_imm_def`,
asm `word_cmp_def`, `word_exp_def`, `set_var_def`, `call_env_def`, misc
`fromList2_def`, `mem_load_def`, `bad_dest_args_def`, `get_vars_def`,
`find_code_def`, `add_ret_loc_def`, sptree `list_insert_def`, `dec_clock_def`,
`the_words_def` and wordLang `word_op_def`. The Lean statement has one conjunct
per theorem in the same order, each stated over the tagged Lean renderings of the
same definitions, with HOL's binder order.

* The first conjunct is literally the statement of the reviewed port
  `WordSemStateFiniteExact.evaluate_def_rebound` of the rebound `evaluate_def`,
  instantiated at this theorem's `width`, `C` and `F` (as in the capture, where
  `evaluate_def` uses the same `(α, γ, 'ffi) state` as the other conjuncts).
* Type variables: the capture shares HOL's `γ` between the word state's
  compiler-configuration type and `find_code`/`add_ret_loc`'s stack-size and
  names types, and shares `β` among `bad_dest_args`, `find_code` and
  `add_ret_loc`; Lean shares `C` and `B` in exactly those places.  HOL also uses
  the word-dimension variable `α` as the element type of `lookup_insert`,
  `fromList2` and `bad_dest_args`'s `dest`.  Lean's word dimension is a `Nat`
  width, so that element type is the separate type binder `V`.  This makes the
  Lean statement at least as general as HOL's: HOL's instance at `α` is the
  Lean instance at `width := dimindex (:α)` and `V := α`.
* `word_cmp` returns HOL `bool`; its `⇔` clauses compare `wordCmpHOL … = true`.
  HOL's word `<` is the signed `holAsmSignedLess` and `<₊` is unsigned `BitVec`
  `<`.  `bad_dest_args`'s `⇔` likewise compares the Boolean with `true`.
* `find_code`'s `LAST args` and `FRONT args` under the `args = []` guard are
  `args.getLast h` (with the guard's negation `h`) and `args.dropLast`.
* HOL's free variables of the `add_ret_loc_def` and `the_words_def` conjuncts are
  universally quantified inside their conjuncts; they occur in no other conjunct.

The evaluator inherits the real-model assumption in `docs/SOUNDNESS.md` item 8. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_bignumProofScript.sml" "eq_eval"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem eqEval {width : Nat} [NeZero width] {C F V B D : Type} :
    (type_of% (WordSemStateFiniteExact.evaluate_def_rebound (width := width) (C := C) (F := F))) ∧
    (∀ (v : Nat) (s : WordSemStateFiniteExact width C F),
      WordSemStateFiniteExact.getVar v s = sptLookup v s.locals) ∧
    (∀ (k2 : Nat) (v : V) (t : Spt V) (k1 : Nat),
      sptLookup k1 (sptInsert k2 v t) = if k1 = k2 then some v else sptLookup k1 t) ∧
    ((∀ (n : Nat) (s : WordSemStateFiniteExact width C F),
        WordSemStateFiniteExact.getVarImm (.reg n) s = WordSemStateFiniteExact.getVar n s) ∧
      ∀ (w : BitVec width) (s : WordSemStateFiniteExact width C F),
        WordSemStateFiniteExact.getVarImm (.imm w) s = some (.word w)) ∧
    ((∀ (w1 w2 : BitVec width), wordCmpHOL .equal w1 w2 = true ↔ w1 = w2) ∧
      (∀ (w1 w2 : BitVec width), wordCmpHOL .less w1 w2 = true ↔ holAsmSignedLess w1 w2 = true) ∧
      (∀ (w1 w2 : BitVec width), wordCmpHOL .lower w1 w2 = true ↔ w1 < w2) ∧
      (∀ (w1 w2 : BitVec width), wordCmpHOL .test w1 w2 = true ↔ w1 &&& w2 = 0) ∧
      (∀ (w1 w2 : BitVec width), wordCmpHOL .notEqual w1 w2 = true ↔ w1 ≠ w2) ∧
      (∀ (w1 w2 : BitVec width), wordCmpHOL .notLess w1 w2 = true ↔ ¬ holAsmSignedLess w1 w2 = true) ∧
      (∀ (w1 w2 : BitVec width), wordCmpHOL .notLower w1 w2 = true ↔ ¬ w1 < w2) ∧
      ∀ (w1 w2 : BitVec width), wordCmpHOL .notTest w1 w2 = true ↔ w1 &&& w2 ≠ 0) ∧
    ((∀ (w : BitVec width) (s : WordSemStateFiniteExact width C F),
        WordSemStateFiniteExact.wordExp s (.const w) = some (.word w)) ∧
      (∀ (v : Nat) (s : WordSemStateFiniteExact width C F),
        WordSemStateFiniteExact.wordExp s (.var v) = WordSemStateFiniteExact.getVar v s) ∧
      (∀ (s : WordSemStateFiniteExact width C F) (name : WordStoreHOL),
        WordSemStateFiniteExact.wordExp s (.lookup name) = WordSemStateFiniteExact.getStore name s) ∧
      (∀ (s : WordSemStateFiniteExact width C F) (addr : WordLangExpHOL (BitVec width)),
        WordSemStateFiniteExact.wordExp s (.load addr) =
          match WordSemStateFiniteExact.wordExp s addr with
          | none => none
          | some (.word w) => WordSemStateFiniteExact.memLoad w s
          | some (.loc _ _) => none) ∧
      (∀ (wexps : List (WordLangExpHOL (BitVec width))) (s : WordSemStateFiniteExact width C F)
          (op : BinOp),
        WordSemStateFiniteExact.wordExp s (.op op wexps) =
          match theWords (wexps.map fun a => WordSemStateFiniteExact.wordExp s a) with
          | none => none
          | some ws => (wordOpHOL op ws).map WordLocW.word) ∧
      ∀ (wexp1 wexp : WordLangExpHOL (BitVec width)) (sh : Shift)
          (s : WordSemStateFiniteExact width C F),
        WordSemStateFiniteExact.wordExp s (.shift sh wexp wexp1) =
          match WordSemStateFiniteExact.wordExp s wexp, WordSemStateFiniteExact.wordExp s wexp1 with
          | none, _ => none
          | some (.word _), none => none
          | some (.word w), some (.word w1) => (wordShiftHOL sh w w1.toNat).map WordLocW.word
          | some (.word _), some (.loc _ _) => none
          | some (.loc _ _), _ => none) ∧
    (∀ (v : Nat) (x : WordLocW width) (s : WordSemStateFiniteExact width C F),
      WordSemStateFiniteExact.setVar v x s = { s with locals := sptInsert v x s.locals }) ∧
    (∀ (args : List (WordLocW width)) (size : Option Nat) (s : WordSemStateFiniteExact width C F),
      WordSemStateFiniteExact.callEnv args size s =
        { s with locals := sptFromList2 args, localsSize := size,
                 stackMax := wordSemOptionMax s.stackMax
                   (wordSemOptionAdd (wordSemStackSize s.stack) size) }) ∧
    (∀ (l : List V),
      sptFromList2 l = (l.foldl (fun (it : Nat × Spt V) (a : V) => (it.1 + 2, sptInsert it.1 a it.2))
        (0, .ln)).2) ∧
    (∀ (addr : BitVec width) (s : WordSemStateFiniteExact width C F),
      WordSemStateFiniteExact.memLoad addr s =
        if s.mdomain addr = true then some (s.memory addr) else none) ∧
    (∀ (dest : Option V) (args : List B),
      wordSemBadDestArgs dest args = true ↔ dest = none ∧ args = []) ∧
    ((∀ (s : WordSemStateFiniteExact width C F), WordSemStateFiniteExact.getVars [] s = some []) ∧
      ∀ (v : Nat) (vs : List Nat) (s : WordSemStateFiniteExact width C F),
        WordSemStateFiniteExact.getVars (v :: vs) s =
          match WordSemStateFiniteExact.getVar v s with
          | none => none
          | some x =>
              match WordSemStateFiniteExact.getVars vs s with
              | none => none
              | some xs => some (x :: xs)) ∧
    ((∀ (p : Nat) (args : List (WordLocW width)) (code : Spt (Nat × B)) (ssize : Spt C),
        wordSemFindCode (some p) args code ssize =
          match sptLookup p code with
          | none => none
          | some (arity, exp) =>
              if args.length = arity then some (args, exp, sptLookup p ssize) else none) ∧
      ∀ (args : List (WordLocW width)) (code : Spt (Nat × B)) (ssize : Spt C),
        wordSemFindCode none args code ssize =
          if h : args = [] then none
          else
            match args.getLast h with
            | .word _ => none
            | .loc loc 0 =>
                (match sptLookup loc code with
                 | none => none
                 | some (arity, exp) =>
                     if args.length = arity + 1 then
                       some (args.dropLast, exp, sptLookup loc ssize)
                     else none)
            | .loc _ (_ + 1) => none) ∧
    (∀ (xs : List (WordLocW width)) (n : B) (names : C) (retHandler : D) (l1 l2 : Nat),
      wordSemAddRetLoc (none : Option (B × C × D × Nat × Nat)) xs = xs ∧
        wordSemAddRetLoc (some (n, names, retHandler, l1, l2)) xs = .loc l1 l2 :: xs) ∧
    ((∀ (t : NumSet), sptListInsert [] t = t) ∧
      ∀ (n : Nat) (ns : List Nat) (t : NumSet),
        sptListInsert (n :: ns) t = sptListInsert ns (sptInsert n () t)) ∧
    (∀ (s : WordSemStateFiniteExact width C F),
      WordSemStateFiniteExact.decClock s = { s with clock := s.clock - 1 }) ∧
    (theWords ([] : List (Option (WordLocW width))) = some [] ∧
      ∀ (w : Option (WordLocW width)) (ws : List (Option (WordLocW width))),
        theWords (w :: ws) =
          match w, theWords ws with
          | none, _ => none
          | some (.word _), none => none
          | some (.word x), some xs => some (x :: xs)
          | some (.loc _ _), _ => none) ∧
    ∀ (op : BinOp) (ws : List (BitVec width)),
      wordOpHOL op ws =
        match op, ws with
        | .add, ws => some (ws.foldr (fun a b => a + b) 0)
        | .sub, [] => none
        | .sub, [_] => none
        | .sub, [w1, w2] => some (w1 - w2)
        | .sub, _ :: _ :: _ :: _ => none
        | .and, ws => some (ws.foldr (fun a b => a &&& b) (~~~ 0))
        | .or, ws => some (ws.foldr (fun a b => a ||| b) 0)
        | .xor, ws => some (ws.foldr (fun a b => a ^^^ b) 0) := by
  refine ⟨WordSemStateFiniteExact.evaluate_def_rebound, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro v s; rfl
  · intro k2 v t k1
    by_cases h : k1 = k2
    · subst h; simp [sptLookup_sptInsert_same]
    · simp [h, sptLookup_sptInsert_ne _ _ _ _ h]
  · exact ⟨fun _ _ => rfl, fun _ _ => rfl⟩
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> intro w1 w2 <;>
      simp [wordCmpHOL] <;> exact Iff.rfl
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro w s
      simp [WordSemStateFiniteExact.wordExp]
    · intro v s
      simp [WordSemStateFiniteExact.wordExp]
    · intro s name
      simp [WordSemStateFiniteExact.wordExp]
    · intro s addr
      simp only [WordSemStateFiniteExact.wordExp]
      rcases s.wordExp addr with _ | _ | _ <;> rfl
    · intro wexps s op
      simp only [WordSemStateFiniteExact.wordExp]
      rw [List.map_attach_eq_pmap, List.pmap_eq_map]
      cases theWords (List.map s.wordExp wexps) <;> rfl
    · intro wexp1 wexp sh s
      simp only [WordSemStateFiniteExact.wordExp]
      rcases s.wordExp wexp with _ | _ | _ <;> rcases s.wordExp wexp1 with _ | _ | _ <;> rfl
  · intro v x s; rfl
  · intro args size s; rfl
  · intro l; rfl
  · intro addr s; rfl
  · intro dest args
    cases dest <;> cases args <;> simp [wordSemBadDestArgs]
  · exact ⟨fun _ => rfl, fun _ _ _ => rfl⟩
  · refine ⟨fun _ _ _ _ => rfl, ?_⟩
    intro args code ssize
    by_cases h : args = []
    · subst h; rfl
    · simp only [wordSemFindCode, h, ↓reduceDIte]
      rcases args.getLast h with w | ⟨loc, _ | k⟩ <;> rfl
  · intro xs n names retHandler l1 l2
    exact ⟨rfl, rfl⟩
  · exact ⟨fun _ => rfl, fun _ _ _ => rfl⟩
  · intro s; rfl
  · refine ⟨rfl, ?_⟩
    intro w ws
    cases w with
    | none => rfl
    | some x => cases x <;> cases h : theWords ws <;> simp [theWords, h]
  · intro op ws
    cases op <;> rcases ws with _ | ⟨a, _ | ⟨b, _ | ⟨c, _⟩⟩⟩ <;> rfl

end Flapjack.Compiler.Backend.DataToWord.Proofs.Bignum
