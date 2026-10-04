import Flapjack.Compiler.Backend.Semantics.WordSem.Env

/-!
# Exact HOL `wordSem` call and loop helpers

Counterpart of `cakeml/compiler/backend/semantics/wordSemScript.sml:946-1014`
(bead `flapjack-h29l.7`).  It covers the helpers used by `evaluate_def`:
`add_ret_loc`, `bad_dest_args`, the local `termdep_rw` and
`fix_clock_IMP_LESS_EQ`, `MustTerminate_limit` (tagged under the
`word_dimension_as_width` qualifier), `const_addresses`, `const_writes`, `STOP`,
`bad_fun_return`, `cont_loop`, and `exit_loop`.
The carrier translations are those of the tagged `state` port.

HOL `bytes_in_word = n2w (dimindex (:'a) DIV 8)` (HOL
`src/n-bit/byteScript.sml`, outside `cakeml/`) is the untagged helper
`wordSemBytesInWord`.
-/

namespace Flapjack

namespace WordSemCallHelpersSupport

/-- Same-module canonical finite-support witness for the `fpRegs`/`store`
    fields named by the tagged state lemmas of this module. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} [NeZero width] {C : Type} {F : Type} :
    (∀ (state : WordSemStateBroad width C F) (h : state.FiniteSupport),
        (WordSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : WordSemStateFiniteExact width C F,
        WordSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  WordSemStateExact.holFmapAsFiniteSupportWitness

end WordSemCallHelpersSupport

/-- HOL `bytes_in_word_def` (`HOL/src/n-bit/byteScript.sml:193-195`):
    `bytes_in_word = n2w (dimindex (:'a) DIV 8) : 'a word`, with `dimindex (:'a)` the
    positive word width.  The other Flapjack renderings (`StackRemove.bytesInWord`,
    `bytesInWordHOL`, `panBytesInWord`) are untagged copies with the same body. -/
@[hol "HOL/src/n-bit/byteScript.sml" "bytes_in_word_def" (words_as_type_indexed_bitvec)]
def wordSemBytesInWord {width : Nat} [NeZero width] : BitVec width :=
  BitVec.ofNat width (width / 8)

/-- Exact HOL `add_ret_loc_def` (`wordSemScript.sml:946-949`):
    `add_ret_loc NONE xs = xs` and
    `add_ret_loc (SOME (n,names,ret_handler,l1,l2)) xs = Loc l1 l2 :: xs`.  The
    first three return-metadata fields have independent arbitrary HOL types;
    the function observes only the two numeric labels. These metadata types
    are independent of the word dimension carried by `xs`. -/
@[hol "cakeml/compiler/backend/semantics/wordSemScript.sml" "add_ret_loc_def"
  (words_as_type_indexed_bitvec)]
def wordSemAddRetLoc {width : Nat} [NeZero width]
    {ReturnValue ReturnNames ReturnHandler : Type} :
    Option (ReturnValue × ReturnNames × ReturnHandler × Nat × Nat) →
      List (WordLocW width) → List (WordLocW width)
  | none, xs => xs
  | some (_, _, _, l1, l2), xs => .loc l1 l2 :: xs

/-- Exact HOL `bad_dest_args_def` (`wordSemScript.sml:952-954`):
    `bad_dest_args dest args ⇔ dest = NONE ∧ args = []`. -/
@[hol "cakeml/compiler/backend/semantics/wordSemScript.sml" "bad_dest_args_def"]
def wordSemBadDestArgs (dest : Option Nat) (args : List Nat) : Bool :=
  decide (dest = none ∧ args = [])

namespace WordSemStateFiniteExact

/-- Exact HOL local `termdep_rw` (`wordSemScript.sml:956-962`).  `call_env`,
    `dec_clock`, and `set_var` all preserve `termdep`. -/
@[hol "cakeml/compiler/backend/semantics/wordSemScript.sml" "termdep_rw"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem termdep_rw {width : Nat} [NeZero width] {C : Type} {F : Type}
    (p_1 : List (WordLocW width)) (ss : Option Nat) (s : WordSemStateFiniteExact width C F)
    (n : Nat) (v : WordLocW width) :
    (callEnv p_1 ss s).termdep = s.termdep ∧ (decClock s).termdep = s.termdep ∧
      (setVar n v s).termdep = s.termdep :=
  ⟨rfl, rfl, rfl⟩

/-- Exact HOL local `fix_clock_IMP_LESS_EQ` (`wordSemScript.sml:964-968`):
    `∀x. fix_clock s x = (res,s1) ⇒ s1.clock ≤ s.clock ∧ s1.termdep =
    s.termdep`, where `res` and `s1` are free in HOL and bound here. -/
@[hol "cakeml/compiler/backend/semantics/wordSemScript.sml" "fix_clock_IMP_LESS_EQ"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem fixClock_IMP_LESS_EQ {width : Nat} [NeZero width] {C : Type} {F : Type} {β : Type}
    (s : WordSemStateFiniteExact width C F) (res : β) (s1 : WordSemStateFiniteExact width C F) :
    ∀ x, fixClock s x = (res, s1) → s1.clock ≤ s.clock ∧ s1.termdep = s.termdep := by
  intro x h
  simp only [fixClock, Prod.mk.injEq] at h
  obtain ⟨_, rfl⟩ := h
  refine ⟨?_, rfl⟩
  dsimp only
  split <;> omega

end WordSemStateFiniteExact

/-- Exact HOL `MustTerminate_limit_def` (`wordSemScript.sml:970-978`, `[nocompute]`):
    `2 * dimword (:'a) + dimword (:'a) * dimword (:'a) + dimword (:'a) **
    dimword (:'a) + dimword (:'a) ** dimword (:'a) ** dimword (:'a)`.  Here
    `dimword (:'a) = 2 ^ width`, and HOL `**` is right-associative like Lean
    `^`.  As in HOL, the number is a specification constant and is never
    evaluated.  The HOL row `must_terminate_limit_1=28` of
    `word_sem_call_helpers_probe.out` is checked in
    `Flapjack.Test.WordSemCallHelpersParity`.

    The HOL type argument `(:'a)` is used only through `dimword (:'a)` as a
    Nat; Lean names that dimension with the explicit `width : Nat` binder and
    retains `[NeZero width]`. This is the word-free dimension translation
    `word_dimension_as_width`, not a claim that this signature carries a word.
    The equation is otherwise unchanged; direct HOL row `must_terminate_limit_1`
    in `word_sem_call_helpers_probe.out` is checked by
    `Flapjack.Test.WordSemCallHelpersParity`. -/
@[hol "cakeml/compiler/backend/semantics/wordSemScript.sml" "MustTerminate_limit_def"
  (word_dimension_as_width := width)]
def wordSemMustTerminateLimit (width : Nat) [NeZero width] : Nat :=
  let dimword := (2 : Nat) ^ width
  2 * dimword + dimword * dimword + dimword ^ dimword + dimword ^ (dimword ^ dimword)

/-- Exact HOL `const_addresses_def` (`wordSemScript.sml:980-984`):
    `const_addresses a [] d = T` and
    `const_addresses a (x::xs) d = (a IN d ∧ const_addresses (a +
    bytes_in_word) xs d)`.  The `'a word set` uses the set-as-Bool rendering. -/
@[hol "cakeml/compiler/backend/semantics/wordSemScript.sml" "const_addresses_def"
  (words_as_type_indexed_bitvec)]
def wordSemConstAddresses {width : Nat} [NeZero width] :
    BitVec width → List (Bool × BitVec width) → (BitVec width → Bool) → Bool
  | _, [], _ => true
  | a, _ :: xs, d => d a && wordSemConstAddresses (a + wordSemBytesInWord) xs d

/-- Exact HOL `const_writes_def` (`wordSemScript.sml:986-991`):
    `const_writes a off [] m = m` and
    `const_writes a off ((b,x)::xs) m = const_writes (a + bytes_in_word) off xs
    ((a =+ Word (if b then x + off else x)) m)`. -/
@[hol "cakeml/compiler/backend/semantics/wordSemScript.sml" "const_writes_def"
  (words_as_type_indexed_bitvec)]
def wordSemConstWrites {width : Nat} [NeZero width] :
    BitVec width → BitVec width → List (Bool × BitVec width) →
      (BitVec width → WordLocW width) → BitVec width → WordLocW width
  | _, _, [], m => m
  | a, off, (b, x) :: xs, m =>
      wordSemConstWrites (a + wordSemBytesInWord) off xs
        (fun addr => if addr = a then .word (if b then x + off else x) else m addr)

/-- Exact HOL `STOP_def` (`wordSemScript.sml:993-995`): `STOP x = x`. -/
@[hol "cakeml/compiler/backend/semantics/wordSemScript.sml" "STOP_def"]
def wordSemSTOP {α : Type} (x : α) : α := x

/-- Exact HOL `bad_fun_return_def` (`wordSemScript.sml:997-1002`): `NONE`,
    `SOME (Break _)` and `SOME (Continue _)` are bad returns; every other
    result is not. -/
@[hol "cakeml/compiler/backend/semantics/wordSemScript.sml" "bad_fun_return_def"
  (words_as_type_indexed_bitvec)]
def wordSemBadFunReturn {width : Nat} [NeZero width] : Option (WordSemResult width) → Bool
  | none => true
  | some (.break _) => true
  | some (.continue _) => true
  | _ => false

/-- Exact HOL `cont_loop_def` (`wordSemScript.sml:1004-1008`):
    `cont_loop NONE = T`, `cont_loop (SOME (Continue n)) = (n = 0)` and
    `cont_loop _ = F`. -/
@[hol "cakeml/compiler/backend/semantics/wordSemScript.sml" "cont_loop_def"
  (words_as_type_indexed_bitvec)]
def wordSemContLoop {width : Nat} [NeZero width] : Option (WordSemResult width) → Bool
  | none => true
  | some (.continue n) => decide (n = 0)
  | _ => false

/-- Exact HOL `exit_loop_def` (`wordSemScript.sml:1010-1014`): decrement the
    label of `SOME (Break n)` and `SOME (Continue n)` (`num` monus), and leave
    every other result unchanged. -/
@[hol "cakeml/compiler/backend/semantics/wordSemScript.sml" "exit_loop_def"
  (words_as_type_indexed_bitvec)]
def wordSemExitLoop {width : Nat} [NeZero width] :
    Option (WordSemResult width) → Option (WordSemResult width)
  | some (.break n) => some (.break (n - 1))
  | some (.continue n) => some (.continue (n - 1))
  | res => res

end Flapjack
