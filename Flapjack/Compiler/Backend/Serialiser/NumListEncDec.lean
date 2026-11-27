module

public import Flapjack.Misc.AppList
public import Flapjack.Basis.Pure.MlString
public import Flapjack.Misc.Sptree.Wf

@[expose] public section

/-!
# Encoder/decoder well-formedness for natural-number list prefixes

Counterparts of the `dec_ok` / `enc_dec_ok` / `enc_dec_ok'` predicates and the
first helper theorems of
`cakeml/compiler/backend/serialiser/num_list_enc_decScript.sml`. HOL's `##` pair
map is Lean's `Prod.map` and HOL `∘` is composition.
-/

namespace Flapjack.Compiler.Backend.Serialiser

-- Public declarations below use private helpers.
set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

open Flapjack
open Flapjack.Basis.Pure.MlString

/-- Original `dec_ok_def`: a decoder never returns more input than it consumed. -/
@[hol "cakeml/compiler/backend/serialiser/num_list_enc_decScript.sml" "dec_ok_def"]
def decOk {α : Type} (dec : List Nat → α × List Nat) : Prop :=
  ∀ i, (dec i).2.length ≤ i.length

/-- Original `enc_dec_ok_def`: the decoder inverts the encoder on any suffix. -/
@[hol "cakeml/compiler/backend/serialiser/num_list_enc_decScript.sml" "enc_dec_ok_def"]
def encDecOk {α : Type} (enc : α → AppList Nat) (dec : List Nat → α × List Nat) : Prop :=
  decOk dec ∧ ∀ x xs, dec (appListAppend (enc x) ++ xs) = (x, xs)

/-- Original `dec_ok_simp`: mapping the decoded value does not change the bound. -/
@[hol "cakeml/compiler/backend/serialiser/num_list_enc_decScript.sml" "dec_ok_simp"]
theorem decOk_comp_map {α β : Type} (f : β → α) (d : List Nat → β × List Nat) :
    decOk (fun i => Prod.map f id (d i)) ↔ decOk d := by
  simp [decOk, Prod.map]

/-- Original `enc_dec_ok_o`: composing the encoder with a left inverse keeps the
    round trip. -/
@[hol "cakeml/compiler/backend/serialiser/num_list_enc_decScript.sml" "enc_dec_ok_o"]
theorem encDecOk_comp {α β : Type} (e : α → AppList Nat) (d : List Nat → α × List Nat)
    (f : α → β) (g : β → α) (premise : encDecOk e d ∧ ∀ x, f (g x) = x) :
    encDecOk (fun x => e (g x)) (fun i => Prod.map f id (d i)) := by
  obtain ⟨⟨dec, roundtrip⟩, inverse⟩ := premise
  refine ⟨?_, ?_⟩
  · simpa [decOk, Prod.map] using dec
  · intro x xs
    simp only [Prod.map, id]
    rw [roundtrip (g x) xs, inverse]

/-- Original `enc_dec_ok'_def`: the conditional form of the round trip. -/
@[hol "cakeml/compiler/backend/serialiser/num_list_enc_decScript.sml" "enc_dec_ok'_def"]
def encDecOkPrime {α : Type} (p : α → Bool) (enc : α → AppList Nat)
    (dec : List Nat → α × List Nat) : Prop :=
  decOk dec ∧ ∀ x xs, p x = true → dec (appListAppend (enc x) ++ xs) = (x, xs)

/-- Original `IMP_enc_dec_ok`: an unconditional round trip is the total case. -/
@[hol "cakeml/compiler/backend/serialiser/num_list_enc_decScript.sml" "IMP_enc_dec_ok"]
theorem encDecOk_imp_prime {α : Type} (enc : α → AppList Nat) (dec : List Nat → α × List Nat)
    (ok : encDecOk enc dec) : encDecOkPrime (fun _ => true) enc dec := by
  obtain ⟨bound, roundtrip⟩ := ok
  refine ⟨bound, ?_⟩
  intro x xs _
  exact roundtrip x xs

/-- Original `enc_dec_ok'_IMP`: the total conditional round trip is unconditional. -/
@[hol "cakeml/compiler/backend/serialiser/num_list_enc_decScript.sml" "enc_dec_ok'_IMP"]
theorem encDecOkPrime_imp {α : Type} (enc : α → AppList Nat) (dec : List Nat → α × List Nat)
    (ok : encDecOkPrime (fun _ => true) enc dec) : encDecOk enc dec := by
  obtain ⟨bound, roundtrip⟩ := ok
  exact ⟨bound, fun x xs => roundtrip x xs rfl⟩

/-- Original `const_dec_def`: a decoder that returns a fixed value. -/
@[hol "cakeml/compiler/backend/serialiser/num_list_enc_decScript.sml" "const_dec_def"]
def constDec {α : Type} (a : α) (xs : List Nat) : α × List Nat := (a, xs)

/-- Original `enc_dec_ok'_const`: the constant decoder accepts its own value. -/
@[hol "cakeml/compiler/backend/serialiser/num_list_enc_decScript.sml" "enc_dec_ok'_const"]
theorem encDecOkPrime_const {α : Type} [DecidableEq α] (x : α) :
    encDecOkPrime (fun y => decide (y = x)) (fun _ => AppList.list []) (constDec x) := by
  refine ⟨?_, ?_⟩
  · intro i
    simp [constDec]
  · intro y xs guard
    have same : y = x := by simpa using guard
    subst same
    simp [constDec, appListAppend, appendAux]

/-- Original `enc_dec_ok'_o`: the conditional round trip survives composition. -/
@[hol "cakeml/compiler/backend/serialiser/num_list_enc_decScript.sml" "enc_dec_ok'_o"]
theorem encDecOkPrime_comp {α β : Type} (p : α → Bool) (e : α → AppList Nat)
    (d : List Nat → α × List Nat) (f : α → β) (g : β → α)
    (premise : encDecOkPrime p e d ∧ ∀ x, f (g x) = x) :
    encDecOkPrime (fun x => p (g x)) (fun x => e (g x)) (fun i => Prod.map f id (d i)) := by
  obtain ⟨⟨bound, roundtrip⟩, inverse⟩ := premise
  refine ⟨?_, ?_⟩
  · simpa [decOk, Prod.map] using bound
  · intro x xs guard
    have step := roundtrip (g x) xs guard
    simp only [Prod.map, id]
    rw [step, inverse]

/-- Original `fix_res_def`: keep whichever input list is shorter. -/
@[hol "cakeml/compiler/backend/serialiser/num_list_enc_decScript.sml" "fix_res_def"]
def fixRes {α β : Type} (ns : List β) (result : α × List β) : α × List β :=
  if ns.length < result.2.length then (result.1, ns) else result

/-- Original `fix_res_IMP`: the returned suffix is no longer than the input. -/
@[hol "cakeml/compiler/backend/serialiser/num_list_enc_decScript.sml" "fix_res_IMP"]
theorem fixRes_bound {α β : Type} (ns1 : List β) (y : α × List β) (x : α) (ns2 : List β)
    (h : (x, ns2) = fixRes ns1 y) : ns2.length ≤ ns1.length := by
  obtain ⟨value, rest⟩ := y
  simp only [fixRes] at h
  split at h
  · obtain ⟨_, rfl⟩ := h
    omega
  · obtain ⟨_, rfl⟩ := h
    omega

/-- Original `unit_enc_def`: the unit encoder emits nothing. -/
@[hol "cakeml/compiler/backend/serialiser/num_list_enc_decScript.sml" "unit_enc_def"]
def unitEnc {α : Type} : Unit → AppList α := fun _ => AppList.list []

/-- Original `unit_dec_def`: the unit decoder consumes nothing. -/
@[hol "cakeml/compiler/backend/serialiser/num_list_enc_decScript.sml" "unit_dec_def"]
def unitDec (ns : List Nat) : Unit × List Nat := ((), ns)

/-- Original `unit_enc_dec_ok`. -/
@[hol "cakeml/compiler/backend/serialiser/num_list_enc_decScript.sml" "unit_enc_dec_ok"]
theorem unitEncDecOk : encDecOk unitEnc unitDec := by
  refine ⟨?_, ?_⟩
  · intro i
    simp [unitDec]
  · intro x xs
    simp [unitEnc, unitDec, appListAppend, appendAux]

/-- Original `num_enc_def`: one number per value. -/
@[hol "cakeml/compiler/backend/serialiser/num_list_enc_decScript.sml" "num_enc_def"]
def numEnc (n : Nat) : AppList Nat := AppList.list [n]

/-- Original `num_dec_def`: read one number, defaulting to zero. -/
@[hol "cakeml/compiler/backend/serialiser/num_list_enc_decScript.sml" "num_dec_def"]
def numDec : List Nat → Nat × List Nat
  | [] => (0, [])
  | r :: rs => (r, rs)

/-- Original `num_enc_dec_ok`. -/
@[hol "cakeml/compiler/backend/serialiser/num_list_enc_decScript.sml" "num_enc_dec_ok"]
theorem numEncDecOk : encDecOk numEnc numDec := by
  refine ⟨?_, ?_⟩
  · intro i
    cases i with
    | nil => simp [numDec]
    | cons r rs => simp [numDec]
  · intro x xs
    simp [numEnc, numDec, appListAppend, appendAux]

/-- Original `word64_enc_def`: one word per value. -/
@[hol "cakeml/compiler/backend/serialiser/num_list_enc_decScript.sml" "word64_enc_def"]
def word64Enc (w : BitVec 64) : AppList Nat := AppList.list [w.toNat]

/-- Original `word64_dec_def`: read one word, defaulting to zero. -/
@[hol "cakeml/compiler/backend/serialiser/num_list_enc_decScript.sml" "word64_dec_def"]
def word64Dec : List Nat → BitVec 64 × List Nat
  | [] => (0, [])
  | r :: rs => (BitVec.ofNat 64 r, rs)

/-- Original `word64_enc_dec_ok`. -/
@[hol "cakeml/compiler/backend/serialiser/num_list_enc_decScript.sml" "word64_enc_dec_ok"]
theorem word64EncDecOk : encDecOk word64Enc word64Dec := by
  refine ⟨?_, ?_⟩
  · intro i
    cases i with
    | nil => simp [word64Dec]
    | cons r rs => simp [word64Dec]
  · intro x xs
    simp [word64Enc, word64Dec, appListAppend, appendAux]

/-- Original `bool_enc_def`: encode a boolean as one number. -/
@[hol "cakeml/compiler/backend/serialiser/num_list_enc_decScript.sml" "bool_enc_def"]
def boolEnc : Bool → AppList Nat := fun b => numEnc (if b then 1 else 0)

/-- Original `bool_dec_def`: decode a boolean from one number. -/
@[hol "cakeml/compiler/backend/serialiser/num_list_enc_decScript.sml" "bool_dec_def"]
def boolDec : List Nat → Bool × List Nat :=
  fun ns => Prod.map (fun r => decide (r = 1)) id (numDec ns)

/-- Original `bool_enc_dec_ok`. -/
@[hol "cakeml/compiler/backend/serialiser/num_list_enc_decScript.sml" "bool_enc_dec_ok"]
theorem boolEncDecOk : encDecOk boolEnc boolDec := by
  have inverse : ∀ x : Bool, decide ((if x = true then 1 else 0) = 1) = x := by
    intro x
    cases x with
    | true => rfl
    | false => rfl
  have step := encDecOk_comp (e := numEnc) (d := numDec) (f := fun r => decide (r = 1))
    (g := fun b => if b = true then 1 else 0) ⟨numEncDecOk, inverse⟩
  exact step

/-- The integer-to-number half of HOL's `int_enc`. -/
private def intEncNat (x : Int) : Nat :=
  if x < 0 then 2 * x.natAbs + 1 else 2 * x.natAbs

/-- The number-to-integer half of HOL's `int_dec`. -/
private def intDecInt (r : Nat) : Int :=
  if r % 2 = 1 then -((r / 2 : Nat) : Int) else ((r / 2 : Nat) : Int)

/-- Original `int_enc_def`: zig-zag encoding of integers as numbers. -/
@[hol "cakeml/compiler/backend/serialiser/num_list_enc_decScript.sml" "int_enc_def"]
def intEnc : Int → AppList Nat := fun n => numEnc (intEncNat n)

/-- Original `int_dec_def`: zig-zag decoding of numbers as integers. -/
@[hol "cakeml/compiler/backend/serialiser/num_list_enc_decScript.sml" "int_dec_def"]
def intDec : List Nat → Int × List Nat := fun ns => Prod.map intDecInt id (numDec ns)

private theorem intDecInt_intEncNat (x : Int) : intDecInt (intEncNat x) = x := by
  unfold intEncNat intDecInt
  cases x with
  | ofNat n =>
    have notNeg : ¬ (↑n : Int) < 0 := by simp
    have even : (2 * n) % 2 ≠ 1 := by omega
    have half : (2 * n) / 2 = n := by omega
    simp only [Int.ofNat_eq_natCast, notNeg, if_false, Int.natAbs_natCast, even, half]
  | negSucc n =>
    have neg : Int.negSucc n < 0 := by omega
    have odd : (2 * (n + 1) + 1) % 2 = 1 := by omega
    have half : (2 * (n + 1) + 1) / 2 = n + 1 := by omega
    simp only [neg, if_true, Int.natAbs_negSucc, odd, half]
    rfl

/-- Original `int_enc_dec_ok`. -/
@[hol "cakeml/compiler/backend/serialiser/num_list_enc_decScript.sml" "int_enc_dec_ok"]
theorem intEncDecOk : encDecOk intEnc intDec := by
  have inverse : ∀ x : Int, intDecInt (intEncNat x) = x := intDecInt_intEncNat
  have step := encDecOk_comp (e := numEnc) (d := numDec) (f := intDecInt) (g := intEncNat)
    ⟨numEncDecOk, inverse⟩
  exact step

/-- Original `list_enc_def`: a length prefix followed by the element encodings. -/
@[hol "cakeml/compiler/backend/serialiser/num_list_enc_decScript.sml" "list_enc_def"]
def listEnc {α : Type} (e : α → AppList Nat) (xs : List α) : AppList Nat :=
  AppList.append (AppList.list [xs.length])
    (xs.foldr (fun x acc => AppList.append (e x) acc) (AppList.list []))

/-- Original `list_dec'_def`: decode `k` elements, threading the input. -/
@[hol "cakeml/compiler/backend/serialiser/num_list_enc_decScript.sml" "list_dec'_def"]
def listDecAux {α : Type} :
    Nat → (List Nat → α × List Nat) → List Nat → List α × List Nat
  | 0, _, ns => ([], ns)
  | k + 1, d, ns =>
      let step := d ns
      let rest := listDecAux k d step.2
      (step.1 :: rest.1, rest.2)

/-- Original `list_dec_def`: read the length prefix, then that many elements. -/
@[hol "cakeml/compiler/backend/serialiser/num_list_enc_decScript.sml" "list_dec_def"]
def listDec {α : Type} (d : List Nat → α × List Nat) :
    List Nat → List α × List Nat
  | [] => ([], [])
  | n :: ns => listDecAux n d ns

/-- Original `list_dec'_length`: decoding never grows the input. -/
@[hol "cakeml/compiler/backend/serialiser/num_list_enc_decScript.sml" "list_dec'_length"]
theorem listDecAux_length {α : Type} (k : Nat) (d : List Nat → α × List Nat)
    (ns : List Nat) (x : List α) (ns1 : List Nat)
    (premise : listDecAux k d ns = (x, ns1) ∧ decOk d) : ns1.length ≤ ns.length := by
  obtain ⟨run, bound⟩ := premise
  induction k generalizing ns x ns1 with
  | zero =>
    simp only [listDecAux, Prod.mk.injEq] at run
    obtain ⟨_, rfl⟩ := run
    omega
  | succ k ih =>
    simp only [listDecAux] at run
    generalize headRun : d ns = headResult at run
    rcases headResult with ⟨value, rest⟩
    generalize tailRun : listDecAux k d rest = tailResult at run
    rcases tailResult with ⟨values, final⟩
    simp only [Prod.mk.injEq] at run
    obtain ⟨_, rfl⟩ := run
    have headBound := bound ns
    rw [headRun] at headBound
    dsimp only at headBound
    have tailBound := ih rest values final tailRun
    omega

/-- Original `list_dec_ok`: decoding a list keeps the decoder bound. -/
@[hol "cakeml/compiler/backend/serialiser/num_list_enc_decScript.sml" "list_dec_ok"]
theorem listDecOk {α : Type} (d : List Nat → α × List Nat) (bound : decOk d) :
    decOk (listDec d) := by
  intro i
  cases i with
  | nil => simp [listDec]
  | cons n ns =>
    simp only [listDec, List.length_cons]
    generalize run : listDecAux n d ns = result
    rcases result with ⟨values, final⟩
    have step := listDecAux_length n d ns values final ⟨run, bound⟩
    dsimp only
    omega

/-- Appending two trees flattens to the concatenation of their flattens. -/
private theorem appListAppend_append {α : Type} (left right : AppList α) :
    appListAppend (AppList.append left right) = appListAppend left ++ appListAppend right := by
  simp only [appListAppend]
  exact appendAux_thm left (appendAux right [])

/-- The element encodings flatten to a prefix followed by the suffix. -/
private theorem listFoldr_append {α : Type} (e : α → AppList Nat) (xs : List α)
    (ys : List Nat) :
    appListAppend (xs.foldr (fun x acc => AppList.append (e x) acc) (AppList.list [])) ++ ys
      = xs.foldr (fun x acc => appListAppend (e x) ++ acc) ys := by
  induction xs with
  | nil => simp [appListAppend, appendAux]
  | cons x xs ih =>
    simp only [List.foldr_cons, appListAppend_append]
    rw [List.append_assoc, ih]

/-- The decoded list consumes exactly its encodings, given the element round trip. -/
private theorem listDecAux_foldr {α : Type} (e : α → AppList Nat)
    (d : List Nat → α × List Nat) (roundtrip : ∀ x ys, d (appListAppend (e x) ++ ys) = (x, ys))
    (xs : List α) (ys : List Nat) :
    listDecAux xs.length d
      (appListAppend (xs.foldr (fun x acc => AppList.append (e x) acc) (AppList.list [])) ++ ys)
      = (xs, ys) := by
  induction xs generalizing ys with
  | nil => simp [listDecAux, appListAppend, appendAux]
  | cons x xs ih =>
    rw [List.length_cons, List.foldr_cons, appListAppend_append]
    simp only [List.append_assoc, listDecAux, roundtrip]
    rw [ih ys]

/-- Original `list_enc_dec_ok`: list encodings round trip. -/
@[hol "cakeml/compiler/backend/serialiser/num_list_enc_decScript.sml" "list_enc_dec_ok"]
theorem listEncDecOk {α : Type} (e : α → AppList Nat) (d : List Nat → α × List Nat)
    (ok : encDecOk e d) : encDecOk (listEnc e) (listDec d) := by
  obtain ⟨bound, roundtrip⟩ := ok
  refine ⟨listDecOk d bound, ?_⟩
  intro xs ys
  simp only [listEnc, appListAppend, appendAux]
  rw [List.append_assoc, List.singleton_append]
  exact listDecAux_foldr e d roundtrip xs ys

/-! ## Word, character, string, mlstring, product, option and sum codecs -/

/-- HOL `ORD`: the code of a character.  Untagged infrastructure for the
    character codecs below. -/
def holOrd (c : HolChar) : Nat := c.toNat

/-- HOL `CHR`: the character with the given code, reduced modulo 256.
    Untagged infrastructure. -/
def holChr (n : Nat) : HolChar := BitVec.ofNat 8 n

/-- Original `word_enc_def`: one word per value. -/
@[hol "cakeml/compiler/backend/serialiser/num_list_enc_decScript.sml" "word_enc_def"
  (words_as_type_indexed_bitvec)]
def wordEnc {width : Nat} [NeZero width] : BitVec width → AppList Nat :=
  fun w => numEnc (BitVec.toNat w)

/-- Original `word_dec_def`: read one word and map it back to the word type. -/
@[hol "cakeml/compiler/backend/serialiser/num_list_enc_decScript.sml" "word_dec_def"
  (words_as_type_indexed_bitvec)]
def wordDec {width : Nat} [NeZero width] : List Nat → BitVec width × List Nat :=
  fun ns => Prod.map (fun n => BitVec.ofNat width n) id (numDec ns)

/-- Original `word_enc_dec_ok`. -/
@[hol "cakeml/compiler/backend/serialiser/num_list_enc_decScript.sml" "word_enc_dec_ok"
  (words_as_type_indexed_bitvec)]
theorem wordEncDecOk {width : Nat} [NeZero width] :
    encDecOk (wordEnc : BitVec width → AppList Nat)
      (wordDec : List Nat → BitVec width × List Nat) := by
  have inverse : ∀ x : BitVec width, BitVec.ofNat width x.toNat = x := by
    intro x
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt x.isLt]
  exact encDecOk_comp (e := numEnc) (d := numDec) (f := fun n => BitVec.ofNat width n)
    (g := BitVec.toNat) ⟨numEncDecOk, inverse⟩

/-- Original `char_enc_def`: a character as its code. -/
@[hol "cakeml/compiler/backend/serialiser/num_list_enc_decScript.sml" "char_enc_def"]
def charEnc : HolChar → AppList Nat := fun c => numEnc (holOrd c)

/-- Original `safe_chr_def`: the character with the given code modulo 256. -/
@[hol "cakeml/compiler/backend/serialiser/num_list_enc_decScript.sml" "safe_chr_def"]
def safeChr (n : Nat) : HolChar := holChr (n % 256)

/-- Original `char_dec_def`: decode a character from its code. -/
@[hol "cakeml/compiler/backend/serialiser/num_list_enc_decScript.sml" "char_dec_def"]
def charDec : List Nat → HolChar × List Nat :=
  fun ns => Prod.map safeChr id (numDec ns)

/-- Original `char_enc_dec_ok`. -/
@[hol "cakeml/compiler/backend/serialiser/num_list_enc_decScript.sml" "char_enc_dec_ok"]
theorem charEncDecOk : encDecOk charEnc charDec := by
  have inverse : ∀ x : HolChar, safeChr (holOrd x) = x := by
    intro x
    have mod : x.toNat % 256 = x.toNat := Nat.mod_eq_of_lt x.isLt
    simp only [safeChr, holOrd, holChr, mod]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt x.isLt]
  exact encDecOk_comp (e := numEnc) (d := numDec) (f := safeChr) (g := holOrd)
    ⟨numEncDecOk, inverse⟩

/-- Original `safe_chr_list_def`: map the safe character code over a list. -/
@[hol "cakeml/compiler/backend/serialiser/num_list_enc_decScript.sml" "safe_chr_list_def"]
def safeChrList (ns : List Nat) : List HolChar := ns.map safeChr

/-- Original `take_pad_def`: take `n` numbers, padding short input with zero. -/
@[hol "cakeml/compiler/backend/serialiser/num_list_enc_decScript.sml" "take_pad_def"]
def takePad : Nat → List Nat → List Nat × List Nat
  | 0, ns => ([], ns)
  | n + 1, [] =>
      let rest := takePad n []
      (0 :: rest.1, rest.2)
  | n + 1, x :: xs =>
      let rest := takePad n xs
      (x :: rest.1, rest.2)

/-- Original `string_dec_def`: decode a string from a length prefix. -/
@[hol "cakeml/compiler/backend/serialiser/num_list_enc_decScript.sml" "string_dec_def"]
def stringDec : List Nat → List HolChar × List Nat
  | [] => ([], [])
  | n :: ns =>
      let step := takePad n ns
      (safeChrList step.1, step.2)

private theorem listDecAux_charDec (k : Nat) (ns : List Nat) :
    listDecAux k charDec ns = ((takePad k ns).1.map safeChr, (takePad k ns).2) := by
  induction k generalizing ns with
  | zero => simp [listDecAux, takePad]
  | succ k ih =>
    cases ns with
    | nil =>
      simp only [listDecAux, takePad, charDec, numDec, Prod.map, id, List.map_cons]
      rw [ih []]
    | cons x xs =>
      simp only [listDecAux, takePad, charDec, numDec, Prod.map, List.map_cons, id]
      rw [ih xs]

/-- Original `string_dec_thm`: string decoding is list decoding of characters. -/
@[hol "cakeml/compiler/backend/serialiser/num_list_enc_decScript.sml" "string_dec_thm"]
theorem stringDec_thm : stringDec = listDec charDec := by
  funext ns
  cases ns with
  | nil => rfl
  | cons n ns =>
    simp only [stringDec, listDec, safeChrList]
    rw [listDecAux_charDec]

/-- Original `string_enc_dec_ok`. -/
@[hol "cakeml/compiler/backend/serialiser/num_list_enc_decScript.sml" "string_enc_dec_ok"]
theorem stringEncDecOk : encDecOk (listEnc charEnc) stringDec := by
  rw [stringDec_thm]
  exact listEncDecOk charEnc charDec charEncDecOk

/-- Original `string_dec_ok`. -/
@[hol "cakeml/compiler/backend/serialiser/num_list_enc_decScript.sml" "string_dec_ok"]
theorem stringDecOk : decOk stringDec := stringEncDecOk.1

/-- Original `mlstring_enc_def`: encode a string by its characters. -/
@[hol "cakeml/compiler/backend/serialiser/num_list_enc_decScript.sml" "mlstring_enc_def"]
def mlstringEnc : MlString → AppList Nat
  | .implode s => listEnc charEnc s

/-- Original `mlstring_dec_def`: decode a string by its characters. -/
@[hol "cakeml/compiler/backend/serialiser/num_list_enc_decScript.sml" "mlstring_dec_def"]
def mlstringDec : List Nat → MlString × List Nat :=
  fun ns => Prod.map MlString.implode id (listDec charDec ns)

/-- Original `mlstring_enc_dec_ok`. -/
@[hol "cakeml/compiler/backend/serialiser/num_list_enc_decScript.sml" "mlstring_enc_dec_ok"]
theorem mlstringEncDecOk : encDecOk mlstringEnc mlstringDec := by
  obtain ⟨bound, roundtrip⟩ := listEncDecOk charEnc charDec charEncDecOk
  refine ⟨?_, ?_⟩
  · intro i
    exact bound i
  · intro x xs
    cases x with
    | implode s => simp [mlstringEnc, mlstringDec, roundtrip]

/-- Original `mlstring_dec_ok`. -/
@[hol "cakeml/compiler/backend/serialiser/num_list_enc_decScript.sml" "mlstring_dec_ok"]
theorem mlstringDecOk : decOk mlstringDec := mlstringEncDecOk.1

/-- The second component of a mapped pair is the original second component. -/
private theorem prodMap_snd {α β : Type} (f : α → β) (p : α × List Nat) :
    (Prod.map f id p).2 = p.2 := by
  obtain ⟨a, b⟩ := p
  rfl

/-- Flattening a single-element tree and appending a suffix. -/
private theorem appListAppend_single (n : Nat) (xs : List Nat) :
    appListAppend (AppList.list [n]) ++ xs = n :: xs := by
  simp only [appListAppend, appendAux, List.nil_append, List.cons_append]

/-- Flattening a tagged tree and appending a suffix. -/
private theorem appListAppend_cons (n : Nat) (rest : AppList Nat) (xs : List Nat) :
    appListAppend (AppList.append (AppList.list [n]) rest) ++ xs
      = n :: (appListAppend rest ++ xs) := by
  simp only [appListAppend, appendAux, List.nil_append, List.cons_append]

/-- Original `prod_enc_def`: encode a pair by its components. -/
@[hol "cakeml/compiler/backend/serialiser/num_list_enc_decScript.sml" "prod_enc_def"]
def prodEnc {α β : Type} (e1 : α → AppList Nat) (e2 : β → AppList Nat) :
    α × β → AppList Nat
  | (x, y) => AppList.append (e1 x) (e2 y)

/-- Original `prod_dec_def`: decode the two components in sequence. -/
@[hol "cakeml/compiler/backend/serialiser/num_list_enc_decScript.sml" "prod_dec_def"]
def prodDec {α β : Type} (d1 : List Nat → α × List Nat) (d2 : List Nat → β × List Nat) :
    List Nat → (α × β) × List Nat :=
  fun ns =>
    let step1 := d1 ns
    let step2 := d2 step1.2
    ((step1.1, step2.1), step2.2)

/-- Original `prod_dec_ok`: decoding both components keeps the bound. -/
@[hol "cakeml/compiler/backend/serialiser/num_list_enc_decScript.sml" "prod_dec_ok"]
theorem prodDecOk {α β : Type} (d1 : List Nat → α × List Nat) (d2 : List Nat → β × List Nat)
    (ok1 : decOk d1) (ok2 : decOk d2) : decOk (prodDec d1 d2) := by
  intro i
  generalize step1 : d1 i = first
  obtain ⟨x, ns1⟩ := first
  generalize step2 : d2 ns1 = second
  obtain ⟨y, ns2⟩ := second
  have b1 := ok1 i
  have b2 := ok2 ns1
  simp only [prodDec, step1, step2] at b1 b2 ⊢
  omega

/-- Original `prod_enc_dec_ok`. -/
@[hol "cakeml/compiler/backend/serialiser/num_list_enc_decScript.sml" "prod_enc_dec_ok"]
theorem prodEncDecOk {α β : Type} (e1 : α → AppList Nat) (d1 : List Nat → α × List Nat)
    (e2 : β → AppList Nat) (d2 : List Nat → β × List Nat)
    (ok1 : encDecOk e1 d1) (ok2 : encDecOk e2 d2) :
    encDecOk (prodEnc e1 e2) (prodDec d1 d2) := by
  obtain ⟨b1, r1⟩ := ok1
  obtain ⟨b2, r2⟩ := ok2
  refine ⟨prodDecOk d1 d2 b1 b2, ?_⟩
  intro x xs
  obtain ⟨v1, v2⟩ := x
  simp only [prodEnc, appListAppend_append, List.append_assoc, prodDec]
  rw [r1 v1 (appListAppend (e2 v2) ++ xs), r2 v2 xs]

/-- Original `prod_enc_dec_ok'`: the conditional product round trip. -/
@[hol "cakeml/compiler/backend/serialiser/num_list_enc_decScript.sml" "prod_enc_dec_ok'"]
theorem prodEncDecOkPrime {α β : Type} (p1 : α → Bool) (e1 : α → AppList Nat)
    (d1 : List Nat → α × List Nat) (p2 : β → Bool) (e2 : β → AppList Nat)
    (d2 : List Nat → β × List Nat)
    (ok1 : encDecOkPrime p1 e1 d1) (ok2 : encDecOkPrime p2 e2 d2) :
    encDecOkPrime (fun x => p1 x.1 && p2 x.2) (prodEnc e1 e2) (prodDec d1 d2) := by
  obtain ⟨b1, r1⟩ := ok1
  obtain ⟨b2, r2⟩ := ok2
  refine ⟨prodDecOk d1 d2 b1 b2, ?_⟩
  intro x xs guard
  obtain ⟨v1, v2⟩ := x
  have both : p1 v1 = true ∧ p2 v2 = true := by simpa using guard
  have g1 := both.1
  have g2 := both.2
  simp only [prodEnc, appListAppend_append, List.append_assoc, prodDec]
  rw [r1 v1 (appListAppend (e2 v2) ++ xs) g1, r2 v2 xs g2]

/-- Original `option_enc_def`: a tag for `NONE` or `SOME`. -/
@[hol "cakeml/compiler/backend/serialiser/num_list_enc_decScript.sml" "option_enc_def"]
def optionEnc {α : Type} (e : α → AppList Nat) : Option α → AppList Nat
  | none => AppList.list [0]
  | some y => AppList.append (AppList.list [1]) (e y)

/-- Original `option_dec_def`: read the tag, then the payload for `SOME`. -/
@[hol "cakeml/compiler/backend/serialiser/num_list_enc_decScript.sml" "option_dec_def"]
def optionDec {α : Type} (d : List Nat → α × List Nat) : List Nat → Option α × List Nat
  | [] => (none, [])
  | n :: ns => if n = 0 then (none, ns) else Prod.map some id (d ns)

/-- Original `option_enc_dec_ok`. -/
@[hol "cakeml/compiler/backend/serialiser/num_list_enc_decScript.sml" "option_enc_dec_ok"]
theorem optionEncDecOk {α : Type} (e : α → AppList Nat) (d : List Nat → α × List Nat)
    (ok : encDecOk e d) : encDecOk (optionEnc e) (optionDec d) := by
  obtain ⟨bound, roundtrip⟩ := ok
  refine ⟨?_, ?_⟩
  · intro i
    cases i with
    | nil => simp [optionDec]
    | cons n ns =>
      by_cases h : n = 0
      · simp only [optionDec, h, if_true, List.length_cons]
        omega
      · simp only [optionDec, h, if_false, List.length_cons]
        rw [prodMap_snd some (d ns)]
        have step := bound ns
        omega
  · intro x xs
    cases x with
    | none =>
      simp only [optionEnc]
      rw [appListAppend_single 0 xs]
      simp [optionDec]
    | some y =>
      simp only [optionEnc]
      rw [appListAppend_cons 1 (e y) xs]
      simp [optionDec, roundtrip]

/-- Original `sum_enc_def`: a tag for `INL` or `INR`. -/
@[hol "cakeml/compiler/backend/serialiser/num_list_enc_decScript.sml" "sum_enc_def"]
def sumEnc {α β : Type} (e1 : α → AppList Nat) (e2 : β → AppList Nat) :
    α ⊕ β → AppList Nat
  | .inl x => AppList.append (AppList.list [0]) (e1 x)
  | .inr y => AppList.append (AppList.list [1]) (e2 y)

/-- Original `sum_dec_def`: read the tag, then the matching payload. -/
@[hol "cakeml/compiler/backend/serialiser/num_list_enc_decScript.sml" "sum_dec_def"]
def sumDec {α β : Type} (d1 : List Nat → α × List Nat) (d2 : List Nat → β × List Nat) :
    List Nat → (α ⊕ β) × List Nat
  | [] => Prod.map Sum.inl id (d1 [])
  | n :: ns => if n = 0 then Prod.map Sum.inl id (d1 ns) else Prod.map Sum.inr id (d2 ns)

/-- Original `sum_enc_dec_ok`. -/
@[hol "cakeml/compiler/backend/serialiser/num_list_enc_decScript.sml" "sum_enc_dec_ok"]
theorem sumEncDecOk {α β : Type} (e1 : α → AppList Nat) (d1 : List Nat → α × List Nat)
    (e2 : β → AppList Nat) (d2 : List Nat → β × List Nat)
    (ok1 : encDecOk e1 d1) (ok2 : encDecOk e2 d2) :
    encDecOk (sumEnc e1 e2) (sumDec d1 d2) := by
  obtain ⟨b1, r1⟩ := ok1
  obtain ⟨b2, r2⟩ := ok2
  refine ⟨?_, ?_⟩
  · intro i
    cases i with
    | nil =>
      simp only [sumDec, List.length_nil]
      rw [prodMap_snd Sum.inl (d1 [])]
      have step := b1 []
      omega
    | cons n ns =>
      by_cases h : n = 0
      · simp only [sumDec, h, if_true, List.length_cons]
        rw [prodMap_snd Sum.inl (d1 ns)]
        have step := b1 ns
        omega
      · simp only [sumDec, h, if_false, List.length_cons]
        rw [prodMap_snd Sum.inr (d2 ns)]
        have step := b2 ns
        omega
  · intro x xs
    cases x with
    | inl v =>
      simp only [sumEnc]
      rw [appListAppend_cons 0 (e1 v) xs]
      simp [sumDec, r1]
    | inr v =>
      simp only [sumEnc]
      rw [appListAppend_cons 1 (e2 v) xs]
      simp [sumDec, r2]

/-! ## Tree and reverse-append codecs -/

/-- HOL `REV` from the external list library: reverse a list onto an
    accumulator.  Untagged infrastructure; `REV xs res = REVERSE xs ++ res`. -/
def holRev {α : Type} : List α → List α → List α
  | [], res => res
  | x :: xs, res => holRev xs (x :: res)

private theorem holRev_eq_reverse_append {α : Type} (xs res : List α) :
    holRev xs res = xs.reverse ++ res := by
  induction xs generalizing res with
  | nil => simp [holRev]
  | cons x xs ih =>
    simp only [holRev, ih, List.reverse_cons, List.append_assoc, List.singleton_append]

/-- Original `append_rev_def`: flatten a tree onto an accumulator in reverse. -/
@[hol "cakeml/compiler/backend/serialiser/num_list_enc_decScript.sml" "append_rev_def"]
def appendRev {α : Type} : AppList α → List α → List α
  | .nil, res => res
  | .list xs, res => holRev xs res
  | .append l1 l2, res => appendRev l2 (appendRev l1 res)

/-- Original `append_rev_thm`: reversing onto an accumulator is the reverse of
    the flattening followed by the accumulator. -/
@[hol "cakeml/compiler/backend/serialiser/num_list_enc_decScript.sml" "append_rev_thm"]
theorem appendRev_thm {α : Type} (l : AppList α) (res : List α) :
    appendRev l res = (appListAppend l).reverse ++ res := by
  induction l generalizing res with
  | nil => simp [appendRev, appListAppend, appendAux]
  | list xs => simp [appendRev, holRev_eq_reverse_append, appListAppend, appendAux]
  | append l1 l2 ih1 ih2 =>
    simp only [appendRev]
    rw [ih2, ih1, appListAppend_append, List.reverse_append, List.append_assoc]

/-- Original `spt_enc'_def`: encode a tree by its constructor tags and payloads. -/
@[hol "cakeml/compiler/backend/serialiser/num_list_enc_decScript.sml" "spt_enc'_def"]
def sptEncPrime {α : Type} (e : α → AppList Nat) : Spt α → AppList Nat
  | .ln => AppList.list [0]
  | .ls x => AppList.append (AppList.list [1]) (e x)
  | .bn t1 t2 =>
      AppList.append (AppList.list [2])
        (AppList.append (sptEncPrime e t1) (sptEncPrime e t2))
  | .bs t1 x t2 =>
      AppList.append (AppList.list [3])
        (AppList.append (sptEncPrime e t1) (AppList.append (e x) (sptEncPrime e t2)))

/-- Original `spt_depth_def`: the maximum depth of a tree. -/
@[hol "cakeml/compiler/backend/serialiser/num_list_enc_decScript.sml" "spt_depth_def"]
def sptDepth {α : Type} : Spt α → Nat
  | .bn t1 t2 => max (sptDepth t1) (sptDepth t2) + 1
  | .bs t1 _ t2 => max (sptDepth t1) (sptDepth t2) + 1
  | _ => 0

/-- Original `spt_enc''_def`: the depth-prefixed tree encoding. -/
@[hol "cakeml/compiler/backend/serialiser/num_list_enc_decScript.sml" "spt_enc''_def"]
def sptEncPrimePrime {α : Type} (e : α → AppList Nat) (t : Spt α) : AppList Nat :=
  prodEnc numEnc (sptEncPrime e) (sptDepth t, t)

/-- Original `spt_dec'_def`: decode a tree bounded by a depth budget. -/
@[hol "cakeml/compiler/backend/serialiser/num_list_enc_decScript.sml" "spt_dec'_def"]
def sptDecPrime {α : Type} :
    Nat → (List Nat → α × List Nat) → List Nat → Spt α × List Nat
  | _, _, [] => (.ln, [])
  | _, _, 0 :: rest => (.ln, rest)
  | _, d, 1 :: rest =>
      let step := d rest
      (.ls step.1, step.2)
  | 0, _, _ :: rest => (.ln, rest)
  | k + 1, d, 2 :: rest =>
      let step1 := sptDecPrime k d rest
      let step2 := sptDecPrime k d step1.2
      (.bn step1.1 step2.1, step2.2)
  | k + 1, d, _ :: rest =>
      let step1 := sptDecPrime k d rest
      let step2 := d step1.2
      let step3 := sptDecPrime k d step2.2
      (.bs step1.1 step2.1 step3.1, step3.2)

/-- Original `spt_dec''_def`: read the depth prefix, then the tree. -/
@[hol "cakeml/compiler/backend/serialiser/num_list_enc_decScript.sml" "spt_dec''_def"]
def sptDecPrimePrime {α : Type} (d : List Nat → α × List Nat) :
    List Nat → Spt α × List Nat
  | [] => (.ln, [])
  | m :: ms => sptDecPrime m d ms

/-- Original `spt_enc_def`: encode a well-formed tree by its association list,
    and any other tree by the depth-prefixed form. -/
@[hol "cakeml/compiler/backend/serialiser/num_list_enc_decScript.sml" "spt_enc_def"]
def sptEnc {α : Type} (e : α → AppList Nat) : Spt α → AppList Nat :=
  fun t =>
    sumEnc (listEnc (prodEnc numEnc e)) (sptEncPrimePrime e)
      (if sptWf t = true then Sum.inl (sptToAList t) else Sum.inr t)

/-- Original `spt_dec_def`: decode the tagged association list or tree. -/
@[hol "cakeml/compiler/backend/serialiser/num_list_enc_decScript.sml" "spt_dec_def"]
def sptDec {α : Type} (d : List Nat → α × List Nat) : List Nat → Spt α × List Nat :=
  fun ns =>
    Prod.map
      (fun x =>
        match x with
        | .inl xs => sptFromAList xs
        | .inr t => t)
      id
      (sumDec (listDec (prodDec numDec d)) (sptDecPrimePrime d) ns)

/-- Original `spt_dec'_def` never consumes more input than it is given. -/
private theorem sptDecPrime_bound_aux {α : Type} :
    ∀ (k : Nat) (d : List Nat → α × List Nat) (ns : List Nat),
      decOk d → (sptDecPrime k d ns).2.length ≤ ns.length := by
  intro k d ns
  induction k, d, ns using sptDecPrime.induct with
  | case1 t x =>
      intro _
      simp [sptDecPrime]
  | case2 t x rest =>
      intro _
      simp [sptDecPrime]
  | case3 t x rest =>
      intro hb
      have h := hb rest
      simp only [sptDecPrime, List.length_cons]
      omega
  | case4 x head rest h0 h1 =>
      intro _
      simp [sptDecPrime]
  | case5 k d rest step1 ih1 ih2 =>
      intro hb
      generalize hs1 : sptDecPrime k d rest = s1
      obtain ⟨t1, ns1⟩ := s1
      have b1 := ih1 hb
      simp only [hs1] at b1
      generalize hs2 : sptDecPrime k d ns1 = s2
      obtain ⟨t2, ns2⟩ := s2
      have b2 := ih2 hb
      simp only [step1, hs1, hs2] at b2
      simp only [sptDecPrime, hs1, hs2, List.length_cons]
      omega
  | case6 k d head rest h0 h1 h2 step1 step2 ih1 ih2 =>
      intro hb
      generalize hs1 : sptDecPrime k d rest = s1
      obtain ⟨t1, ns1⟩ := s1
      have b1 := ih1 hb
      simp only [hs1] at b1
      generalize hs2 : d ns1 = s2
      obtain ⟨x, ns2⟩ := s2
      have b3 := hb ns1
      simp only [hs2] at b3
      generalize hs3 : sptDecPrime k d ns2 = s3
      obtain ⟨t2, ns3⟩ := s3
      have b2 := ih2 hb
      simp only [step1, step2, hs1, hs2, hs3] at b2
      simp only [sptDecPrime, hs1, hs2, hs3, List.length_cons]
      omega

/-- `spt_dec'` inverts `spt_enc'` at any depth budget above the tree depth. -/
private theorem sptDecPrime_sptEncPrime_aux {α : Type} :
    ∀ (e : α → AppList Nat) (d : List Nat → α × List Nat), encDecOk e d →
      ∀ (t : Spt α) (xs : List Nat) (l : Nat), sptDepth t ≤ l →
        sptDecPrime l d (appListAppend (sptEncPrime e t) ++ xs) = (t, xs) := by
  intro e d ok t
  obtain ⟨bound, roundtrip⟩ := ok
  induction t using sptEncPrime.induct with
  | case1 =>
      intro xs l hd
      simp [sptEncPrime, sptDecPrime, appListAppend, appendAux]
  | case2 x =>
      intro xs l hd
      have hls : sptEncPrime e (.ls x) = AppList.append (AppList.list [1]) (e x) := rfl
      rw [hls, appListAppend_cons 1 (e x) xs]
      simp only [sptDecPrime]
      rw [roundtrip x xs]
  | case3 t1 t2 ih1 ih2 =>
      intro xs l hd
      cases l with
      | zero =>
          simp only [sptDepth] at hd
          omega
      | succ l' =>
          have h1 : sptDepth t1 ≤ l' := by
            simp only [sptDepth] at hd
            omega
          have h2 : sptDepth t2 ≤ l' := by
            simp only [sptDepth] at hd
            omega
          have hbn : sptEncPrime e (.bn t1 t2)
              = AppList.append (AppList.list [2])
                  (AppList.append (sptEncPrime e t1) (sptEncPrime e t2)) := rfl
          rw [hbn]
          rw [appListAppend_cons 2
              (AppList.append (sptEncPrime e t1) (sptEncPrime e t2)) xs,
            appListAppend_append]
          simp only [List.append_assoc]
          simp only [sptDecPrime]
          rw [ih1 (appListAppend (sptEncPrime e t2) ++ xs) l' h1, ih2 xs l' h2]
  | case4 t1 x t2 ih1 ih2 =>
      intro xs l hd
      cases l with
      | zero =>
          simp only [sptDepth] at hd
          omega
      | succ l' =>
          have h1 : sptDepth t1 ≤ l' := by
            simp only [sptDepth] at hd
            omega
          have h2 : sptDepth t2 ≤ l' := by
            simp only [sptDepth] at hd
            omega
          have hbs : sptEncPrime e (.bs t1 x t2)
              = AppList.append (AppList.list [3])
                  (AppList.append (sptEncPrime e t1)
                    (AppList.append (e x) (sptEncPrime e t2))) := rfl
          rw [hbs]
          rw [appListAppend_cons 3
              (AppList.append (sptEncPrime e t1)
                (AppList.append (e x) (sptEncPrime e t2))) xs,
            appListAppend_append, appListAppend_append]
          simp only [List.append_assoc]
          simp only [sptDecPrime]
          rw [ih1 (appListAppend (e x) ++ (appListAppend (sptEncPrime e t2) ++ xs)) l' h1]
          rw [roundtrip x (appListAppend (sptEncPrime e t2) ++ xs)]
          rw [ih2 xs l' h2]

/-- Original `spt_enc''_dec_ok`. -/
@[hol "cakeml/compiler/backend/serialiser/num_list_enc_decScript.sml" "spt_enc''_dec_ok"]
theorem sptEncPrimePrimeDecOk {α : Type} (e : α → AppList Nat)
    (d : List Nat → α × List Nat) (ok : encDecOk e d) :
    encDecOk (sptEncPrimePrime e) (sptDecPrimePrime d) := by
  obtain ⟨bound, roundtrip⟩ := ok
  refine ⟨?_, ?_⟩
  · intro i
    cases i with
    | nil => simp [sptDecPrimePrime]
    | cons m ms =>
      simp only [sptDecPrimePrime]
      have h := sptDecPrime_bound_aux m d ms bound
      simp only [List.length_cons]
      omega
  · intro t xs
    have henc : sptEncPrimePrime e t
        = AppList.append (AppList.list [sptDepth t]) (sptEncPrime e t) := rfl
    rw [henc, appListAppend_cons, sptDecPrimePrime]
    exact sptDecPrime_sptEncPrime_aux e d ⟨bound, roundtrip⟩ t xs (sptDepth t)
      (Nat.le_refl _)

/-- Original `spt_enc_dec_ok`. -/
@[hol "cakeml/compiler/backend/serialiser/num_list_enc_decScript.sml" "spt_enc_dec_ok"]
theorem sptEncDecOk {α : Type} (e : α → AppList Nat) (d : List Nat → α × List Nat)
    (ok : encDecOk e d) : encDecOk (sptEnc e) (sptDec d) := by
  have sumOk : encDecOk (sumEnc (listEnc (prodEnc numEnc e)) (sptEncPrimePrime e))
      (sumDec (listDec (prodDec numDec d)) (sptDecPrimePrime d)) := by
    exact sumEncDecOk (listEnc (prodEnc numEnc e)) (listDec (prodDec numDec d))
      (sptEncPrimePrime e) (sptDecPrimePrime d)
      (listEncDecOk (prodEnc numEnc e) (prodDec numDec d)
        (prodEncDecOk numEnc numDec e d numEncDecOk ok))
      (sptEncPrimePrimeDecOk e d ok)
  have inverse : ∀ t : Spt α,
      (fun x =>
        match x with
        | .inl xs => sptFromAList xs
        | .inr t => t)
        ((fun t => if sptWf t = true then Sum.inl (sptToAList t) else Sum.inr t) t) = t := by
    intro t
    dsimp only
    by_cases h : sptWf t = true
    · rw [if_pos h]
      exact sptFromAList_sptToAList t h
    · rw [if_neg h]
  exact encDecOk_comp (e := sumEnc (listEnc (prodEnc numEnc e)) (sptEncPrimePrime e))
    (d := sumDec (listDec (prodDec numDec d)) (sptDecPrimePrime d))
    (f := fun x =>
      match x with
      | .inl xs => sptFromAList xs
      | .inr t => t)
    (g := fun t => if sptWf t = true then Sum.inl (sptToAList t) else Sum.inr t)
    ⟨sumOk, inverse⟩

end Flapjack.Compiler.Backend.Serialiser
