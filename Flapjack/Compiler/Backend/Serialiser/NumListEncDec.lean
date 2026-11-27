module

public import Flapjack.Misc.AppList

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

end Flapjack.Compiler.Backend.Serialiser
