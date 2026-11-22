module

public import Flapjack.Compiler.Backend.WordBignum.Generate
public import Flapjack.Compiler.Backend.WordBignum.Proofs.CompileEquations

@[expose] public section

set_option autoImplicit false

/-! Width-independent code indices of the generated bignum stubs.

HOL proves the stub facts of `data_to_wordProofScript.sml` by `EVAL`, which
decides every code-cache comparison of `word_bignum$compile` structurally even
for a symbolic word dimension. In Lean `hasCompiled` compares `Mini (BitVec
width)` bodies, which does not reduce for a symbolic `width`. This module is
Flapjack infrastructure with no HOL counterpart: it proves that the cache
evolution of `compile` on `mcIopCode width` agrees with a reference run over
`Mini Nat` that compares body shapes (constants ignored), provided the shape
comparison is injective on the program's loop bodies, which is checked by
kernel evaluation. The reference run then evaluates to the installed indices. -/
namespace Flapjack.Compiler.Backend.WordBignum.Indices
open Flapjack Flapjack.Compiler.Backend.WordBignum

/-! ### Maps and parametric structural comparison -/

mutual
/-- Map the constants of a word expression. -/
def expMap {α β : Type} (f : α → β) : WordLangExpHOL α → WordLangExpHOL β
  | .const v => .const (f v)
  | .var n => .var n
  | .lookup s => .lookup s
  | .load a => .load (expMap f a)
  | .op o args => .op o (expListMap f args)
  | .shift o a b => .shift o (expMap f a) (expMap f b)

/-- Map the constants of a list of word expressions. -/
def expListMap {α β : Type} (f : α → β) : List (WordLangExpHOL α) → List (WordLangExpHOL β)
  | [] => []
  | e :: es => expMap f e :: expListMap f es
end

/-- Map the constant of a register-or-immediate operand. -/
def regImmMap {α β : Type} (f : α → β) : WordRegImm α → WordRegImm β
  | .imm v => .imm (f v)
  | .reg r => .reg r

/-- Map the constants of a mini-program. -/
def miniMap {α β : Type} (f : α → β) : Mini α → Mini β
  | .skip => .skip
  | .assign d e => .assign d (expMap f e)
  | .delete rs => .delete rs
  | .seq a b => .seq (miniMap f a) (miniMap f b)
  | .load d i a => .load d i a
  | .store v i => .store v i
  | .ite o r arg a b => .ite o r (regImmMap f arg) (miniMap f a) (miniMap f b)
  | .swap => .swap
  | .add o c l r ci => .add o c l (regImmMap f r) (regImmMap f ci)
  | .sub o c l r ci => .sub o c l (regImmMap f r) (regImmMap f ci)
  | .mul o c l r => .mul o c l r
  | .div o c l r d => .div o c l r d
  | .loop rc live body => .loop rc live (miniMap f body)
  | .continue => .continue
  | .recurse s n => .recurse s n
  | .loopBody body => .loopBody (miniMap f body)

mutual
/-- Structural comparison of expressions with constants compared by `r`. -/
def expEqBy {α β : Type} (r : α → β → Bool) : WordLangExpHOL α → WordLangExpHOL β → Bool
  | .const x, .const y => r x y
  | .var x, .var y => x == y
  | .lookup x, .lookup y => decide (x = y)
  | .load x, .load y => expEqBy r x y
  | .op o xs, .op o' ys => decide (o = o') && expListEqBy r xs ys
  | .shift o a b, .shift o' a' b' => decide (o = o') && expEqBy r a a' && expEqBy r b b'
  | _, _ => false

/-- Structural comparison of expression lists. -/
def expListEqBy {α β : Type} (r : α → β → Bool) :
    List (WordLangExpHOL α) → List (WordLangExpHOL β) → Bool
  | [], [] => true
  | x :: xs, y :: ys => expEqBy r x y && expListEqBy r xs ys
  | _, _ => false
end

/-- Comparison of register-or-immediate operands with constants compared by `r`. -/
def regImmEqBy {α β : Type} (r : α → β → Bool) : WordRegImm α → WordRegImm β → Bool
  | .imm x, .imm y => r x y
  | .reg x, .reg y => x == y
  | _, _ => false

/-- Structural comparison of mini-programs with constants compared by `r`. -/
def miniEqBy {α β : Type} (r : α → β → Bool) : Mini α → Mini β → Bool
  | .skip, .skip | .swap, .swap | .continue, .continue => true
  | .assign a e, .assign b f => a == b && expEqBy r e f
  | .delete a, .delete b => decide (a = b)
  | .seq a b, .seq c d => miniEqBy r a c && miniEqBy r b d
  | .load a b c, .load d e f => a == d && b == e && decide (c = f)
  | .store a b, .store c d => a == c && b == d
  | .ite op a b c d, .ite op' a' b' c' d' =>
      decide (op = op') && a == a' && regImmEqBy r b b' && miniEqBy r c c' && miniEqBy r d d'
  | .add a b c d e, .add a' b' c' d' e' =>
      a == a' && b == b' && c == c' && regImmEqBy r d d' && regImmEqBy r e e'
  | .sub a b c d e, .sub a' b' c' d' e' =>
      a == a' && b == b' && c == c' && regImmEqBy r d d' && regImmEqBy r e e'
  | .mul a b c d, .mul a' b' c' d' => a == a' && b == b' && c == c' && d == d'
  | .div a b c d e, .div a' b' c' d' e' =>
      a == a' && b == b' && c == c' && d == d' && e == e'
  | .loop rc vs body, .loop rc' vs' body' =>
      rc == rc' && decide (vs = vs') && miniEqBy r body body'
  | .recurse a b, .recurse c d => decide (a = c) && decide (b = d)
  | .loopBody a, .loopBody b => miniEqBy r a b
  | _, _ => false

/-- Comparison of shapes: everything except the word constants. -/
def shapeEq {α β : Type} : Mini α → Mini β → Bool := miniEqBy fun _ _ => true

/-- Exact comparison of `Mini Nat` programs. -/
def exactEq : Mini Nat → Mini Nat → Bool := miniEqBy fun x y => x == y

theorem expEqBy_map {α β γ δ : Type} (r : γ → δ → Bool) (f : α → γ) (h : β → δ) :
    (∀ (x : WordLangExpHOL α) (y : WordLangExpHOL β),
      expEqBy r (expMap f x) (expMap h y) = expEqBy (fun a b => r (f a) (h b)) x y) ∧
    (∀ (xs : List (WordLangExpHOL α)) (ys : List (WordLangExpHOL β)),
      expListEqBy r (expListMap f xs) (expListMap h ys) =
        expListEqBy (fun a b => r (f a) (h b)) xs ys) := by
  have key : ∀ x : WordLangExpHOL α, ∀ y, expEqBy r (expMap f x) (expMap h y) =
        expEqBy (fun a b => r (f a) (h b)) x y := by
    intro x
    induction x using WordLangExpHOL.rec
      (motive_2 := fun xs => ∀ ys, expListEqBy r (expListMap f xs) (expListMap h ys) =
        expListEqBy (fun a b => r (f a) (h b)) xs ys) with
    | const _ => intro y; cases y <;> simp [expMap, expEqBy]
    | var _ => intro y; cases y <;> simp [expMap, expEqBy]
    | lookup _ => intro y; cases y <;> simp [expMap, expEqBy]
    | load _ ih => intro y; cases y <;> simp [expMap, expEqBy, ih]
    | op _ _ ih => intro y; cases y <;> simp [expMap, expEqBy, ih]
    | shift _ _ _ iha ihb => intro y; cases y <;> simp [expMap, expEqBy, iha, ihb]
    | nil => rename_i ys; cases ys <;> simp [expListMap, expListEqBy]
    | cons _ _ ihh iht => rename_i ys; cases ys <;> simp [expListMap, expListEqBy, ihh, iht]
  refine ⟨key, ?_⟩
  intro xs
  induction xs with
  | nil => intro ys; cases ys <;> simp [expListMap, expListEqBy]
  | cons _ _ iht => intro ys; cases ys <;> simp [expListMap, expListEqBy, key, iht]

theorem miniEqBy_map {α β γ δ : Type} (r : γ → δ → Bool) (f : α → γ) (h : β → δ)
    (x : Mini α) (y : Mini β) :
    miniEqBy r (miniMap f x) (miniMap h y) = miniEqBy (fun a b => r (f a) (h b)) x y := by
  have he := (expEqBy_map r f h).1
  have hr : ∀ (a : WordRegImm α) (b : WordRegImm β),
      regImmEqBy r (regImmMap f a) (regImmMap h b) = regImmEqBy (fun a b => r (f a) (h b)) a b := by
    intro a b; cases a <;> cases b <;> rfl
  induction x generalizing y <;> cases y <;> simp_all [miniMap, miniEqBy]

theorem expEqBy_refl {α : Type} (r : α → α → Bool) (hr : ∀ x, r x x = true) :
    (∀ x : WordLangExpHOL α, expEqBy r x x = true) ∧
    (∀ xs : List (WordLangExpHOL α), expListEqBy r xs xs = true) := by
  have key : ∀ x : WordLangExpHOL α, expEqBy r x x = true := by
    intro x
    induction x using WordLangExpHOL.rec (motive_2 := fun xs => expListEqBy r xs xs = true) <;>
      simp_all [expEqBy, expListEqBy]
  refine ⟨key, fun xs => ?_⟩
  induction xs <;> simp_all [expListEqBy]

theorem miniEqBy_refl {α : Type} (r : α → α → Bool) (hr : ∀ x, r x x = true) (x : Mini α) :
    miniEqBy r x x = true := by
  have he := (expEqBy_refl r hr).1
  have hri : ∀ a : WordRegImm α, regImmEqBy r a a = true := by
    intro a; cases a <;> simp [regImmEqBy, hr]
  induction x <;> simp_all [miniEqBy]

theorem expEqBy_iff {α : Type} (r : α → α → Bool) (hr : ∀ x y, r x y = true ↔ x = y) :
    (∀ x y : WordLangExpHOL α, expEqBy r x y = true ↔ x = y) ∧
    (∀ xs ys : List (WordLangExpHOL α), expListEqBy r xs ys = true ↔ xs = ys) := by
  have key : ∀ x y : WordLangExpHOL α, expEqBy r x y = true ↔ x = y := by
    intro x
    induction x using WordLangExpHOL.rec
      (motive_2 := fun xs => ∀ ys, expListEqBy r xs ys = true ↔ xs = ys) with
    | nil => rename_i ys; cases ys <;> simp [expListEqBy]
    | cons _ _ ihh iht => rename_i ys; cases ys <;> simp [expListEqBy, ihh, iht]
    | _ => intro y; cases y <;> simp_all [expEqBy, and_assoc]
  refine ⟨key, ?_⟩
  intro xs
  induction xs with
  | nil => intro ys; cases ys <;> simp [expListEqBy]
  | cons _ _ iht => intro ys; cases ys <;> simp [expListEqBy, key, iht]

theorem miniEqBy_iff {α : Type} (r : α → α → Bool) (hr : ∀ x y, r x y = true ↔ x = y)
    (x y : Mini α) : miniEqBy r x y = true ↔ x = y := by
  have he := (expEqBy_iff r hr).1
  have hri : ∀ a b : WordRegImm α, regImmEqBy r a b = true ↔ a = b := by
    intro a b; cases a <;> cases b <;> simp [regImmEqBy, hr]
  induction x generalizing y <;> cases y <;> simp_all [miniEqBy, and_assoc]

theorem exactEq_eq (x y : Mini Nat) : exactEq x y = true → x = y :=
  (miniEqBy_iff _ (by simp) x y).1

/-- Equal images under any constant map have equal shapes. -/
theorem shapeEq_of_map_eq {α β : Type} (g : α → β) (a b : Mini α)
    (h : miniMap g a = miniMap g b) : shapeEq a b = true := by
  have := miniEqBy_map (fun _ _ => true) g g a b
  rw [h, miniEqBy_refl _ (fun _ => rfl)] at this
  exact this.symm

/-! ### Reference run over `Mini Nat` -/

/-- Code cache of the reference run: next index and installed body shapes. -/
abbrev IdxAcc := Nat × List (Mini Nat × Nat)

/-- First installed body with the same shape. -/
def idxLookup (body : Mini Nat) : List (Mini Nat × Nat) → Option Nat
  | [] => none
  | (b, k) :: rest => if shapeEq body b then some k else idxLookup body rest

/-- The code-cache evolution of `compile`, comparing shapes. -/
def idxRun : IdxAcc → Mini Nat → IdxAcc
  | cs, .loop _ _ body =>
    match idxLookup body cs.2 with
    | some _ => cs
    | none =>
      let cs' := idxRun (cs.1 + 1, cs.2) body
      (cs'.1, (body, cs.1) :: cs'.2)
  | cs, .loopBody b => idxRun cs b
  | cs, .seq a b => idxRun (idxRun cs a) b
  | cs, .ite _ _ _ a b => idxRun (idxRun cs a) b
  | cs, _ => cs

/-- Every loop body occurring in a program, nested ones included. -/
def loopBodies {α : Type} : Mini α → List (Mini α)
  | .loop _ _ b => b :: loopBodies b
  | .loopBody b => loopBodies b
  | .seq a b | .ite _ _ _ a b => loopBodies a ++ loopBodies b
  | _ => []

/-- `mcIopCode` with natural-number constants. -/
def refNat : Mini Nat := miniMap BitVec.toNat (mcIopCode 64)

theorem mcIopCode_eq_map (width : Nat) [NeZero width] :
    mcIopCode width = miniMap (BitVec.ofNat width) refNat := by
  rfl

/-! ### Simulation -/

/-- The reference cache describes the real one: same next index, and the same
installed indices with each real body the image of the reference body. -/
def AccRel {width : Nat} (g : Nat → BitVec width) (csR : IdxAcc) (csW : CodeAcc width) : Prop :=
  csW.1 = csR.1 ∧
    csW.2.map (fun e => (e.1, e.2.1)) = csR.2.map (fun e => (miniMap g e.1, e.2))

/-- Shape comparison is exact on `S`. -/
def ShapeInj (S : List (Mini Nat)) : Prop := ∀ a ∈ S, ∀ b ∈ S, shapeEq a b = true → a = b

theorem map_eq_iff_shapeEq {width : Nat} (g : Nat → BitVec width) (S : List (Mini Nat))
    (hS : ShapeInj S) (a b : Mini Nat) (ha : a ∈ S) (hb : b ∈ S) :
    miniMap g a = miniMap g b ↔ shapeEq a b = true :=
  ⟨shapeEq_of_map_eq g a b, fun h => by rw [hS a ha b hb h]⟩

theorem lookup_sim {width : Nat} (g : Nat → BitVec width) (S : List (Mini Nat))
    (hS : ShapeInj S) (body : Mini Nat) (hb : body ∈ S) :
    ∀ (LR : List (Mini Nat × Nat)) (LW : List (CodeEntry width)),
      (∀ e ∈ LR, e.1 ∈ S) →
      LW.map (fun e => (e.1, e.2.1)) = LR.map (fun e => (miniMap g e.1, e.2)) →
      (@List.lookup _ _ ⟨fun x y => decide (x = y)⟩ (miniMap g body) LW).map (·.1) =
        idxLookup body LR := by
  intro LR
  induction LR with
  | nil => intro LW _ h; cases LW <;> simp_all [idxLookup]
  | cons e LR ih =>
    intro LW hmem h
    cases LW with
    | nil => simp at h
    | cons w LW =>
      simp only [List.map_cons, List.cons.injEq, Prod.mk.injEq] at h
      obtain ⟨⟨h1, h2⟩, h3⟩ := h
      have hiff := map_eq_iff_shapeEq g S hS body e.1 hb (hmem e (by simp))
      rw [← h1] at hiff
      have := ih LW (fun x hx => hmem x (by simp [hx])) h3
      simp only [List.lookup, idxLookup]
      by_cases hs : shapeEq body e.1 = true
      · have : miniMap g body = w.1 := hiff.2 hs
        simp [this, hs, h2]
      · have : ¬ miniMap g body = w.1 := fun h => hs (hiff.1 h)
        simp only [hs, if_false, Bool.false_eq_true]
        simpa [this] using ‹_›

/-- The real cache after compiling `miniMap g c` is described by the reference run. -/
theorem compile_sim {width : Nat} [NeZero width] (g : Nat → BitVec width)
    (S : List (Mini Nat)) (hS : ShapeInj S) (c : Mini Nat) :
    ∀ (n l i : Nat) (csR : IdxAcc) (csW : CodeAcc width), AccRel g csR csW →
      (∀ b ∈ loopBodies c, b ∈ S) → (∀ e ∈ csR.2, e.1 ∈ S) →
      AccRel g (idxRun csR c) (compile n l i csW (miniMap g c)).2.2.2 ∧
        ∀ e ∈ (idxRun csR c).2, e.1 ∈ S := by
  induction c with
  | seq a b iha ihb =>
    intro n l i csR csW hR hL hC
    rw [miniMap, compile_seq]
    obtain ⟨hRa, hCa⟩ := iha n l i csR csW hR (fun x hx => hL x (by simp [loopBodies, hx])) hC
    generalize compile n l i csW (miniMap g a) = ra at hRa
    obtain ⟨a', la, ia, ca⟩ := ra
    exact ihb n la ia _ ca hRa (fun x hx => hL x (by simp [loopBodies, hx])) hCa
  | ite op r arg a b iha ihb =>
    intro n l i csR csW hR hL hC
    rw [miniMap, compile_ite]
    simp only [idxRun]
    obtain ⟨hRa, hCa⟩ := iha n l i csR csW hR (fun x hx => hL x (by simp [loopBodies, hx])) hC
    rcases ha' : compile n l i csW (miniMap g a) with ⟨a', la, ia, ca⟩
    rw [ha'] at hRa
    obtain ⟨hRb, hCb⟩ := ihb n la ia _ ca hRa (fun x hx => hL x (by simp [loopBodies, hx])) hCa
    rcases hb' : compile n la ia ca (miniMap g b) with ⟨b', lb, ib, cb⟩
    rw [hb'] at hRb
    cases arg <;> simp only [regImmMap] <;> exact ⟨hRb, hCb⟩
  | loopBody body ih =>
    intro n l i csR csW hR hL hC
    rw [miniMap, compile_loopBody]
    exact ih n l i csR csW hR (fun x hx => hL x (by simpa [loopBodies] using hx)) hC
  | loop rc live body ih =>
    intro n l i csR csW hR hL hC
    have hb : body ∈ S := hL body (by simp [loopBodies])
    have hlk := lookup_sim g S hS body hb csR.2 csW.2 hC hR.2
    rw [miniMap, compile_loop]
    simp only [hasCompiled]
    simp only [idxRun]
    cases hk : idxLookup body csR.2 with
    | some k =>
      rw [hk] at hlk
      cases hw : @List.lookup _ _ ⟨fun x y => decide (x = y)⟩ (miniMap g body) csW.2 with
      | none => rw [hw] at hlk; simp at hlk
      | some v => exact ⟨hR, hC⟩
    | none =>
      rw [hk] at hlk
      cases hw : @List.lookup _ _ ⟨fun x y => decide (x = y)⟩ (miniMap g body) csW.2 with
      | some v => rw [hw] at hlk; simp at hlk
      | none =>
        have hR' : AccRel g (csR.1 + 1, csR.2) (codeAccNext csW) := by
          simp [AccRel, codeAccNext, hR.1, hR.2]
        obtain ⟨hR2, hC2⟩ := ih csW.1 2 1 (csR.1 + 1, csR.2) (codeAccNext csW) hR'
          (fun x hx => hL x (by simp [loopBodies, hx])) hC
        rcases hcb : compile csW.1 2 1 (codeAccNext csW) (miniMap g body) with
          ⟨b', lb, ib, cb⟩
        rw [hcb] at hR2
        refine ⟨?_, ?_⟩
        · simp only [install, AccRel, hcb] at hR2 ⊢
          exact ⟨hR2.1, by simp [hR2.2, hR.1]⟩
        · intro e he
          simp only [List.mem_cons] at he
          rcases he with rfl | he
          · exact hb
          · exact hC2 e he
  | _ =>
    intro n l i csR csW hR hL hC
    simp only [miniMap, compile_skip, compile_continue, compile_recurse, compile_assign,
      compile_delete, compile_swap, compile_store, compile_load, compile_add, compile_sub,
      compile_mul, compile_div, idxRun]
    exact ⟨hR, hC⟩

theorem shapeInj_of_check (S : List (Mini Nat))
    (h : (S.all fun a => S.all fun b => !shapeEq a b || exactEq a b) = true) : ShapeInj S := by
  intro a ha b hb hs
  have := List.all_eq_true.1 (List.all_eq_true.1 h a ha) b hb
  simp only [hs, Bool.not_true, Bool.false_or] at this
  exact exactEq_eq a b this

/-- Shape comparison is exact on the loop bodies of `mcIopCode`, by kernel evaluation. -/
theorem shapeInj_refNat : ShapeInj (loopBodies refNat) :=
  shapeInj_of_check _ (by decide +kernel)

/-- The reference run installs the bodies at these indices, by kernel evaluation. -/
theorem idxRun_refNat :
    (idxRun (40, []) refNat).2.map (·.2) =
      [61, 60, 59, 58, 54, 57, 56, 55, 53, 52, 51, 50, 49, 47, 48, 46, 45, 44, 43, 42, 41, 40] := by
  decide +kernel

/-- The code indices of the generated bignum stubs, for every positive width. -/
theorem generatedBignumStubs_map_fst (width : Nat) [NeZero width] :
    (generatedBignumStubs width 39).map Prod.fst =
      [39, 61, 60, 59, 58, 54, 57, 56, 55, 53, 52, 51, 50, 49, 47, 48, 46, 45, 44, 43, 42, 41,
        40] := by
  have hsim := (compile_sim (BitVec.ofNat width) _ shapeInj_refNat refNat 39 2 1
    (40, []) (40, []) ⟨rfl, rfl⟩ (fun _ hb => hb)
    (by simp)).1.2
  rw [← mcIopCode_eq_map] at hsim
  simp only [generatedBignumStubs]
  rcases hc : compile 39 2 1 (40, []) (mcIopCode width) with
    ⟨body, l', i', n', installed⟩
  rw [hc] at hsim
  have h2 := congrArg (List.map Prod.snd) hsim
  simp only [List.map_map] at h2
  have h3 : installed.map (fun e => e.2.1) = [61, 60, 59, 58, 54, 57, 56, 55, 53, 52, 51, 50, 49,
      47, 48, 46, 45, 44, 43, 42, 41, 40] := by
    rw [← idxRun_refNat]
    simpa [Function.comp_def] using h2
  simp only [List.map_cons, List.map_map]
  have h4 : (Prod.fst ∘ fun (x : CodeEntry width) => (x.2.1, 1,
      WordLangProgHOL.seq x.2.2 (WordLangProgHOL.return 0 [0]))) = fun e => e.2.1 := rfl
  rw [h4, h3]

end Flapjack.Compiler.Backend.WordBignum.Indices
