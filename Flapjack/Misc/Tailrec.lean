module

public import Flapjack.Misc.While
public import Flapjack.Misc.Sum

@[expose] public section

/-! Tail-recursive functions from a step function, from HOL's machine-code
`tailrec` theory.

Representation convention: HOL's step functions have type
`'a -> ('a + 'b) # bool`; their side-condition flag is a `bool` in a data
position. Here it is a `Prop` component, `α → (α ⊕ β) × Prop`, matching the
`Prop` guards and preconditions of `holTailrecPre`. The two are equivalent
under propositional extensionality, and every step function defined through
HOL's `tailrec_define` (for example in `mc_multiword`) follows this
convention. -/
namespace Flapjack

/-- The precondition of a tail recursion: the side condition holds along the
iteration up to its first exit, and the iteration exits. -/
@[hol "HOL/examples/machine-code/hoare-triple/tailrecScript.sml" "TAILREC_PRE_def"]
def holTailrecPre {α : Type} (f1 : α → α) (guard precondition : α → Prop) (x : α) : Prop :=
  (∀ k, (∀ m, m < k → guard (f1^[m] x)) → precondition (f1^[k] x)) ∧
    ∃ n, ¬ guard (f1^[n] x)

/-- A tail recursion: iterate `f1` while `g` holds, then finish with `f2`. -/
@[hol "HOL/examples/machine-code/hoare-triple/tailrecScript.sml" "TAILREC_def"]
noncomputable def holTailrec {α β : Type} (f1 : α → α) (f2 : α → β) (g : α → Prop) (x : α) : β :=
  f2 (holWhile g f1 x)

/-- A tail recursion given by one step function returning `INL` to continue
and `INR` to stop. -/
@[hol "HOL/examples/machine-code/hoare-triple/tailrecScript.sml" "SHORT_TAILREC_def"
  (total_function_inhabitants := [α, β])]
noncomputable def holShortTailrec {α β : Type} [Nonempty α] [Nonempty β]
    (f : α → (α ⊕ β) × Prop) : α → β :=
  holTailrec (holOutl ∘ Prod.fst ∘ f) (holOutr ∘ Prod.fst ∘ f) (holIsl ∘ Prod.fst ∘ f)

/-- The precondition of a step-function tail recursion. -/
@[hol "HOL/examples/machine-code/hoare-triple/tailrecScript.sml" "SHORT_TAILREC_PRE_def"
  (total_function_inhabitants := [α])]
def holShortTailrecPre {α β : Type} [Nonempty α] (f : α → (α ⊕ β) × Prop) : α → Prop :=
  holTailrecPre (holOutl ∘ Prod.fst ∘ f) (holIsl ∘ Prod.fst ∘ f) (Prod.snd ∘ f)

/-- One-step unfolding of the precondition. -/
@[hol "HOL/examples/machine-code/hoare-triple/tailrecScript.sml" "TAILREC_PRE_THM"]
theorem holTailrecPre_thm {α : Type} :
    ∀ (f1 : α → α) (g p : α → Prop) (x : α),
      holTailrecPre f1 g p x ↔ p x ∧ (g x → holTailrecPre f1 g p (f1 x)) := by
  intro f1 g p x
  constructor
  · rintro ⟨hall, n, hn⟩
    refine ⟨by simpa using hall 0 (by simp), fun gx => ⟨fun k hk => ?_, ?_⟩⟩
    · have := hall (k + 1) (by
        intro m hm
        cases m with
        | zero => simpa using gx
        | succ m => simpa [Function.iterate_succ_apply] using hk m (by omega))
      simpa [Function.iterate_succ_apply] using this
    · cases n with
      | zero => exact absurd gx (by simpa using hn)
      | succ n => exact ⟨n, by simpa [Function.iterate_succ_apply] using hn⟩
  · rintro ⟨px, rest⟩
    by_cases gx : g x
    · obtain ⟨hall, n, hn⟩ := rest gx
      refine ⟨fun k hk => ?_, ⟨n + 1, by simpa [Function.iterate_succ_apply] using hn⟩⟩
      cases k with
      | zero => simpa using px
      | succ k =>
        have := hall k (fun m hm => by
          simpa [Function.iterate_succ_apply] using hk (m + 1) (by omega))
        simpa [Function.iterate_succ_apply] using this
    · refine ⟨fun k hk => ?_, ⟨0, by simpa using gx⟩⟩
      cases k with
      | zero => simpa using px
      | succ k => exact absurd (by simpa using hk 0 (by omega)) gx

/-- Induction over a terminating, side-condition-respecting iteration. -/
@[hol "HOL/examples/machine-code/hoare-triple/tailrecScript.sml" "TAILREC_PRE_INDUCT"]
theorem holTailrecPre_induct {α : Type} {f1 : α → α} {g p : α → Prop} :
    ∀ P : α → Prop,
      (∀ x, holTailrecPre f1 g p x ∧ p x ∧ g x ∧ P (f1 x) → P x) ∧
        (∀ x, holTailrecPre f1 g p x ∧ p x ∧ ¬ g x → P x) →
      ∀ x, holTailrecPre f1 g p x → P x := by
  rintro P ⟨step, stop⟩ x pre
  obtain ⟨n, hn⟩ := pre.2
  induction n generalizing x with
  | zero =>
    have px := ((holTailrecPre_thm f1 g p x).mp pre).1
    exact stop x ⟨pre, px, by simpa using hn⟩
  | succ n ih =>
    have ⟨px, next⟩ := (holTailrecPre_thm f1 g p x).mp pre
    by_cases gx : g x
    · exact step x ⟨pre, px, gx, ih (f1 x) (next gx)
        (by simpa [Function.iterate_succ_apply] using hn)⟩
    · exact stop x ⟨pre, px, gx⟩

open Classical in
/-- One-step unfolding of a tail recursion. -/
@[hol "HOL/examples/machine-code/hoare-triple/tailrecScript.sml" "TAILREC_THM"]
theorem holTailrec_thm {α β : Type} :
    ∀ (f1 : α → α) (f2 : α → β) (g : α → Prop) (x : α),
      holTailrec f1 f2 g x = if g x then holTailrec f1 f2 g (f1 x) else f2 x := by
  intro f1 f2 g x
  unfold holTailrec
  rw [holWhile_spec]
  split <;> rfl

/-- Equal components give equal tail recursions and preconditions. -/
@[hol "HOL/examples/machine-code/hoare-triple/tailrecScript.sml" "TAILREC_EQ_THM"]
theorem holTailrec_eq_thm {α β : Type} {f1 f1' : α → α} {f2 f2' : α → β} {g g' s s' : α → Prop} :
    f1 = f1' ∧ f2 = f2' ∧ g = g' ∧ s = s' →
      holTailrec f1 f2 g = holTailrec f1' f2' g' ∧ holTailrecPre f1 g s = holTailrecPre f1' g' s' := by
  rintro ⟨rfl, rfl, rfl, rfl⟩
  exact ⟨rfl, rfl⟩

open Classical in
/-- One-step unfolding of a step-function tail recursion and of its precondition. -/
@[hol "HOL/examples/machine-code/hoare-triple/tailrecScript.sml" "SHORT_TAILREC_THM"
  (total_function_inhabitants := [α, β])]
theorem holShortTailrec_thm {α β : Type} [Nonempty α] [Nonempty β] :
    ∀ (f : α → (α ⊕ β) × Prop) (x : α),
      (holShortTailrec f x = if holIsl (f x).1 then holShortTailrec f (holOutl (f x).1)
        else holOutr (f x).1) ∧
      (holShortTailrecPre f x ↔ (f x).2 ∧ (holIsl (f x).1 → holShortTailrecPre f (holOutl (f x).1))) := by
  intro f x
  constructor
  · unfold holShortTailrec
    rw [holTailrec_thm]
    rfl
  · unfold holShortTailrecPre
    rw [holTailrecPre_thm]
    rfl

/-- Induction over the precondition of a step-function tail recursion. -/
@[hol "HOL/examples/machine-code/hoare-triple/tailrecScript.sml" "SHORT_TAILREC_PRE_INDUCT"
  (total_function_inhabitants := [α])]
theorem holShortTailrecPre_induct {α β : Type} [Nonempty α] {f : α → (α ⊕ β) × Prop} :
    ∀ P : α → Prop,
      (∀ x, holShortTailrecPre f x ∧ (f x).2 ∧ (∀ y, (f x).1 = .inl y → P y) → P x) →
      ∀ x, holShortTailrecPre f x → P x := by
  intro P step
  apply holTailrecPre_induct P
  constructor
  · rintro x ⟨pre, px, gx, py⟩
    refine step x ⟨pre, px, fun y hy => ?_⟩
    simp only [Function.comp_apply, hy, holOutl] at py
    exact py
  · rintro x ⟨pre, px, gx⟩
    refine step x ⟨pre, px, fun y hy => ?_⟩
    simp [Function.comp_apply, hy, holIsl] at gx

/-- Simulation of one step-function tail recursion by another. HOL's
hypothesis also quantifies a variable `r` of an independent type that occurs
nowhere in it; since HOL types are nonempty that quantifier is vacuous, and it
is omitted here (in Lean an empty type would make it hold trivially). -/
@[hol "HOL/examples/machine-code/hoare-triple/tailrecScript.sml" "SHORT_TAILREC_SIM"
  (total_function_inhabitants := [α, β, γ, δ])]
theorem holShortTailrec_sim {α β γ δ : Type} [Nonempty α] [Nonempty β] [Nonempty γ] [Nonempty δ] :
    ∀ (f : α → (α ⊕ β) × Prop) (g : γ → (γ ⊕ δ) × Prop) (R : α → γ → Prop) (P : β → δ → Prop),
      (∀ (x : α) (s : γ) (q : α ⊕ β), R x s ∧ f x = (q, True) →
        (∀ y, q = .inl y → ∃ y1, g s = (.inl y1, True) ∧ R y y1) ∧
        (∀ y, q = .inr y → ∃ y1, g s = (.inr y1, True) ∧ P y y1)) →
      ∀ x, holShortTailrecPre f x → ∀ s, R x s →
        P (holShortTailrec f x) (holShortTailrec g s) ∧ holShortTailrecPre g s := by
  intro f g R P hyp
  apply holShortTailrecPre_induct (fun x => ∀ s, R x s →
    P (holShortTailrec f x) (holShortTailrec g s) ∧ holShortTailrecPre g s)
  rintro x ⟨_, px, ih⟩ s rxs
  rcases hfx : f x with ⟨q, b⟩
  have bt : b = True := by rw [hfx] at px; exact eq_true px
  subst bt
  have ⟨hl, hr⟩ := hyp x s q ⟨rxs, hfx⟩
  have fthm := (holShortTailrec_thm f x).1
  have gthm := holShortTailrec_thm g s
  rw [hfx] at fthm
  cases q with
  | inl y =>
    obtain ⟨y1, hg, ry⟩ := hl y rfl
    rw [hg] at gthm
    have ⟨a, b⟩ := ih y (by rw [hfx]) y1 ry
    have c1 : holIsl ((Sum.inl y : α ⊕ β), True).1 := trivial
    have c2 : holIsl ((Sum.inl y1 : γ ⊕ δ), True).1 := trivial
    have g1 := gthm.1
    rw [if_pos c1] at fthm
    rw [if_pos c2] at g1
    refine ⟨by rw [fthm, g1]; exact a, gthm.2.mpr ⟨trivial, fun _ => b⟩⟩
  | inr y =>
    obtain ⟨y1, hg, py⟩ := hr y rfl
    rw [hg] at gthm
    have c1 : ¬ holIsl ((Sum.inr y : α ⊕ β), True).1 := fun h => h
    have c2 : ¬ holIsl ((Sum.inr y1 : γ ⊕ δ), True).1 := fun h => h
    have g1 := gthm.1
    rw [if_neg c1] at fthm
    rw [if_neg c2] at g1
    refine ⟨by rw [fthm, g1]; exact py, gthm.2.mpr ⟨trivial, fun h => (c2 h).elim⟩⟩

/-- Unfolding a step-function tail recursion at a continuing step (Flapjack
proof infrastructure). -/
theorem holShortTailrec_inl {α β : Type} [Nonempty α] [Nonempty β] {f : α → (α ⊕ β) × Prop}
    {x y : α} {c : Prop} (h : f x = (.inl y, c)) : holShortTailrec f x = holShortTailrec f y := by
  rw [(holShortTailrec_thm f x).1, h]
  exact if_pos trivial

/-- Unfolding a step-function tail recursion at a stopping step (Flapjack
proof infrastructure). -/
theorem holShortTailrec_inr {α β : Type} [Nonempty α] [Nonempty β] {f : α → (α ⊕ β) × Prop}
    {x : α} {z : β} {c : Prop} (h : f x = (.inr z, c)) : holShortTailrec f x = z := by
  rw [(holShortTailrec_thm f x).1, h]
  exact if_neg (fun h => h)

/-- Unfolding the precondition at a continuing step (Flapjack proof
infrastructure). -/
theorem holShortTailrecPre_inl {α β : Type} [Nonempty α] [Nonempty β] {f : α → (α ⊕ β) × Prop}
    {x y : α} {c : Prop} (h : f x = (.inl y, c)) :
    holShortTailrecPre f x ↔ c ∧ holShortTailrecPre f y := by
  rw [(holShortTailrec_thm (β := β) f x).2, h]
  exact ⟨fun ⟨hc, hy⟩ => ⟨hc, hy trivial⟩, fun ⟨hc, hy⟩ => ⟨hc, fun _ => hy⟩⟩

/-- Unfolding the precondition at a stopping step (Flapjack proof
infrastructure). -/
theorem holShortTailrecPre_inr {α β : Type} [Nonempty α] [Nonempty β] {f : α → (α ⊕ β) × Prop}
    {x : α} {z : β} {c : Prop} (h : f x = (.inr z, c)) : holShortTailrecPre f x ↔ c := by
  rw [(holShortTailrec_thm (β := β) f x).2, h]
  exact ⟨fun ⟨hc, _⟩ => hc, fun hc => ⟨hc, fun h => h.elim⟩⟩

/-- A step-function tail recursion as a case analysis on its step (Flapjack
proof infrastructure). -/
theorem holShortTailrec_eq_elim {α β : Type} [Nonempty α] [Nonempty β]
    (f : α → (α ⊕ β) × Prop) (x : α) :
    holShortTailrec f x = Sum.elim (holShortTailrec f) id (f x).1 := by
  rcases h : f x with ⟨q, c⟩
  cases q with
  | inl y => rw [holShortTailrec_inl h]; rfl
  | inr z => rw [holShortTailrec_inr h]; rfl

/-- The precondition as a case analysis on the step (Flapjack proof
infrastructure). -/
theorem holShortTailrecPre_eq_elim {α β : Type} [Nonempty α] [Nonempty β]
    (f : α → (α ⊕ β) × Prop) (x : α) :
    holShortTailrecPre f x ↔ (f x).2 ∧ Sum.elim (holShortTailrecPre f) (fun _ => True) (f x).1 := by
  rcases h : f x with ⟨q, c⟩
  cases q with
  | inl y => rw [holShortTailrecPre_inl (β := β) h]; rfl
  | inr z => rw [holShortTailrecPre_inr (β := β) h]; simp

end Flapjack
