import Flapjack.HolRef
import Flapjack.Compiler.Backend.WordAlloc.WordAllocDef
import Flapjack.Compiler.Backend.WordAlloc.Proofs.EvaluateApplyColour
import Flapjack.Compiler.Backend.WordAlloc.Proofs.ClashTreeColouringOk.Assembly
import Flapjack.Compiler.Backend.WordAlloc.Proofs.SelectRegAllocCorrect
import Flapjack.Compiler.Backend.WordAlloc.Proofs.EvenStartingLocals
import Flapjack.Compiler.Backend.WordAlloc.Proofs.GetForced

/-!
# `word_alloc_correct`

Port of `word_allocProofScript.sml:3399-3477`, `word_alloc_correct`: on a program with
well-formed cut sets started from locals with only physical registers, some permutation
oracle makes the source run either fail or agree with the run of the allocated program on
the result, `word_state_eq_rel` and, for results other than `Break`/`Continue`, the locals.
Both branches of `word_alloc` are covered: an accepted oracle colouring and the colouring
computed by `select_reg_alloc`.
-/

namespace Flapjack.WordAlloc

open Flapjack Flapjack.RegAlloc Flapjack.Compiler.Encoders.Asm WordSemStateFiniteExact
open Flapjack.Compiler.Backend.WordAlloc.Proofs (evenStartingLocals)

namespace WordAllocCorrectWitnesses

/-- Canonical imported WordSem carrier roundtrip for the state-field ports. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : WordSemStateBroad width C F) (h : state.FiniteSupport),
        (WordSemStateBroad.ofBroad state h).toBroad = state) ∧
      (∀ state : WordSemStateFiniteExact width C F,
        WordSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  WordSemStateExact.holFmapAsFiniteSupportWitness

end WordAllocCorrectWitnesses

/-- A colouring that is twice the half of every physical register fixes those registers
(Flapjack infrastructure). -/
theorem totalColour_phys (col : Spt Nat)
    (h : ∀ x v, sptLookup x col = some v → isPhyVar x = true → 2 * v = x) :
    ∀ n, isPhyVar n = true → totalColour col n = n := fun n hn => by
  unfold totalColour
  cases hl : sptLookup n col with
  | none => simp [hn]
  | some v => exact h n v hl hn

/-- Even starting locals are related to themselves under such a colouring. -/
theorem strongLocals_self {width : Nat} [NeZero width] (f : Nat → Nat)
    (locals : Spt (WordLocW width)) (live : Nat → Prop) (hesl : evenStartingLocals locals)
    (hf : ∀ n, isPhyVar n = true → f n = n) : strongLocalsRel f live locals locals := by
  intro n v ⟨_, hl⟩
  have hd : sptDomain locals n := by simp [sptDomain, hl]
  rw [hf n (hesl n hd)]
  exact hl

open Classical in
/-- From `evaluate_apply_colour` at the empty live set and loop stack to the conclusion of
`word_alloc_correct` (Flapjack infrastructure). -/
theorem post_to_goal {width : Nat} [NeZero width] {C F : Type} (f : Nat → Nat)
    (prog prog' : WordLangProgHOL (BitVec width)) (st : WordSemStateFiniteExact width C F)
    (hp : prog' = applyColour f prog) (h : applyColourPost f prog .ln [] st st) :
    ∃ perm',
      let (res, rst) := evaluate prog { st with permute := perm' }
      if res = some .error then True
      else
        let (res', rcst) := evaluate prog' st
        res = res' ∧ wordStateEqRel rst rcst ∧
          match res with
          | none => True
          | some (.break _) => True
          | some (.continue _) => True
          | some _ => rst.locals = rcst.locals := by
  subst hp
  obtain ⟨perm', h⟩ := h
  refine ⟨perm', ?_⟩
  revert h
  rcases evaluate prog { st with permute := perm' } with ⟨res, rst⟩
  rcases evaluate (applyColour f prog) st with ⟨res', rcst⟩
  dsimp only
  intro h
  by_cases he : res = some .error
  · rw [if_pos he]; trivial
  · rw [if_neg he] at h ⊢
    obtain ⟨e1, e2, e3⟩ := h
    refine ⟨e1, e2, ?_⟩
    unfold applyColourLocals at e3
    rcases res with _ | r
    · trivial
    · cases r <;> first | trivial | exact e3

open Classical in
/-- Exact HOL `word_alloc_correct` (`word_allocProofScript.sml:3399-3477`). HOL's
`if res = SOME Error` is decided classically, as in the accepted `evaluate_apply_colour`
motive. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem wordAllocCorrect {width : Nat} [NeZero width] {C F : Type} :
    ∀ (fc : Nat) (c : AsmConfigExact width) (alg : Nat) (prog : WordLangProgHOL (BitVec width))
      (k : Nat) (col_opt : Option (Spt Nat)) (st : WordSemStateFiniteExact width C F),
      evenStartingLocals st.locals ∧ wfCutsets prog →
      ∃ perm',
        let (res, rst) := evaluate prog { st with permute := perm' }
        if res = some .error then True
        else
          let (res', rcst) := evaluate (wordAlloc fc c alg k prog col_opt) st
          res = res' ∧ wordStateEqRel rst rcst ∧
            match res with
            | none => True
            | some (.break _) => True
            | some (.continue _) => True
            | some _ => rst.locals = rcst.locals := by
  intro fc c alg prog k col_opt st ⟨hesl, hwf⟩
  have hln : ∀ x, ¬ sptDomain (.ln : NumSet) x := fun x h => by
    simp [sptDomain, sptLookup] at h
  have hlnimg : ∀ (f : Nat → Nat), sptDomain (.ln : NumSet) =
      (fun y => ∃ x, sptDomain (.ln : NumSet) x ∧ f x = y) := fun f => by
    funext y
    apply propext
    exact ⟨fun h => absurd h (hln y), fun ⟨x, hx, _⟩ => absurd hx (hln x)⟩
  have hrefl : wordStateEqRel st st := by simp only [wordStateEqRel, and_self]
  -- the common tail: a colouring accepted by `check_clash_tree` that fixes physical registers
  have tail : ∀ (f : Nat → Nat) (livein flivein : NumSet),
      checkClashTree f (getClashTree prog []) .ln .ln = some (livein, flivein) →
      (∀ n, isPhyVar n = true → f n = n) →
      applyColourPost f prog .ln [] st st := fun f livein flivein hcc hf => by
    have hco := (clashTreeColouringOk prog [] f .ln .ln livein flivein
      ⟨hwf, rfl, (fun _ h => by cases h), hlnimg f,
        (fun a _ ha => absurd ha (hln a)), hcc⟩).2.2.1
    exact evaluateApplyColour prog st st f .ln [] ⟨hco, hrefl,
      strongLocals_self f st.locals _ hesl hf⟩
  unfold wordAlloc
  simp only []
  cases hor : oracleColourOk k col_opt (getClashTree prog []) prog (getForced c prog []) with
  | some cp =>
      cases col_opt with
      | none => simp [oracleColourOk] at hor
      | some col =>
          simp only [oracleColourOk] at hor
          split at hor
          · next h1 =>
              split at hor
              · simp only [Option.some.injEq] at hor
                simp only [Bool.and_eq_true] at h1
                obtain ⟨hev, hcc⟩ := h1
                obtain ⟨⟨livein, flivein⟩, hcc⟩ := Option.isSome_iff_exists.mp hcc
                have hevc : ∀ x v, sptLookup x col = some v → isPhyVar x = true → 2 * v = x :=
                  fun x v hl hp => by
                    have hm := (sptMemToAList col x v).mpr hl
                    have := List.all_eq_true.mp hev (x, v) hm
                    simp only [hp, ↓reduceIte, beq_iff_eq] at this
                    simp only [isPhyVar, decide_eq_true_eq] at hp
                    omega
                exact post_to_goal (totalColour col) prog cp st hor.symm
                  (tail _ livein flivein hcc (totalColour_phys col hevc))
              · cases hor
          · cases hor
  | none =>
      obtain ⟨hs, hgh⟩ : ∃ p, getHeuristics alg fc prog = p := ⟨_, rfl⟩
      obtain ⟨spcol, livein, flivein, hsel, hcc, hdom, hsup, _⟩ :=
        selectRegAllocCorrect alg hs.2 k hs.1 (getClashTree prog []) (getForced c prog [])
          (getStackOnly prog) (getForcedInGetClashTree prog [] c)
      have hinj : ∀ a b : Nat, (fun x => 2 * x) a = (fun x => 2 * x) b → a = b := fun a b h => by
        simp only at h; omega
      have hci := checkClashTreeInj (getClashTree prog []) (spDefault spcol) (fun x => 2 * x)
        .ln .ln .ln ⟨hinj, hlnimg _⟩
      rw [hcc] at hci
      obtain ⟨gout, hcc2, _⟩ := hci
      rw [← totalColourAlt] at hcc2
      have hphys : ∀ x v, sptLookup x spcol = some v → isPhyVar x = true → 2 * v = x :=
        fun x v hl hp => by
          have hd : sptDomain spcol x := by simp [sptDomain, hl]
          have hx := (hdom x (hsup x hd)).2
          rw [if_pos hp] at hx
          have : spDefault spcol x = v := by simp only [spDefault, hl]
          rw [this] at hx
          simp only [isPhyVar, decide_eq_true_eq] at hp
          omega
      refine post_to_goal (totalColour spcol) prog _ st ?_
        (tail _ livein gout hcc2 (totalColour_phys spcol hphys))
      rw [hgh]
      simp only [hsel]

end Flapjack.WordAlloc
