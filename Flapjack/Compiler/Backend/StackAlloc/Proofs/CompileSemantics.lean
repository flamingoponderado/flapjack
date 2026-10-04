import Flapjack.Compiler.Backend.StackAlloc.Proofs.CompCorrect
import Flapjack.Compiler.Backend.Semantics.StackSem.Semantics
import Flapjack.Compiler.Backend.StackProps.EvaluateAddClockIoEventsMono
import Flapjack.Misc.LprefixLub

/-!
# `stack_allocProof` `compile_semantics`

`compile_semantics` of `cakeml/compiler/backend/proofs/stack_allocProofScript.sml`
(5909-6066): the observational StackSem `semantics` is preserved by the
`stack_alloc` code transformation. As in HOL, every clock-indexed run of the
entry call `Call NONE (INL start) NONE` (which `comp` leaves unchanged) is
simulated by `comp_correct` with some extra clock, and `evaluate_add_clock` and
`evaluate_add_clock_io_events_mono` relate runs at different clocks; the
divergence case compares the two I/O-event chains with
`IMP_build_lprefix_lub_EQ`.
-/

namespace Flapjack.Compiler.Backend.StackAlloc

open Flapjack Flapjack.StackSemStateOps Flapjack.Compiler.Backend.StackLang
open Flapjack.StackSemEvaluate Flapjack.Compiler.Backend.StackProps
open Flapjack.Compiler.Backend.DataToWord Flapjack.Compiler.Backend.WordGcFunctions
open HolLList

namespace CompileSemanticsSupport

/-- Canonical codec for the imported owning StackSem state carrier. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : StackSemStateBroad width C F) (h : state.FiniteSupport),
        (StackSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : StackSemStateFiniteExact width C F,
        StackSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  StackSemStateOps.holFmapAsFiniteSupportWitness

/-- The "fail" results of `semantics_def`. -/
def Bad {width : Nat} [NeZero width] (res : Option (StackSemResult width)) : Prop :=
  res ≠ some .timeOut ∧ res ≠ some (.result (.loc 1 0)) ∧
    (∀ w, res ≠ some (.halt (.word w))) ∧ ∀ e, res ≠ some (.finalFFI e)

/-- The terminating-behaviour predicate of `semantics_def` over a clock-indexed
family of runs. -/
def Term {width : Nat} [NeZero width] {C F : Type}
    (E : Nat → Option (StackSemResult width) × StackSemStateFiniteExact width C F)
    (res : HolBehaviour) : Prop :=
  ∃ k t r outcome,
    E k = (some r, t) ∧
    (match r with
     | .finalFFI e => outcome = HolOutcome.ffiOutcome e
     | .halt w => outcome =
         if w = .word 0 then HolOutcome.success else HolOutcome.resourceLimitHit
     | .result _ => outcome = HolOutcome.success
     | _ => False) ∧
    res = HolBehaviour.terminate outcome t.ffi.ioEvents

/-- Semantics preservation under a clock-shifted simulation (Flapjack
infrastructure for HOL's `compile_semantics` proof). `E` and `E'` are the
clock-indexed entry-call runs of the source and target. Every source run is
matched by a target run with some extra clock (`hsim`), both families are
stable under extra clock once they stop timing out (`hadd`, `hadd'`) and have
monotone I/O events (`hio`, `hio'`), and the source never fails (`hok`). -/
theorem semanticsAux_shift {width : Nat} [NeZero width] {C F : Type}
    (E E' : Nat → Option (StackSemResult width) × StackSemStateFiniteExact width C F)
    (hok : ∀ k, ¬ Bad (E k).1)
    (hsim : ∀ k, ∃ ck, (E' (k + ck)).1 = (E k).1 ∧ (E' (k + ck)).2.ffi = (E k).2.ffi)
    (hadd' : ∀ k d, (E' k).1 ≠ some .timeOut →
      (E' (k + d)).1 = (E' k).1 ∧ (E' (k + d)).2.ffi = (E' k).2.ffi)
    (hio : ∀ k d, (E k).2.ffi.ioEvents <+: (E (k + d)).2.ffi.ioEvents)
    (hio' : ∀ k d, (E' k).2.ffi.ioEvents <+: (E' (k + d)).2.ffi.ioEvents) :
    semanticsAux E' = semanticsAux E := by
  have hnb' : ¬ ∃ k, Bad (E' k).1 := by
    rintro ⟨k, hb⟩
    obtain ⟨ck, h1, -⟩ := hsim k
    have h2 := (hadd' k ck hb.1).1
    exact hok k (h1 ▸ h2 ▸ hb)
  have hnb : ¬ ∃ k, Bad (E k).1 := fun ⟨k, hb⟩ => hok k hb
  have hT : Term E' = Term E := by
    funext res
    apply propext
    constructor
    · rintro ⟨k, t, r, o, he, hm, hr⟩
      have hto : r ≠ .timeOut := by rintro rfl; exact hm
      obtain ⟨ck, h1, h2⟩ := hsim k
      obtain ⟨h3, h4⟩ := hadd' k ck (by rw [he]; simpa using hto)
      rw [he] at h3 h4
      refine ⟨k, (E k).2, r, o, Prod.ext (h1 ▸ h3) rfl, hm, ?_⟩
      rw [hr, ← h2, h4]
    · rintro ⟨k, t, r, o, he, hm, hr⟩
      obtain ⟨ck, h1, h2⟩ := hsim k
      rw [he] at h1 h2
      exact ⟨k + ck, (E' (k + ck)).2, r, o, Prod.ext h1 rfl, hm, by rw [hr, h2]⟩
  have hchain : ∀ (G : Nat → Option (StackSemResult width) × StackSemStateFiniteExact width C F),
      (∀ k d, (G k).2.ffi.ioEvents <+: (G (k + d)).2.ffi.ioEvents) →
      lprefixChain (fun l => ∃ k, l = fromList (G k).2.ffi.ioEvents) := by
    intro G hG
    rintro _ _ ⟨i, rfl⟩ ⟨j, rfl⟩
    rcases Nat.le_total i j with hij | hji
    · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hij
      exact Or.inl ((lprefix_fromList _ _).2 (hG i d))
    · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hji
      exact Or.inr ((lprefix_fromList _ _).2 (hG j d))
  have hlub : buildLprefixLub (fun l => ∃ k, l = fromList (E' k).2.ffi.ioEvents) =
      buildLprefixLub (fun l => ∃ k, l = fromList (E k).2.ffi.ioEvents) := by
    apply IMP_build_lprefix_lub_EQ (hchain E' hio') (hchain E hio)
    · rintro _ ⟨k, rfl⟩
      obtain ⟨ck, -, h2⟩ := hsim k
      refine ⟨_, ⟨k, rfl⟩, (lprefix_fromList _ _).2 ?_⟩
      rw [← h2]; exact hio' k ck
    · rintro _ ⟨k, rfl⟩
      obtain ⟨ck, -, h2⟩ := hsim k
      exact ⟨_, ⟨k + ck, rfl⟩, by rw [h2]; exact lprefix_refl _⟩
  unfold semanticsAux
  split_ifs with h1 h2 h2
  · exact absurd h1 hnb'
  · exact absurd h1 hnb'
  · exact absurd h2 hnb
  change (match holOptionSome (Term E') with
      | some res => res
      | none => HolBehaviour.diverge
          (buildLprefixLub (fun l => ∃ k, l = fromList (E' k).2.ffi.ioEvents))) =
    (match holOptionSome (Term E) with
      | some res => res
      | none => HolBehaviour.diverge
          (buildLprefixLub (fun l => ∃ k, l = fromList (E k).2.ffi.ioEvents)))
  rw [hT, hlub]

end CompileSemanticsSupport

/-- Exact HOL `with_same_regs_lemma` (`stack_allocProofScript.sml:5901-5905`):
re-setting `regs` to its own value is redundant in a record update. HOL's free
`s cc oracle anything k c` are implicit. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem with_same_regs_lemma {width : Nat} [NeZero width] {C F : Type}
    {s : StackSemStateFiniteExact width C F}
    {cc : C → List (Nat × HolProg width) → Option (List (BitVec 8) × C)}
    {oracle : Nat → C × List (Nat × HolProg width) × List (BitVec width)}
    {anything : WordSemGcFun width} {k : Nat} {c : Spt (HolProg width)} :
    { s with
        regs := s.regs, compile := cc, compileOracle := oracle, gcFun := anything
        useStack := true, useStore := true, useAlloc := false, clock := k, code := c } =
      { s with
        compile := cc, compileOracle := oracle, gcFun := anything
        useStack := true, useStore := true, useAlloc := false, clock := k, code := c } := rfl

open CompileSemanticsSupport in
/-- Exact HOL `compile_semantics` (`stack_allocProofScript.sml:5909-6066`), with
all nine source premises. HOL's free `s c compile_rest start anything` are
implicit; the bound variables of the oracle premise and of the compiler lambda
are renamed `i k q` and `cfg`; `dimword (:'a)` is `2 ^ width` and
`(I ## MAP prog_comp ## I) o oracle` is
`Prod.map id (Prod.map (List.map progComp) id) ∘ oracle`. The proof follows HOL:
`comp_correct` at every clock of the entry call with `regs := s.regs` (HOL's
`comp_correct_thm`), `evaluate_add_clock` and
`evaluate_add_clock_io_events_mono`. The native evaluator's instruction closure
inherits the `reals_as_rational_cuts` limit (`docs/SOUNDNESS.md` item 8). -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem compile_semantics {width : Nat} [NeZero width] {C F : Type}
    {s : StackSemStateFiniteExact width C F} {c : DataToWord.Config}
    {compile_rest : C → List (Nat × HolProg width) → Option (List (BitVec 8) × C)}
    {start : Nat} {anything : WordSemGcFun width} :
    (∀ k prog, sptLookup k s.code = some prog → k ≠ gcStubLocation ∧ StackProps.allocArg prog) ∧
    (∀ (i k : Nat) (q : HolProg width), (k, q) ∈ (s.compileOracle i).2.1 →
      k ≠ gcStubLocation ∧ StackProps.allocArg q) ∧
    s.gcFun = wordGcFun c ∧
    s.bitmaps.length + s.dataBuffer.buffer.length + s.dataBuffer.spaceLeft < 2 ^ width - 1 ∧
    s.stack.length * (width / 8) < 2 ^ width ∧
    s.useStack = true ∧ s.useAlloc = true ∧
    s.compile = (fun cfg => compile_rest cfg ∘ List.map progComp) ∧
    semantics start s ≠ .fail →
    semantics start { s with
        code := sptFromAList (compile c (sptToAList s.code))
        gcFun := anything
        compile := compile_rest
        compileOracle := Prod.map id (Prod.map (List.map progComp) id) ∘ s.compileOracle
        useStore := true, useStack := true, useAlloc := false } =
      semantics start s := by
  rintro ⟨hcode, horacle, hgc, hbuf, hst, hK, hA, hC, hsem⟩
  have hok : ∀ k, ¬ Bad (evaluate ((.call none (.inl start) none : HolProg width),
      { s with clock := k })).1 := by
    intro k hb
    apply hsem
    rw [semantics_eq_aux]
    unfold semanticsAux
    rw [if_pos ⟨k, hb⟩]
  have addc : ∀ (S : StackSemStateFiniteExact width C F) (d : Nat),
      (evaluate ((.call none (.inl start) none : HolProg width), S)).1 ≠ some .timeOut →
      (evaluate ((.call none (.inl start) none : HolProg width),
          { S with clock := S.clock + d })).1 =
        (evaluate ((.call none (.inl start) none : HolProg width), S)).1 ∧
      (evaluate ((.call none (.inl start) none : HolProg width),
          { S with clock := S.clock + d })).2.ffi =
        (evaluate ((.call none (.inl start) none : HolProg width), S)).2.ffi := by
    intro S d h
    have := evaluateAddClock d _ S _ _ ⟨rfl, h⟩
    exact ⟨by rw [this]; rfl, by rw [this]; rfl⟩
  rw [semantics_eq_aux, semantics_eq_aux]
  apply semanticsAux_shift
  · exact hok
  · intro k
    rcases he : evaluate ((.call none (.inl start) none : HolProg width),
      { s with clock := k }) with ⟨r, t⟩
    have hr : r ≠ some .error := by
      rintro rfl
      exact hok k (by rw [he]; simp [Bad])
    obtain ⟨ck, regs1, he', -⟩ :=
      comp_correct (anything := anything) (compile_rest := compile_rest)
        (.call none (.inl start) none) { s with clock := k } r t 0 0 c s.regs
        ⟨he, hr, ⟨trivial, trivial⟩, hcode, horacle, hgc, hA, hst, fun _ _ h => h, hK, hbuf, hC⟩
    exact ⟨ck, (congrArg Prod.fst he').trans rfl, (congrArg (fun p => p.2.ffi) he').trans rfl⟩
  · intro k d hto
    exact addc _ d hto
  · intro k d
    exact EvaluateAddClockIoEventsMono.evaluateAddClockIoEventsMono d _ { s with clock := k }
  · intro k d
    exact EvaluateAddClockIoEventsMono.evaluateAddClockIoEventsMono d _ _

end Flapjack.Compiler.Backend.StackAlloc
