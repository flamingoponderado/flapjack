import Flapjack.Compiler.Backend.WordRemove
import Flapjack.Pancake.LoopToWord.WordProgCarrierCodec
import Flapjack.Pancake.LoopToWord.WordProgCarrierCodec.RoundTrip

/-!
# Executed `remove_must_terminate` through the reviewed definition

HOL `word_to_word$full_compile_single` (`word_to_wordScript.sml:37-40`) applies
`remove_must_terminate` to every allocated function. The executed compiler runs
the tagged `WordRemove.removeMustTerminate` at the same point: the allocated
production program is encoded with `wordLangProgToHOL`, the reviewed pass runs
on the exact `wordLang$prog` carrier, and the result is decoded with
`wordLangProgFromHOL`. A program outside the codec's domain (the executable-only
five-register AddCarry, which the original compiler never produces) is an
explicit failure; no second implementation of the pass is used. Flapjack
production routing with no HOL declaration of its own.
-/

namespace Flapjack.RiscV

/-- Executed MustTerminate removal via the reviewed `removeMustTerminate`. -/
def wordRemoveMustTerminateViaHOL? {width : Nat} [NeZero width]
    (program : WordProg (BitVec width)) : Option (WordProg (BitVec width)) :=
  (wordLangProgToHOL program).bind
    (fun native => wordLangProgFromHOL (Compiler.Backend.WordRemove.removeMustTerminate native))

/-- Every accepted executed result is the decoded reviewed pass output on the
encoded input (Flapjack routing fact; no evaluation is assumed). -/
theorem wordRemoveMustTerminateViaHOL?_native {width : Nat} [NeZero width]
    (program result : WordProg (BitVec width))
    (accepted : wordRemoveMustTerminateViaHOL? program = some result) :
    ∃ native, wordLangProgToHOL program = some native ∧
      wordLangProgFromHOL (Compiler.Backend.WordRemove.removeMustTerminate native) = some result := by
  unfold wordRemoveMustTerminateViaHOL? at accepted
  cases hencode : wordLangProgToHOL program with
  | none => simp [hencode] at accepted
  | some native =>
      simp only [hencode, Option.bind_some] at accepted
      exact ⟨native, rfl, accepted⟩

/-- Every instruction in the encoder's image decodes (Flapjack carrier fact). -/
theorem wordLangInstFromHOL_isSome_of_toHOL {width : Nat} (i : WordInst (BitVec width))
    (j : WordLangInst (BitVec width)) (h : wordLangInstToHOL i = some j) :
    (wordLangInstFromHOL j).isSome = true := by
  cases i with
  | const a b => simp only [wordLangInstToHOL, Option.some.injEq] at h; subst h; rfl
  | arith a =>
    cases a <;> simp only [wordLangInstToHOL, wordLangArithToHOL, Option.map_some,
      Option.map_none, Option.some.injEq, reduceCtorEq] at h <;> subst h <;> rfl
  | mem op a b =>
    simp only [wordLangInstToHOL, Option.some.injEq] at h; subst h
    simp [wordLangInstFromHOL]
  | memOffset op a b off =>
    simp only [wordLangInstToHOL, Option.some.injEq] at h; subst h
    simp only [wordLangInstFromHOL]
    split <;> rfl

set_option linter.unusedSimpArgs false in
/-- Every program in the encoder's image decodes (Flapjack carrier fact). -/
theorem wordLangProgFromHOL_isSome_of_toHOL {width : Nat} :
    ∀ (p : WordProg (BitVec width)) (n : WordLangProgHOL (BitVec width)),
      wordLangProgToHOL p = some n → (wordLangProgFromHOL n).isSome = true
  | .inst i, n, h => by
      simp only [wordLangProgToHOL] at h
      rcases hi : wordLangInstToHOL i with _ | j <;> simp [hi] at h
      subst h
      have := wordLangInstFromHOL_isSome_of_toHOL i j hi
      simp only [wordLangProgFromHOL]
      rcases hj : wordLangInstFromHOL j with _ | k <;> simp_all
  | .mustTerminate b, n, h => by
      simp only [wordLangProgToHOL] at h
      rcases hb : wordLangProgToHOL b with _ | nb <;> simp [hb] at h
      subst h
      have := wordLangProgFromHOL_isSome_of_toHOL b nb hb
      simp only [wordLangProgFromHOL]
      rcases hf : wordLangProgFromHOL nb with _ | q <;> simp_all
  | .seq a b, n, h => by
      simp only [wordLangProgToHOL] at h
      rcases ha : wordLangProgToHOL a with _ | na <;> rcases hb : wordLangProgToHOL b with _ | nb <;>
        simp [ha, hb] at h
      subst h
      have h1 := wordLangProgFromHOL_isSome_of_toHOL a na ha
      have h2 := wordLangProgFromHOL_isSome_of_toHOL b nb hb
      simp only [wordLangProgFromHOL]
      rcases hf1 : wordLangProgFromHOL na with _ | q1 <;> rcases hf2 : wordLangProgFromHOL nb with _ | q2 <;>
        simp_all
  | .ite op c r a b, n, h => by
      simp only [wordLangProgToHOL] at h
      rcases ha : wordLangProgToHOL a with _ | na <;> rcases hb : wordLangProgToHOL b with _ | nb <;>
        simp [ha, hb] at h
      subst h
      have h1 := wordLangProgFromHOL_isSome_of_toHOL a na ha
      have h2 := wordLangProgFromHOL_isSome_of_toHOL b nb hb
      simp only [wordLangProgFromHOL]
      rcases hf1 : wordLangProgFromHOL na with _ | q1 <;> rcases hf2 : wordLangProgFromHOL nb with _ | q2 <;>
        simp_all
  | .loop li b lo, n, h => by
      simp only [wordLangProgToHOL] at h
      rcases hb : wordLangProgToHOL b with _ | nb <;> simp [hb] at h
      subst h
      have := wordLangProgFromHOL_isSome_of_toHOL b nb hb
      simp only [wordLangProgFromHOL]
      rcases hf : wordLangProgFromHOL nb with _ | q <;> simp_all
  | .call none tgt args none, n, h => by
      simp [wordLangProgToHOL] at h
      subst h
      simp only [wordLangProgFromHOL]
      rfl
  | .call none tgt args (some (e, hb, m1, m2)), n, h => by
      simp only [wordLangProgToHOL] at h
      rcases hhb : wordLangProgToHOL hb with _ | nhb <;> simp [hhb] at h
      subst h
      have i0 := wordLangProgFromHOL_isSome_of_toHOL hb nhb hhb
      simp only [wordLangProgFromHOL]
      rcases f0 : wordLangProgFromHOL nhb with _ | q0 <;> simp_all
  | .call (some (vs, sets, rb, l1, l2)) tgt args none, n, h => by
      simp only [wordLangProgToHOL] at h
      rcases hrb : wordLangProgToHOL rb with _ | nrb <;> simp [hrb] at h
      subst h
      have i0 := wordLangProgFromHOL_isSome_of_toHOL rb nrb hrb
      simp only [wordLangProgFromHOL]
      rcases f0 : wordLangProgFromHOL nrb with _ | q0 <;> simp_all
  | .call (some (vs, sets, rb, l1, l2)) tgt args (some (e, hb, m1, m2)), n, h => by
      simp only [wordLangProgToHOL] at h
      rcases hrb : wordLangProgToHOL rb with _ | nrb <;> simp [hrb] at h
      rcases hhb : wordLangProgToHOL hb with _ | nhb <;> simp [hhb] at h
      subst h
      have i0 := wordLangProgFromHOL_isSome_of_toHOL rb nrb hrb
      have i1 := wordLangProgFromHOL_isSome_of_toHOL hb nhb hhb
      simp only [wordLangProgFromHOL]
      rcases f0 : wordLangProgFromHOL nrb with _ | q0 <;> simp_all
      rcases f1 : wordLangProgFromHOL nhb with _ | q1 <;> simp_all
  | .skip, n, h => by simp [wordLangProgToHOL] at h; subst h; rfl
  | .move a b, n, h => by simp [wordLangProgToHOL] at h; subst h; rfl
  | .assign a b, n, h => by simp [wordLangProgToHOL] at h; subst h; rfl
  | .get a b, n, h => by simp [wordLangProgToHOL] at h; subst h; rfl
  | .store a b, n, h => by simp [wordLangProgToHOL] at h; subst h; rfl
  | .set a b, n, h => by simp [wordLangProgToHOL] at h; subst h; rfl
  | .break a, n, h => by simp [wordLangProgToHOL] at h; subst h; rfl
  | .continue a, n, h => by simp [wordLangProgToHOL] at h; subst h; rfl
  | .raise a, n, h => by simp [wordLangProgToHOL] at h; subst h; rfl
  | .return a b, n, h => by simp [wordLangProgToHOL] at h; subst h; rfl
  | .tick, n, h => by simp [wordLangProgToHOL] at h; subst h; rfl
  | .locValue a b, n, h => by simp [wordLangProgToHOL] at h; subst h; rfl
  | .alloc a b, n, h => by simp [wordLangProgToHOL] at h; subst h; rfl
  | .storeConsts a b c d e, n, h => by simp [wordLangProgToHOL] at h; subst h; rfl
  | .opCurrHeap a b c, n, h => by simp [wordLangProgToHOL] at h; subst h; rfl
  | .install a b c d e, n, h => by simp [wordLangProgToHOL] at h; subst h; rfl
  | .codeBufferWrite a b, n, h => by simp [wordLangProgToHOL] at h; subst h; rfl
  | .dataBufferWrite a b, n, h => by simp [wordLangProgToHOL] at h; subst h; rfl
  | .ffi a b c d e f, n, h => by simp [wordLangProgToHOL] at h; subst h; rfl
  | .shareInst a b c, n, h => by simp [wordLangProgToHOL] at h; subst h; rfl
termination_by p => sizeOf p

set_option linter.unusedSimpArgs false in
/-- The reviewed `removeMustTerminate` creates no instruction, so it keeps every
    program inside the decoder's domain (Flapjack carrier fact). -/
theorem wordLangProgFromHOL_isSome_removeMustTerminate {width : Nat} [NeZero width] :
    ∀ n : WordLangProgHOL (BitVec width), (wordLangProgFromHOL n).isSome = true →
      (wordLangProgFromHOL (Compiler.Backend.WordRemove.removeMustTerminate n)).isSome = true
  | .mustTerminate b, h => by
      have hb : (wordLangProgFromHOL b).isSome = true := by
        simp only [wordLangProgFromHOL] at h
        rcases hf : wordLangProgFromHOL b with _ | q <;> simp_all
      exact wordLangProgFromHOL_isSome_removeMustTerminate b hb
  | .seq a b, h => by
      simp only [wordLangProgFromHOL] at h
      rcases ha : wordLangProgFromHOL a with _ | qa <;> rcases hb : wordLangProgFromHOL b with _ | qb <;>
        simp [ha, hb] at h
      have i1 := wordLangProgFromHOL_isSome_removeMustTerminate a (by simp [ha])
      have i2 := wordLangProgFromHOL_isSome_removeMustTerminate b (by simp [hb])
      show (wordLangProgFromHOL (.seq _ _)).isSome = true
      simp only [wordLangProgFromHOL]
      rcases f1 : wordLangProgFromHOL (Compiler.Backend.WordRemove.removeMustTerminate a) with _ | r1 <;>
        rcases f2 : wordLangProgFromHOL (Compiler.Backend.WordRemove.removeMustTerminate b) with _ | r2 <;>
        simp_all
  | .ite op c r a b, h => by
      simp only [wordLangProgFromHOL] at h
      rcases ha : wordLangProgFromHOL a with _ | qa <;> rcases hb : wordLangProgFromHOL b with _ | qb <;>
        simp [ha, hb] at h
      have i1 := wordLangProgFromHOL_isSome_removeMustTerminate a (by simp [ha])
      have i2 := wordLangProgFromHOL_isSome_removeMustTerminate b (by simp [hb])
      show (wordLangProgFromHOL (.ite _ _ _ _ _)).isSome = true
      simp only [wordLangProgFromHOL]
      rcases f1 : wordLangProgFromHOL (Compiler.Backend.WordRemove.removeMustTerminate a) with _ | r1 <;>
        rcases f2 : wordLangProgFromHOL (Compiler.Backend.WordRemove.removeMustTerminate b) with _ | r2 <;>
        simp_all
  | .loop li b lo, h => by
      simp only [wordLangProgFromHOL] at h
      rcases hb : wordLangProgFromHOL b with _ | qb <;> simp [hb] at h
      have i1 := wordLangProgFromHOL_isSome_removeMustTerminate b (by simp [hb])
      show (wordLangProgFromHOL (.loop _ _ _)).isSome = true
      simp only [wordLangProgFromHOL]
      rcases f1 : wordLangProgFromHOL (Compiler.Backend.WordRemove.removeMustTerminate b) with _ | r1 <;>
        simp_all
  | .call none tgt args none, h => h
  | .call none tgt args (some (e, hb, m1, m2)), h => by
      simp only [wordLangProgFromHOL] at h
      rcases hf : wordLangProgFromHOL hb with _ | q <;> simp [hf] at h
      have i1 := wordLangProgFromHOL_isSome_removeMustTerminate hb (by simp [hf])
      show (wordLangProgFromHOL (.call none tgt args (some (e, _, m1, m2)))).isSome = true
      simp only [wordLangProgFromHOL]
      rcases f1 : wordLangProgFromHOL (Compiler.Backend.WordRemove.removeMustTerminate hb) with _ | r1 <;>
        simp_all
  | .call (some (vs, sets, rb, l1, l2)) tgt args none, h => by
      simp only [wordLangProgFromHOL] at h
      rcases hf : wordLangProgFromHOL rb with _ | q <;> simp [hf] at h
      have i1 := wordLangProgFromHOL_isSome_removeMustTerminate rb (by simp [hf])
      show (wordLangProgFromHOL (.call (some (vs, sets, _, l1, l2)) tgt args none)).isSome = true
      simp only [wordLangProgFromHOL]
      rcases f1 : wordLangProgFromHOL (Compiler.Backend.WordRemove.removeMustTerminate rb) with _ | r1 <;>
        simp_all
  | .call (some (vs, sets, rb, l1, l2)) tgt args (some (e, hb, m1, m2)), h => by
      simp only [wordLangProgFromHOL] at h
      rcases hf : wordLangProgFromHOL rb with _ | q <;> rcases hg : wordLangProgFromHOL hb with _ | q' <;>
        simp [hf, hg] at h
      have i1 := wordLangProgFromHOL_isSome_removeMustTerminate rb (by simp [hf])
      have i2 := wordLangProgFromHOL_isSome_removeMustTerminate hb (by simp [hg])
      show (wordLangProgFromHOL
        (.call (some (vs, sets, _, l1, l2)) tgt args (some (e, _, m1, m2)))).isSome = true
      simp only [wordLangProgFromHOL]
      rcases f1 : wordLangProgFromHOL (Compiler.Backend.WordRemove.removeMustTerminate rb) with _ | r1 <;>
        rcases f2 : wordLangProgFromHOL (Compiler.Backend.WordRemove.removeMustTerminate hb) with _ | r2 <;>
        simp_all
  | .skip, h => h
  | .move a b, h => h
  | .inst a, h => h
  | .assign a b, h => h
  | .get a b, h => h
  | .set a b, h => h
  | .store a b, h => h
  | .alloc a b, h => h
  | .storeConsts a b c d e, h => h
  | .raise a, h => h
  | WordLangProgHOL.return a b, h => h
  | WordLangProgHOL.break a, h => h
  | WordLangProgHOL.continue a, h => h
  | .tick, h => h
  | .opCurrHeap a b c, h => h
  | .locValue a b, h => h
  | .install a b c d e, h => h
  | .codeBufferWrite a b, h => h
  | .dataBufferWrite a b, h => h
  | .ffi a b c d e f, h => h
  | .shareInst a b c, h => h
termination_by n => sizeOf n

/-- Conditional codec-image totality for the native `remove_must_terminate` route.
    The premise establishes that the input is in the encoder's image. This does
    not establish that allocator output satisfies that premise at the production
    call site, including its legacy fallback. -/
theorem wordRemoveMustTerminateViaHOL?_isSome {width : Nat} [NeZero width]
    (program : WordProg (BitVec width)) (h : (wordLangProgToHOL program).isSome = true) :
    (wordRemoveMustTerminateViaHOL? program).isSome = true := by
  unfold wordRemoveMustTerminateViaHOL?
  rcases hn : wordLangProgToHOL program with _ | native
  · simp [hn] at h
  simp only [Option.bind_some]
  exact wordLangProgFromHOL_isSome_removeMustTerminate native
    (wordLangProgFromHOL_isSome_of_toHOL program native hn)

/-- In particular the route succeeds on every executed program that was itself
    decoded from an exact native program (the output of any reviewed native pass
    routed through the codec). -/
theorem wordRemoveMustTerminateViaHOL?_isSome_of_fromHOL {width : Nat} [NeZero width]
    (native : WordLangProgHOL (BitVec width)) (program : WordProg (BitVec width))
    (h : wordLangProgFromHOL native = some program) :
    (wordRemoveMustTerminateViaHOL? program).isSome = true :=
  wordRemoveMustTerminateViaHOL?_isSome program
    (by rw [wordLangProgToHOL_of_fromHOL native program h]; rfl)

end Flapjack.RiscV
