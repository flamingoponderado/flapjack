import Flapjack.Compiler.Backend.WordSimp.ProductionConstFp
import Flapjack.RiscV.WordFuseConditions

/-! Executed duplicate-if hoisting against native `try_if_hoist2`,
`try_if_hoist1` and `simp_duplicate_if`. Flapjack carrier correspondence with
no HOL original: from encoded inputs the executed results encode to the native
ones, and the executed hoist fails exactly when the native one does. Only
input encoding is assumed. -/
namespace Flapjack.Compiler.Backend.WordSimp

open RiscV

/-- The encoder preserves the outer constructor: a native `Seq` comes only
from an executed `seq` whose components encode. -/
private theorem encoded_seq {width : Nat} {p : WordProg (BitVec width)}
    {a b : WordLangProgHOL (BitVec width)} (encoded : wordLangProgToHOL p = some (.seq a b)) :
    ∃ pa pb, p = .seq pa pb ∧ wordLangProgToHOL pa = some a ∧ wordLangProgToHOL pb = some b := by
  cases p <;> (try simp [wordLangProgToHOL, Option.bind_eq_some_iff] at encoded)
  case seq pa pb => exact ⟨pa, pb, rfl, encoded⟩
  case call returns target arguments handler =>
    rcases returns with _ | ⟨_, _, _, _, _⟩ <;> rcases handler with _ | ⟨_, _, _, _⟩ <;>
      simp [wordLangProgToHOL, Option.bind_eq_some_iff] at encoded

/-- Native `If` comes only from an executed `ite` with encoded branches. -/
private theorem encoded_ite {width : Nat} {p : WordProg (BitVec width)} {cmp : Cmp} {c : Nat}
    {r : WordRegImm (BitVec width)} {a b : WordLangProgHOL (BitVec width)}
    (encoded : wordLangProgToHOL p = some (.ite cmp c r a b)) :
    ∃ pa pb, p = .ite cmp c r pa pb ∧ wordLangProgToHOL pa = some a ∧
      wordLangProgToHOL pb = some b := by
  cases p <;> (try simp [wordLangProgToHOL, Option.bind_eq_some_iff] at encoded)
  case ite cmp' c' r' pa pb =>
    obtain ⟨_, ha, _, hb, rfl, rfl, rfl, rfl, rfl⟩ := encoded
    exact ⟨pa, pb, rfl, ha, hb⟩
  case call returns target arguments handler =>
    rcases returns with _ | ⟨_, _, _, _, _⟩ <;> rcases handler with _ | ⟨_, _, _, _⟩ <;>
      simp [wordLangProgToHOL, Option.bind_eq_some_iff] at encoded

/-- Native `Raise` comes only from an executed `raise`. -/
private theorem encoded_raise {width : Nat} {p : WordProg (BitVec width)} {n : Nat}
    (encoded : wordLangProgToHOL p = some (.raise n)) : p = .raise n := by
  cases p <;> (try simp [wordLangProgToHOL, Option.bind_eq_some_iff] at encoded)
  case raise => rw [encoded]
  case call returns target arguments handler =>
    rcases returns with _ | ⟨_, _, _, _, _⟩ <;> rcases handler with _ | ⟨_, _, _, _⟩ <;>
      simp [wordLangProgToHOL, Option.bind_eq_some_iff] at encoded

theorem destRaise_production {width : Nat} [NeZero width] (p : WordProg (BitVec width))
    (native : WordLangProgHOL (BitVec width)) (encoded : wordLangProgToHOL p = some native) :
    wordDestRaise p = destRaiseNum native := by
  cases native
  case raise n => rw [encoded_raise encoded]; rfl
  all_goals
    simp only [destRaiseNum]
    cases p <;> first | rfl | (simp [wordLangProgToHOL] at encoded)

theorem destSeqRaise_production {width : Nat} [NeZero width] (p : WordProg (BitVec width))
    (native : WordLangProgHOL (BitVec width)) (encoded : wordLangProgToHOL p = some native) :
    wordDestRaise (wordDestSeq p).2 = destRaiseNum (destSeq native).2 := by
  cases native
  case seq a b =>
    obtain ⟨pa, pb, rfl, _, hb⟩ := encoded_seq encoded
    exact destRaise_production pb b hb
  all_goals
    simp only [destSeq]
    rw [← destRaise_production p _ encoded]
    cases p <;> first | rfl | (simp [wordLangProgToHOL, Option.bind_eq_some_iff] at encoded)

theorem prefixSafe_production {width : Nat} [NeZero width] (p : WordProg (BitVec width))
    (native : WordLangProgHOL (BitVec width)) (encoded : wordLangProgToHOL p = some native) :
    wordConditionPrefixSafe p = isSimple native := by
  cases p <;> (try simp [wordLangProgToHOL, Option.bind_eq_some_iff, Option.map_eq_some_iff] at encoded)
  all_goals (try subst encoded)
  all_goals (try rfl)
  case call returns target arguments handler =>
    rcases returns with _ | ⟨_, _, _, _, _⟩ <;> rcases handler with _ | ⟨_, _, _, _⟩ <;>
      simp [wordLangProgToHOL, Option.bind_eq_some_iff] at encoded
    all_goals first
      | (subst encoded; rfl)
      | (obtain ⟨_, _, rfl⟩ := encoded; rfl)
      | (obtain ⟨_, _, _, _, rfl⟩ := encoded; rfl)
  all_goals first
    | (obtain ⟨_, _, rfl⟩ := encoded; rfl)
    | (obtain ⟨_, _, _, _, rfl⟩ := encoded; rfl)

private theorem hoistConstFp_production {width : Nat} [NeZero width]
    (p : WordProg (BitVec width)) (native : WordLangProgHOL (BitVec width))
    (encoded : wordLangProgToHOL p = some native) :
    wordLangProgToHOL (wordHoistConstFp p) = some (constFp native) :=
  constFpLoop_empty_production p native encoded

private theorem seq3_encoded {width : Nat} {b i d : WordProg (BitVec width)}
    {nb ni nd : WordLangProgHOL (BitVec width)} (hb : wordLangProgToHOL b = some nb)
    (hi : wordLangProgToHOL i = some ni) (hd : wordLangProgToHOL d = some nd) :
    wordLangProgToHOL (.seq (.seq b i) d) = some (.seq (.seq nb ni) nd) := by
  simp [wordLangProgToHOL, hb, hi, hd]

theorem hoistCandidate_production {width : Nat} [NeZero width] (cmp : Cmp) (c : Nat)
    (r : WordRegImm (BitVec width)) (d b1 b2 i k : WordProg (BitVec width))
    (nd nb1 nb2 ni nk : WordLangProgHOL (BitVec width))
    (hd : wordLangProgToHOL d = some nd) (hb1 : wordLangProgToHOL b1 = some nb1)
    (hb2 : wordLangProgToHOL b2 = some nb2) (hi : wordLangProgToHOL i = some ni)
    (hk : wordLangProgToHOL k = some nk) :
    (wordHoistIfCandidate cmp c r d b1 b2 i k).map wordLangProgToHOL =
      (let res1 := destRaiseNum (destSeq (constFp (.seq (.seq nb1 ni) nd))).2
       if res1 = 0 then none
       else
         let res2 := destRaiseNum (destSeq (constFp (.seq (.seq nb2 ni) nd))).2
         if res1 + res2 ≠ 3 then none
         else some (constFp (.ite cmp c r (.seq (.seq nb1 ni) nk) (.seq (.seq nb2 ni) nk)))).map
        some := by
  have t1 := destSeqRaise_production _ _ (hoistConstFp_production _ _ (seq3_encoded hb1 hi hd))
  have t2 := destSeqRaise_production _ _ (hoistConstFp_production _ _ (seq3_encoded hb2 hi hd))
  have fin : wordLangProgToHOL (wordHoistConstFp (.ite cmp c r (.seq (.seq b1 i) k)
      (.seq (.seq b2 i) k))) =
      some (constFp (.ite cmp c r (.seq (.seq nb1 ni) nk) (.seq (.seq nb2 ni) nk))) :=
    hoistConstFp_production _ _ (by simp [wordLangProgToHOL, hb1, hb2, hi, hk])
  unfold wordHoistIfCandidate
  simp only [t1, t2]
  generalize destRaiseNum (destSeq (constFp ((nb1.seq ni).seq nd))).2 = x1
  generalize destRaiseNum (destSeq (constFp ((nb2.seq ni).seq nd))).2 = x2
  by_cases h1 : x1 = 0 <;> by_cases h2 : x1 + x2 = 3 <;> simp [h1, h2, fin]

theorem tryIfHoist2_production {width : Nat} [NeZero width] :
    ∀ (n : Nat) (p i d k : WordProg (BitVec width)) (np ni nd nk : WordLangProgHOL (BitVec width)),
      wordLangProgToHOL p = some np → wordLangProgToHOL i = some ni →
      wordLangProgToHOL d = some nd → wordLangProgToHOL k = some nk →
      (wordTryIfHoist2 n p i d k).map wordLangProgToHOL = (tryIfHoist2 n np ni nd nk).map some
  | 0, _, _, _, _, _, _, _, _, _, _, _, _ => by simp [wordTryIfHoist2, tryIfHoist2]
  | n + 1, p, i, d, k, np, ni, nd, nk, hp, hi, hd, hk => by
      cases np with
      | ite cmp c r a b =>
        obtain ⟨pa, pb, rfl, ha, hb⟩ := encoded_ite hp
        simp only [wordTryIfHoist2, tryIfHoist2]
        exact hoistCandidate_production cmp c r d pa pb i k nd a b ni nk hd ha hb hi hk
      | seq p3 p4 =>
        obtain ⟨pa, pb, rfl, ha, hb⟩ := encoded_seq hp
        simp only [wordTryIfHoist2, tryIfHoist2]
        cases p4 with
        | ite cmp c r b1 b2 =>
          obtain ⟨q1, q2, rfl, h1, h2⟩ := encoded_ite hb
          simp only [destIf]
          have t1 := destSeqRaise_production _ _
            (hoistConstFp_production _ _ (seq3_encoded h1 hi hd))
          have t2 := destSeqRaise_production _ _
            (hoistConstFp_production _ _ (seq3_encoded h2 hi hd))
          have fin : wordLangProgToHOL (wordHoistConstFp (.ite cmp c r (.seq (.seq q1 i) k)
              (.seq (.seq q2 i) k))) =
              some (constFp (.ite cmp c r (.seq (.seq b1 ni) nk) (.seq (.seq b2 ni) nk))) :=
            hoistConstFp_production _ _ (by simp [wordLangProgToHOL, h1, h2, hi, hk])
          unfold wordHoistIfCandidate
          simp only [t1, t2]
          generalize destRaiseNum (destSeq (constFp ((b1.seq ni).seq nd))).2 = x1
          generalize destRaiseNum (destSeq (constFp ((b2.seq ni).seq nd))).2 = x2
          by_cases e1 : x1 = 0 <;> by_cases e2 : x1 + x2 = 3 <;>
            simp [e1, e2, fin, wordLangProgToHOL, ha]
        | _ =>
          simp only [destIf]
          split
          · simp [wordLangProgToHOL, Option.bind_eq_some_iff] at hb
          · rw [prefixSafe_production pb _ hb]
            split
            · exact tryIfHoist2_production n pa (.seq pb i) d k p3 _ nd nk ha
                (by simp [wordLangProgToHOL, hb, hi]) hd hk
            · rfl
      | _ =>
        simp only [wordTryIfHoist2, tryIfHoist2]
        split
        · simp [wordLangProgToHOL, Option.bind_eq_some_iff] at hp
        · simp [wordLangProgToHOL, Option.bind_eq_some_iff] at hp
        · rfl

theorem tryIfHoist1_production {width : Nat} [NeZero width] (p1 p2 : WordProg (BitVec width))
    (np1 np2 : WordLangProgHOL (BitVec width)) (h1 : wordLangProgToHOL p1 = some np1)
    (h2 : wordLangProgToHOL p2 = some np2) :
    (wordTryIfHoist1 p1 p2).map wordLangProgToHOL = (tryIfHoist1 np1 np2).map some := by
  cases np2 with
  | ite cmp c r a b =>
    obtain ⟨pa, pb, rfl, ha, hb⟩ := encoded_ite h2
    simp only [wordTryIfHoist1, tryIfHoist1, destIf, rewriteDuplicateIfMaxReassoc]
    exact tryIfHoist2_production 8 p1 .skip _ _ np1 .skip _ _ h1 rfl
      (by simp [wordLangProgToHOL]) h2
  | _ =>
    simp only [wordTryIfHoist1, tryIfHoist1, destIf]
    split
    · simp [wordLangProgToHOL, Option.bind_eq_some_iff] at h2
    · rfl

/-- Executed `wordSimpDuplicateIf` encodes to native `simpDuplicateIf` for every
encoded input. Flapjack carrier correspondence; no HOL original. -/
theorem simpDuplicateIf_production {width : Nat} [NeZero width] :
    ∀ (p : WordProg (BitVec width)) (native : WordLangProgHOL (BitVec width)),
      wordLangProgToHOL p = some native →
      wordLangProgToHOL (wordSimpDuplicateIf p) = some (simpDuplicateIf native)
  | .seq a b, native, encoded => by
      simp only [wordLangProgToHOL, Option.bind_eq_bind, Option.bind_eq_some_iff,
        Option.pure_def, Option.some.injEq] at encoded
      obtain ⟨na, ha, nb, hb, rfl⟩ := encoded
      have ia := simpDuplicateIf_production a na ha
      have ib := simpDuplicateIf_production b nb hb
      have hh := tryIfHoist1_production _ _ _ _ ia ib
      unfold wordSimpDuplicateIf simpDuplicateIf
      dsimp only
      cases hx : wordTryIfHoist1 (wordSimpDuplicateIf a) (wordSimpDuplicateIf b) with
      | none =>
        rw [hx] at hh
        cases hn : tryIfHoist1 (simpDuplicateIf na) (simpDuplicateIf nb) with
        | none => simp [wordLangProgToHOL, ia, ib]
        | some _ => rw [hn] at hh; simp at hh
      | some r =>
        rw [hx] at hh
        cases hn : tryIfHoist1 (simpDuplicateIf na) (simpDuplicateIf nb) with
        | none => rw [hn] at hh; simp at hh
        | some nr =>
          rw [hn] at hh
          simp only [Option.map_some, Option.some.injEq] at hh
          exact seqAssoc_production r nr hh
  | .ite op c r a b, native, encoded => by
      simp only [wordLangProgToHOL, Option.bind_eq_bind, Option.bind_eq_some_iff,
        Option.pure_def, Option.some.injEq] at encoded
      obtain ⟨na, ha, nb, hb, rfl⟩ := encoded
      unfold wordSimpDuplicateIf simpDuplicateIf
      simp [wordLangProgToHOL, simpDuplicateIf_production a na ha,
        simpDuplicateIf_production b nb hb]
  | .loop li body lo, native, encoded => by
      simp only [wordLangProgToHOL, Option.bind_eq_bind, Option.bind_eq_some_iff,
        Option.pure_def, Option.some.injEq] at encoded
      obtain ⟨nbody, hbody, rfl⟩ := encoded
      unfold wordSimpDuplicateIf simpDuplicateIf
      simp [wordLangProgToHOL, simpDuplicateIf_production body nbody hbody]
  | .mustTerminate body, native, encoded => by
      simp only [wordLangProgToHOL, Option.map_eq_some_iff] at encoded
      obtain ⟨nbody, hbody, rfl⟩ := encoded
      unfold wordSimpDuplicateIf simpDuplicateIf
      simp [wordLangProgToHOL, simpDuplicateIf_production body nbody hbody]
  | .call none tgt args none, native, encoded => by
      simp [wordLangProgToHOL] at encoded; subst encoded
      unfold wordSimpDuplicateIf simpDuplicateIf
      simp [wordLangProgToHOL]
  | .call none tgt args (some (exn, hbody, h1, h2)), native, encoded => by
      cases hh : wordLangProgToHOL hbody <;> simp [wordLangProgToHOL, hh] at encoded
      subst encoded
      unfold wordSimpDuplicateIf simpDuplicateIf
      simp [wordLangProgToHOL, simpDuplicateIf_production hbody _ hh]
  | .call (some (names, sets, body, l1, l2)) tgt args none, native, encoded => by
      cases hbd : wordLangProgToHOL body <;> simp [wordLangProgToHOL, hbd] at encoded
      subst encoded
      unfold wordSimpDuplicateIf simpDuplicateIf
      simp [wordLangProgToHOL, simpDuplicateIf_production body _ hbd]
  | .call (some (names, sets, body, l1, l2)) tgt args (some (exn, hbody, h1, h2)), native,
      encoded => by
      cases hbd : wordLangProgToHOL body <;> cases hh : wordLangProgToHOL hbody <;>
        simp [wordLangProgToHOL, hbd, hh] at encoded
      subst encoded
      unfold wordSimpDuplicateIf simpDuplicateIf
      simp [wordLangProgToHOL, simpDuplicateIf_production body _ hbd,
        simpDuplicateIf_production hbody _ hh]
  | .skip, native, encoded | .move _ _, native, encoded | .assign _ _, native, encoded
  | .get _ _, native, encoded | .set _ _, native, encoded | .store _ _, native, encoded
  | .alloc _ _, native, encoded | .storeConsts _ _ _ _ _, native, encoded
  | .raise _, native, encoded | .return _ _, native, encoded | .break _, native, encoded
  | .continue _, native, encoded | .tick, native, encoded | .opCurrHeap _ _ _, native, encoded
  | .locValue _ _, native, encoded | .install _ _ _ _ _, native, encoded
  | .codeBufferWrite _ _, native, encoded | .dataBufferWrite _ _, native, encoded
  | .ffi _ _ _ _ _ _, native, encoded | .shareInst _ _ _, native, encoded => by
      simp only [wordLangProgToHOL, Option.some.injEq] at encoded; subst encoded
      unfold wordSimpDuplicateIf simpDuplicateIf
      simp [wordLangProgToHOL]
  | .inst i, native, encoded => by
      simp only [wordLangProgToHOL, Option.map_eq_some_iff] at encoded
      obtain ⟨ni, hi, rfl⟩ := encoded
      unfold wordSimpDuplicateIf simpDuplicateIf
      simp [wordLangProgToHOL, hi]
termination_by p => sizeOf p

end Flapjack.Compiler.Backend.WordSimp
