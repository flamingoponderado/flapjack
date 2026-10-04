import Mathlib.Tactic.Set
import Flapjack.Compiler.Backend.StackToLab.Proofs.CodeInstalled
import Flapjack.Compiler.Backend.StackAlloc.Proofs.Labels
import Flapjack.Compiler.Backend.Semantics.StackSem.Control
import Flapjack.Compiler.Backend.Semantics.TargetSem.State
import Flapjack.Compiler.Backend.StackToLab.Proofs.Prelude
import Flapjack.Compiler.Backend.LabSem.Evaluate
import Flapjack.Compiler.Backend.Semantics.StackSem.EvaluateDef

/-! Flatten helper lemmas and result views of `stack_to_labProofScript.sml`
(lines 890-1206), used by `flatten_correct`. -/

namespace Flapjack.Compiler.Backend.StackToLab.Proofs.FlattenHelpers
open Flapjack Flapjack.Compiler.Backend.LabLang Flapjack.Compiler.Backend.LabSem
open Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.StackToLab.Proofs.CodeInstalled
open Flapjack.Basis.Pure.MlString

/-- `flatten` never decreases the next free label. -/
theorem flattenLeq {width : Nat} [NeZero width] :
    ∀ (t : Bool) (x : HolProg width) (y z : Nat) (cs bs : List Nat),
      z ≤ (flattenHOL t x y z cs bs).2.2 := by
  intro t x y z cs bs
  induction t, x, z, cs, bs using flattenHOL.induct y
  case case26 =>
    rw [flattenHOL]
    all_goals assumption
  all_goals
    rw [flattenHOL]
    try simp (config := { zetaDelta := true }) only [*] at *
  all_goals (try split_ifs) <;> (try simp_all) <;> omega

/-- A non-bad function return is present. -/
theorem notBadFunReturnImpSome {width : Nat} [NeZero width] :
    ∀ q : Option (StackSemResult width), ¬StackSemControl.badFunReturn q = true →
      ∃ n, q = some n := by
  intro q h
  cases q with
  | none => simp [StackSemControl.badFunReturn] at h
  | some n => exact ⟨n, rfl⟩

/-- Every program's next label from 2 is at least 2. -/
theorem nextLabNonZero {width : Nat} [NeZero width] :
    ∀ p : HolProg width, 2 ≤ StackAlloc.nextLabHOL p 2 := by
  intro p
  rw [StackAlloc.next_lab_EQ_MAX p 0 2]
  omega

/-- The tail flag only affects `Seq`. -/
theorem flattenTF {width : Nat} [NeZero width] {p_2 : HolProg width} {p_1 m : Nat}
    {cs bs : List Nat} :
    ¬isSeqHOL p_2 = true → flattenHOL true p_2 p_1 m cs bs = flattenHOL false p_2 p_1 m cs bs := by
  intro h
  cases p_2 with
  | seq => simp [isSeqHOL] at h
  | call r d hd =>
    rcases r with _ | ⟨_, _, _, _⟩ <;> rcases hd with _ | ⟨_, _, _⟩ <;> simp only [flattenHOL]
  | _ => simp only [flattenHOL]

/-- An out-of-list `find_lab` result is the default zero. -/
theorem notMemFindLabImp : ∀ (bs : List Nat) (n : Nat), findLabHOL n bs ∉ bs → findLabHOL n bs = 0 := by
  intro bs n h
  unfold findLabHOL at *
  cases hn : bs[n]? with
  | none => simp
  | some v =>
    rw [hn] at h
    exact absurd (List.mem_of_getElem? hn) h

/-- A defined label position stays defined in an extended program. -/
theorem isSomeLocToPcPrefix {width : Nat} [NeZero width] {n k : Nat}
    {c1 c2 : List (Section (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width)))} :
    (locToPc n k c1).isSome ∧ c1 <+: c2 → (locToPc n k c2).isSome := by
  rintro ⟨some_, pre⟩
  obtain ⟨pc, hpc⟩ := Option.isSome_iff_exists.mp some_
  rw [locToPcIsPrefix n k c1 pc c2 ⟨hpc, pre⟩]
  rfl

/-- Pointwise form of `is_some_loc_to_pc_prefix`. -/
theorem everyIsSomeLocToPcPrefix {width : Nat} [NeZero width] {n : Nat} {cs : List Nat}
    {c1 c2 : List (Section (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width)))} :
    (∀ k ∈ cs, (locToPc n k c1).isSome) ∧ c1 <+: c2 → ∀ k ∈ cs, (locToPc n k c2).isSome := by
  rintro ⟨all, pre⟩ k mem
  exact isSomeLocToPcPrefix ⟨all k mem, pre⟩

/-- Canonical native StackSem state roundtrip, re-exported here as qualifier
infrastructure; this witness has no independently named HOL original. -/
theorem holFmapAsFiniteSupportRelationWitness_StackSemStateFiniteExact
    {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : StackSemStateBroad width C F) (h : state.FiniteSupport),
      (StackSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : StackSemStateFiniteExact width C F,
      StackSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  StackSemStateSupport.holFmapAsFiniteSupportWitness

/-- Programs that `flatten` marks as not returning always produce a StackSem
result. The quantified native state translates the original `regs`, `fp_regs`
and `store` finite maps through the canonical finite-support representation;
the `code` field remains a literal sptree and is not qualified as a finite map. -/
theorem noRetCorrect {width : Nat} [NeZero width] {C F : Type} :
    ∀ (t : Bool) (p : HolProg width) (y z : Nat) (cs bs : List Nat),
      (flattenHOL t p y z cs bs).2.1 = true →
      ∀ s : StackSemStateFiniteExact width C F, (StackSemEvaluate.evaluate (p, s)).1.isSome := by
  intro t p y z cs bs
  induction t, p, z, cs, bs using flattenHOL.induct y
  all_goals intro hnr s
  case case26 =>
    rw [flattenHOL] at hnr
    all_goals first | assumption | simp at hnr
  all_goals rw [flattenHOL] at hnr
  all_goals try simp (config := { zetaDelta := true }) only [*] at *
  all_goals try (simp at hnr; done)
  all_goals try simp at hnr
  case case3 => rw [StackSemEvaluate.evaluate_halt]; split <;> rfl
  case case12 => rw [StackSemEvaluate.evaluate_raise]; split <;> rfl
  case case13 => rw [StackSemEvaluate.evaluate_ret]; split <;> rfl
  case case14 => rw [StackSemEvaluate.evaluate_break]; rfl
  case case15 => rw [StackSemEvaluate.evaluate_continue]; rfl
  case case4 =>
    rename_i ihFirst ihSecond
    rw [StackSemEvaluate.evaluate_seq]
    split
    · rename_i s1 heq
      have first := congrArg Prod.fst heq
      simp only [StackSemControl.fixClock] at first
      rcases hnr with h1 | h2
      · have := ihFirst h1 s; rw [first] at this; simp at this
      · exact ihSecond h2 _
    · rename_i res s1 hres heq
      have first := congrArg Prod.fst heq
      simp only [StackSemControl.fixClock] at first
      cases res with
      | none => exact absurd rfl hres
      | some r => rfl
  case case8 =>
    rename_i ihThen ihElse
    rw [StackSemEvaluate.evaluate_ite]
    repeat' split
    all_goals first | rfl | exact ihThen trivial _ | exact ihElse hnr _
  case case16 =>
    rw [StackSemEvaluate.evaluate_rawCall]
    repeat' split
    all_goals first | rfl |
      (rename_i hb; obtain ⟨n, hn⟩ := notBadFunReturnImpSome _ hb; simp [hn])
  case case17 =>
    simp only [StackSemEvaluate.evaluate_call]
    repeat' split
    all_goals first | rfl |
      (rename_i hb; obtain ⟨n, hn⟩ := notBadFunReturnImpSome _ hb; simp [hn])
  case case6 => split_ifs at hnr
  case case18 =>
    rename_i ihRet
    simp only [StackSemEvaluate.evaluate_call]
    repeat' split
    all_goals first | rfl | exact ihRet hnr _ | (simp_all; done) |
      exact Option.isSome_iff_ne_none.mpr ‹¬_ = none›
  case case19 =>
    rename_i ihRet ihHandler
    simp only [StackSemEvaluate.evaluate_call]
    repeat' split
    all_goals first | rfl | exact ihRet hnr.1 _ | exact ihHandler hnr.2 _ | (simp_all; done) |
      exact Option.isSome_iff_ne_none.mpr ‹¬_ = none›

private theorem appAppend {α : Type} (a b : AppList α) :
    appListAppend (.append a b) = appListAppend a ++ appListAppend b :=
  (appListAppend_thm a b []).1

private theorem appList {α : Type} (l : List α) : appListAppend (.list l) = l :=
  (appListAppend_thm .nil .nil l).2.1

/-- The label-preservation invariant of `stack_to_lab_lab_pres`, for a
flattening of a program with labels `E` from `nl` to `nl'` producing labels `L`. -/
private def LabPres (n nl nl' : Nat) (E L : List (Nat × Nat)) : Prop :=
  (∀ l ∈ L, l.1 = n ∧ l.2 ≠ 0 ∧ l.2 ≠ 1) ∧ L.Nodup ∧
    (∀ lab ∈ L, lab ∈ E ∨ (nl ≤ lab.2 ∧ lab.2 < nl')) ∧ nl ≤ nl'

private theorem labPresNil (n nl : Nat) (E : List (Nat × Nat)) : LabPres n nl nl E [] := by
  simp [LabPres]

private theorem labPresFresh {n k : Nat} (hk : 2 ≤ k) (E : List (Nat × Nat)) :
    LabPres n k (k + 1) E [(n, k)] := by
  refine ⟨?_, by simp, ?_, by omega⟩
  · intro l hl; simp at hl; subst hl; simp; omega
  · intro l hl; simp at hl; subst hl; right; simp

private theorem labPresKnown {n nl : Nat} {E : List (Nat × Nat)} {x : Nat × Nat}
    (hx : x ∈ E) (hgood : x.1 = n ∧ x.2 ≠ 0 ∧ x.2 ≠ 1) : LabPres n nl nl E [x] := by
  refine ⟨?_, by simp, ?_, le_refl _⟩
  · intro l hl; simp at hl; subst hl; exact hgood
  · intro l hl; simp at hl; subst hl; left; exact hx

private theorem labPresWeaken {n nl0 nl nl' : Nat} {E E' L : List (Nat × Nat)}
    (h : LabPres n nl nl' E L) (hnl : nl0 ≤ nl) (hE : ∀ x ∈ E, x ∈ E') :
    LabPres n nl0 nl' E' L := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨h1, h2, ?_, by omega⟩
  intro lab hl
  rcases h3 lab hl with h | h
  · exact .inl (hE _ h)
  · exact .inr ⟨by omega, h.2⟩

private theorem labPresPerm {n nl nl' : Nat} {E L L' : List (Nat × Nat)}
    (h : LabPres n nl nl' E L) (hp : L.Perm L') : LabPres n nl nl' E L' := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  exact ⟨fun l hl => h1 l (hp.mem_iff.mpr hl), hp.nodup_iff.mp h2,
    fun l hl => h3 l (hp.mem_iff.mpr hl), h4⟩

private theorem labPresAppend {n nl nl1 nl2 : Nat} {E E1 E2 L1 L2 : List (Nat × Nat)}
    (h1 : LabPres n nl nl1 E1 L1) (h2 : LabPres n nl1 nl2 E2 L2)
    (disj : ∀ x ∈ E1, x ∉ E2) (b1 : ∀ e ∈ E1, e.2 < nl) (b2 : ∀ e ∈ E2, e.2 < nl)
    (s1 : ∀ x ∈ E1, x ∈ E) (s2 : ∀ x ∈ E2, x ∈ E) :
    LabPres n nl nl2 E (L1 ++ L2) := by
  obtain ⟨g1, d1, m1, o1⟩ := h1
  obtain ⟨g2, d2, m2, o2⟩ := h2
  refine ⟨?_, ?_, ?_, by omega⟩
  · intro l hl
    rcases List.mem_append.mp hl with hl | hl
    · exact g1 l hl
    · exact g2 l hl
  · rw [List.nodup_append]
    refine ⟨d1, d2, ?_⟩
    intro x hx1 y hy2 hxy
    subst hxy
    rcases m1 x hx1 with e1 | f1 <;> rcases m2 x hy2 with e2 | f2
    · exact disj x e1 e2
    · have := b1 x e1; omega
    · have := b2 x e2; omega
    · omega
  · intro lab hl
    rcases List.mem_append.mp hl with hl | hl
    · rcases m1 lab hl with e | f
      · exact .inl (s1 _ e)
      · exact .inr ⟨f.1, by omega⟩
    · rcases m2 lab hl with e | f
      · exact .inl (s2 _ e)
      · exact .inr ⟨by omega, f.2⟩

private theorem labPresNil' {n nl nl' : Nat} (E : List (Nat × Nat)) (h : nl ≤ nl') :
    LabPres n nl nl' E [] := by
  simp [LabPres, h]

private theorem labPresApp {n nl nl1 nl2 : Nat} {E1 E2 L1 L2 : List (Nat × Nat)}
    (h1 : LabPres n nl nl1 E1 L1) (h2 : LabPres n nl1 nl2 E2 L2)
    (hD : (E1 ++ E2).Nodup) (hb : ∀ e ∈ E1 ++ E2, e.2 < nl) :
    LabPres n nl nl2 (E1 ++ E2) (L1 ++ L2) := by
  rw [List.nodup_append] at hD
  exact labPresAppend h1 h2 (fun x hx hx2 => hD.2.2 x hx x hx2 rfl)
    (fun e he => hb e (List.mem_append_left _ he)) (fun e he => hb e (List.mem_append_right _ he))
    (fun x hx => List.mem_append_left _ hx) (fun x hx => List.mem_append_right _ hx)

private theorem labPresFresh' {n k : Nat} (hk : 2 ≤ k) :
    LabPres n k (k + 1) [] [(n, k)] := labPresFresh hk []

private theorem labelsBound {width : Nat} [NeZero width] {p : HolProg width} {nl : Nat}
    (h : StackAlloc.nextLabHOL p 2 ≤ nl) :
    ∀ e ∈ StackPropsCodeLabels.extractLabels p, e.2 < nl := fun e he => by
  have := StackAlloc.extract_labels_next_lab p 0 e he
  omega

private theorem nodupLeft {α : Type} {A B : List α} (h : (A ++ B).Nodup) : A.Nodup :=
  (List.nodup_append.mp h).1

private theorem nodupRight {α : Type} {A B : List α} (h : (A ++ B).Nodup) : B.Nodup :=
  (List.nodup_append.mp h).2.1

set_option maxHeartbeats 1000000 in
private theorem labPresAux {width : Nat} [NeZero width] (n : Nat) :
    ∀ (p : HolProg width) (nl : Nat) (cs bs : List Nat),
      (∀ l ∈ StackPropsCodeLabels.extractLabels p, l.1 = n ∧ l.2 ≠ 0 ∧ l.2 ≠ 1) →
      (StackPropsCodeLabels.extractLabels p).Nodup →
      StackAlloc.nextLabHOL p 2 ≤ nl →
      LabPres n nl (flattenHOL false p n nl cs bs).2.2 (StackPropsCodeLabels.extractLabels p)
        (LabProps.LabelSets.extractLabels (appListAppend (flattenHOL false p n nl cs bs).1))
  | .seq a b, nl, cs, bs, hE, hD, hnl => by
    have two : 2 ≤ nl := le_trans (nextLabNonZero _) hnl
    have bnd := labelsBound hnl
    rw [StackAlloc.next_lab_thm] at hnl
    dsimp only at hnl
    simp only [StackPropsCodeLabels.extractLabels] at hE hD bnd ⊢
    rcases h1 : flattenHOL false a n nl cs bs with ⟨ys1, nr1, nl1⟩
    have pa := labPresAux n a nl cs bs (fun l h => hE l (List.mem_append_left _ h))
      (nodupLeft hD) (by omega)
    rw [h1] at pa; dsimp only at pa
    rcases h2 : flattenHOL false b n nl1 cs bs with ⟨ys2, nr2, nl2⟩
    have pb := labPresAux n b nl1 cs bs (fun l h => hE l (List.mem_append_right _ h))
      (nodupRight hD) (by have := pa.2.2.2; omega)
    rw [h2] at pb; dsimp only at pb
    rw [flattenHOL]
    simp only [h1, h2, Bool.false_eq_true, if_false, appAppend, LabProps.LabelSets.extractLabels_append]
    exact labPresApp pa pb hD bnd
  | .ite c r ri a b, nl, cs, bs, hE, hD, hnl => by
    have two : 2 ≤ nl := le_trans (nextLabNonZero _) hnl
    have bnd := labelsBound hnl
    rw [StackAlloc.next_lab_thm] at hnl
    dsimp only at hnl
    simp only [StackPropsCodeLabels.extractLabels] at hE hD bnd ⊢
    rcases h1 : flattenHOL false a n nl cs bs with ⟨ys1, nr1, nl1⟩
    have pa := labPresAux n a nl cs bs (fun l h => hE l (List.mem_append_left _ h))
      (nodupLeft hD) (by omega)
    rw [h1] at pa; dsimp only at pa
    rcases h2 : flattenHOL false b n nl1 cs bs with ⟨ys2, nr2, nl2⟩
    have pb := labPresAux n b nl1 cs bs (fun l h => hE l (List.mem_append_right _ h))
      (nodupRight hD) (by have := pa.2.2.2; omega)
    rw [h2] at pb; dsimp only at pb
    have le1 := pa.2.2.2
    have le2 := pb.2.2.2
    have fr : LabPres n nl2 (nl2 + 1) [] [(n, nl2)] := labPresFresh' (by omega)
    have fr2 : LabPres n (nl2 + 1) (nl2 + 1 + 1) [] [(n, nl2 + 1)] := labPresFresh' (by omega)
    have both := labPresApp pa pb hD bnd
    have hD' : (StackPropsCodeLabels.extractLabels a ++ StackPropsCodeLabels.extractLabels b ++
        []).Nodup := by simpa using hD
    have bnd' : ∀ e ∈ StackPropsCodeLabels.extractLabels a ++ StackPropsCodeLabels.extractLabels b
        ++ [], e.2 < nl := by simpa using bnd
    rw [flattenHOL]
    simp only [h1, h2]
    split_ifs with s1 s2 s3 s4 s5
    · simp only [appList, LabProps.LabelSets.extractLabels]
      exact labPresNil' _ (by omega)
    · have := labPresApp (labPresApp (labPresNil' (StackPropsCodeLabels.extractLabels a) le1) pb
        hD bnd) fr hD' bnd'
      simpa [appAppend, appList, LabProps.LabelSets.extractLabels_append,
        LabProps.LabelSets.extractLabels] using this
    · have := labPresApp (labPresApp pa (labPresNil' (StackPropsCodeLabels.extractLabels b) le2)
        hD bnd) fr hD' bnd'
      simpa [appAppend, appList, LabProps.LabelSets.extractLabels_append,
        LabProps.LabelSets.extractLabels] using this
    · have := labPresApp both fr hD' bnd'
      simp only [List.append_nil] at this
      simp only [appAppend, appList, LabProps.LabelSets.extractLabels_append,
        LabProps.LabelSets.extractLabels, List.nil_append]
      refine labPresPerm this ?_
      rw [List.perm_iff_count]; intro x; simp only [List.count_append]; omega
    · have := labPresApp both fr hD' bnd'
      simp only [List.append_nil] at this
      simp only [appAppend, appList, LabProps.LabelSets.extractLabels_append,
        LabProps.LabelSets.extractLabels, List.nil_append]
      refine labPresPerm this ?_
      rw [List.perm_iff_count]; intro x; simp only [List.count_append]; omega
    · have hD'' : (StackPropsCodeLabels.extractLabels a ++ StackPropsCodeLabels.extractLabels b ++
          [] ++ []).Nodup := by simpa using hD
      have bnd'' : ∀ e ∈ StackPropsCodeLabels.extractLabels a ++
          StackPropsCodeLabels.extractLabels b ++ [] ++ [], e.2 < nl := by simpa using bnd
      have := labPresApp (labPresApp both fr hD' bnd') fr2 hD'' bnd''
      simp only [List.append_nil] at this
      simp only [appAppend, appList, LabProps.LabelSets.extractLabels_append,
        LabProps.LabelSets.extractLabels, List.nil_append]
      refine labPresPerm this ?_
      rw [List.perm_iff_count]; intro x; simp only [List.count_append]; omega
  | .loop body, nl, cs, bs, hE, hD, hnl => by
    have two : 2 ≤ nl := le_trans (nextLabNonZero _) hnl
    rw [StackAlloc.next_lab_thm] at hnl
    dsimp only at hnl
    simp only [StackPropsCodeLabels.extractLabels] at hE hD ⊢
    rcases h1 : flattenHOL false body n (nl + 2) (nl :: cs) ((nl + 1) :: bs) with ⟨ys, nr, nl1⟩
    have pb := labPresAux n body (nl + 2) (nl :: cs) ((nl + 1) :: bs) hE hD (by omega)
    rw [h1] at pb; dsimp only at pb
    have f1 : LabPres n nl (nl + 1) [] [(n, nl)] := labPresFresh' two
    have f2 : LabPres n (nl + 1) (nl + 2) [] [(n, nl + 1)] := labPresFresh' (by omega)
    have := labPresApp (labPresApp f1 f2 (by simp) (by simp)) pb (by simpa using hD)
      (by simpa using labelsBound (p := body) (by omega))
    simp only [List.nil_append] at this
    rw [flattenHOL]
    simp only [h1, appAppend, appList, LabProps.LabelSets.extractLabels_append,
      LabProps.LabelSets.extractLabels]
    refine labPresPerm this ?_
    rw [List.perm_iff_count]; intro x; simp only [List.count_append, List.count_cons]; omega
  | .call none d h, nl, cs, bs, hE, hD, hnl => by
    rw [flattenHOL]
    cases d <;> simp only [compileJumpHOL, appList, LabProps.LabelSets.extractLabels] <;>
      exact labPresNil' _ le_rfl
  | .call (some (rp, lr, l1, l2)) d none, nl, cs, bs, hE, hD, hnl => by
    have bnd := labelsBound hnl
    rw [StackAlloc.next_lab_thm] at hnl
    dsimp only at hnl
    simp only [StackPropsCodeLabels.extractLabels] at hE hD bnd ⊢
    have k : LabPres n nl nl [(l1, l2)] [(l1, l2)] :=
      labPresKnown (by simp) (hE (l1, l2) (by simp))
    rcases h1 : flattenHOL false rp n nl cs bs with ⟨xs, nr, nl1⟩
    have pr := labPresAux n rp nl cs bs (fun l h => hE l (List.mem_append_right _ h))
      (nodupRight hD) (by omega)
    rw [h1] at pr; dsimp only at pr
    have := labPresApp k pr hD bnd
    rw [flattenHOL]
    cases d <;> simpa [h1, compileJumpHOL, appAppend, appList,
      LabProps.LabelSets.extractLabels_append, LabProps.LabelSets.extractLabels] using this
  | .call (some (rp, lr, l1, l2)) d (some (hp, k1, k2)), nl, cs, bs, hE, hD, hnl => by
    have two : 2 ≤ nl := le_trans (nextLabNonZero _) hnl
    have bnd := labelsBound hnl
    rw [StackAlloc.next_lab_thm] at hnl
    dsimp only at hnl
    simp only [StackPropsCodeLabels.extractLabels] at hE hD bnd ⊢
    have ka : LabPres n nl nl [(l1, l2)] [(l1, l2)] :=
      labPresKnown (by simp) (hE (l1, l2) (by simp))
    have kb : LabPres n nl nl [(k1, k2)] [(k1, k2)] :=
      labPresKnown (by simp) (hE (k1, k2) (by simp))
    rcases h1 : flattenHOL false rp n nl cs bs with ⟨xs, nr1, nl1⟩
    have pr := labPresAux n rp nl cs bs (fun l h => hE l (by simp [h]))
      (by have := nodupLeft hD; simp only [List.nodup_append] at this; exact this.2.1) (by omega)
    rw [h1] at pr; dsimp only at pr
    rcases h2 : flattenHOL false hp n nl1 cs bs with ⟨ys, nr2, nl2⟩
    have ph := labPresAux n hp nl1 cs bs (fun l h => hE l (by simp [h])) (nodupRight hD)
      (by have := pr.2.2.2; omega)
    rw [h2] at ph; dsimp only at ph
    have le2 : nl ≤ nl2 := by have := pr.2.2.2; have := ph.2.2.2; omega
    have fr : LabPres n nl2 (nl2 + 1) [] [(n, nl2)] := labPresFresh' (by omega)
    have hD1 : ([(l1, l2)] ++ [(k1, k2)]).Nodup := by
      have := nodupLeft (nodupLeft hD); simpa using this
    have hD2 : ([(l1, l2)] ++ [(k1, k2)] ++ StackPropsCodeLabels.extractLabels rp).Nodup := by
      have := nodupLeft hD; simpa using this
    have hD3 : ([(l1, l2)] ++ [(k1, k2)] ++ StackPropsCodeLabels.extractLabels rp ++
        StackPropsCodeLabels.extractLabels hp).Nodup := by simpa using hD
    have hD4 : ([(l1, l2)] ++ [(k1, k2)] ++ StackPropsCodeLabels.extractLabels rp ++
        StackPropsCodeLabels.extractLabels hp ++ []).Nodup := by simpa using hD
    have sub : ∀ (P : Nat × Nat → Prop), (∀ e, e ∈ [(l1, l2), (k1, k2)] ++
        StackPropsCodeLabels.extractLabels rp ++ StackPropsCodeLabels.extractLabels hp → P e) →
        ∀ e, (e = (l1, l2) ∨ e = (k1, k2) ∨ e ∈ StackPropsCodeLabels.extractLabels rp ∨
          e ∈ StackPropsCodeLabels.extractLabels hp) → P e := by
      intro P h e he
      apply h
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false]
      tauto
    have b1 : ∀ e ∈ [(l1, l2)] ++ [(k1, k2)], e.2 < nl := fun e he =>
      sub _ bnd e (by simp at he; tauto)
    have b2 : ∀ e ∈ [(l1, l2)] ++ [(k1, k2)] ++ StackPropsCodeLabels.extractLabels rp,
        e.2 < nl := fun e he => sub _ bnd e (by simp at he; tauto)
    have b3 : ∀ e ∈ [(l1, l2)] ++ [(k1, k2)] ++ StackPropsCodeLabels.extractLabels rp ++
        StackPropsCodeLabels.extractLabels hp, e.2 < nl := fun e he =>
      sub _ bnd e (by simp at he; tauto)
    have b4 : ∀ e ∈ [(l1, l2)] ++ [(k1, k2)] ++ StackPropsCodeLabels.extractLabels rp ++
        StackPropsCodeLabels.extractLabels hp ++ [], e.2 < nl := fun e he =>
      sub _ bnd e (by simp at he; tauto)
    have this := labPresApp (labPresApp (labPresApp (labPresApp ka kb hD1 b1)
      pr hD2 b2) ph hD3 b3) fr hD4 b4
    simp only [List.append_nil, List.cons_append] at this
    rw [flattenHOL]
    cases d <;>
    · simp only [h1, h2, compileJumpHOL, appAppend, appList,
        LabProps.LabelSets.extractLabels_append, LabProps.LabelSets.extractLabels,
        List.nil_append, List.cons_append]
      refine labPresPerm this ?_
      rw [List.perm_iff_count]; intro x
      simp only [List.count_append, List.count_cons, List.count_nil]
      split_ifs <;> omega
  | .ffi f a b c d ret, nl, cs, bs, hE, hD, hnl => by
    have two : 2 ≤ nl := le_trans (nextLabNonZero _) hnl
    rw [flattenHOL]
    simp only [appList, LabProps.LabelSets.extractLabels, StackPropsCodeLabels.extractLabels]
    exact labPresFresh two []
  | .install a b c d ret, nl, cs, bs, hE, hD, hnl => by
    have two : 2 ≤ nl := le_trans (nextLabNonZero _) hnl
    rw [flattenHOL]
    simp only [appList, LabProps.LabelSets.extractLabels, StackPropsCodeLabels.extractLabels]
    exact labPresFresh two []
  | .skip, nl, cs, bs, _, _, _ | .inst _, nl, cs, bs, _, _, _ | .get _ _, nl, cs, bs, _, _, _
  | .set _ _, nl, cs, bs, _, _, _ | .opCurrHeap _ _ _, nl, cs, bs, _, _, _
  | .jumpLower _ _ _, nl, cs, bs, _, _, _ | .alloc _, nl, cs, bs, _, _, _
  | .storeConsts _ _ _, nl, cs, bs, _, _, _ | .raise _, nl, cs, bs, _, _, _
  | .ret _, nl, cs, bs, _, _, _ | .break _, nl, cs, bs, _, _, _
  | .continue _, nl, cs, bs, _, _, _ | .tick, nl, cs, bs, _, _, _
  | .locValue _ _ _, nl, cs, bs, _, _, _ | .shMemOp _ _ _, nl, cs, bs, _, _, _
  | .codeBufferWrite _ _, nl, cs, bs, _, _, _ | .dataBufferWrite _ _, nl, cs, bs, _, _, _
  | .rawCall _, nl, cs, bs, _, _, _ | .stackAlloc _, nl, cs, bs, _, _, _
  | .stackFree _, nl, cs, bs, _, _, _ | .stackStore _ _, nl, cs, bs, _, _, _
  | .stackStoreAny _ _, nl, cs, bs, _, _, _ | .stackLoad _ _, nl, cs, bs, _, _, _
  | .stackLoadAny _ _, nl, cs, bs, _, _, _ | .stackGetSize _, nl, cs, bs, _, _, _
  | .stackSetSize _, nl, cs, bs, _, _, _ | .bitmapLoad _ _, nl, cs, bs, _, _, _
  | .halt _, nl, cs, bs, _, _, _ => by
    simp only [flattenHOL, appList, LabProps.LabelSets.extractLabels]
    exact labPresNil' _ le_rfl
termination_by p => sizeOf p

/-- Non-tail flattening keeps the program's labels, which all belong to the
section and avoid 0 and 1, distinct, and adds only fresh labels in
`[nl, nl')`. -/
theorem stackToLabLabPres {width : Nat} [NeZero width] :
    ∀ (t : Bool) (p : HolProg width) (n nl : Nat) (cs bs : List Nat),
      (∀ l ∈ StackPropsCodeLabels.extractLabels p, l.1 = n ∧ l.2 ≠ 0 ∧ l.2 ≠ 1) ∧
        (StackPropsCodeLabels.extractLabels p).Nodup ∧ ¬t = true ∧
        StackAlloc.nextLabHOL p 2 ≤ nl →
      (∀ l ∈ LabProps.LabelSets.extractLabels (appListAppend (flattenHOL t p n nl cs bs).1),
          l.1 = n ∧ l.2 ≠ 0 ∧ l.2 ≠ 1) ∧
        (LabProps.LabelSets.extractLabels (appListAppend (flattenHOL t p n nl cs bs).1)).Nodup ∧
        (∀ lab ∈ LabProps.LabelSets.extractLabels (appListAppend (flattenHOL t p n nl cs bs).1),
          lab ∈ StackPropsCodeLabels.extractLabels p ∨
            (nl ≤ lab.2 ∧ lab.2 < (flattenHOL t p n nl cs bs).2.2)) ∧
        nl ≤ (flattenHOL t p n nl cs bs).2.2 := by
  rintro t p n nl cs bs ⟨hE, hD, ht, hnl⟩
  simp only [Bool.not_eq_true] at ht
  subst ht
  exact labPresAux n p nl cs bs hE hD hnl

/-- Tail flattening keeps the program's labels distinct within the section,
adding the `Seq` continuation label 1 and fresh labels below `nl'`. -/
theorem stackToLabLabPresT {width : Nat} [NeZero width] :
    ∀ (t : Bool) (p : HolProg width) (n nl : Nat) (cs bs : List Nat),
      (∀ l ∈ StackPropsCodeLabels.extractLabels p, l.1 = n ∧ l.2 ≠ 0 ∧ l.2 ≠ 1) ∧
        (StackPropsCodeLabels.extractLabels p).Nodup ∧ t = true ∧
        StackAlloc.nextLabHOL p 2 ≤ nl →
      (∀ l ∈ LabProps.LabelSets.extractLabels (appListAppend (flattenHOL t p n nl cs bs).1),
          l.1 = n ∧ l.2 ≠ 0) ∧
        (LabProps.LabelSets.extractLabels (appListAppend (flattenHOL t p n nl cs bs).1)).Nodup ∧
        (∀ lab ∈ LabProps.LabelSets.extractLabels (appListAppend (flattenHOL t p n nl cs bs).1),
          lab ∈ StackPropsCodeLabels.extractLabels p ∨ lab.2 < (flattenHOL t p n nl cs bs).2.2) ∧
        nl ≤ (flattenHOL t p n nl cs bs).2.2 := by
  rintro t p n nl cs bs ⟨hE, hD, ht, hnl⟩
  subst ht
  by_cases hs : isSeqHOL p = true
  · obtain ⟨a, b, rfl⟩ : ∃ a b, p = .seq a b := by
      cases p <;> simp [isSeqHOL] at hs; exact ⟨_, _, rfl⟩
    have two : 2 ≤ nl := le_trans (nextLabNonZero _) hnl
    have bnd := labelsBound hnl
    rw [StackAlloc.next_lab_thm] at hnl
    dsimp only at hnl
    simp only [StackPropsCodeLabels.extractLabels] at hE hD bnd ⊢
    rcases h1 : flattenHOL false a n nl cs bs with ⟨ys1, nr1, nl1⟩
    have pa := labPresAux n a nl cs bs (fun l h => hE l (List.mem_append_left _ h))
      (nodupLeft hD) (by omega)
    rw [h1] at pa; dsimp only at pa
    rcases h2 : flattenHOL false b n nl1 cs bs with ⟨ys2, nr2, nl2⟩
    have pb := labPresAux n b nl1 cs bs (fun l h => hE l (List.mem_append_right _ h))
      (nodupRight hD) (by have := pa.2.2.2; omega)
    rw [h2] at pb; dsimp only at pb
    obtain ⟨g, d, m, o⟩ := labPresApp pa pb hD bnd
    rw [flattenHOL]
    simp only [h1, h2, if_true, appAppend, appList, LabProps.LabelSets.extractLabels_append,
      LabProps.LabelSets.extractLabels]
    have one : (n, 1) ∉ LabProps.LabelSets.extractLabels (appListAppend ys1) ++
        LabProps.LabelSets.extractLabels (appListAppend ys2) := fun h => (g _ h).2.2 rfl
    refine ⟨?_, ?_, ?_, o⟩
    · intro l hl
      simp only [List.mem_append, List.mem_singleton] at hl
      rcases hl with (hl | rfl) | hl
      · exact ⟨(g l (List.mem_append_left _ hl)).1, (g l (List.mem_append_left _ hl)).2.1⟩
      · exact ⟨rfl, by simp⟩
      · exact ⟨(g l (List.mem_append_right _ hl)).1, (g l (List.mem_append_right _ hl)).2.1⟩
    · have : (LabProps.LabelSets.extractLabels (appListAppend ys1) ++
          LabProps.LabelSets.extractLabels (appListAppend ys2) ++ [(n, 1)]).Nodup := by
        rw [List.nodup_append]
        exact ⟨d, by simp, fun x hx y hy hxy => by simp at hy; subst hy; subst hxy; exact one hx⟩
      refine (List.Perm.nodup_iff ?_).mp this
      rw [List.perm_iff_count]; intro x; simp only [List.count_append]; omega
    · intro lab hl
      simp only [List.mem_append, List.mem_singleton] at hl
      rcases hl with (hl | rfl) | hl
      · rcases m lab (List.mem_append_left _ hl) with h | h
        · exact .inl h
        · exact .inr h.2
      · right; simp only; omega
      · rcases m lab (List.mem_append_right _ hl) with h | h
        · exact .inl h
        · exact .inr h.2
  · rw [flattenTF hs]
    obtain ⟨g, d, m, o⟩ := labPresAux n p nl cs bs hE hD hnl
    exact ⟨fun l hl => ⟨(g l hl).1, (g l hl).2.1⟩, d,
      fun lab hl => (m lab hl).imp id (fun h => h.2), o⟩

/-- Every program section produced from well-labelled source programs with
distinct names satisfies `labels_ok`. -/
theorem progToSectionLabelsOk {width : Nat} [NeZero width] {prog : List (Nat × HolProg width)} :
    (∀ np ∈ prog, (∀ l ∈ StackPropsCodeLabels.extractLabels np.2,
        l.1 = np.1 ∧ l.2 ≠ 0 ∧ l.2 ≠ 1) ∧ (StackPropsCodeLabels.extractLabels np.2).Nodup) ∧
      (prog.map Prod.fst).Nodup →
    labelsOk (prog.map progToSectionHOL) := by
  rintro ⟨hall, hnames⟩
  refine ⟨by rw [mapProgToSectionFst]; exact hnames, ?_⟩
  intro sec hsec
  obtain ⟨⟨n, p⟩, hmem, rfl⟩ := List.mem_map.mp hsec
  obtain ⟨hE, hD⟩ := hall (n, p) hmem
  rw [progToSection_eq]
  have hnl : StackAlloc.nextLabHOL p 2 ≤ StackAlloc.nextLab p 2 := le_rfl
  obtain ⟨g, d, m, o⟩ := stackToLabLabPresT true p n (StackAlloc.nextLab p 2) [] []
    ⟨hE, hD, rfl, hnl⟩
  have two : 2 ≤ StackAlloc.nextLab p 2 := nextLabNonZero p
  simp only [LabProps.LabelSets.extractLabels_append, LabProps.LabelSets.extractLabels]
  set L := LabProps.LabelSets.extractLabels
    (appListAppend (flattenHOL true p n (StackAlloc.nextLab p 2) [] []).1) with hL
  set k := (if isSeqHOL p = true then (flattenHOL true p n (StackAlloc.nextLab p 2) [] []).2.2
    else 1) with hk
  have notin : (n, k) ∉ L := by
    intro h
    by_cases hs : isSeqHOL p = true
    · rw [if_pos hs] at hk
      rcases m _ h with e | lt
      · have := labelsBound (p := p) hnl _ e
        simp only at this
        omega
      · simp only at lt; omega
    · rw [if_neg hs] at hk
      rw [hL, flattenTF hs] at h
      have := (labPresAux n p _ [] [] hE hD hnl).1 _ h
      exact this.2.2 hk
  refine ⟨?_, ?_⟩
  · intro l hl
    simp only [List.mem_append, List.mem_singleton] at hl
    rcases hl with hl | rfl
    · exact g l hl
    · refine ⟨rfl, ?_⟩
      simp only [hk]
      split_ifs <;> omega
  · rw [List.nodup_append]
    exact ⟨d, by simp, fun x hx y hy hxy => by simp at hy; subst hy; subst hxy; exact notin hx⟩

/-- A fetched compiled jump to an installed destination takes one LabSem
step to the destination position. -/
theorem compileJumpCorrect {width : Nat} [NeZero width] {C F : Type}
    {s : Flapjack.Compiler.Backend.LabSem.State width C F} {pc pc' : Nat}
    {code : List (Section (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width)))}
    {dest : Nat ⊕ Nat} {regs : Nat → WordLocW width} :
    asmFetchAux pc code = some (compileJumpHOL dest) ∧
      locToPc (Prelude.destToLoc' regs dest) 0 code = some pc' ∧
      (∀ r, dest = .inr r → ∃ p, s.regs r = .loc p 0) ∧
      s.pc = pc ∧ s.code = code ∧ s.regs = regs ∧ s.clock ≠ 0 →
    evaluate s = evaluate (updPc pc' (decClock s)) := by
  rintro ⟨fetch, loc, regsLoc, rfl, rfl, rfl, clk⟩
  rw [evaluate]
  cases dest with
  | inl n =>
    simp only [Prelude.destToLoc'] at loc
    simp [clk, asmFetch, fetch, compileJumpHOL, getPcValue, loc]
  | inr r =>
    obtain ⟨p, hp⟩ := regsLoc r rfl
    simp only [Prelude.destToLoc', hp] at loc
    simp [clk, asmFetch, fetch, compileJumpHOL, hp, loc]

/-- HOL `result_view`: the target-observable shape of a StackSem result. -/
inductive ResultView where
  | vloc (n1 n2 : Nat)
  | vcont (n1 n2 : Nat)
  | vtimeout
  | verr
  deriving DecidableEq, Repr

/-- Complete original view of a StackSem result at section `l` with the
continue and break label stacks. -/
def resultView {width : Nat} [NeZero width] :
    StackSemResult width → Nat → List Nat → List Nat → ResultView
  | .result (.loc n1 n2), _, _, _ => .vloc n1 n2
  | .exception (.loc n1 n2), _, _, _ => .vloc n1 n2
  | .timeOut, _, _, _ => .vtimeout
  | .continue n, l, cs, _ => .vcont l (findLabHOL n cs)
  | .break n, l, _, bs => .vloc l (findLabHOL n bs)
  | _, _, _, _ => .verr

/-- Complete original view of a halting word as a machine result. -/
def haltWordView {width : Nat} [NeZero width] : WordLocW width → MachineResult
  | .word w => if w = 0 then .halt .success else .halt .resourceLimitHit
  | .loc _ _ => .error

/-- Complete original view of a halting StackSem result. -/
def haltView {width : Nat} [NeZero width] : Option (StackSemResult width) → Option MachineResult
  | some (.halt w) => some (haltWordView w)
  | some (.finalFFI outcome) => some (.halt (.ffiOutcome outcome))
  | _ => none

end Flapjack.Compiler.Backend.StackToLab.Proofs.FlattenHelpers
