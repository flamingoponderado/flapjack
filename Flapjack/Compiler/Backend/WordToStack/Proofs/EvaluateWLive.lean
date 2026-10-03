import Flapjack.Compiler.Backend.WordToStack.Proofs.AllocStateRel
import Flapjack.Compiler.Backend.WordToStack.NativeLive
import Flapjack.Compiler.Backend.WordToStack.Proofs.BitmapWrite
import Flapjack.Compiler.Backend.WordToStack.Proofs.BitmapInsert
import Flapjack.Compiler.Backend.WordToStack.Proofs.BitmapAppend
import Flapjack.Compiler.Backend.WordToStack.Proofs.SortedKeys
import Flapjack.Compiler.Backend.WordToStack.Proofs.KeyValueOrder
import Flapjack.Compiler.Backend.WordToStack.Proofs.IndexListLemmas
import Flapjack.Basis.Pure.MlList.SortPerm
import Flapjack.Misc.Sptree.ToAList
import Flapjack.Compiler.Backend.Semantics.StackSem.EvaluateDef

/-!
# Word-to-Stack `evaluate_wLive`

Running the `wLive` frame header (`word_to_stackProofScript.sml:1339-1598`)
pushes the live variables' frame: afterwards the target relates both to the
source state with the cut environment pushed (frame sizes `0`) and to the
unchanged source state.
-/

namespace Flapjack.WordToStackProofs.EvaluateWLive
open Flapjack.StackSem Flapjack.Compiler.Encoders.Asm Flapjack.WordSemStateFiniteExact
  Flapjack.Compiler.Backend.WordToStack Flapjack.Compiler.Backend.WordToStack.Native

/-- Canonical source-state relation codec re-export; no separate HOL original. -/
theorem holFmapAsFiniteSupportRelationWitness_WordSemStateFiniteExact
    {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : WordSemStateBroad width C F) (h : state.FiniteSupport),
      (WordSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : WordSemStateFiniteExact width C F,
      WordSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  WordSemStateExact.holFmapAsFiniteSupportWitness

/-- Canonical target-state relation codec re-export; no separate HOL original. -/
theorem holFmapAsFiniteSupportRelationWitness_StackSemStateFiniteExact
    {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : StackSemStateBroad width C F) (h : state.FiniteSupport),
      (StackSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : StackSemStateFiniteExact width C F,
      StackSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  StackSemStateSupport.holFmapAsFiniteSupportWitness

/-- Inhabitation of the source frame carrier for total HOL `EL`, as in `stackRelAux`. -/
local instance {width : Nat} [NeZero width] : Nonempty (WordSemStackFrame width) :=
  ⟨.stackFrame none [] [] none⟩

theorem listRearrange_id {α : Type} (xs : List α) : wordSemListRearrange id xs = xs := by
  unfold wordSemListRearrange
  split
  · apply List.ext_getElem
    · simp
    · intro i h1 h2
      simp
  · rfl

theorem envToList_fst {width : Nat} [NeZero width] (env : Spt (WordLocW width))
    (p : Nat → Nat → Nat) (hp : p 0 = id) :
    (wordSemEnvToList env p).1 =
      Basis.Pure.MlList.sort wordSemKeyValCompare (sptToAList env) := by
  simp only [wordSemEnvToList, hp, listRearrange_id]

theorem holSorted_chain {α : Type} (R : α → α → Prop) :
    ∀ l : List α, holSorted R l → List.IsChain R l
  | [], _ => List.IsChain.nil
  | [_], _ => List.IsChain.singleton _
  | _ :: y :: rest, h => List.IsChain.cons_cons h.1 (holSorted_chain R (y :: rest) h.2)

/-- The `env_to_list` list of an environment has strictly descending keys. -/
theorem sortEnv_pairwise {width : Nat} [NeZero width] (env : Spt (WordLocW width)) :
    (Basis.Pure.MlList.sort wordSemKeyValCompare (sptToAList env)).Pairwise
      (fun a b => a.1 > b.1) := by
  have hs := Basis.Pure.MlList.sortSorted wordSemKeyValCompare (sptToAList env)
    ⟨fun x y z h => transitiveKeyValCompare x y z h.1 h.2,
     fun x y => totalKeyValCompare x y⟩
  have hc := holSorted_chain _ _ hs
  have : Trans (fun a b : Nat × WordLocW width => wordSemKeyValCompare a b = true)
      (fun a b => wordSemKeyValCompare a b = true)
      (fun a b => wordSemKeyValCompare a b = true) :=
    ⟨fun hab hbc => transitiveKeyValCompare _ _ _ hab hbc⟩
  have hp := hc.pairwise
  have hperm := (holPerm_iff _ _).mp (Basis.Pure.MlList.sortPerm wordSemKeyValCompare
    (sptToAList env))
  have hnd : ((Basis.Pure.MlList.sort wordSemKeyValCompare (sptToAList env)).map
      Prod.fst).Nodup := (hperm.map Prod.fst).nodup_iff.mp (sptAllDistinctMapFstToAList env)
  rw [List.nodup_iff_pairwise_ne, List.pairwise_map] at hnd
  refine (hp.and hnd).imp ?_
  rintro ⟨a, va⟩ ⟨b, vb⟩ ⟨hab, hne⟩
  simp only at hne ⊢
  simp only [wordSemKeyValCompare, Bool.or_eq_true, decide_eq_true_eq, Bool.and_eq_true,
    hne, false_and, or_false] at hab
  exact hab

theorem descendingKeys_of_pairwise {α : Type} :
    ∀ xs : List (Nat × α), xs.Pairwise (fun a b => a.1 > b.1) → descendingKeys xs
  | [], _ => by simp [descendingKeys]
  | [_], _ => by simp [descendingKeys]
  | x :: y :: rest, h => by
      have hxy : x.1 > y.1 := List.rel_of_pairwise_cons h (by simp)
      have ih := descendingKeys_of_pairwise (y :: rest) h.of_cons
      simp only [descendingKeys, List.tail_cons, List.zip_cons_cons, List.all_cons,
        Bool.and_eq_true, decide_eq_true_eq] at ih ⊢
      exact ⟨hxy, ih⟩

theorem indexList_pairwise {α : Type} (k : Nat) :
    ∀ xs : List α, (indexList xs k).Pairwise (fun a b => a.1 > b.1)
  | [] => by simp [indexList]
  | x :: xs => by
      simp only [indexList, List.pairwise_cons]
      refine ⟨?_, indexList_pairwise k xs⟩
      intro a ha
      have := memIndexListLim xs a.1 a.2 k ha
      have hk : k ≤ a.1 := by
        obtain ⟨i, hi, he⟩ := List.mem_iff_getElem.mp ha
        have hil : i < xs.length := by simpa only [lengthIndexList] using hi
        rw [elIndexList xs i k hil] at he
        rw [← he]; simp only; omega
      omega

/-- The bitmap written by `wLive` selects exactly the spilled GC-live variables
from the indexed frame, in `env_to_list` order. Flapjack helper isolating the
`filter_bitmap` conjunct of HOL `evaluate_wLive`'s pushed `stack_rel_aux`; no
separate HOL original. -/
theorem wLiveFilterBitmap {width : Nat} [NeZero width] (k f' : Nat) (names2 : Spt Unit)
    (locals : Spt (WordLocW width)) (perm : Nat → Nat → Nat) (frame : List (WordLocW width))
    (hperm : perm 0 = id)
    (hsub : ∀ r, sptDomain names2 r → (sptLookup r locals).isSome)
    (hsnd : ∀ x, sptDomain names2 x → x % 2 = 0 ∧ k ≤ x / 2)
    (hframe : frame.length = f')
    (hloc : ∀ n v, sptLookup n locals = some v → n % 2 = 0 → k ≤ n / 2 →
      n / 2 < k + f' ∧ frame[f' - 1 - (n / 2 - k)]? = some v) :
    filterBitmap ((List.range f').map (fun x => decide
        (x ∈ (sptToAList names2).map (fun (r, _) => f' - 1 - (r / 2 - k)))))
      (indexList frame k) =
      some ((wordSemEnvToList (sptInter locals names2) perm).1.map
        (fun p => (adjustNames p.1, p.2)), []) := by
  set bits := (List.range f').map (fun x => decide
    (x ∈ (sptToAList names2).map (fun (r, _) => f' - 1 - (r / 2 - k)))) with hbits
  have hbl : bits.length = f' := by simp [bits]
  have hil : (indexList frame k).length = f' := by rw [lengthIndexList, hframe]
  -- entries of the cut environment
  have henv : ∀ r v, (r, v) ∈ (wordSemEnvToList (sptInter locals names2) perm).1 ↔
      sptLookup r locals = some v ∧ sptDomain names2 r := by
    intro r v
    rw [wordSemEnvToList_mem_iff, sptToAList_mem_iff_lookup, sptLookup_sptInterCases]
    unfold sptDomain
    cases sptLookup r locals <;> cases sptLookup r names2 <;> simp
  apply filterBitmapEqSomeNil bits (indexList frame k) _ (by rw [hbl, hil])
  apply sortedImpEqLists
  · -- the selected entries have descending keys
    apply descendingKeys_of_pairwise
    rw [List.pairwise_map]
    apply List.Pairwise.sublist List.filter_sublist
    have hz : ((indexList frame k).zip bits).map Prod.fst = indexList frame k :=
      List.map_fst_zip (by rw [hbl, hil])
    have := indexList_pairwise k frame
    rw [← hz, List.pairwise_map] at this
    exact this
  · -- the env_to_list entries have descending even keys, so their halves descend
    apply descendingKeys_of_pairwise
    rw [envToList_fst _ _ hperm, List.pairwise_map]
    refine (sortEnv_pairwise (sptInter locals names2)).imp_of_mem ?_
    rintro ⟨a, va⟩ ⟨b, vb⟩ ha hb hab
    rw [← envToList_fst _ perm hperm] at ha hb
    have ea := hsnd a ((henv a va).mp ha).2
    have eb := hsnd b ((henv b vb).mp hb).2
    simp only [adjustNames] at hab ⊢
    omega
  · rintro ⟨j, v⟩
    simp only [List.mem_map, List.mem_filter, Prod.exists]
    constructor
    · rintro ⟨j', v', b, ⟨hzip, hb⟩, hjv⟩
      simp only [Prod.mk.injEq] at hjv
      obtain ⟨rfl, rfl⟩ := hjv
      subst hb
      obtain ⟨i, hi, hget⟩ := List.mem_iff_getElem.mp hzip
      rw [List.getElem_zip] at hget
      simp only [Prod.mk.injEq] at hget
      obtain ⟨hidx, hbit⟩ := hget
      have hif : i < f' := by simp [hbl, hil] at hi; omega
      rw [elIndexList frame i k (by omega)] at hidx
      simp only [Prod.mk.injEq] at hidx
      obtain ⟨hj, hv⟩ := hidx
      simp only [bits, List.getElem_map, List.getElem_range, decide_eq_true_eq, List.mem_map,
        Prod.exists] at hbit
      obtain ⟨r, u, hru, hri⟩ := hbit
      have hdom : sptDomain names2 r := by
        unfold sptDomain; rw [(sptToAList_mem_iff_lookup names2 r u).mp hru]; rfl
      obtain ⟨heven, hk⟩ := hsnd r hdom
      obtain ⟨w, hw⟩ := Option.isSome_iff_exists.mp (hsub r hdom)
      obtain ⟨hlt, hfr⟩ := hloc r w hw heven hk
      rw [hri] at hfr
      have hfi : frame[i]'(by omega) = w := (List.getElem?_eq_some_iff.mp hfr).2
      refine ⟨r, w, (henv r w).mpr ⟨hw, hdom⟩, ?_⟩
      simp only [Prod.mk.injEq, adjustNames]
      refine ⟨by omega, ?_⟩
      rw [← hv, hfi]
    · rintro ⟨r, v', hmem, hj⟩
      simp only [Prod.mk.injEq] at hj
      obtain ⟨rfl, rfl⟩ := hj
      obtain ⟨hlk, hdom⟩ := (henv r v').mp hmem
      obtain ⟨heven, hk⟩ := hsnd r hdom
      obtain ⟨hlt, hfr⟩ := hloc r v' hlk heven hk
      have hi : f' - 1 - (r / 2 - k) < f' := by omega
      have hfi : frame[f' - 1 - (r / 2 - k)]'(by omega) = v' :=
        (List.getElem?_eq_some_iff.mp hfr).2
      refine ⟨r / 2, v', true, ⟨?_, rfl⟩, rfl⟩
      refine List.mem_iff_getElem.mpr ⟨f' - 1 - (r / 2 - k), by simp [hbl, hil]; omega, ?_⟩
      rw [List.getElem_zip]
      congr 1
      · rw [elIndexList frame _ k (by omega), hfi]
        congr 1
        omega
      · simp only [bits, List.getElem_map, List.getElem_range, decide_eq_true_eq, List.mem_map,
          Prod.exists]
        obtain ⟨u, hu⟩ := Option.isSome_iff_exists.mp hdom
        exact ⟨r, u, (sptToAList_mem_iff_lookup names2 r u).mpr hu, rfl⟩

theorem drop_set_self {α : Type} (l : List α) (i : Nat) (a : α) (h : i < l.length) :
    (l.set i a).drop i = a :: l.drop (i + 1) := by
  rw [List.drop_set, if_neg (by omega), Nat.sub_self, List.drop_eq_getElem_cons h]
  rfl

theorem cutEnvs_subset {β : Type} {names : WordLangCutsetsHOL} {env : Spt β}
    {envs : Spt β × Spt β} (h : wordSemCutEnvs names env = some envs) :
    ∀ r, sptDomain names.2 r → (sptLookup r env).isSome := by
  unfold wordSemCutEnvs wordSemCutNames at h
  by_cases h2 : LoopSemStateFiniteExact.sptSubsetLive names.2 env
  · intro r hr; exact h2 r hr
  · by_cases h1 : LoopSemStateFiniteExact.sptSubsetLive names.1 env <;>
      simp [h1, h2] at h

/-- Exact HOL `evaluate_wLive` (`word_to_stackProofScript.sml:1339-1598`). HOL's
free `names`, `bs`, `n`, `k`, `f`, `f'`, `ac`, `lens` and `envs` are explicit;
`x ∈ domain t` is `sptDomain t x`, `EVEN x` is `x % 2 = 0`, and `isPREFIX` is
`List.IsPrefix`. The conclusion's existential `bs5` occurs nowhere in its body
and is omitted. The pushed state is HOL's `push_env envs NONE s with
<|locals := LN; locals_size := SOME 0|>`. -/
@[hol "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "evaluate_wLive"
  (fmap_as_finite_support_relation := [WordSemStateFiniteExact.fpRegs, WordSemStateFiniteExact.store,
    StackSemStateFiniteExact.regs, StackSemStateFiniteExact.fpRegs, StackSemStateFiniteExact.store])
  (words_as_type_indexed_bitvec)]
theorem evaluateWLive {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) (k f f' : Nat) (names : WordLangCutsetsHOL)
    (bs : AppList (BitVec width)) (n : Nat) (wliveProg : Compiler.Backend.StackLang.HolProg width)
    (bs' : AppList (BitVec width)) (n' : Nat)
    (s : WordSemStateFiniteExact width (Nat × C) F) (t : StackSemStateFiniteExact width C F)
    (lens : List Nat) (envs : Spt (WordLocW width) × Spt (WordLocW width)) :
    wLiveNative names (bs, n) (k, f, f') = (wliveProg, (bs', n')) ∧
      (∀ x, sptDomain names.1 x → x % 2 = 0 ∧ k ≤ x / 2) ∧
      (∀ x, sptDomain names.2 x → x % 2 = 0 ∧ k ≤ x / 2) ∧
      stateRel ac k f f' s t lens 0 ∧ 1 ≤ f ∧
      wordSemCutEnvs names s.locals = some envs ∧
      (appListAppend bs).length ≤ n ∧ n - (appListAppend bs).length ≤ t.bitmaps.length ∧
      (appListAppend bs').IsPrefix (t.bitmaps.drop (n - (appListAppend bs).length)) →
    ∃ t5 : StackSemStateFiniteExact width C F,
      StackSemEvaluate.evaluate (wliveProg, t) = (none, t5) ∧
      stateRel ac k 0 0 { pushEnv envs none s with locals := .ln, localsSize := some 0 } t5
        (f' :: lens) 0 ∧
      stateRel ac k f f' s t5 lens 0 ∧
      t5.stack.length = t.stack.length ∧ t5.stackSpace = t.stackSpace ∧
      ∀ i, i ≠ k → StackSemStateOps.getVar i t5 = StackSemStateOps.getVar i t := by
  rintro ⟨hw, hfst, hsnd, hrel, hf1, hcut, hbsn, hbsl, hpre⟩
  have hf0 : ¬ f = 0 := by omega
  simp only [wLiveNative, hf0, if_false, insertBitmap, Prod.mk.injEq] at hw
  obtain ⟨rfl, rfl, rfl⟩ := hw
  have hrel' := hrel
  unfold stateRel at hrel'
  obtain ⟨r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18,
    r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36,
    r37, r38, rloc⟩ := hrel'
  simp only [Nat.add_zero] at r38 rloc
  have hff : f = f' + 1 := by
    by_cases h0 : f' = 0
    · rw [if_pos h0] at r35; omega
    · rw [if_neg h0] at r35; exact r35
  have hsp : t.stackSpace < t.stack.length := by omega
  set w : WordLocW width := .word (BitVec.ofNat width (n + 1)) with hwdef
  set t5 : StackSemStateFiniteExact width C F :=
    { StackSemStateOps.setVar k w t with stack := t.stack.set t.stackSpace w } with ht5
  have heval : StackSemEvaluate.evaluate
      ((Compiler.Backend.StackLang.Prog.inst (HolInst.const k (BitVec.ofNat width (n + 1)))).seq
        (Compiler.Backend.StackLang.Prog.stackStore k 0), t) = (none, t5) := by
    rw [StackSemEvaluate.evaluate_seq, StackSemEvaluate.evaluate_inst]
    simp only [StackSemInst.instHOL, StackSemIntegerInstructions.instInteger,
      StackSemExpressions.assign, StackSemExpressions.wordExp, Option.join_some]
    simp only [StackSemControl.fixClock, StackSemStateOps.setVar, Nat.min_self]
    rw [StackSemEvaluate.evaluate_stackStore]
    simp only [r5, Bool.not_true, Bool.false_eq_true, if_false, Nat.add_zero,
      if_neg (by omega : ¬ t.stack.length ≤ t.stackSpace), StackSemStateOps.getVar,
      HolFiniteMapExact.updateEq, FUPDATE_HOL, if_true]
    simp [t5, StackSemStateOps.setVar, HolFiniteMapExact.updateEq, r5, hwdef]
  have ht5regs : ∀ i, i ≠ k → t5.regs.lookup i = t.regs.lookup i := by
    intro i hi
    simp [t5, StackSemStateOps.setVar, HolFiniteMapExact.updateEq, FUPDATE_HOL, hi]
  have ht5len : t5.stack.length = t.stack.length := by simp [t5]
  have hdrop5 : t5.stack.drop t.stackSpace = w :: t.stack.drop (t.stackSpace + 1) :=
    drop_set_self _ _ _ hsp
  have hdrop : t.stack.drop t.stackSpace = t.stack[t.stackSpace] :: t.stack.drop (t.stackSpace + 1) :=
    List.drop_eq_getElem_cons hsp
  set rest := t.stack.drop (t.stackSpace + 1) with hrest
  have hrestlen : f' ≤ rest.length := by simp [rest]; omega
  -- source locals sit in the registers or in the frame below the header slot
  have hloc' : ∀ n v, sptLookup n s.locals = some v → n % 2 = 0 → k ≤ n / 2 →
      n / 2 < k + f' ∧ (rest.take f')[f' - 1 - (n / 2 - k)]? = some v := by
    intro m v hm _ hk
    obtain ⟨-, hif⟩ := rloc m v hm
    rw [if_neg (by omega)] at hif
    obtain ⟨hslot, hlt⟩ := hif
    refine ⟨hlt, ?_⟩
    rw [hdrop, hff, List.take_succ_cons,
      show f' + 1 - 1 - (m / 2 - k) = (f' - 1 - (m / 2 - k)) + 1 by omega,
      List.getElem?_cons_succ] at hslot
    exact hslot
  -- the frame header word names the freshly written bitmap
  have hpre' := hpre
  rw [(appListAppend_thm _ _ ([] : List (BitVec width))).1,
    (appListAppend_thm bs bs (writeBitmapExact names.2 k f' : List (BitVec width))).2.1] at hpre'
  obtain ⟨extra, hextra⟩ := hpre'
  have hdropn : t.bitmaps.drop n =
      (writeBitmapExact names.2 k f' : List (BitVec width)) ++ extra := by
    have := congrArg (List.drop (appListAppend bs).length) hextra
    rw [List.drop_drop, show n - (appListAppend bs).length + (appListAppend bs).length = n by
      omega] at this
    rw [← this, List.append_assoc, List.drop_left]
  have hnb : n ≤ t.bitmaps.length := by
    have := congrArg List.length hextra
    simp only [List.length_append, List.length_drop] at this
    omega
  have hn1 : n + 1 < 2 ^ width := by omega
  set bits := (List.range f').map (fun x => decide
    (x ∈ (sptToAList names.2).map (fun (r, _) => f' - 1 - (r / 2 - k)))) with hbits
  have hbitslen : bits.length = f' := by simp [bits]
  have hfrb : fullReadBitmap t.bitmaps w = some bits := by
    have hne0 : (BitVec.ofNat width (n + 1)) ≠ 0 := by
      intro h
      have := congrArg BitVec.toNat h
      simp [Nat.mod_eq_of_lt hn1] at this
    have h1 : (1 : BitVec width).toNat = 1 := by
      have h2 := Nat.one_lt_two_pow (n := width) (by omega)
      simp [Nat.mod_eq_of_lt h2]
    have hsub1 : (BitVec.ofNat width (n + 1) - 1).toNat = n := by
      rw [BitVec.toNat_sub, h1, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn1,
        show 2 ^ width - 1 + (n + 1) = n + 2 ^ width by
          have := Nat.one_lt_two_pow (n := width) (by omega); omega,
        Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
    simp only [hwdef, fullReadBitmap, if_neg hne0, hsub1, hdropn]
    exact readBitmapAppendExtra _ _ _ (readBitmapWriteBitmap names.2 k f' r29)
  have hperm0 : s.permute 0 = id := by rw [r3]
  obtain ⟨he1, he2⟩ := AllocStateRel.cutEnvs_eq hcut
  have hsub := cutEnvs_subset hcut
  refine ⟨t5, heval, ?_, ?_, ht5len, rfl, fun i hi => ht5regs i hi⟩
  · rw [hdrop, hff, List.drop_succ_cons] at r38
    obtain ⟨rsorted, ys, hys, rH, raux⟩ := r38
    have hysLen : ys.length = s.stack.length := (absStackImpLength _ _ _ _ _ hys).1
    obtain ⟨rf, rlim, rmax⟩ := r37
    have hls : s.localsSize.getD f = f := rf hf0
    unfold stateRel
    refine ⟨r1, r2, ?_, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18,
      r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, ?_, ?_, by simp,
      sptWf_ln, ?_, ?_, ?_⟩
    · show (wordSemEnvToList envs.2 s.permute).2 = fun _ => id
      simp [wordSemEnvToList, r3]
    · show t.stackSpace + 0 ≤ t5.stack.length
      omega
    · show t5.stack.length < 2 ^ width
      omega
    · show stackSizeRel 0 (some 0) s.stackLimit
        (wordSemOptionMax s.stackMax (wordSemStackSize
          (.stackFrame s.localsSize (sptToAList envs.1) (wordSemEnvToList envs.2 s.permute).1 none ::
            s.stack)))
        (.stackFrame s.localsSize (sptToAList envs.1) (wordSemEnvToList envs.2 s.permute).1 none ::
          s.stack) t5.stack t.stackSpace 0
      refine ⟨by simp, by rw [ht5len]; exact rlim, ?_⟩
      intro m hm
      simp only [wordSemOptionMax] at hm
      split at hm
      · rename_i a b ha hb
        simp only [Option.some.injEq] at hm
        obtain ⟨hle, hsome, size, hsize, hsz⟩ := rmax a ha
        have hcons : wordSemStackSize
            (WordSemStackFrame.stackFrame s.localsSize (sptToAList envs.1)
              (wordSemEnvToList envs.2 s.permute).1 none :: s.stack) =
            wordSemOptionAdd s.localsSize (wordSemStackSize s.stack) := rfl
        rw [hcons, hsize] at hb
        rcases hloc : s.localsSize with _ | a'
        · rw [hloc] at hsome; cases hsome
        rw [hloc] at hb hls
        simp only [wordSemOptionAdd, Option.some.injEq, Option.getD_some] at hb hls
        refine ⟨by rw [ht5len]; omega, rfl, b, ?_, by rw [ht5len]; omega⟩
        show wordSemOptionAdd (some a') (wordSemStackSize s.stack) = some b
        rw [hsize]
        simp only [wordSemOptionAdd]
        rw [hb]
      · cases hm
    · show stackRel k s.handler
        (.stackFrame s.localsSize (sptToAList envs.1) (wordSemEnvToList envs.2 s.permute).1 none ::
          s.stack) (t.store.lookup .handler) ((t5.stack.drop (t.stackSpace + 0)).drop 0)
        t5.stack.length t.bitmaps (f' :: lens)
      rw [Nat.add_zero, List.drop_zero, hdrop5, ht5len]
      refine ⟨?_, (none, bits, rest.take f') :: ys, ?_, ?_, ?_⟩
      · simp only [List.all_cons, Bool.and_eq_true]
        refine ⟨?_, rsorted⟩
        have hd := descendingKeys_of_pairwise (wordSemEnvToList envs.2 s.permute).1
          (by rw [envToList_fst _ _ hperm0]; exact sortEnv_pairwise envs.2)
        exact hd
      · rw [absStack.eq_def]
        simp only [hfrb]
        rw [if_neg (by simp [hbitslen]), if_neg (by omega), hys]
      · intro hlt hhf
        simp only [List.length_cons] at hlt hhf ⊢
        by_cases heq : s.handler = s.stack.length
        · rw [heq, show s.stack.length + 1 - (s.stack.length + 1) = 0 by omega] at hhf
          simp [holEl, holHd, isHandlerFrame] at hhf
        · have hlt' : s.handler < s.stack.length := by omega
          rw [show s.stack.length + 1 - (s.handler + 1) = (s.stack.length - (s.handler + 1)) + 1 by
            omega, holEl_cons_succ] at hhf
          rw [rH hlt' hhf, show ys.length + 1 - (s.handler + 1) = (ys.length - (s.handler + 1)) + 1 by
            omega, List.drop_succ_cons]
      · simp only [stackRelAux]
        refine ⟨?_, ?_, ?_, by rw [ht5len] at *; exact raux⟩
        · intro n0 v h0 hnone
          have hlk1 : sptLookup n0 envs.1 = some v := by
            rw [GcSimulation.lookup_eq_sptAListLookup, ← sptLookup_sptFromAList,
              sptLookup_sptFromAList_sptToAList] at h0
            exact h0
          have hdom1 : sptDomain names.1 n0 ∧ sptLookup n0 s.locals = some v := by
            rw [he1, sptLookup_sptInterCases] at hlk1
            unfold sptDomain
            revert hlk1
            cases sptLookup n0 s.locals <;> cases sptLookup n0 names.1 <;> simp
          obtain ⟨heven, hk⟩ := hfst n0 hdom1.1
          obtain ⟨hlt, hslot⟩ := hloc' n0 v hdom1.2 heven hk
          rw [hbitslen]
          refine ⟨by simp only [adjustNames]; omega, ?_, ?_⟩
          · simp only [bits, adjustNames, List.getElem?_map,
              List.getElem?_range (show k + f' - (n0 / 2 + 1) < f' by omega), Option.map_some,
              Option.some.injEq, decide_eq_false_iff_not]
            intro hmem
            obtain ⟨⟨r, u⟩, hru, hri⟩ := List.mem_map.mp hmem
            simp only at hri
            have hdom2 : sptDomain names.2 r := by
              unfold sptDomain; rw [(sptToAList_mem_iff_lookup names.2 r u).mp hru]; rfl
            obtain ⟨heven2, hk2⟩ := hsnd r hdom2
            obtain ⟨w2, hw2⟩ := Option.isSome_iff_exists.mp (hsub r hdom2)
            obtain ⟨hlt2, -⟩ := hloc' r w2 hw2 heven2 hk2
            have hrn : r = n0 := by omega
            subst hrn
            have hmemL : (r, v) ∈ (wordSemEnvToList envs.2 s.permute).1 := by
              rw [wordSemEnvToList_mem_iff, sptToAList_mem_iff_lookup, he2,
                sptLookup_sptInterCases, hdom1.2]
              obtain ⟨u', hu'⟩ := Option.isSome_iff_exists.mp hdom2
              rw [hu']
            have := (List.lookup_eq_none_iff.mp hnone) (r, v) hmemL
            simp at this
          · rw [GcSimulation.lookup_eq_sptAListLookup,
              aLookupIndexList _ _ _ (by simp only [List.length_take]; omega)]
            simp only [List.length_take, Nat.min_eq_left hrestlen]
            rw [show f' + k - (n0 / 2 + 1) = f' - 1 - (n0 / 2 - k) by omega]
            exact hslot
        · rw [he2]
          exact wLiveFilterBitmap k f' names.2 s.locals s.permute (rest.take f') hperm0 hsub hsnd
            (by simp only [List.length_take]; omega) hloc'
        · simp only [List.length_take, Nat.min_eq_left hrestlen]
          rw [← hff]; exact hls
    · intro m v hm
      change sptLookup m Spt.ln = some v at hm
      simp [sptLookup] at hm
  · unfold stateRel
    refine ⟨r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18,
      r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, ?_, ?_, r35, r36,
      ?_, ?_, ?_⟩
    · show t.stackSpace + f ≤ t5.stack.length
      omega
    · show t5.stack.length < 2 ^ width
      omega
    · show stackSizeRel f s.localsSize s.stackLimit s.stackMax s.stack t5.stack t.stackSpace 0
      simpa only [stackSizeRel, ht5len] using r37
    · show stackRel k s.handler s.stack (t.store.lookup .handler)
        ((t5.stack.drop (t.stackSpace + 0)).drop f) t5.stack.length t.bitmaps lens
      rw [Nat.add_zero, hdrop5, ht5len, hff, List.drop_succ_cons]
      rw [hdrop, hff, List.drop_succ_cons] at r38
      exact r38
    · intro m v hm
      obtain ⟨he, hif⟩ := rloc m v hm
      refine ⟨he, ?_⟩
      show if m / 2 < k then t5.regs.lookup (m / 2) = some v
        else ((t5.stack.drop (t.stackSpace + 0)).take f)[f - 1 - (m / 2 - k)]? = some v ∧
          m / 2 < k + f'
      by_cases hlt : m / 2 < k
      · rw [if_pos hlt] at hif ⊢
        rw [ht5regs _ (by omega)]
        exact hif
      · rw [if_neg hlt] at hif ⊢
        obtain ⟨hslot, hbound⟩ := hif
        refine ⟨?_, hbound⟩
        rw [Nat.add_zero, hdrop5, hff, List.take_succ_cons,
          show f' + 1 - 1 - (m / 2 - k) = (f' - 1 - (m / 2 - k)) + 1 by omega,
          List.getElem?_cons_succ]
        rw [hdrop, hff, List.take_succ_cons,
          show f' + 1 - 1 - (m / 2 - k) = (f' - 1 - (m / 2 - k)) + 1 by omega,
          List.getElem?_cons_succ] at hslot
        exact hslot

end Flapjack.WordToStackProofs.EvaluateWLive
