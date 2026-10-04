import Flapjack.Compiler.Backend.Semantics.WordSem.Props.EvaluateAddClock

/-!
# wordProps `permute_swap_lemma` over the exact wordSem evaluator

Counterpart of `cakeml/compiler/backend/semantics/wordPropsScript.sml:3241-3382`.
The permutation oracle `permute` is read only by `push_env` (in `Alloc` and
returning `Call`). Every other helper commutes with a change of `permute`;
those commuting facts are untagged support here, as with the clock-constancy
lemmas of `evaluate_add_clock`. The tagged theorem is proved by recursion on
HOL's termination measure, following HOL's `evaluate_ind` case split.
-/

namespace Flapjack

namespace WordSemPermuteSwapSupport

/-- Same-module canonical finite-support witness for the `fpRegs`/`store`
    fields named by the tagged theorem of this module. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} [NeZero width] {C : Type} {F : Type} :
    (∀ (state : WordSemStateBroad width C F) (h : state.FiniteSupport),
        (WordSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : WordSemStateFiniteExact width C F,
        WordSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  WordSemStateExact.holFmapAsFiniteSupportWitness

end WordSemPermuteSwapSupport

namespace WordSemStateFiniteExact

section PermuteConst

variable {width : Nat} [NeZero width] {C : Type} {F : Type}

theorem wordExp_withPermute (s : WordSemStateFiniteExact width C F) (k : Nat → Nat → Nat) :
    ∀ e : WordLangExpHOL (BitVec width), wordExp { s with permute := k } e = wordExp s e
  | .const w => by rw [wordExp, wordExp]
  | .var v => by rw [wordExp, wordExp]; rfl
  | .lookup n => by rw [wordExp, wordExp]; rfl
  | .load a => by
      rw [wordExp, wordExp, wordExp_withPermute s k a]
      rfl
  | .op op args => by
      rw [wordExp, wordExp]
      have : (args.attach.map fun (x : { x // x ∈ args }) => wordExp { s with permute := k } x.1) =
          (args.attach.map fun (x : { x // x ∈ args }) => wordExp s x.1) := by
        apply List.map_congr_left
        intro ⟨e, he⟩ _
        have := List.sizeOf_lt_of_mem he
        exact wordExp_withPermute s k e
      simp only [] at this ⊢
      rw [this]
  | .shift sh e1 e2 => by
      rw [wordExp, wordExp, wordExp_withPermute s k e1, wordExp_withPermute s k e2]
termination_by e => sizeOf e

theorem getVars_withPermute (s : WordSemStateFiniteExact width C F) (k : Nat → Nat → Nat) :
    ∀ ns, getVars ns { s with permute := k } = getVars ns s
  | [] => rfl
  | n :: ns => by
      simp only [getVars, getVars_withPermute s k ns]
      rfl

theorem memStore_withPermute (s : WordSemStateFiniteExact width C F) (k : Nat → Nat → Nat)
    (a : BitVec width) (w : WordLocW width) :
    memStore a w { s with permute := k } =
      (memStore a w s).map (fun s' => { s' with permute := k }) := by
  unfold memStore
  by_cases h : s.mdomain a = true <;> simp [h]

set_option linter.unusedSimpArgs false in
theorem inst_withPermute (s : WordSemStateFiniteExact width C F) (k : Nat → Nat → Nat)
    (i : WordLangInst (BitVec width)) :
    inst i { s with permute := k } = (inst i s).map (fun s' => { s' with permute := k }) := by
  cases i with
  | skip => rfl
  | const r w => simp only [inst, assign, wordExp_withPermute]; split <;> rfl
  | arith a =>
    cases a <;> simp only [inst, assign, wordExp_withPermute, getVars_withPermute] <;>
      (repeat' split) <;> first | rfl | simp_all
  | mem op r a =>
    cases a
    cases op <;> simp only [inst, wordExp_withPermute, getVar, memStore_withPermute] <;>
      (repeat' split) <;> first | rfl | (subst_vars; rfl) |
        (simp_all [memLoad, memStore, setVar]; done) |
        (simp_all [memLoad, memStore, setVar]; obtain ⟨_, rfl⟩ := ‹_ ∧ _›; subst_vars; rfl)
theorem popEnv_withPermute (s : WordSemStateFiniteExact width C F) (k : Nat → Nat → Nat) :
    popEnv { s with permute := k } = (popEnv s).map (fun s' => { s' with permute := k }) := by
  unfold popEnv
  simp only
  split <;> rfl

theorem gc_withPermute (s : WordSemStateFiniteExact width C F) (k : Nat → Nat → Nat) :
    gc { s with permute := k } = (gc s).map (fun s' => { s' with permute := k }) := by
  unfold gc
  simp only
  split
  · rfl
  · split <;> rfl

theorem jumpExc_withPermute (s : WordSemStateFiniteExact width C F) (k : Nat → Nat → Nat) :
    jumpExc { s with permute := k } =
      (jumpExc s).map (fun p => ({ p.1 with permute := k }, p.2.1, p.2.2)) := by
  unfold jumpExc
  simp only
  split
  · split <;> rfl
  · rfl

theorem cutState_withPermute (s : WordSemStateFiniteExact width C F) (k : Nat → Nat → Nat)
    (names : WordLangCutsetsHOL) :
    cutState names { s with permute := k } =
      (cutState names s).map (fun s' => { s' with permute := k }) := by
  unfold cutState
  simp only
  split <;> rfl

theorem shMemSetVar_withPermute (s : WordSemStateFiniteExact width C F) (k : Nat → Nat → Nat)
    (res : Option (HolFfiResult F)) (v : Nat) :
    shMemSetVar (rw := width) res v { s with permute := k } =
      ((shMemSetVar (rw := width) res v s).1,
        { (shMemSetVar (rw := width) res v s).2 with permute := k }) := by
  cases res with
  | none => rfl
  | some r => cases r <;> rfl

set_option linter.unusedSimpArgs false in
theorem shareInst_withPermute (s : WordSemStateFiniteExact width C F) (k : Nat → Nat → Nat)
    (op : WordMemOp) (v : Nat) (ad : BitVec width) :
    shareInst (rw := width) op v ad { s with permute := k } =
      ((shareInst (rw := width) op v ad s).1,
        { (shareInst (rw := width) op v ad s).2 with permute := k }) := by
  cases op <;> simp only [shareInst, shMemSetVar_withPermute] <;>
    simp only [shMemLoad, shMemLoadByte, shMemLoad16, shMemLoad32,
      shMemStore, shMemStoreByte, shMemStore16, shMemStore32, getVar] <;>
    (repeat' split) <;> first | rfl | simp_all [flushState, setVar]

/-- The statements whose evaluation neither reads `permute` nor recurses. -/
def wordProgPermuteConst {α : Type} : WordLangProgHOL α → Bool
  | .mustTerminate _ | .call _ _ _ _ | .seq _ _ | .ite _ _ _ _ _ | .loop _ _ _
  | .alloc _ _ => false
  | _ => true

set_option linter.unusedSimpArgs false in
/-- A permute-constant statement runs the same under any permutation oracle
    and keeps it. -/
theorem evaluate_withPermute_const (s : WordSemStateFiniteExact width C F)
    (k : Nat → Nat → Nat) (p : WordLangProgHOL (BitVec width))
    (hp : wordProgPermuteConst p = true) :
    evaluate p { s with permute := k } =
      ((evaluate p s).1, { (evaluate p s).2 with permute := k }) := by
  cases p <;> simp only [wordProgPermuteConst, Bool.false_eq_true] at hp <;>
    rw [evaluate, evaluate] <;>
    simp only [getVar, getVars_withPermute, wordExp_withPermute, inst_withPermute,
      shareInst_withPermute, jumpExc_withPermute, memStore_withPermute, getStore] <;>
    (repeat' split) <;>
    first | rfl | simp_all [flushState, setVar, setVars, setStore, unsetVar, decClock]

end PermuteConst

section PermuteSwap

variable {width : Nat} [NeZero width] {C : Type} {F : Type}

/-- HOL's chosen source oracle for a `push_env`: keep the first permutation
    and shift the requested continuation by one. -/
def permuteShift (first : Nat → Nat) (q : Nat → Nat → Nat) : Nat → Nat → Nat :=
  fun x => if x = 0 then first else q (x - 1)

theorem pushEnv_permuteShift (s : WordSemStateFiniteExact width C F) (q : Nat → Nat → Nat)
    (envs : Spt (WordLocW width) × Spt (WordLocW width))
    (h : Option (Nat × WordLangProgHOL (BitVec width) × Nat × Nat)) :
    pushEnv envs h { s with permute := permuteShift (s.permute 0) q } =
      { pushEnv envs h s with permute := q } := by
  cases h with
  | none => simp [pushEnv, wordSemEnvToList, permuteShift]
  | some v =>
      obtain ⟨_, _, _, _⟩ := v
      simp [pushEnv, wordSemEnvToList, permuteShift]

theorem alloc_permuteShift (s : WordSemStateFiniteExact width C F) (q : Nat → Nat → Nat)
    (w : BitVec width) (names : WordLangCutsetsHOL)
    (h : (alloc w names s).1 ≠ some .error) :
    alloc w names { s with permute := permuteShift (s.permute 0) q } =
      ((alloc w names s).1, { (alloc w names s).2 with permute := q }) := by
  unfold alloc at h ⊢
  simp only at h ⊢
  split
  · rename_i hc; rw [hc] at h; exact absurd rfl h
  · rename_i envs hc
    rw [hc] at h
    simp only at h
    have hpush : pushEnv envs none
        (setStore .allocSize (.word w) { s with permute := permuteShift (s.permute 0) q }) =
        { pushEnv envs none (setStore .allocSize (.word w) s) with permute := q } :=
      pushEnv_permuteShift (setStore .allocSize (.word w) s) q envs none
    rw [hpush, gc_withPermute]
    cases hg : gc (pushEnv envs none (setStore .allocSize (.word w) s)) with
    | none => rw [hg] at h; exact absurd rfl h
    | some g =>
      rw [hg] at h
      simp only [Option.map_some, popEnv_withPermute] at h ⊢
      cases hp : popEnv g with
      | none => rw [hp] at h; exact absurd rfl h
      | some p =>
        rw [hp] at h
        simp only [Option.map_some] at h ⊢
        cases hs : getStore .allocSize p with
        | none => rw [hs] at h; exact absurd rfl h
        | some a =>
          have hs' : getStore .allocSize { p with permute := q } = some a := hs
          rw [hs] at h
          simp only [hs'] at h ⊢
          have hsp : hasSpace a { p with permute := q } = hasSpace a p := rfl
          rw [hsp]
          split <;> rfl

theorem pushEnv_stackMax_withPermute (s : WordSemStateFiniteExact width C F)
    (k : Nat → Nat → Nat) (envs : Spt (WordLocW width) × Spt (WordLocW width))
    (h : Option (Nat × WordLangProgHOL (BitVec width) × Nat × Nat)) :
    (pushEnv envs h { s with permute := k }).stackMax = (pushEnv envs h s).stackMax := by
  cases h with
  | none => simp [pushEnv, wordSemStackSize, wordSemStackSizeFrame]
  | some v =>
      obtain ⟨_, _, _, _⟩ := v
      simp [pushEnv, wordSemStackSize, wordSemStackSizeFrame]

theorem callEnv_pushEnv_stackMax_withPermute (s : WordSemStateFiniteExact width C F)
    (k : Nat → Nat → Nat) (args : List (WordLocW width)) (ss : Option Nat)
    (envs : Spt (WordLocW width) × Spt (WordLocW width))
    (h : Option (Nat × WordLangProgHOL (BitVec width) × Nat × Nat)) :
    (callEnv args ss (pushEnv envs h { s with permute := k })).stackMax =
      (callEnv args ss (pushEnv envs h s)).stackMax := by
  cases h with
  | none => simp [callEnv, pushEnv, wordSemStackSize, wordSemStackSizeFrame]
  | some v =>
      obtain ⟨_, _, _, _⟩ := v
      simp [callEnv, pushEnv, wordSemStackSize, wordSemStackSizeFrame]

set_option linter.unusedSimpArgs false in
/-- Recursive core of HOL `permute_swap_lemma`, by recursion on HOL's
    termination measure. -/
theorem permute_swap_aux :
    ∀ (p : WordLangProgHOL (BitVec width)) (s : WordSemStateFiniteExact width C F)
      (perm : Nat → Nat → Nat),
      (evaluate p s).1 ≠ some .error →
      ∃ perm', evaluate p { s with permute := perm' } =
        ((evaluate p s).1, { (evaluate p s).2 with permute := perm })
  | .alloc n names, s, perm, h => by
      have ht := (evaluate_def_rebound (width := width) (C := C) (F := F)).2.1
      rw [ht] at h
      refine ⟨permuteShift (s.permute 0) perm, ?_⟩
      rw [ht, ht]
      have hv : getVar n { s with permute := permuteShift (s.permute 0) perm } = getVar n s := rfl
      rw [hv]
      rcases hg : getVar n s with _ | ⟨w⟩ | ⟨a, b⟩ <;> rw [hg] at h <;> simp only at h ⊢
      · exact absurd rfl h
      · exact alloc_permuteShift s perm w names h
      · exact absurd rfl h
  | .mustTerminate q, s, perm, h => by
      have ht := (evaluate_def_rebound (width := width) (C := C) (F := F)).2.2.2.2.2.2.2.2.2.2.2.1
      rw [ht] at h
      by_cases hz : s.termdep = 0
      · simp [hz] at h
      simp only [hz, if_false] at h
      rcases hq : evaluate q { s with
          clock := wordSemMustTerminateLimit width
          termdep := s.termdep - 1 } with ⟨r, s1⟩
      rw [hq] at h
      have hr : r ≠ some .error := by
        intro hr; subst hr; simp at h
      obtain ⟨p', hp'⟩ := permute_swap_aux q { s with
          clock := wordSemMustTerminateLimit width
          termdep := s.termdep - 1 } perm (by rw [hq]; exact hr)
      rw [hq] at hp'
      refine ⟨p', ?_⟩
      rw [ht, ht]
      have hzs : ({ s with permute := p' } : WordSemStateFiniteExact width C F).termdep ≠ 0 := hz
      simp only [hzs, hz, if_false]
      have hin : ({ { s with permute := p' } with
            clock := wordSemMustTerminateLimit width
            termdep := ({ s with permute := p' } : WordSemStateFiniteExact width C F).termdep - 1 } :
            WordSemStateFiniteExact width C F) =
          { { s with clock := wordSemMustTerminateLimit width, termdep := s.termdep - 1 } with
            permute := p' } := rfl
      rw [hin, hp', hq]
      simp only
      rcases r with _ | x
      · rfl
      · cases x <;> first | rfl | simp at h
  | .seq c1 c2, s, perm, h => by
      have ht := (evaluate_def_rebound (width := width) (C := C) (F := F)).2.2.2.2.2.2.2.2.2.2.2.2.1
      rw [ht] at h
      rcases h1 : evaluate c1 s with ⟨r1, s1⟩
      rw [h1] at h
      have hc := evaluate_clock c1 s r1 s1 h1
      cases r1 with
      | none =>
        simp only at h
        obtain ⟨p2, hp2⟩ := permute_swap_aux c2 s1 perm h
        obtain ⟨p1, hp1⟩ := permute_swap_aux c1 s p2 (by rw [h1]; simp)
        rw [h1] at hp1
        refine ⟨p1, ?_⟩
        rw [ht, ht, hp1, h1]
        simp only
        exact hp2
      | some x =>
        simp only at h
        obtain ⟨p1, hp1⟩ := permute_swap_aux c1 s perm (by rw [h1]; exact h)
        rw [h1] at hp1
        refine ⟨p1, ?_⟩
        rw [ht, ht, hp1, h1]
  | .ite cmp r1 ri c1 c2, s, perm, h => by
      have ht := (evaluate_def_rebound (width := width) (C := C) (F := F)).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      rw [ht] at h
      have hv : ∀ q : Nat → Nat → Nat, getVar r1 { s with permute := q } = getVar r1 s :=
        fun _ => rfl
      have hi : ∀ q : Nat → Nat → Nat, getVarImm ri { s with permute := q } = getVarImm ri s := by
        intro q; cases ri <;> rfl
      rcases hx : getVar r1 s with _ | x
      · simp [hx] at h
      rcases hy : getVarImm ri s with _ | y
      · simp [hx, hy] at h
      simp only [hx, hy] at h
      rcases hw : wordSemWordCmp cmp x y with _ | _ | _
      · simp [hw] at h
      all_goals simp only [hw] at h
      · obtain ⟨p1, hp1⟩ := permute_swap_aux c2 s perm h
        refine ⟨p1, ?_⟩
        rw [ht, ht, hv, hi, hx, hy]
        simp only [hw]
        exact hp1
      · obtain ⟨p1, hp1⟩ := permute_swap_aux c1 s perm h
        refine ⟨p1, ?_⟩
        rw [ht, ht, hv, hi, hx, hy]
        simp only [hw]
        exact hp1
  | .loop names c exitNames, s, perm, h => by
      have ht := (evaluate_def_rebound (width := width) (C := C) (F := F)).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      rw [ht] at h
      rcases hcs : cutState (names, .ln) s with _ | s'
      · simp [hcs] at h
      simp only [hcs] at h
      have hc2 := cutState_clock_termdep _ _ _ hcs
      have hcsP : ∀ q : Nat → Nat → Nat,
          cutState (names, .ln) { s with permute := q } = some { s' with permute := q } := by
        intro q; rw [cutState_withPermute, hcs]; rfl
      rcases hb : evaluate c s' with ⟨rb, s1⟩
      rw [hb] at h
      have hc := evaluate_clock c s' rb s1 hb
      by_cases hcont : wordSemContLoop rb = true
      · have hrb : rb ≠ some .error := by
          intro hr; subst hr; simp [wordSemContLoop] at hcont
        simp only [hcont, if_true] at h
        by_cases hz : s1.clock = 0
        · obtain ⟨p1, hp1⟩ := permute_swap_aux c s' perm (by rw [hb]; exact hrb)
          rw [hb] at hp1
          refine ⟨p1, ?_⟩
          rw [ht, ht, hcsP p1, hcs]
          simp only
          rw [hp1, hb]
          have hz' : ({ s1 with permute := perm } : WordSemStateFiniteExact width C F).clock = 0 := hz
          simp only [hcont, if_true, hz, hz']
          simp [flushState, hz]
        · simp only [hz, if_false, wordSemSTOP] at h
          obtain ⟨p2, hp2⟩ := permute_swap_aux (.loop names c exitNames) (decClock s1) perm h
          obtain ⟨p1, hp1⟩ := permute_swap_aux c s' p2 (by rw [hb]; exact hrb)
          rw [hb] at hp1
          refine ⟨p1, ?_⟩
          rw [ht, ht, hcsP p1, hcs]
          simp only
          rw [hp1, hb]
          have hz' : ¬ ({ s1 with permute := p2 } : WordSemStateFiniteExact width C F).clock = 0 := hz
          simp only [hcont, if_true, hz, hz', if_false, wordSemSTOP]
          exact hp2
      · simp only [hcont, Bool.false_eq_true, if_false] at h
        have hrb : rb ≠ some .error := by
          intro hr; subst hr; simp [wordSemExitLoop] at h
        obtain ⟨p1, hp1⟩ := permute_swap_aux c s' perm (by rw [hb]; exact hrb)
        rw [hb] at hp1
        refine ⟨p1, ?_⟩
        rw [ht, ht, hcsP p1, hcs]
        simp only
        rw [hp1, hb]
        simp only [hcont, Bool.false_eq_true, if_false]
        rcases rb with _ | x
        · simp [wordSemContLoop] at hcont
        cases x with
        | «break» n =>
            rcases n with _ | n
            · simp only
              rw [cutState_withPermute]
              rcases hce : cutState (exitNames, .ln) s1 with _ | s2
              · simp [hce] at h
              · rfl
            · rfl
        | _ => rfl
  | .call ret dest args handler, s, perm, h => by
      have ht := (evaluate_def_rebound (width := width) (C := C) (F := F)).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
      rw [ht] at h
      rcases hg : getVars args s with _ | xs
      · simp [hg] at h
      simp only [hg] at h
      by_cases hbad : wordSemBadDestArgs dest args = true
      · simp [hbad] at h
      simp only [hbad, Bool.false_eq_true, if_false] at h
      rcases hf : wordSemFindCode dest (wordSemAddRetLoc ret xs) s.code s.stackSize with
        _ | ⟨args1, prog, ss⟩
      · simp [hf] at h
      simp only [hf] at h
      have hf' : ∀ q : Nat → Nat → Nat, wordSemFindCode dest (wordSemAddRetLoc ret xs)
          ({ s with permute := q } : WordSemStateFiniteExact width C F).code
          ({ s with permute := q } : WordSemStateFiniteExact width C F).stackSize =
            some (args1, prog, ss) := fun _ => hf
      cases ret with
      | none =>
        cases handler with
        | some _ => simp at h
        | none =>
          simp only at h
          by_cases hz : s.clock = 0
          · refine ⟨perm, ?_⟩
            rw [ht, ht, getVars_withPermute, hg]
            simp only [hbad, Bool.false_eq_true, if_false]
            simp only [hf', hf]
            have hz' : ({ s with permute := perm } : WordSemStateFiniteExact width C F).clock = 0 := hz
            simp only [hz, hz', if_true]
            simp [flushState, hz]
          simp only [hz, if_false] at h
          rcases hcv : evaluate prog (callEnv args1 ss (decClock s)) with ⟨rc, sc⟩
          rw [hcv] at h
          have hc := evaluate_clock prog _ rc sc hcv
          have hrc : rc ≠ some .error := by
            intro hr; subst hr; simp [wordSemBadFunReturn] at h
          obtain ⟨p1, hp1⟩ := permute_swap_aux prog (callEnv args1 ss (decClock s)) perm
            (by rw [hcv]; exact hrc)
          rw [hcv] at hp1
          refine ⟨p1, ?_⟩
          rw [ht, ht, getVars_withPermute, hg]
          simp only [hbad, Bool.false_eq_true, if_false]
          simp only [hf', hf]
          have hz' : ¬ ({ s with permute := p1 } : WordSemStateFiniteExact width C F).clock = 0 := hz
          simp only [hz, hz', if_false]
          have hce : callEnv args1 ss (decClock { s with permute := p1 }) =
              { callEnv args1 ss (decClock s) with permute := p1 } := rfl
          rw [hce, hp1, hcv]
          simp only
          split <;> rfl
      | some rv =>
        obtain ⟨n, names, retHandler, l1, l2⟩ := rv
        simp only at h
        by_cases hdc : sptDomainEmpty names.fst ∨ ¬ n.Nodup
        · simp [hdc] at h
        simp only [hdc, if_false] at h
        rcases hce : wordSemCutEnvs names s.locals with _ | envs
        · simp [hce] at h
        simp only [hce] at h
        have hce' : ∀ q : Nat → Nat → Nat, wordSemCutEnvs names
            ({ s with permute := q } : WordSemStateFiniteExact width C F).locals = some envs :=
          fun _ => hce
        have hopen : ∀ q : Nat → Nat → Nat, ¬ s.clock = 0 →
            evaluate (.call (some (n, names, retHandler, l1, l2)) dest args handler)
              { s with permute := q } =
              match evaluate prog (callEnv args1 ss (pushEnv envs handler
                  (decClock ({ s with permute := q } : WordSemStateFiniteExact width C F)))) with
              | (some (.result x ys), s2) =>
                  if x ≠ .loc l1 l2 ∨ ys.length ≠ n.length then (some .error, s2)
                  else
                    match popEnv s2 with
                    | none => (some .error, s2)
                    | some s1 =>
                        if sptDomainEqUnion s1.locals envs.1 envs.2 then
                          evaluate retHandler (setVars n ys s1)
                        else (some .error, s1)
              | (some (.exception x y), s2) =>
                  match (generalizing := false) handler with
                  | none => (some (.exception x y), s2)
                  | some (n, hprog, l1, l2) =>
                      if x ≠ .loc l1 l2 then (some .error, s2)
                      else if sptDomainEqUnion s2.locals envs.1 envs.2 then
                        evaluate hprog (setVar n y s2)
                      else (some .error, s2)
              | (none, s) => (some .error, s)
              | (some (.break _), s) => (some .error, s)
              | (some (.continue _), s) => (some .error, s)
              | res => res := by
          intro q hz0
          rw [ht, getVars_withPermute, hg]
          simp only [hbad, Bool.false_eq_true, if_false]
          rw [hf']
          simp only [hdc, if_false]
          rw [hce']
          have hz0' : ¬ ({ s with permute := q } : WordSemStateFiniteExact width C F).clock = 0 := hz0
          simp only [hz0', if_false]
          rfl
        by_cases hz : s.clock = 0
        · refine ⟨perm, ?_⟩
          rw [ht, ht, getVars_withPermute, hg]
          simp only [hbad, Bool.false_eq_true, if_false, hf', hf, hdc, hce', hce]
          have hz' : ({ s with permute := perm } : WordSemStateFiniteExact width C F).clock = 0 := hz
          rw [if_pos hz', if_pos hz, callEnv_pushEnv_stackMax_withPermute]
          rfl
        simp only [hz, if_false] at h
        have hpush : ∀ q : Nat → Nat → Nat,
            callEnv args1 ss (pushEnv envs handler
              (decClock { s with permute := permuteShift (s.permute 0) q })) =
              { callEnv args1 ss (pushEnv envs handler (decClock s)) with permute := q } := by
          intro q
          exact congrArg (callEnv args1 ss) (pushEnv_permuteShift (decClock s) q envs handler)
        have hzq : ∀ q : Nat → Nat → Nat,
            ¬ ({ s with permute := q } : WordSemStateFiniteExact width C F).clock = 0 := fun _ => hz
        rcases hcv : evaluate prog (callEnv args1 ss (pushEnv envs handler (decClock s))) with
          ⟨rc, s2⟩
        rw [hcv] at h
        have hc := evaluate_clock prog _ rc s2 hcv
        have hR : ∀ q : Nat → Nat → Nat,
            evaluate prog (callEnv args1 ss (pushEnv envs handler
              (decClock { s with permute := permuteShift (s.permute 0) q }))) =
            evaluate prog { callEnv args1 ss (pushEnv envs handler (decClock s)) with permute := q } :=
          fun q => by rw [hpush]
        have hRHS : evaluate (.call (some (n, names, retHandler, l1, l2)) dest args handler) s =
            match (rc, s2) with
            | (some (.result x ys), s2) =>
                if x ≠ .loc l1 l2 ∨ ys.length ≠ n.length then (some .error, s2)
                else
                  match popEnv s2 with
                  | none => (some .error, s2)
                  | some s1 =>
                      if sptDomainEqUnion s1.locals envs.1 envs.2 then
                        evaluate retHandler (setVars n ys s1)
                      else (some .error, s1)
            | (some (.exception x y), s2) =>
                match (generalizing := false) handler with
                | none => (some (.exception x y), s2)
                | some (n, hprog, l1, l2) =>
                    if x ≠ .loc l1 l2 then (some .error, s2)
                    else if sptDomainEqUnion s2.locals envs.1 envs.2 then
                      evaluate hprog (setVar n y s2)
                    else (some .error, s2)
            | (none, s) => (some .error, s)
            | (some (.break _), s) => (some .error, s)
            | (some (.continue _), s) => (some .error, s)
            | res => res := by
          rw [ht]
          simp only [hg, hbad, Bool.false_eq_true, if_false, hf, hdc, hce, hz]
          rw [hcv]
          rfl
        rcases rc with _ | ⟨x, ys⟩ | ⟨x, y⟩ | k | k | _ | _ | _ | _
        · simp at h
        · by_cases hx : x ≠ WordLocW.loc l1 l2 ∨ ys.length ≠ n.length
          · simp [hx] at h
          simp only [hx, if_false] at h
          rcases hp : popEnv s2 with _ | s1
          · simp [hp] at h
          simp only [hp] at h
          have hc2 : s1.clock = s2.clock ∧ s1.termdep = s2.termdep :=
            ⟨popEnv_clock _ _ hp, popEnv_termdep _ _ hp⟩
          by_cases hdom : sptDomainEqUnion s1.locals envs.fst envs.snd
          · simp only [hdom, if_true] at h
            obtain ⟨p2, hp2⟩ := permute_swap_aux retHandler (setVars n ys s1) perm h
            obtain ⟨p1, hp1⟩ := permute_swap_aux prog
              (callEnv args1 ss (pushEnv envs handler (decClock s))) p2 (by rw [hcv]; simp)
            rw [hcv] at hp1
            refine ⟨permuteShift (s.permute 0) p1, ?_⟩
            rw [hopen _ hz, hR, hp1, hRHS]
            simp only [hx, if_false]
            rw [popEnv_withPermute, hp]
            have hdom' : sptDomainEqUnion ({ s1 with permute := p2 } :
                WordSemStateFiniteExact width C F).locals envs.fst envs.snd := hdom
            simp only [Option.map_some, hdom', hdom, if_true]
            exact hp2
          · simp [hdom] at h
        · cases handler with
          | none =>
            obtain ⟨p1, hp1⟩ := permute_swap_aux prog
              (callEnv args1 ss (pushEnv envs none (decClock s))) perm (by rw [hcv]; simp)
            rw [hcv] at hp1
            refine ⟨permuteShift (s.permute 0) p1, ?_⟩
            rw [hopen _ hz, hR, hp1, hRHS]
          | some hv =>
            obtain ⟨n', hprog, l1', l2'⟩ := hv
            simp only at h
            by_cases hx : x ≠ WordLocW.loc l1' l2'
            · simp [hx] at h
            simp only [hx, if_false] at h
            by_cases hdom : sptDomainEqUnion s2.locals envs.fst envs.snd
            · simp only [hdom, if_true] at h
              obtain ⟨p2, hp2⟩ := permute_swap_aux hprog (setVar n' y s2) perm h
              obtain ⟨p1, hp1⟩ := permute_swap_aux prog
                (callEnv args1 ss (pushEnv envs (some (n', hprog, l1', l2')) (decClock s))) p2
                (by rw [hcv]; simp)
              rw [hcv] at hp1
              refine ⟨permuteShift (s.permute 0) p1, ?_⟩
              rw [hopen _ hz, hR, hp1, hRHS]
              have hdom' : sptDomainEqUnion ({ s2 with permute := p2 } :
                  WordSemStateFiniteExact width C F).locals envs.fst envs.snd := hdom
              simp only [hx, if_false, hdom', hdom, if_true]
              exact hp2
            · simp [hdom] at h
        all_goals
          first
          | (simp at h; done)
          | (obtain ⟨p1, hp1⟩ := permute_swap_aux prog
                (callEnv args1 ss (pushEnv envs handler (decClock s))) perm
                (by rw [hcv]; simp)
             rw [hcv] at hp1
             refine ⟨permuteShift (s.permute 0) p1, ?_⟩
             rw [hopen _ hz, hR, hp1, hRHS])
  | .skip, s, perm, _ => ⟨perm, evaluate_withPermute_const s _ _ rfl⟩
  | .move a b, s, perm, _ => ⟨perm, evaluate_withPermute_const s _ _ rfl⟩
  | .inst a, s, perm, _ => ⟨perm, evaluate_withPermute_const s _ _ rfl⟩
  | .assign a b, s, perm, _ => ⟨perm, evaluate_withPermute_const s _ _ rfl⟩
  | .get a b, s, perm, _ => ⟨perm, evaluate_withPermute_const s _ _ rfl⟩
  | .set a b, s, perm, _ => ⟨perm, evaluate_withPermute_const s _ _ rfl⟩
  | .store a b, s, perm, _ => ⟨perm, evaluate_withPermute_const s _ _ rfl⟩
  | .tick, s, perm, _ => ⟨perm, evaluate_withPermute_const s _ _ rfl⟩
  | .storeConsts a b c d f, s, perm, _ => ⟨perm, evaluate_withPermute_const s _ _ rfl⟩
  | .raise a, s, perm, _ => ⟨perm, evaluate_withPermute_const s _ _ rfl⟩
  | WordLangProgHOL.return a b, s, perm, _ => ⟨perm, evaluate_withPermute_const s _ _ rfl⟩
  | WordLangProgHOL.break a, s, perm, _ => ⟨perm, evaluate_withPermute_const s _ _ rfl⟩
  | WordLangProgHOL.continue a, s, perm, _ => ⟨perm, evaluate_withPermute_const s _ _ rfl⟩
  | .opCurrHeap a b c, s, perm, _ => ⟨perm, evaluate_withPermute_const s _ _ rfl⟩
  | .locValue a b, s, perm, _ => ⟨perm, evaluate_withPermute_const s _ _ rfl⟩
  | .install a b c d f, s, perm, _ => ⟨perm, evaluate_withPermute_const s _ _ rfl⟩
  | .codeBufferWrite a b, s, perm, _ => ⟨perm, evaluate_withPermute_const s _ _ rfl⟩
  | .dataBufferWrite a b, s, perm, _ => ⟨perm, evaluate_withPermute_const s _ _ rfl⟩
  | .ffi a b c d f g, s, perm, _ => ⟨perm, evaluate_withPermute_const s _ _ rfl⟩
  | .shareInst a b c, s, perm, _ => ⟨perm, evaluate_withPermute_const s _ _ rfl⟩
termination_by p s _ => (s.termdep, s.clock, sizeOf p)
decreasing_by
  all_goals
    simp_wf
    apply wordSemLex
    try (rcases hc with ⟨_, _⟩)
    try (rcases hc2 with ⟨_, _⟩)
    try simp only [decClock, callEnv, setVars, setVar, pushEnv_clock, pushEnv_termdep,
      true_and] at *
    omega


end PermuteSwap

/-- Exact HOL `wordProps$permute_swap_lemma` (`wordPropsScript.sml:3241-3247`):

    ```
    ∀prog st perm.
      let (res,rst) = evaluate(prog,st) in
        res ≠ SOME Error ⇒
        ∃perm'. evaluate(prog,st with permute := perm') = (res,rst with permute:=perm)
    ```
-/
theorem permute_swap_lemma {width : Nat} [NeZero width] {C : Type} {F : Type} :
    ∀ (prog : WordLangProgHOL (BitVec width)) (st : WordSemStateFiniteExact width C F)
      (perm : Nat → Nat → Nat),
      let (res, rst) := evaluate prog st
      res ≠ some .error →
        ∃ perm', evaluate prog { st with permute := perm' } = (res, { rst with permute := perm }) := by
  intro prog st perm
  exact permute_swap_aux prog st perm

end WordSemStateFiniteExact

end Flapjack
