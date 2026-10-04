import Flapjack.Compiler.Backend.WordAlloc.Proofs.EvaluateRemoveDead.Leaves

/-!
# `evaluate_remove_dead` Inst case

The `Inst` case of `word_allocProofScript.sml:3900-4472` `evaluate_remove_dead`
(Resume block 4031). HOL unfolds every instruction at once; here the instruction
semantics is first summarised by its register footprint (`instReads`,
`instWrites`) and a congruence lemma for `inst`, and the case then follows from
`remove_dead_inst_def` and `get_live_inst_def` for that footprint.
-/

namespace Flapjack.WordAlloc

open WordSemStateFiniteExact

namespace EvaluateRemoveDeadInstWitnesses
/-- Roundtrip for the evaluator's actual imported canonical state carrier. -/
theorem holFmapAsFiniteSupportRelationWitness_WordSemStateFiniteExact
    {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : WordSemStateBroad width C F) (h : state.FiniteSupport),
        (WordSemStateBroad.ofBroad state h).toBroad = state) ∧
      (∀ state : WordSemStateFiniteExact width C F,
        WordSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  WordSemStateExact.holFmapAsFiniteSupportWitness
end EvaluateRemoveDeadInstWitnesses

/-- The integer registers an instruction reads (Flapjack infrastructure, no HOL
counterpart). -/
def instReads {width : Nat} : WordLangInst (BitVec width) → List Nat
  | .arith (.binop _ _ r2 (.reg r3)) | .arith (.shift _ _ r2 (.reg r3)) => [r2, r3]
  | .arith (.binop _ _ r2 (.imm _)) | .arith (.shift _ _ r2 (.imm _)) => [r2]
  | .arith (.div _ r2 r3) => [r3, r2]
  | .arith (.addCarry _ r2 r3 r4) => [r2, r3, r4]
  | .arith (.addOverflow _ r2 r3 _) | .arith (.subOverflow _ r2 r3 _) => [r2, r3]
  | .arith (.longMul _ _ r3 r4) => [r3, r4]
  | .arith (.longDiv _ _ r3 r4 r5) => [r3, r4, r5]
  | .mem .load _ (.addr a _) | .mem .load8 _ (.addr a _) | .mem .load32 _ (.addr a _) => [a]
  | .mem .store r (.addr a _) | .mem .store8 r (.addr a _) | .mem .store32 r (.addr a _) =>
      [a, r]
  | _ => []

/-- The integer registers an instruction writes (Flapjack infrastructure, no HOL
counterpart). -/
def instWrites {width : Nat} : WordLangInst (BitVec width) → List Nat
  | .const r _ => [r]
  | .arith (.binop _ r1 _ _) | .arith (.shift _ r1 _ _) | .arith (.div r1 _ _) => [r1]
  | .arith (.addCarry r1 _ _ r4) | .arith (.addOverflow r1 _ _ r4)
  | .arith (.subOverflow r1 _ _ r4) => [r1, r4]
  | .arith (.longMul r1 r2 _ _) | .arith (.longDiv r1 r2 _ _ _) => [r1, r2]
  | .mem .load r _ | .mem .load8 r _ | .mem .load32 r _ => [r]
  | _ => []

/-- `get_live_inst` keeps every register the instruction reads (Flapjack
infrastructure). -/
theorem getLiveInst_reads {width : Nat} [NeZero width] (i : WordLangInst (BitVec width))
    (live : NumSet) : ∀ x, x ∈ instReads i → sptDomain (getLiveInst i live) x := by
  intro x hx
  unfold instReads at hx
  split at hx
  all_goals first
    | (simp at hx; done)
    | (simp only [getLiveInst, getLiveInstCore]
       (try split at hx) <;> (try split) <;>
         simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx <;>
         rcases hx with rfl | rfl | rfl <;> simp_all [sptDomain_ins, sptDomain_del])

/-- `get_live_inst` keeps every live register the instruction does not write
(Flapjack infrastructure). -/
theorem getLiveInst_frame {width : Nat} [NeZero width] (i : WordLangInst (BitVec width))
    (live : NumSet) :
    ∀ k, sptDomain live k → k ∉ instWrites i → sptDomain (getLiveInst i live) k := by
  intro k hk hw
  unfold getLiveInst getLiveInstCore
  split
  all_goals first
    | exact hk
    | (simp only [instWrites] at hw
       (try split at hw) <;> (try split) <;> simp_all [sptDomain_ins, sptDomain_del])

/-- A removable instruction writes only dead registers (Flapjack infrastructure). -/
theorem removeDeadInst_writes {width : Nat} [NeZero width] (i : WordLangInst (BitVec width))
    (live : NumSet) (h : removeDeadInst i live = true) :
    ∀ k, k ∈ instWrites i → ¬ sptDomain live k := by
  intro k hk
  unfold removeDeadInst removeDeadInstCore at h
  split at h
  all_goals first
    | (simp [instWrites] at hk; done)
    | (simp only [instWrites] at hk
       (try split at h) <;> (try split at hk) <;>
         simp only [List.mem_cons, List.mem_nil_iff, or_false] at hk <;>
         rcases hk with rfl | rfl <;> simp_all [sptDomain, Option.isNone_iff_eq_none])

/-- The conclusion of `instCongr` (Flapjack infrastructure): running the instruction
on related locals and any store gives the source result with locals that agree on
the written registers and are unchanged elsewhere; the store is untouched. -/
def InstCongrPost {width : Nat} [NeZero width] {C F : Type} (i : WordLangInst (BitVec width))
    (s s1 : WordSemStateFiniteExact width C F) (t : Spt (WordLocW width))
    (ts : HolFiniteMapExact WordStoreHOL (WordLocW width)) : Prop :=
  ∃ t' : Spt (WordLocW width),
    inst i { s with locals := t, store := ts } = some { s1 with locals := t', store := ts } ∧
    (∀ k, k ∉ instWrites i →
      sptLookup k s1.locals = sptLookup k s.locals ∧ sptLookup k t' = sptLookup k t) ∧
    (∀ k, k ∈ instWrites i → sptLookup k t' = sptLookup k s1.locals) ∧
    s1.store = s.store

theorem instCongrPostOne {width : Nat} [NeZero width] {C F : Type}
    (i : WordLangInst (BitVec width)) (s : WordSemStateFiniteExact width C F)
    (t : Spt (WordLocW width)) (ts : HolFiniteMapExact WordStoreHOL (WordLocW width))
    (r : Nat) (v : WordLocW width) (hw : instWrites i = [r])
    (h : inst i { s with locals := t, store := ts } =
      some (setVar r v { s with locals := t, store := ts })) :
    InstCongrPost i s (setVar r v s) t ts := by
  refine ⟨sptInsert r v t, h, ?_, ?_, rfl⟩
  · intro k hk
    rw [hw] at hk
    have hkr : k ≠ r := by simpa using hk
    simp only [setVar, sptLookup_sptInsert_ne _ _ _ _ hkr, and_self]
  · intro k hk
    rw [hw] at hk
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hk
    subst hk
    simp only [setVar, sptLookup_sptInsert_same]

theorem instCongrPostTwo {width : Nat} [NeZero width] {C F : Type}
    (i : WordLangInst (BitVec width)) (s : WordSemStateFiniteExact width C F)
    (t : Spt (WordLocW width)) (ts : HolFiniteMapExact WordStoreHOL (WordLocW width))
    (a b : Nat) (x y : WordLocW width) (hw : ∀ k, k ∈ instWrites i ↔ k = a ∨ k = b)
    (h : inst i { s with locals := t, store := ts } =
      some (setVar b y (setVar a x { s with locals := t, store := ts }))) :
    InstCongrPost i s (setVar b y (setVar a x s)) t ts := by
  refine ⟨sptInsert b y (sptInsert a x t), h, ?_, ?_, rfl⟩
  · intro k hk
    rw [hw, not_or] at hk
    simp only [setVar, sptLookup_sptInsert_ne _ _ _ _ hk.1, sptLookup_sptInsert_ne _ _ _ _ hk.2,
      and_self]
  · intro k hk
    rw [hw] at hk
    simp only [setVar]
    rcases hk with rfl | rfl
    · by_cases hab : k = b
      · subst hab; simp only [sptLookup_sptInsert_same]
      · rw [sptLookup_sptInsert_ne _ _ _ _ hab, sptLookup_sptInsert_ne _ _ _ _ hab,
          sptLookup_sptInsert_same, sptLookup_sptInsert_same]
    · simp only [sptLookup_sptInsert_same]

theorem instCongrPostZero {width : Nat} [NeZero width] {C F : Type}
    (i : WordLangInst (BitVec width)) (s s1 : WordSemStateFiniteExact width C F)
    (t : Spt (WordLocW width)) (ts : HolFiniteMapExact WordStoreHOL (WordLocW width))
    (hw : instWrites i = []) (hl : s1.locals = s.locals) (hs : s1.store = s.store)
    (h : inst i { s with locals := t, store := ts } = some { s1 with locals := t, store := ts }) :
    InstCongrPost i s s1 t ts := by
  refine ⟨t, h, fun k _ => ⟨by rw [hl], rfl⟩, fun k hk => ?_, hs⟩
  rw [hw] at hk
  cases hk

/-- `get_vars` transfers to related locals (Flapjack infrastructure). -/
theorem getVarsTransfer {width : Nat} [NeZero width] {C F : Type}
    (s : WordSemStateFiniteExact width C F) (t : Spt (WordLocW width))
    (ts : HolFiniteMapExact WordStoreHOL (WordLocW width)) :
    ∀ (ls : List Nat) (vs : List (WordLocW width)),
      (∀ x v, x ∈ ls → sptLookup x s.locals = some v → sptLookup x t = some v) →
      WordSemStateFiniteExact.getVars ls s = some vs →
      WordSemStateFiniteExact.getVars ls { s with locals := t, store := ts } = some vs
  | [], vs, _, h => h
  | x :: xs, vs, hr, h => by
      simp only [WordSemStateFiniteExact.getVars, WordSemStateFiniteExact.getVar] at h ⊢
      cases hx : sptLookup x s.locals with
      | none => rw [hx] at h; cases h
      | some v =>
        cases hxs : WordSemStateFiniteExact.getVars xs s with
        | none => rw [hx, hxs] at h; cases h
        | some ws =>
          rw [hx, hxs] at h
          have hxs' := getVarsTransfer s t ts xs ws (fun y w hy => hr y w (by simp [hy])) hxs
          rw [hr x v (by simp) hx, hxs']
          exact h

/-- Two finite maps agree outside the union of their supports (Flapjack
infrastructure). -/
theorem liveStoreRelSupports {α β : Type} (a b : HolFiniteMapExact α β) :
    ∃ nl, liveStoreRel nl a b := by
  obtain ⟨ka, hka⟩ := a.finiteSupport
  obtain ⟨kb, hkb⟩ := b.finiteSupport
  refine ⟨ka ++ kb, fun n hn => ?_⟩
  cases h1 : a.lookup n with
  | some _ => exact absurd (List.mem_append_left _ (hka n (by rw [h1]; simp))) hn
  | none =>
    cases h2 : b.lookup n with
    | some _ => exact absurd (List.mem_append_right _ (hkb n (by rw [h2]; simp))) hn
    | none => rfl

/-- A store-free expression evaluates identically on related locals and any store
(Flapjack infrastructure; specialises `strong_locals_rel_I_word_exp`). -/
theorem wordExpTransfer {width : Nat} [NeZero width] {C F : Type}
    (s : WordSemStateFiniteExact width C F) (t : Spt (WordLocW width))
    (ts : HolFiniteMapExact WordStoreHOL (WordLocW width)) (e : WordLangExpHOL (BitVec width))
    (r : WordLocW width) (hn : ∀ nl, nliveStore nl e)
    (hr : ∀ k v, sptDomain (getLiveExp e) k → sptLookup k s.locals = some v →
      sptLookup k t = some v)
    (h : WordSemStateFiniteExact.wordExp s e = some r) :
    WordSemStateFiniteExact.wordExp { s with locals := t, store := ts } e = some r := by
  obtain ⟨nl, hnl⟩ := liveStoreRelSupports s.store ts
  refine strongLocalsRelIWordExp t .ln nl ts s e r ⟨h, fun k v ⟨hk, hv⟩ => hr k v ?_ hv, hnl, hn nl⟩
  rw [sptDomain_sptUnion] at hk
  exact hk.resolve_right (sptDomain_ln k)

theorem nliveStoreVar {width : Nat} [NeZero width] (nl : List WordStoreHOL) (r : Nat) :
    nliveStore nl (.var r : WordLangExpHOL (BitVec width)) := by
  rw [nliveStore] <;> first | trivial | (intros; contradiction) | simp

theorem nliveStoreConst {width : Nat} [NeZero width] (nl : List WordStoreHOL) (w : BitVec width) :
    nliveStore nl (.const w : WordLangExpHOL (BitVec width)) := by
  rw [nliveStore] <;> first | trivial | (intros; contradiction) | simp

theorem nliveStoreOp2 {width : Nat} [NeZero width] (nl : List WordStoreHOL) (b : BinOp)
    (e1 e2 : WordLangExpHOL (BitVec width)) (h1 : nliveStore nl e1) (h2 : nliveStore nl e2) :
    nliveStore nl (.op b [e1, e2]) := by
  rw [nliveStore]
  rintro ⟨e, he⟩
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at he
  rcases he with rfl | rfl <;> assumption

/-- Integer register reads of an expression of variables and constants
(Flapjack infrastructure). -/
theorem sptDomain_getLiveExp_var {width : Nat} [NeZero width] (r k : Nat) :
    sptDomain (getLiveExp (.var r : WordLangExpHOL (BitVec width))) k ↔ k = r := by
  simp [getLiveExp, sptDomain_ins, sptDomain_ln]

theorem sptDomain_getLiveExp_const {width : Nat} [NeZero width] (w : BitVec width) (k : Nat) :
    ¬ sptDomain (getLiveExp (.const w : WordLangExpHOL (BitVec width))) k := by
  simp [getLiveExp, sptDomain_ln]

theorem sptDomain_getLiveExp_op2 {width : Nat} [NeZero width] (b : BinOp)
    (e1 e2 : WordLangExpHOL (BitVec width)) (k : Nat) :
    sptDomain (getLiveExp (.op b [e1, e2])) k ↔
      sptDomain (getLiveExp e1) k ∨ sptDomain (getLiveExp e2) k := by
  simp [getLiveExp, bigUnion, sptDomain_sptUnion, sptDomain_ln]

theorem sptDomain_getLiveExp_shift {width : Nat} [NeZero width] (sh : Shift)
    (e1 e2 : WordLangExpHOL (BitVec width)) (k : Nat) :
    sptDomain (getLiveExp (.shift sh e1 e2)) k ↔
      sptDomain (getLiveExp e1) k ∨ sptDomain (getLiveExp e2) k := by
  simp [getLiveExp, sptDomain_sptUnion]

/-- `instCongr` for constants and arithmetic (Flapjack infrastructure). -/
theorem instCongrArith {width : Nat} [NeZero width] {C F : Type}
    (i : WordLangInst (BitVec width)) (hi_shape : (∃ r w, i = .const r w) ∨ ∃ op, i = .arith op)
    (s s1 : WordSemStateFiniteExact width C F) (t : Spt (WordLocW width))
    (ts : HolFiniteMapExact WordStoreHOL (WordLocW width)) (hi : inst i s = some s1)
    (hr : ∀ x v, x ∈ instReads i → sptLookup x s.locals = some v → sptLookup x t = some v) :
    InstCongrPost i s s1 t ts := by
  rcases hi_shape with ⟨r, w, rfl⟩ | ⟨op, rfl⟩
  · simp only [inst, assign, WordSemStateFiniteExact.wordExp, Option.some.injEq] at hi
    subst hi
    exact instCongrPostOne _ s t ts r _ rfl (by simp only [inst, assign, WordSemStateFiniteExact.wordExp])
  cases op with
  | binop bop r1 r2 ri =>
    cases ri with
    | reg r3 =>
      simp only [inst, assign] at hi
      cases hw : WordSemStateFiniteExact.wordExp s (.op bop [.var r2, .var r3]) with
      | none => rw [hw] at hi; cases hi
      | some w =>
        rw [hw] at hi; simp only [Option.some.injEq] at hi; subst hi
        refine instCongrPostOne _ s t ts r1 w rfl ?_
        have hw' := wordExpTransfer s t ts _ w
          (fun nl => nliveStoreOp2 nl bop _ _ (nliveStoreVar nl r2) (nliveStoreVar nl r3))
          (fun k v hk hv => hr k v (by
            rw [sptDomain_getLiveExp_op2, sptDomain_getLiveExp_var, sptDomain_getLiveExp_var]
              at hk
            simpa [instReads] using hk) hv) hw
        simp only [inst, assign, hw']
    | imm c =>
      simp only [inst, assign] at hi
      cases hw : WordSemStateFiniteExact.wordExp s (.op bop [.var r2, .const c]) with
      | none => rw [hw] at hi; cases hi
      | some w =>
        rw [hw] at hi; simp only [Option.some.injEq] at hi; subst hi
        refine instCongrPostOne _ s t ts r1 w rfl ?_
        have hw' := wordExpTransfer s t ts _ w
          (fun nl => nliveStoreOp2 nl bop _ _ (nliveStoreVar nl r2) (nliveStoreConst nl c))
          (fun k v hk hv => hr k v (by
            rw [sptDomain_getLiveExp_op2, sptDomain_getLiveExp_var] at hk
            rcases hk with hk | hk
            · simpa [instReads] using hk
            · exact absurd hk (sptDomain_getLiveExp_const c k)) hv) hw
        simp only [inst, assign, hw']
  | shift sh r1 r2 ri =>
    cases ri with
    | reg r3 =>
      simp only [inst, assign] at hi
      cases hw : WordSemStateFiniteExact.wordExp s (.shift sh (.var r2) (.var r3)) with
      | none => rw [hw] at hi; cases hi
      | some w =>
        rw [hw] at hi; simp only [Option.some.injEq] at hi; subst hi
        refine instCongrPostOne _ s t ts r1 w rfl ?_
        have hw' := wordExpTransfer s t ts _ w
          (fun nl => by rw [nliveStore]; exact ⟨nliveStoreVar nl r2, nliveStoreVar nl r3⟩)
          (fun k v hk hv => hr k v (by
            rw [sptDomain_getLiveExp_shift, sptDomain_getLiveExp_var, sptDomain_getLiveExp_var]
              at hk
            simpa [instReads] using hk) hv) hw
        simp only [inst, assign, hw']
    | imm c =>
      simp only [inst, assign] at hi
      cases hw : WordSemStateFiniteExact.wordExp s (.shift sh (.var r2) (.const c)) with
      | none => rw [hw] at hi; cases hi
      | some w =>
        rw [hw] at hi; simp only [Option.some.injEq] at hi; subst hi
        refine instCongrPostOne _ s t ts r1 w rfl ?_
        have hw' := wordExpTransfer s t ts _ w
          (fun nl => by rw [nliveStore]; exact ⟨nliveStoreVar nl r2, nliveStoreConst nl c⟩)
          (fun k v hk hv => hr k v (by
            rw [sptDomain_getLiveExp_shift, sptDomain_getLiveExp_var] at hk
            rcases hk with hk | hk
            · simpa [instReads] using hk
            · exact absurd hk (sptDomain_getLiveExp_const c k)) hv) hw
        simp only [inst, assign, hw']
  | div r1 r2 r3 =>
    simp only [inst] at hi
    split at hi
    · rename_i q w2 hgv
      split at hi
      · rename_i hq
        simp only [Option.some.injEq] at hi; subst hi
        refine instCongrPostOne _ s t ts r1 _ rfl ?_
        simp only [inst, getVarsTransfer s t ts [r3, r2] _ hr hgv]
        rw [if_pos hq]
      · cases hi
    · cases hi
  | addCarry r1 r2 r3 r4 =>
    simp only [inst] at hi
    split at hi
    · rename_i l r c hgv
      generalize hac : wordAddCarryHOL l r c = p at hi
      obtain ⟨res, co⟩ := p
      simp only [Option.some.injEq] at hi; subst hi
      refine instCongrPostTwo _ s t ts r1 r4 _ _ (fun k => by simp [instWrites]) ?_
      simp only [inst, getVarsTransfer s t ts [r2, r3, r4] _ hr hgv, hac]
    · cases hi
  | addOverflow r1 r2 r3 r4 =>
    simp only [inst] at hi
    split at hi
    · rename_i w2 w3 hgv
      simp only [Option.some.injEq] at hi; subst hi
      refine instCongrPostTwo _ s t ts r1 r4 _ _ (fun k => by simp [instWrites]) ?_
      simp only [inst, getVarsTransfer s t ts [r2, r3] _ hr hgv]
    · cases hi
  | subOverflow r1 r2 r3 r4 =>
    simp only [inst] at hi
    split at hi
    · rename_i w2 w3 hgv
      simp only [Option.some.injEq] at hi; subst hi
      refine instCongrPostTwo _ s t ts r1 r4 _ _ (fun k => by simp [instWrites]) ?_
      simp only [inst, getVarsTransfer s t ts [r2, r3] _ hr hgv]
    · cases hi
  | longMul r1 r2 r3 r4 =>
    simp only [inst] at hi
    split at hi
    · rename_i w3 w4 hgv
      simp only [Option.some.injEq] at hi; subst hi
      refine instCongrPostTwo _ s t ts r1 r2 _ _ (fun k => by simp [instWrites]) ?_
      simp only [inst, getVarsTransfer s t ts [r3, r4] _ hr hgv]
    · cases hi
  | longDiv r1 r2 r3 r4 r5 =>
    simp only [inst] at hi
    split at hi
    · rename_i w3 w4 w5 hgv
      split at hi
      · rename_i hq
        simp only [Option.some.injEq] at hi; subst hi
        refine instCongrPostTwo _ s t ts r2 r1 _ _ (fun k => by simp [instWrites, or_comm]) ?_
        simp only [inst, getVarsTransfer s t ts [r3, r4, r5] _ hr hgv]
        rw [if_pos hq]
      · cases hi
    · cases hi

/-- `mem_store` touches only the memory (Flapjack infrastructure). -/
theorem memStoreTransfer {width : Nat} [NeZero width] {C F : Type}
    (s s1 : WordSemStateFiniteExact width C F) (t : Spt (WordLocW width))
    (ts : HolFiniteMapExact WordStoreHOL (WordLocW width)) (a : BitVec width) (v : WordLocW width)
    (h : memStore a v s = some s1) :
    s1.locals = s.locals ∧ s1.store = s.store ∧
      memStore a v { s with locals := t, store := ts } = some { s1 with locals := t, store := ts } := by
  unfold memStore at h ⊢
  split at h
  · rename_i hd
    simp only [Option.some.injEq] at h
    subst h
    refine ⟨rfl, rfl, ?_⟩
    rw [if_pos (show ({ s with locals := t, store := ts } : WordSemStateFiniteExact width C F).mdomain a
      from hd)]
  · cases h

/-- The address of a memory instruction transfers (Flapjack infrastructure). -/
theorem memAddrTransfer {width : Nat} [NeZero width] {C F : Type}
    (s : WordSemStateFiniteExact width C F) (t : Spt (WordLocW width))
    (ts : HolFiniteMapExact WordStoreHOL (WordLocW width)) (a : Nat) (w : BitVec width)
    (r : WordLocW width)
    (hr : ∀ v, sptLookup a s.locals = some v → sptLookup a t = some v)
    (h : WordSemStateFiniteExact.wordExp s (.op .add [.var a, .const w]) = some r) :
    WordSemStateFiniteExact.wordExp { s with locals := t, store := ts }
      (.op .add [.var a, .const w]) = some r :=
  wordExpTransfer s t ts _ r
    (fun nl => nliveStoreOp2 nl .add _ _ (nliveStoreVar nl a) (nliveStoreConst nl w))
    (fun k v hk hv => by
      rw [sptDomain_getLiveExp_op2, sptDomain_getLiveExp_var] at hk
      rcases hk with rfl | hk
      · exact hr v hv
      · exact absurd hk (sptDomain_getLiveExp_const w k)) h

/-- `instCongr` for memory instructions (Flapjack infrastructure). -/
theorem instCongrMem {width : Nat} [NeZero width] {C F : Type}
    (op : WordMemOp) (r a : Nat) (w : BitVec width)
    (s s1 : WordSemStateFiniteExact width C F) (t : Spt (WordLocW width))
    (ts : HolFiniteMapExact WordStoreHOL (WordLocW width)) (hi : inst (.mem op r (.addr a w)) s = some s1)
    (hr : ∀ x v, x ∈ instReads (.mem op r (.addr a w) : WordLangInst (BitVec width)) →
      sptLookup x s.locals = some v → sptLookup x t = some v) :
    InstCongrPost (.mem op r (.addr a w)) s s1 t ts := by
  cases op with
  | load =>
    have ha : ∀ v, sptLookup a s.locals = some v → sptLookup a t = some v := fun v =>
      hr a v (by simp [instReads])
    simp only [inst] at hi
    split at hi
    · rename_i ad hwe
      split at hi
      · cases hi
      · rename_i v hm
        simp only [Option.some.injEq] at hi; subst hi
        refine instCongrPostOne _ s t ts r v rfl ?_
        have hm' : memLoad ad ({ s with locals := t, store := ts } :
            WordSemStateFiniteExact width C F) = some v := hm
        simp only [inst, memAddrTransfer s t ts a w _ ha hwe, hm']
    · cases hi
  | load8 =>
    have ha : ∀ v, sptLookup a s.locals = some v → sptLookup a t = some v := fun v =>
      hr a v (by simp [instReads])
    simp only [inst] at hi
    split at hi
    · rename_i ad hwe
      split at hi
      · cases hi
      · rename_i v hm
        simp only [Option.some.injEq] at hi; subst hi
        refine instCongrPostOne _ s t ts r _ rfl ?_
        simp only [inst, memAddrTransfer s t ts a w _ ha hwe, hm]
    · cases hi
  | load16 => simp [inst] at hi
  | load32 =>
    have ha : ∀ v, sptLookup a s.locals = some v → sptLookup a t = some v := fun v =>
      hr a v (by simp [instReads])
    simp only [inst] at hi
    split at hi
    · rename_i ad hwe
      split at hi
      · cases hi
      · rename_i v hm
        simp only [Option.some.injEq] at hi; subst hi
        refine instCongrPostOne _ s t ts r _ rfl ?_
        simp only [inst, memAddrTransfer s t ts a w _ ha hwe, hm]
    · cases hi
  | store =>
    have ha : ∀ v, sptLookup a s.locals = some v → sptLookup a t = some v := fun v =>
      hr a v (by simp [instReads])
    simp only [inst] at hi
    split at hi
    · rename_i ad v hwe hv
      split at hi
      · rename_i s1' hm
        simp only [Option.some.injEq] at hi; subst hi
        obtain ⟨hl, hst, hm'⟩ := memStoreTransfer s _ t ts ad v hm
        refine instCongrPostZero _ s _ t ts rfl hl hst ?_
        have hv' : WordSemStateFiniteExact.getVar r ({ s with locals := t, store := ts } :
            WordSemStateFiniteExact width C F) = some v := hr r v (by simp [instReads]) hv
        simp only [inst, memAddrTransfer s t ts a w _ ha hwe, hv', hm']
      · cases hi
    · cases hi
  | store8 =>
    have ha : ∀ v, sptLookup a s.locals = some v → sptLookup a t = some v := fun v =>
      hr a v (by simp [instReads])
    simp only [inst] at hi
    split at hi
    · rename_i ad v hwe hv
      split at hi
      · rename_i m hm
        simp only [Option.some.injEq] at hi; subst hi
        refine instCongrPostZero _ s _ t ts rfl rfl rfl ?_
        have hv' : WordSemStateFiniteExact.getVar r ({ s with locals := t, store := ts } :
            WordSemStateFiniteExact width C F) = some (.word v) := hr r _ (by simp [instReads]) hv
        simp only [inst, memAddrTransfer s t ts a w _ ha hwe, hv', hm]
      · cases hi
    · cases hi
  | store16 => simp [inst] at hi
  | store32 =>
    have ha : ∀ v, sptLookup a s.locals = some v → sptLookup a t = some v := fun v =>
      hr a v (by simp [instReads])
    simp only [inst] at hi
    split at hi
    · rename_i ad v hwe hv
      split at hi
      · rename_i m hm
        simp only [Option.some.injEq] at hi; subst hi
        refine instCongrPostZero _ s _ t ts rfl rfl rfl ?_
        have hv' : WordSemStateFiniteExact.getVar r ({ s with locals := t, store := ts } :
            WordSemStateFiniteExact width C F) = some (.word v) := hr r _ (by simp [instReads]) hv
        simp only [inst, memAddrTransfer s t ts a w _ ha hwe, hv', hm]
      · cases hi
    · cases hi

theorem getFpVarWith {width : Nat} [NeZero width] {C F : Type} (d : Nat)
    (s : WordSemStateFiniteExact width C F) (t : Spt (WordLocW width))
    (ts : HolFiniteMapExact WordStoreHOL (WordLocW width)) :
    getFpVar d { s with locals := t, store := ts } = getFpVar d s := rfl

/-- An instruction runs on related locals and any store with the source effect on
the written registers (Flapjack infrastructure for HOL's per-instruction
`strong_locals_rel_I_get_var`/`_insert_insert` reasoning). -/
theorem instCongr {width : Nat} [NeZero width] {C F : Type} (i : WordLangInst (BitVec width))
    (s s1 : WordSemStateFiniteExact width C F) (t : Spt (WordLocW width))
    (ts : HolFiniteMapExact WordStoreHOL (WordLocW width)) (hi : inst i s = some s1)
    (hr : ∀ x v, x ∈ instReads i → sptLookup x s.locals = some v → sptLookup x t = some v) :
    InstCongrPost i s s1 t ts := by
  cases i with
  | skip =>
    simp only [inst, Option.some.injEq] at hi; subst hi
    exact instCongrPostZero _ s s t ts rfl rfl rfl rfl
  | const r w => exact instCongrArith _ (Or.inl ⟨r, w, rfl⟩) s s1 t ts hi hr
  | arith op => exact instCongrArith _ (Or.inr ⟨op, rfl⟩) s s1 t ts hi hr
  | mem op r address =>
    cases address with
    | addr a w => exact instCongrMem op r a w s s1 t ts hi hr
/-- A removable instruction changes only the locals (Flapjack infrastructure). -/
theorem instRemovedFrame {width : Nat} [NeZero width] {C F : Type}
    (i : WordLangInst (BitVec width)) (live : NumSet) (s s1 : WordSemStateFiniteExact width C F)
    (hrm : removeDeadInst i live = true) (hi : inst i s = some s1) :
    s1 = { s with locals := s1.locals } := by
  cases i with
  | skip => simp only [inst, Option.some.injEq] at hi; subst hi; rfl
  | const r w =>
    simp only [inst, assign, WordSemStateFiniteExact.wordExp, Option.some.injEq] at hi
    subst hi; rfl
  | arith op =>
    cases op
    all_goals (try rename_i ri; try cases ri)
    all_goals simp only [inst, assign] at hi
    all_goals (repeat' split at hi)
    all_goals first
      | (cases hi; done)
      | (simp only [Option.some.injEq] at hi; subst hi; rfl)
  | mem op r address =>
    cases address
    cases op
    all_goals simp [removeDeadInst, removeDeadInstCore] at hrm
    all_goals simp only [inst] at hi
    all_goals (repeat' split at hi)
    all_goals first
      | (cases hi; done)
      | (simp only [Option.some.injEq] at hi; subst hi; rfl)
/-- HOL `evaluate_remove_dead`, `Inst` case (Resume 4031). -/
theorem evaluateRemoveDead_Inst {width : Nat} [NeZero width] {C F : Type}
    (i : WordLangInst (BitVec width)) :
    removeDeadGoal C F (.inst i : WordLangProgHOL (BitVec width)) := by
  rintro live nlive lt prog' livein nlivein st t tstore res rst ⟨hl, hs, hev, -, hrd, herr⟩
  rw [evaluate] at hev
  cases hi : inst i st with
  | none => rw [hi] at hev; simp only [Prod.mk.injEq] at hev; exact absurd hev.1.symm herr
  | some s1 =>
    rw [hi] at hev
    simp only [Prod.mk.injEq] at hev
    obtain ⟨rfl, rfl⟩ := hev
    simp only [removeDead] at hrd
    split at hrd
    · rename_i hrm
      simp only [Prod.mk.injEq] at hrd
      obtain ⟨rfl, rfl, rfl⟩ := hrd
      have hfr := instRemovedFrame i live st s1 hrm hi
      have hwd := removeDeadInst_writes i live hrm
      obtain ⟨_, _, hframe, -, hstore⟩ := instCongr i st s1 st.locals st.store hi
        (fun _ _ _ h => h)
      refine ⟨t, tstore, ?_, ?_, ?_⟩
      · rw [evaluate, hfr]
      · intro k v ⟨hk, hv⟩
        have hkw : k ∉ instWrites i := fun h => hwd k h hk
        rw [(hframe k hkw).1] at hv
        exact hl k v ⟨hk, hv⟩
      · rw [hstore]; exact hs
    · simp only [Prod.mk.injEq] at hrd
      obtain ⟨rfl, rfl, rfl⟩ := hrd
      obtain ⟨t', heq, hframe, hwr, hstore⟩ := instCongr i st s1 t tstore hi
        (fun x v hx hv => hl x v ⟨getLiveInst_reads i live x hx, hv⟩)
      refine ⟨t', tstore, ?_, ?_, ?_⟩
      · rw [evaluate, heq]
      · intro k v ⟨hk, hv⟩
        by_cases hkw : k ∈ instWrites i
        · simp only [id]; rw [hwr k hkw]; exact hv
        · obtain ⟨h1, h2⟩ := hframe k hkw
          rw [h1] at hv
          simp only [id]; rw [h2]
          exact hl k v ⟨getLiveInst_frame i live k hk hkw, hv⟩
      · rw [hstore]; exact hs

end Flapjack.WordAlloc
