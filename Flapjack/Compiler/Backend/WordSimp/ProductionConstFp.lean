import Flapjack.Compiler.Backend.WordSimp.ProductionSeqAssoc
import Flapjack.Misc.SptreeLookup
import Flapjack.Pancake.LoopToWord.LoopProgCarrierCodec

/-! Executed `wordConstFpLoop` against the reviewed native `constFpLoop`.
Flapjack carrier infrastructure with no HOL original: the executed pass keeps
its knowledge in an association list, the native pass in an `Spt`. The
relation `ConstRel` says the list has distinct keys and the same lookups. From
an encoded input and related knowledge, the executed output encodes to the
native output and the final knowledge stays related. Only input encoding is
assumed; no output encoding or evaluation result is. -/
namespace Flapjack.Compiler.Backend.WordSimp

open RiscV

/-- Executed constant knowledge represents native knowledge: distinct keys and
equal lookups. Flapjack carrier relation, no HOL original. -/
def ConstRel {width : Nat} (m : NatInfoMap (BitVec width)) (s : Spt (BitVec width)) : Prop :=
  (m.map Prod.fst).Nodup ∧ ∀ k, lookupNatInfo k m = sptLookup k s

private theorem lookup_none_of_not_mem {α : Type} (k : Nat) :
    ∀ m : NatInfoMap α, k ∉ m.map Prod.fst → lookupNatInfo k m = none
  | [] , _ => rfl
  | (c, v) :: rest, h => by
      simp only [List.map_cons, List.mem_cons, not_or] at h
      have hne : (c == k) = false := by simpa using Ne.symm h.1
      simp only [lookupNatInfo, hne]
      exact lookup_none_of_not_mem k rest h.2

private theorem lookup_filter {α : Type} (k : Nat) (p : Nat × α → Bool) :
    ∀ m : NatInfoMap α, (m.map Prod.fst).Nodup →
      lookupNatInfo k (m.filter p) =
        match lookupNatInfo k m with
        | some v => if p (k, v) then some v else none
        | none => none
  | [], _ => rfl
  | (c, v) :: rest, nodup => by
      simp only [List.map_cons, List.nodup_cons] at nodup
      have ih := lookup_filter k p rest nodup.2
      by_cases hck : c = k
      · subst hck
        have hrest : lookupNatInfo c (rest.filter p) = none :=
          lookup_none_of_not_mem c _ (fun hm => nodup.1 (by
            simp only [List.mem_map] at hm ⊢
            obtain ⟨e, he, rfl⟩ := hm
            exact ⟨e, (List.mem_filter.mp he).1, rfl⟩))
        by_cases hp : p (c, v) <;> simp [List.filter, hp, lookupNatInfo, hrest]
      · have hne : (c == k) = false := by simpa using hck
        by_cases hp : p (c, v) <;> simp [List.filter, hp, lookupNatInfo, hne, ih]

private theorem nodup_filter {α : Type} (p : Nat × α → Bool) (m : NatInfoMap α)
    (nodup : (m.map Prod.fst).Nodup) : ((m.filter p).map Prod.fst).Nodup :=
  (List.Sublist.map _ (List.filter_sublist)).nodup nodup

theorem lookup_mapDelete {width : Nat} (m : NatInfoMap (BitVec width)) (n k : Nat)
    (nodup : (m.map Prod.fst).Nodup) :
    lookupNatInfo k (wordSimpMapDelete m n) = if k = n then none else lookupNatInfo k m := by
  unfold wordSimpMapDelete
  rw [lookup_filter k _ m nodup]
  by_cases h : k = n
  · subst h; cases lookupNatInfo k m <;> simp
  · cases lookupNatInfo k m <;> simp [h]

theorem constRel_delete {width : Nat} {m : NatInfoMap (BitVec width)} {s : Spt (BitVec width)}
    (rel : ConstRel m s) (n : Nat) : ConstRel (wordSimpMapDelete m n) (sptDelete n s) := by
  refine ⟨nodup_filter _ _ rel.1, fun k => ?_⟩
  rw [lookup_mapDelete m n k rel.1, sptLookup_sptDelete, rel.2 k]

theorem constRel_insert {width : Nat} {m : NatInfoMap (BitVec width)} {s : Spt (BitVec width)}
    (rel : ConstRel m s) (n : Nat) (v : BitVec width) :
    ConstRel (wordSimpMapInsert m n v) (sptInsert n v s) := by
  have del := constRel_delete rel n
  refine ⟨?_, fun k => ?_⟩
  · simp only [wordSimpMapInsert, List.map_cons, List.nodup_cons]
    refine ⟨fun hm => ?_, del.1⟩
    simp only [List.mem_map, List.mem_filter] at hm
    obtain ⟨e, ⟨_, hne⟩, rfl⟩ := hm
    simp at hne
  · by_cases h : k = n
    · subst h
      simp [wordSimpMapInsert, lookupNatInfo, sptLookup_sptInsert_same]
    · have hne : (n == k) = false := by simpa using Ne.symm h
      simp only [wordSimpMapInsert, lookupNatInfo, hne]
      rw [show (List.filter (fun entry => entry.1 != n) m) = wordSimpMapDelete m n from rfl,
        del.2 k, sptLookup_sptDelete, if_neg h, sptLookup_sptInsert_ne n k v s h]
      rfl

theorem constRel_empty {width : Nat} : ConstRel ([] : NatInfoMap (BitVec width)) .ln :=
  ⟨List.nodup_nil, fun k => by simp [lookupNatInfo]⟩

theorem constRel_congr {width : Nat} {m : NatInfoMap (BitVec width)} {s s' : Spt (BitVec width)}
    (rel : ConstRel m s) (same : ∀ k, sptLookup k s = sptLookup k s') : ConstRel m s' :=
  ⟨rel.1, fun k => (rel.2 k).trans (same k)⟩

private theorem sptLookup_deleteAll {width : Nat} (k : Nat) :
    ∀ (names : List Nat) (s : Spt (BitVec width)),
      sptLookup k (deleteAll names s) = if k ∈ names then none else sptLookup k s
  | [], s => by simp [deleteAll]
  | n :: ns, s => by
      have ih := sptLookup_deleteAll k ns s
      simp only [deleteAll, List.foldr_cons] at ih ⊢
      rw [sptLookup_sptDelete, ih]
      by_cases h : k = n <;> simp [h]

theorem constRel_deleteAll {width : Nat} :
    ∀ (names : List Nat) {m : NatInfoMap (BitVec width)} {s : Spt (BitVec width)},
      ConstRel m s → ConstRel (wordSimpMapDeleteAll m names) (deleteAll names s)
  | [], m, s, rel => by simpa [wordSimpMapDeleteAll, deleteAll] using rel
  | n :: ns, m, s, rel => by
      have ih := constRel_deleteAll ns (constRel_delete rel n)
      simp only [wordSimpMapDeleteAll, List.foldl_cons] at ih ⊢
      refine constRel_congr ih (fun k => ?_)
      rw [sptLookup_deleteAll, sptLookup_deleteAll, sptLookup_sptDelete]
      by_cases h : k = n <;> by_cases h' : k ∈ ns <;> simp [h, h']

theorem constRel_filterGc {width : Nat} [NeZero width] {m : NatInfoMap (BitVec width)}
    {s : Spt (BitVec width)} (rel : ConstRel m s) :
    ConstRel (wordSimpMapFilterGc m) (sptFilterV isGcConst s) := by
  refine ⟨nodup_filter _ _ rel.1, fun k => ?_⟩
  unfold wordSimpMapFilterGc
  rw [lookup_filter k _ m rel.1, sptLookupFilterV, rel.2 k]
  cases sptLookup k s <;> simp [isGcConst]

private theorem sptLookup_allNames_cutsets (k : Nat) (sets : List Nat × List Nat) :
    (sptLookup k (allNames (wordCutsetsToHOL sets))).isSome = (sets.1 ++ sets.2).contains k := by
  have h1 := sptLookup_toNumSetHOL_iff_mem k sets.1
  have h2 := sptLookup_toNumSetHOL_iff_mem k sets.2
  simp only [allNames, wordCutsetsToHOL, sptLookup_sptUnion]
  cases a : sptLookup k (LoopToWord.toNumSetHOL sets.1) with
  | some u =>
    cases u
    have : k ∈ sets.1 := h1.mp a
    simp [this]
  | none =>
    have n1 : k ∉ sets.1 := fun hm => by simp [h1.mpr hm] at a
    cases b : sptLookup k (LoopToWord.toNumSetHOL sets.2) with
    | some u =>
      cases u
      have : k ∈ sets.2 := h2.mp b
      simp [this]
    | none =>
      have n2 : k ∉ sets.2 := fun hm => by simp [h2.mpr hm] at b
      simp [n1, n2]

theorem constRel_inter {width : Nat} {m : NatInfoMap (BitVec width)} {s : Spt (BitVec width)}
    (rel : ConstRel m s) (sets : List Nat × List Nat) :
    ConstRel (wordSimpMapInter m (sets.1 ++ sets.2))
      (sptInter s (allNames (wordCutsetsToHOL sets))) := by
  refine ⟨nodup_filter _ _ rel.1, fun k => ?_⟩
  unfold wordSimpMapInter
  rw [lookup_filter k _ m rel.1, sptLookup_sptInterCases, rel.2 k]
  have key := sptLookup_allNames_cutsets k sets
  cases sptLookup k s <;>
    cases hn : sptLookup k (allNames (wordCutsetsToHOL sets)) <;> simp_all

theorem constRel_interEq {width : Nat} {m1 m2 : NatInfoMap (BitVec width)}
    {s1 s2 : Spt (BitVec width)} (rel1 : ConstRel m1 s1) (rel2 : ConstRel m2 s2) :
    ConstRel (wordSimpMapInterEq m1 m2) (sptInterEq s1 s2) := by
  refine ⟨nodup_filter _ _ rel1.1, fun k => ?_⟩
  unfold wordSimpMapInterEq
  rw [lookup_filter k _ m1 rel1.1, sptLookupInterEq, rel1.2 k]
  cases sptLookup k s1 <;> simp [rel2.2 k]

theorem constRel_moves {width : Nat} [NeZero width] (orig : NatInfoMap (BitVec width))
    (origSpt : Spt (BitVec width)) (origRel : ConstRel orig origSpt) :
    ∀ (moves : List (Nat × Nat)) {m : NatInfoMap (BitVec width)} {s : Spt (BitVec width)},
      ConstRel m s → ConstRel (wordSimpMoveConstants moves orig m) (constFpMoveCs moves origSpt s)
  | [], m, s, rel => by simpa [wordSimpMoveConstants, constFpMoveCs] using rel
  | mv :: rest, m, s, rel => by
      simp only [wordSimpMoveConstants, List.foldl_cons, constFpMoveCs]
      rw [origRel.2 mv.2]
      cases sptLookup mv.2 origSpt with
      | some c => exact constRel_moves orig origSpt origRel rest (constRel_insert rel mv.1 c)
      | none => exact constRel_moves orig origSpt origRel rest (constRel_delete rel mv.1)

theorem constRel_inst {width : Nat} [NeZero width] {m : NatInfoMap (BitVec width)}
    {s : Spt (BitVec width)} (rel : ConstRel m s) (inst : WordInst (BitVec width))
    (native : WordLangInst (BitVec width)) (encoded : wordLangInstToHOL inst = some native) :
    ConstRel (wordSimpInstConstants m inst) (constFpInstCs native s) := by
  cases inst with
  | const d v =>
    simp only [wordLangInstToHOL, Option.some.injEq] at encoded; subst encoded
    exact constRel_delete rel d
  | arith a =>
    cases a <;> simp [wordLangInstToHOL, wordLangArithToHOL] at encoded <;> subst encoded <;>
      simp only [wordSimpInstConstants, constFpInstCs]
    all_goals first
      | exact constRel_delete rel _
      | exact constRel_delete (constRel_delete rel _) _
      | refine constRel_congr (constRel_delete (constRel_delete rel _) _) (fun k => ?_)
        simp only [sptLookup_sptDelete]
        split <;> split <;> simp_all
  | mem op d a =>
    simp only [wordLangInstToHOL, Option.some.injEq] at encoded; subst encoded
    cases op <;> simp only [wordSimpInstConstants, constFpInstCs]
    all_goals first | exact constRel_delete rel d | exact rel
  | memOffset op d a off =>
    simp only [wordLangInstToHOL, Option.some.injEq] at encoded; subst encoded
    cases op <;> simp only [wordSimpInstConstants, constFpInstCs]
    all_goals first | exact constRel_delete rel d | exact rel

theorem getVarImm_rel {width : Nat} [NeZero width] {m : NatInfoMap (BitVec width)}
    {s : Spt (BitVec width)} (rel : ConstRel m s) (ri : WordRegImm (BitVec width)) :
    wordSimpGetVarImm m ri = getVarImmCs ri s := by
  cases ri <;> simp [wordSimpGetVarImm, getVarImmCs, rel.2]

theorem evalCmp_eq {width : Nat} [NeZero width] (op : Cmp) (l r : BitVec width) :
    wordSimpEvalCmp op l r = Flapjack.Compiler.Encoders.Asm.wordCmpHOL op l r := by
  cases op <;> rfl

theorem stripConst_production {width : Nat} [NeZero width] :
    ∀ es : List (WordExp (BitVec width)),
      stripConst (es.map wordExpToHOL) = wordSimpStripConst es
  | [] => rfl
  | e :: rest => by
      have ih := stripConst_production rest
      cases e <;> simp [stripConst, wordSimpStripConst, wordExpToHOL, ih]
      cases wordSimpStripConst rest <;> rfl

theorem shiftEval_eq {width : Nat} [NeZero width] (op : Shift) (l r : BitVec width) :
    WordSimpShift.eval op l r = wordShiftHOL op l r.toNat := by
  have pos := Nat.pos_of_ne_zero (NeZero.ne width)
  show (if r.toNat < width then _ else none) = _
  unfold wordShiftHOL
  by_cases h : r.toNat < width
  · have : ¬ (r.toNat ≠ 0 ∧ width ≤ r.toNat) := by omega
    rw [if_pos h, if_neg this]
    cases op <;> rfl
  · have : r.toNat ≠ 0 ∧ width ≤ r.toNat := by omega
    rw [if_neg h, if_pos this]

theorem constExp_production {width : Nat} [NeZero width] {m : NatInfoMap (BitVec width)}
    {s : Spt (BitVec width)} (rel : ConstRel m s) :
    ∀ e : WordExp (BitVec width),
      wordExpToHOL (wordSimpConstExp m e) = constFpExp (wordExpToHOL e) s
  | .const v => by simp [wordSimpConstExp, wordExpToHOL, constFpExp]
  | .var n => by
      simp only [wordSimpConstExp, wordExpToHOL, constFpExp, rel.2 n]
      cases sptLookup n s <;> simp [wordExpToHOL]
  | .lookup st => by simp [wordSimpConstExp, wordExpToHOL, constFpExp]
  | .load a => by simp [wordSimpConstExp, wordExpToHOL, constFpExp]
  | .op op args => by
      have ih : ∀ a ∈ args,
          wordExpToHOL (wordSimpConstExp m a) = constFpExp (wordExpToHOL a) s :=
        fun a _ => constExp_production rel a
      have args_eq : ((args.map wordExpToHOL).attach.map
            (fun x => constFpExp x.1 s)) =
          (args.map (wordSimpConstExp m)).map wordExpToHOL := by
        simp only [List.attach_map_val (f := fun x => constFpExp x s), List.map_map, Function.comp_def]
        exact List.map_congr_left (fun a h => (ih a h).symm)
      rw [wordSimpConstExp, wordExpToHOL, constFpExp]
      try dsimp only
      rw [show ((args.map wordExpToHOL).attach.map
            (fun x => match x with | ⟨a, _⟩ => constFpExp a s)) =
          (args.map wordExpToHOL).attach.map (fun x => constFpExp x.1 s) from rfl,
        args_eq, stripConst_production]
      cases wordSimpStripConst (args.map (wordSimpConstExp m)) with
      | none => simp [wordExpToHOL]
      | some values =>
        simp only [wordSimpFoldOp, wordOpHOL]
        cases wordOp op values <;> simp [wordExpToHOL, Function.comp_def]
  | .shift op l r => by
      have il := constExp_production rel l
      have ir := constExp_production rel r
      rw [wordSimpConstExp, wordExpToHOL, constFpExp]
      try dsimp only
      rw [← il, ← ir]
      cases hl : wordSimpConstExp m l <;> cases hr : wordSimpConstExp m r <;>
        simp [wordExpToHOL, shiftEval_eq] <;> split <;> simp_all [wordExpToHOL]
termination_by e => sizeOf e
decreasing_by
  all_goals simp_wf
  all_goals first
    | (have := List.sizeOf_lt_of_mem ‹_ ∈ args›; omega)
    | omega

theorem dropConsts_production {width : Nat} [NeZero width] {m : NatInfoMap (BitVec width)}
    {s : Spt (BitVec width)} (rel : ConstRel m s) :
    ∀ names : List Nat,
      wordLangProgToHOL (wordSimpDropConsts m names) = some (dropConsts s names)
  | [] => by simp [wordSimpDropConsts, dropConsts, wordLangProgToHOL]
  | n :: ns => by
      have ih := dropConsts_production rel ns
      simp only [wordSimpDropConsts, dropConsts, rel.2 n]
      cases sptLookup n s with
      | none => exact ih
      | some w =>
        exact smartSeq_production _ _ _ _ ih (by simp [wordLangProgToHOL, wordExpToHOL])

/-- Executed constant propagation encodes to native `constFpLoop` and keeps
the knowledge relation, for every encoded input and related knowledge.
Flapjack carrier correspondence; no HOL original. -/
theorem constFpLoop_production {width : Nat} [NeZero width] :
    ∀ (p : WordProg (BitVec width)) (native : WordLangProgHOL (BitVec width))
      (m : NatInfoMap (BitVec width)) (s : Spt (BitVec width)),
      wordLangProgToHOL p = some native → ConstRel m s →
      wordLangProgToHOL (wordConstFpLoop p m).1 = some (constFpLoop native s).1 ∧
        ConstRel (wordConstFpLoop p m).2 (constFpLoop native s).2
  | .skip, native, m, s, encoded, rel => by
      simp only [wordLangProgToHOL, Option.some.injEq] at encoded; subst encoded
      unfold wordConstFpLoop constFpLoop
      exact ⟨rfl, rel⟩
  | .move pri moves, native, m, s, encoded, rel => by
      simp only [wordLangProgToHOL, Option.some.injEq] at encoded; subst encoded
      unfold wordConstFpLoop constFpLoop
      exact ⟨rfl, constRel_moves m s rel moves rel⟩
  | .assign n e, native, m, s, encoded, rel => by
      simp only [wordLangProgToHOL, Option.some.injEq] at encoded; subst encoded
      unfold wordConstFpLoop constFpLoop
      have he := constExp_production rel e
      rw [← he]
      cases hc : wordSimpConstExp m e <;>
        simp [wordLangProgToHOL, wordExpToHOL, constRel_delete rel, constRel_insert rel]
  | .inst i, native, m, s, encoded, rel => by
      simp only [wordLangProgToHOL, Option.map_eq_some_iff] at encoded
      obtain ⟨ni, hi, rfl⟩ := encoded
      unfold wordConstFpLoop constFpLoop
      exact ⟨by simp [wordLangProgToHOL, hi], constRel_inst rel i ni hi⟩
  | .get d st, native, m, s, encoded, rel => by
      simp only [wordLangProgToHOL, Option.some.injEq] at encoded; subst encoded
      unfold wordConstFpLoop constFpLoop
      exact ⟨rfl, constRel_delete rel d⟩
  | .set st e, native, m, s, encoded, rel => by
      simp only [wordLangProgToHOL, Option.some.injEq] at encoded; subst encoded
      unfold wordConstFpLoop constFpLoop
      exact ⟨rfl, rel⟩
  | .store a v, native, m, s, encoded, rel => by
      simp only [wordLangProgToHOL, Option.some.injEq] at encoded; subst encoded
      unfold wordConstFpLoop constFpLoop
      exact ⟨by simp [wordLangProgToHOL, constExp_production rel a], rel⟩
  | .mustTerminate body, native, m, s, encoded, rel => by
      simp only [wordLangProgToHOL, Option.map_eq_some_iff] at encoded
      obtain ⟨nb, hb, rfl⟩ := encoded
      have ih := constFpLoop_production body nb m s hb rel
      unfold wordConstFpLoop constFpLoop
      exact ⟨by simp [wordLangProgToHOL, ih.1], ih.2⟩
  | .seq a b, native, m, s, encoded, rel => by
      simp only [wordLangProgToHOL, Option.bind_eq_bind, Option.bind_eq_some_iff,
        Option.pure_def, Option.some.injEq] at encoded
      obtain ⟨na, ha, nb, hb, rfl⟩ := encoded
      have ia := constFpLoop_production a na m s ha rel
      have ib := constFpLoop_production b nb _ _ hb ia.2
      unfold wordConstFpLoop constFpLoop
      exact ⟨by simp [wordLangProgToHOL, ia.1, ib.1], ib.2⟩
  | .ite op c r a b, native, m, s, encoded, rel => by
      simp only [wordLangProgToHOL, Option.bind_eq_bind, Option.bind_eq_some_iff,
        Option.pure_def, Option.some.injEq] at encoded
      obtain ⟨na, ha, nb, hb, rfl⟩ := encoded
      have ia := constFpLoop_production a na m s ha rel
      have ib := constFpLoop_production b nb m s hb rel
      unfold wordConstFpLoop constFpLoop
      rw [rel.2 c, getVarImm_rel rel r]
      cases sptLookup c s <;> cases getVarImmCs r s
      all_goals try exact ⟨by simp [wordLangProgToHOL, ia.1, ib.1], constRel_interEq ia.2 ib.2⟩
      dsimp only
      rw [evalCmp_eq]
      split
      · exact ia
      · exact ib
  | .loop li body lo, native, m, s, encoded, rel => by
      simp only [wordLangProgToHOL, Option.bind_eq_bind, Option.bind_eq_some_iff,
        Option.pure_def, Option.some.injEq] at encoded
      obtain ⟨nb, hb, rfl⟩ := encoded
      have ib := constFpLoop_production body nb [] .ln hb constRel_empty
      unfold wordConstFpLoop constFpLoop
      exact ⟨by simp [wordLangProgToHOL, ib.1], constRel_empty⟩
  | .call none tgt args none, native, m, s, encoded, rel => by
      have hcall := encoded
      simp [wordLangProgToHOL] at encoded; subst encoded
      unfold wordConstFpLoop constFpLoop
      exact ⟨smartSeq_production _ _ _ _ (dropConsts_production rel _) hcall,
        constRel_filterGc rel⟩
  | .call none tgt args (some (exn, hb, h1, h2)), native, m, s, encoded, rel => by
      have hcall := encoded
      cases hh : wordLangProgToHOL hb <;> simp [wordLangProgToHOL, hh] at encoded
      subst encoded
      unfold wordConstFpLoop constFpLoop
      exact ⟨smartSeq_production _ _ _ _ (dropConsts_production rel _) hcall,
        constRel_filterGc rel⟩
  | .call (some (names, sets, body, l1, l2)) tgt args (some (exn, hb, h1, h2)),
      native, m, s, encoded, rel => by
      have hcall := encoded
      cases hbd : wordLangProgToHOL body <;> cases hh : wordLangProgToHOL hb <;>
        simp [wordLangProgToHOL, hbd, hh] at encoded
      subst encoded
      unfold wordConstFpLoop constFpLoop
      exact ⟨smartSeq_production _ _ _ _ (dropConsts_production rel _) hcall, constRel_empty⟩
  | .call (some (names, sets, body, l1, l2)) tgt args none, native, m, s, encoded, rel => by
      cases hbd : wordLangProgToHOL body with
      | none => simp [wordLangProgToHOL, hbd] at encoded
      | some nbody =>
      simp [wordLangProgToHOL, hbd] at encoded
      subst encoded
      have restrict : ConstRel
          (wordSimpMapDeleteAll (wordSimpMapFilterGc (wordSimpMapInter m (sets.1 ++ sets.2))) names)
          (deleteAll names (sptFilterV isGcConst (sptInter s (allNames (wordCutsetsToHOL sets))))) :=
        constRel_deleteAll names (constRel_filterGc (constRel_inter rel sets))
      have ib := constFpLoop_production body nbody _ _ hbd restrict
      unfold wordConstFpLoop constFpLoop
      refine ⟨smartSeq_production _ _ _ _ (dropConsts_production rel _) ?_, ib.2⟩
      simp [wordLangProgToHOL, ib.1]
  | .alloc d sets, native, m, s, encoded, rel => by
      simp only [wordLangProgToHOL, Option.some.injEq] at encoded; subst encoded
      unfold wordConstFpLoop constFpLoop
      exact ⟨smartSeq_production _ _ _ _ (dropConsts_production rel _) rfl,
        constRel_filterGc (constRel_inter rel sets)⟩
  | .storeConsts a b c d ws, native, m, s, encoded, rel => by
      simp only [wordLangProgToHOL, Option.some.injEq] at encoded; subst encoded
      unfold wordConstFpLoop constFpLoop
      exact ⟨rfl, constRel_deleteAll [a, b, c, d] rel⟩
  | .raise _, native, m, s, encoded, rel
  | .return _ _, native, m, s, encoded, rel
  | .break _, native, m, s, encoded, rel
  | .continue _, native, m, s, encoded, rel
  | .tick, native, m, s, encoded, rel
  | .codeBufferWrite _ _, native, m, s, encoded, rel
  | .dataBufferWrite _ _, native, m, s, encoded, rel => by
      simp only [wordLangProgToHOL, Option.some.injEq] at encoded; subst encoded
      unfold wordConstFpLoop constFpLoop
      exact ⟨rfl, rel⟩
  | .opCurrHeap op d src, native, m, s, encoded, rel => by
      simp only [wordLangProgToHOL, Option.some.injEq] at encoded; subst encoded
      unfold wordConstFpLoop constFpLoop
      exact ⟨rfl, constRel_delete rel d⟩
  | .locValue d src, native, m, s, encoded, rel => by
      simp only [wordLangProgToHOL, Option.some.injEq] at encoded; subst encoded
      unfold wordConstFpLoop constFpLoop
      exact ⟨rfl, constRel_delete rel d⟩
  | .install r1 r2 r3 r4 sets, native, m, s, encoded, rel => by
      simp only [wordLangProgToHOL, Option.some.injEq] at encoded; subst encoded
      unfold wordConstFpLoop constFpLoop
      exact ⟨smartSeq_production _ _ _ _ (dropConsts_production rel _) rfl,
        constRel_delete (constRel_filterGc (constRel_inter rel sets)) r1⟩
  | .ffi f a b c d sets, native, m, s, encoded, rel => by
      simp only [wordLangProgToHOL, Option.some.injEq] at encoded; subst encoded
      unfold wordConstFpLoop constFpLoop
      exact ⟨smartSeq_production _ _ _ _ (dropConsts_production rel _) rfl,
        constRel_inter rel sets⟩
  | .shareInst op v e, native, m, s, encoded, rel => by
      simp only [wordLangProgToHOL, Option.some.injEq] at encoded; subst encoded
      unfold wordConstFpLoop constFpLoop
      cases op <;> exact ⟨by simp [wordLangProgToHOL, constExp_production rel e],
        by first | exact constRel_delete rel v | exact rel⟩
termination_by p => sizeOf p

/-- The native pass from empty knowledge. -/
theorem constFpLoop_empty_production {width : Nat} [NeZero width]
    (p : WordProg (BitVec width)) (native : WordLangProgHOL (BitVec width))
    (encoded : wordLangProgToHOL p = some native) :
    wordLangProgToHOL (wordConstFpLoop p []).1 = some (constFp native) :=
  (constFpLoop_production p native [] .ln encoded constRel_empty).1

/-- The whole executed constant pass (`Seq_assoc Skip` then `const_fp`)
encodes to the native composition for every encoded input. Flapjack carrier
correspondence; no output encoding or evaluation premise. -/
theorem wordConstFp_production {width : Nat} [NeZero width]
    (p : WordProg (BitVec width)) (native : WordLangProgHOL (BitVec width))
    (encoded : wordLangProgToHOL p = some native) :
    wordLangProgToHOL (wordConstFp p) = some (constFp (seqAssoc .skip native)) :=
  constFpLoop_empty_production _ _ (seqAssoc_production p native encoded)

end Flapjack.Compiler.Backend.WordSimp
