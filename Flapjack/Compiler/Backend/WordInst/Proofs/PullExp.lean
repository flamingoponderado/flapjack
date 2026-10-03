import Flapjack.Compiler.Backend.WordInst
import Flapjack.Compiler.Backend.Semantics.WordSem.Accessors
import Flapjack.Misc.ListEl
import Flapjack.Misc.PermPartition
import Flapjack.Misc.Sorting.PartsHaveProp

/-!
# `word_instProof`: `pull_exp` and `flatten_exp` correctness

Counterpart of `cakeml/compiler/backend/proofs/word_instProofScript.sml:19-428`
(bead `flapjack-pxn.18.5.15.2.42`): the permutation helpers, `convert_sub_ok`,
the `pull_ops`/`optimize_consts` evaluation lemmas, `pull_exp_ok`, the
`every_var_exp` preservation lemmas, `flatten_exp_ok`, `binary_branch_exp` and
`flatten_exp_binary_branch_exp`, over the native exact `word_exp` and the
tagged `word_inst` definitions.

HOL `PERM` is the tagged `holPerm`, `PARTITION` the tagged `holPartition`, `EL`
the tagged `holEl`, `THE` the tagged `holThe`; `the_words` is the tagged
`theWords`. Untagged lemmas are Flapjack proof infrastructure that HOL obtains
inline by `fs`/`EVERY_CASE_TAC`.

Inherited assumption: theorems mentioning `word_exp` do not reach `inst`; no
`reals_as_rational_cuts` dependency arises in this module.
-/

namespace Flapjack

namespace WordInstPullExpSupport

/-- Same-module canonical finite-support witness for the `fpRegs`/`store`
    fields named by the tagged theorems of this module. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} [NeZero width] {C : Type} {F : Type} :
    (∀ (state : WordSemStateBroad width C F) (h : state.FiniteSupport),
        (WordSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : WordSemStateFiniteExact width C F,
        WordSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  WordSemStateExact.holFmapAsFiniteSupportWitness

end WordInstPullExpSupport

namespace Compiler.Backend.WordInst

open WordSemStateFiniteExact

/-! ## List permutation helpers (`word_instProofScript.sml:19-51`) -/

/-- Exact HOL local `PERM_SWAP_SIMP` (`word_instProofScript.sml:20-25`). -/
@[hol "cakeml/compiler/backend/proofs/word_instProofScript.sml" "PERM_SWAP_SIMP"]
theorem PERM_SWAP_SIMP {α : Type} (A : List α) (B : α) (C : List α) :
    holPerm (A ++ B :: C) (B :: (A ++ C)) := by
  rw [holPerm_iff]
  exact List.perm_middle

/-- Exact HOL local `EL_FILTER` (`word_instProofScript.sml:27-32`). The
    `[Nonempty α]` instance only discharges the inhabitation that the total
    `holEl` rendering of HOL `EL` needs (every HOL type is inhabited); it adds
    no hypothesis. -/
@[hol "cakeml/compiler/backend/proofs/word_instProofScript.sml" "EL_FILTER"]
theorem EL_FILTER {α : Type} [Nonempty α] (P : α → Bool) :
    ∀ (ls : List α) (x : Nat), x < (ls.filter P).length → P (holEl x (ls.filter P)) = true := by
  intro ls x hx
  rw [holEl_eq_getElem _ _ hx]
  exact (List.mem_filter.mp (List.getElem_mem hx)).2

/-- Exact HOL local `PERM_SWAP` (`word_instProofScript.sml:34-47`). -/
@[hol "cakeml/compiler/backend/proofs/word_instProofScript.sml" "PERM_SWAP"]
theorem PERM_SWAP {α : Type} (A B C : List α) :
    holPerm (A ++ B ++ C) (B ++ (A ++ C)) := by
  rw [holPerm_iff, ← List.append_assoc]
  exact List.perm_append_comm.append_right C

/-! ## `word_exp` on `Op` as a fold (Flapjack infrastructure) -/

section Infrastructure

variable {width : Nat} [NeZero width] {C : Type} {F : Type}

theorem wordExp_op (s : WordSemStateFiniteExact width C F) (op : BinOp)
    (args : List (WordLangExpHOL (BitVec width))) :
    wordExp s (.op op args) =
      match theWords (args.map (fun a => wordExp s a)) with
      | some ws => (wordOpHOL op ws).map WordLocW.word
      | none => none := by
  rw [wordExp]
  simp only [List.map_attach_eq_pmap, List.pmap_eq_map]
  rfl

theorem theWords_cons (x : Option (WordLocW width)) (l : List (Option (WordLocW width))) :
    theWords (x :: l) =
      match x with
      | some (.word a) => (theWords l).map (a :: ·)
      | _ => none := by
  rcases x with _ | (a | _) <;> simp only [theWords] <;> cases theWords l <;> rfl

/-- The fold operator of `word_op` for every operator other than `Sub`. -/
def opFold : BinOp → BitVec width → BitVec width → BitVec width
  | .and => fun left right => AndOp.and left right
  | .or => fun left right => OrOp.or left right
  | .xor => fun left right => HXor.hXor left right
  | _ => fun left right => left + right

/-- The unit of `opFold`. -/
def opUnit : BinOp → BitVec width
  | .and => Complement.complement (0 : BitVec width)
  | _ => 0

theorem wordOpHOL_fold {op : BinOp} (hop : op ≠ .sub) (ws : List (BitVec width)) :
    wordOpHOL op ws = some (ws.foldr (opFold op) (opUnit op)) := by
  cases op <;> first | exact absurd rfl hop | rfl

omit [NeZero width] in
theorem opFold_assoc (op : BinOp) (a b c : BitVec width) :
    opFold op a (opFold op b c) = opFold op (opFold op a b) c := by
  cases op
  · exact (BitVec.add_assoc a b c).symm
  · exact (BitVec.add_assoc a b c).symm
  · exact (BitVec.and_assoc a b c).symm
  · exact (BitVec.or_assoc a b c).symm
  · exact (BitVec.xor_assoc a b c).symm

omit [NeZero width] in
theorem opFold_comm (op : BinOp) (a b : BitVec width) : opFold op a b = opFold op b a := by
  cases op
  · exact BitVec.add_comm a b
  · exact BitVec.add_comm a b
  · exact BitVec.and_comm a b
  · exact BitVec.or_comm a b
  · exact BitVec.xor_comm a b

omit [NeZero width] in
theorem opFold_unit (op : BinOp) (z : BitVec width) : opFold op (opUnit op) z = z := by
  cases op
  · exact BitVec.zero_add z
  · exact BitVec.zero_add z
  · show ~~~(0 : BitVec width) &&& z = z
    simp
  · exact BitVec.zero_or
  · exact BitVec.zero_xor

omit [NeZero width] in
theorem opFold_left_comm (op : BinOp) (a b c : BitVec width) :
    opFold op a (opFold op b c) = opFold op b (opFold op a c) := by
  rw [opFold_assoc, opFold_comm op a b, ← opFold_assoc]

omit [NeZero width] in
theorem foldr_opFold_split (op : BinOp) (z : BitVec width) :
    ∀ w : List (BitVec width),
      w.foldr (opFold op) z = opFold op (w.foldr (opFold op) (opUnit op)) z
  | [] => (opFold_unit op z).symm
  | a :: w => by
      simp only [List.foldr_cons]
      rw [foldr_opFold_split op z w, opFold_assoc]

theorem wordExp_op_fold (s : WordSemStateFiniteExact width C F) {op : BinOp} (hop : op ≠ .sub)
    (ls : List (WordLangExpHOL (BitVec width))) :
    wordExp s (.op op ls) =
      ((theWords (ls.map (fun a => wordExp s a))).map
        (List.foldr (opFold op) (opUnit op))).map WordLocW.word := by
  rw [wordExp_op]
  cases theWords (ls.map (fun a => wordExp s a)) with
  | none => rfl
  | some ws => simp only [wordOpHOL_fold hop, Option.map_some]

/-- Permuting the operands of a commutative fold preserves `the_words`-then-fold. -/
theorem theWords_perm_fold (op : BinOp) {l l' : List (Option (WordLocW width))}
    (h : l.Perm l') :
    (theWords l).map (List.foldr (opFold op) (opUnit op)) =
      (theWords l').map (List.foldr (opFold op) (opUnit op)) := by
  induction h with
  | nil => rfl
  | cons x _ ih =>
      rw [theWords_cons, theWords_cons]
      rcases x with _ | (a | _)
      · rfl
      · simp only [Option.map_map]
        have e : (List.foldr (opFold op) (opUnit op) ∘ fun x => a :: x) =
            (opFold op a ∘ List.foldr (opFold op) (opUnit op)) := rfl
        rw [e]
        simpa only [Option.map_map] using congrArg (Option.map (opFold op a)) ih
      · rfl
  | swap x y l =>
      rw [theWords_cons, theWords_cons, theWords_cons, theWords_cons]
      rcases x with _ | (a | _) <;> rcases y with _ | (b | _) <;> try rfl
      cases theWords l with
      | none => rfl
      | some ws => simp only [Option.map_some, List.foldr_cons, opFold_left_comm]
  | trans _ _ ih1 ih2 => exact ih1.trans ih2

theorem fold_eq_of_wordExp_eq (s : WordSemStateFiniteExact width C F) {op : BinOp}
    (hop : op ≠ .sub) {ls ls' : List (WordLangExpHOL (BitVec width))}
    (h : wordExp s (.op op ls) = wordExp s (.op op ls')) :
    (theWords (ls.map (fun a => wordExp s a))).map (List.foldr (opFold op) (opUnit op)) =
      (theWords (ls'.map (fun a => wordExp s a))).map (List.foldr (opFold op) (opUnit op)) := by
  rw [wordExp_op_fold s hop, wordExp_op_fold s hop] at h
  exact Option.map_injective (fun _ _ e => WordLocW.word.inj e) h

/-- Pointwise result preservation lifts through `the_words`. -/
theorem theWords_map_of_some (s : WordSemStateFiniteExact width C F)
    (f : WordLangExpHOL (BitVec width) → WordLangExpHOL (BitVec width)) :
    ∀ ls : List (WordLangExpHOL (BitVec width)),
      (∀ e ∈ ls, ∀ v, wordExp s e = some v → wordExp s (f e) = some v) →
      ∀ ws, theWords (ls.map (fun a => wordExp s a)) = some ws →
        theWords (ls.map (fun a => wordExp s (f a))) = some ws
  | [], _, ws, h => h
  | e :: ls, hf, ws, h => by
      simp only [List.map_cons, theWords_cons] at h ⊢
      rcases he : wordExp s e with _ | (a | _) <;> rw [he] at h
      · simp at h
      · rw [hf e (List.mem_cons_self ..) _ he]
        cases hl : theWords (ls.map (fun a => wordExp s a)) with
        | none => rw [hl] at h; simp at h
        | some ws' =>
            rw [hl] at h
            rw [theWords_map_of_some s f ls (fun e' h' => hf e' (List.mem_cons_of_mem _ h')) ws' hl]
            exact h
      · simp at h

theorem everyVarExpsHOL_iff (P : Nat → Bool) :
    ∀ ls : List (WordLangExpHOL (BitVec width)),
      everyVarExpsHOL P ls = true ↔ ∀ x ∈ ls, everyVarExpHOL P x = true
  | [] => by simp [everyVarExpsHOL]
  | e :: ls => by
      simp only [everyVarExpsHOL, Bool.and_eq_true, List.mem_cons, forall_eq_or_imp,
        everyVarExpsHOL_iff P ls]

theorem everyVarExpHOL_op (P : Nat → Bool) (op : BinOp) (ls : List (WordLangExpHOL (BitVec width))) :
    everyVarExpHOL P (.op op ls) = true ↔ ∀ x ∈ ls, everyVarExpHOL P x = true := by
  rw [everyVarExpHOL, everyVarExpsHOL_iff]

omit [NeZero width] in
theorem opFold_unit_right (op : BinOp) (z : BitVec width) : opFold op z (opUnit op) = z := by
  rw [opFold_comm, opFold_unit]

end Infrastructure

/-! ## `pull_ops` correctness (`word_instProofScript.sml:59-191`) -/

/-- Exact HOL local `convert_sub_ok` (`word_instProofScript.sml:61-69`); HOL's
    free state `s` is the outer binder. -/
@[hol "cakeml/compiler/backend/proofs/word_instProofScript.sml" "convert_sub_ok"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem convert_sub_ok {width : Nat} [NeZero width] {C : Type} {F : Type}
    (s : WordSemStateFiniteExact width C F) :
    ∀ ls : List (WordLangExpHOL (BitVec width)),
      wordExp s (convertSub ls) = wordExp s (.op .sub ls) := by
  intro ls
  rw [convertSub.eq_def]
  split
  · simp [wordExp_op, theWords, wordOpHOL, wordOp, wordExp]
  · rename_i x w _
    rw [wordExp_op, wordExp_op]
    simp only [List.map_cons, List.map_nil, wordExp, theWords_cons]
    rcases wordExp s x with _ | (a | _)
    · rfl
    · simp only [theWords, Option.map_some, wordOpHOL, wordOp, List.foldr_cons, List.foldr_nil,
        Option.map_some, Option.some.injEq, WordLocW.word.injEq]
      rw [BitVec.sub_eq_add_neg, BitVec.add_comm a (-w)]
      simp
    · rfl
  · rfl

/-- Exact HOL local `word_exp_op_permute_lem` (`word_instProofScript.sml:72-93`);
    HOL's free `op` and `s` are the outer binders. -/
@[hol "cakeml/compiler/backend/proofs/word_instProofScript.sml" "word_exp_op_permute_lem"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem word_exp_op_permute_lem {width : Nat} [NeZero width] {C : Type} {F : Type}
    (op : BinOp) (s : WordSemStateFiniteExact width C F) :
    op ≠ .sub →
      ∀ ls ls' : List (WordLangExpHOL (BitVec width)),
        holPerm ls ls' → wordExp s (.op op ls) = wordExp s (.op op ls') := by
  intro hop ls ls' hp
  rw [holPerm_iff] at hp
  rw [wordExp_op_fold s hop, wordExp_op_fold s hop,
    theWords_perm_fold op (hp.map (fun a => wordExp s a))]

/-- Exact HOL `pull_ops_simp_def` (`word_instProofScript.sml:96-102`), the
    non-tail-recursive `pull_ops` of the proof script. -/
@[hol "cakeml/compiler/backend/proofs/word_instProofScript.sml" "pull_ops_simp_def"
  (words_as_type_indexed_bitvec)]
def pullOpsSimp {width : Nat} [NeZero width] (op : BinOp) :
    List (WordLangExpHOL (BitVec width)) → List (WordLangExpHOL (BitVec width))
  | [] => []
  | x :: xs =>
      match x with
      | .op op' ls => if op = op' then ls ++ pullOpsSimp op xs else x :: pullOpsSimp op xs
      | _ => x :: pullOpsSimp op xs

/-- Exact HOL local `pull_ops_simp_pull_ops_perm` (`word_instProofScript.sml:104-113`);
    HOL's free `op` is the outer binder. -/
@[hol "cakeml/compiler/backend/proofs/word_instProofScript.sml" "pull_ops_simp_pull_ops_perm"
  (words_as_type_indexed_bitvec)]
theorem pull_ops_simp_pull_ops_perm {width : Nat} [NeZero width] (op : BinOp) :
    ∀ ls x : List (WordLangExpHOL (BitVec width)),
      holPerm (pullOps op ls x) (pullOpsSimp op ls ++ x) := by
  intro ls
  induction ls with
  | nil => intro x; rw [holPerm_iff]; exact List.Perm.refl _
  | cons a ls ih =>
      intro x
      have hother : holPerm (pullOps op ls (a :: x)) (a :: pullOpsSimp op ls ++ x) := by
        have := (holPerm_iff _ _).mp (ih (a :: x))
        rw [holPerm_iff]
        exact this.trans List.perm_middle
      cases a with
      | op op' l =>
          simp only [pullOps, pullOpsSimp]
          split
          · have := (holPerm_iff _ _).mp (ih (l ++ x))
            rw [holPerm_iff]
            refine this.trans ?_
            rw [← List.append_assoc, List.append_assoc l]
            rw [← List.append_assoc]
            exact List.perm_append_comm.append_right x
          · exact hother
      | _ => exact hother

/-- Exact HOL local `pull_ops_simp_pull_ops_word_exp` (`word_instProofScript.sml:115-123`);
    HOL's free `op`, `s` and `ls` are explicit binders. -/
@[hol "cakeml/compiler/backend/proofs/word_instProofScript.sml" "pull_ops_simp_pull_ops_word_exp"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem pull_ops_simp_pull_ops_word_exp {width : Nat} [NeZero width] {C : Type} {F : Type}
    (op : BinOp) (s : WordSemStateFiniteExact width C F) (ls : List (WordLangExpHOL (BitVec width))) :
    op ≠ .sub →
      wordExp s (.op op (pullOps op ls [])) = wordExp s (.op op (pullOpsSimp op ls)) := by
  intro hop
  have := pull_ops_simp_pull_ops_perm op ls []
  rw [List.append_nil] at this
  exact word_exp_op_permute_lem op s hop _ _ this

/-- Exact HOL local `word_exp_op_mono` (`word_instProofScript.sml:127-138`); HOL's
    free variables are explicit binders. -/
@[hol "cakeml/compiler/backend/proofs/word_instProofScript.sml" "word_exp_op_mono"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem word_exp_op_mono {width : Nat} [NeZero width] {C : Type} {F : Type}
    (op : BinOp) (s : WordSemStateFiniteExact width C F)
    (ls ls' : List (WordLangExpHOL (BitVec width))) (x : WordLangExpHOL (BitVec width)) :
    op ≠ .sub →
      wordExp s (.op op ls) = wordExp s (.op op ls') →
        wordExp s (.op op (x :: ls)) = wordExp s (.op op (x :: ls')) := by
  intro hop h
  have hf := fold_eq_of_wordExp_eq s hop h
  rw [wordExp_op_fold s hop, wordExp_op_fold s hop]
  simp only [List.map_cons, theWords_cons]
  rcases wordExp s x with _ | (a | _)
  · rfl
  · cases hA : theWords (ls.map (fun a => wordExp s a)) <;>
      cases hB : theWords (ls'.map (fun a => wordExp s a)) <;>
      rw [hA, hB] at hf <;> simp_all
  · rfl

/-- Exact HOL local `the_words_append` (`word_instProofScript.sml:140-155`). -/
@[hol "cakeml/compiler/backend/proofs/word_instProofScript.sml" "the_words_append"
  (words_as_type_indexed_bitvec)]
theorem the_words_append {width : Nat} [NeZero width] :
    ∀ ls ls' : List (Option (WordLocW width)),
      theWords (ls ++ ls') =
        match theWords ls with
        | none => none
        | some w =>
            match theWords ls' with
            | none => none
            | some w' => some (w ++ w') := by
  intro ls ls'
  induction ls with
  | nil => simp only [List.nil_append, theWords]; cases theWords ls' <;> rfl
  | cons x ls ih =>
      rw [List.cons_append, theWords_cons, theWords_cons, ih]
      rcases x with _ | (a | _)
      · rfl
      · cases theWords ls <;> cases theWords ls' <;> rfl
      · rfl

/-- Exact HOL local `word_exp_op_op` (`word_instProofScript.sml:157-174`); HOL's
    free `op`, `s` and `l` are the outer binders. -/
@[hol "cakeml/compiler/backend/proofs/word_instProofScript.sml" "word_exp_op_op"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem word_exp_op_op {width : Nat} [NeZero width] {C : Type} {F : Type}
    (op : BinOp) (s : WordSemStateFiniteExact width C F) (l : List (WordLangExpHOL (BitVec width))) :
    op ≠ .sub →
      ∀ ls ls' : List (WordLangExpHOL (BitVec width)),
        wordExp s (.op op ls) = wordExp s (.op op ls') →
          wordExp s (.op op (l ++ ls)) = wordExp s (.op op (.op op l :: ls')) := by
  intro hop ls ls' h
  have hf := fold_eq_of_wordExp_eq s hop h
  rw [wordExp_op_fold s hop, wordExp_op_fold s hop]
  simp only [List.map_append, List.map_cons, the_words_append, theWords_cons]
  rw [wordExp_op_fold s hop]
  cases hl : theWords (l.map (fun a => wordExp s a)) with
  | none => rfl
  | some w =>
      cases hA : theWords (ls.map (fun a => wordExp s a)) <;>
        cases hB : theWords (ls'.map (fun a => wordExp s a)) <;>
        rw [hA, hB] at hf <;> simp only [Option.map_some, Option.map_none, Option.some.injEq,
          reduceCtorEq] at hf ⊢
      rename_i wa wb
      rw [List.foldr_append, foldr_opFold_split op _ w, hf, List.foldr_cons]

/-- Exact HOL local `pull_ops_ok` (`word_instProofScript.sml:176-189`); HOL's free
    `op` and `s` are the outer binders. -/
@[hol "cakeml/compiler/backend/proofs/word_instProofScript.sml" "pull_ops_ok"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem pull_ops_ok {width : Nat} [NeZero width] {C : Type} {F : Type}
    (op : BinOp) (s : WordSemStateFiniteExact width C F) :
    op ≠ .sub →
      ∀ ls : List (WordLangExpHOL (BitVec width)),
        wordExp s (.op op (pullOps op ls [])) = wordExp s (.op op ls) := by
  intro hop ls
  rw [pull_ops_simp_pull_ops_word_exp op s ls hop]
  induction ls with
  | nil => rfl
  | cons x ls ih =>
      have hm := word_exp_op_mono op s _ _ x hop ih
      cases x with
      | op op' l =>
          simp only [pullOpsSimp]
          split
          · rename_i heq
            subst heq
            exact word_exp_op_op op s l hop _ _ ih
          · exact hm
      | _ => exact hm

/-! ## `optimize_consts` correctness (`word_instProofScript.sml:193-270`) -/

/-- Exact HOL local `word_exp_swap_head` (`word_instProofScript.sml:193-205`);
    HOL's free `op`, `s`, `A` and `w` are the outer binders. -/
@[hol "cakeml/compiler/backend/proofs/word_instProofScript.sml" "word_exp_swap_head"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem word_exp_swap_head {width : Nat} [NeZero width] {C : Type} {F : Type}
    (op : BinOp) (s : WordSemStateFiniteExact width C F) (A : List (WordLangExpHOL (BitVec width)))
    (w : BitVec width) :
    ∀ B : List (WordLangExpHOL (BitVec width)),
      op ≠ .sub →
        wordExp s (.op op A) = some (.word w) →
          wordExp s (.op op (B ++ A)) = wordExp s (.op op (.const w :: B)) := by
  intro B hop hA
  rw [wordExp_op_fold s hop] at hA
  rw [wordExp_op_fold s hop, wordExp_op_fold s hop]
  simp only [List.map_append, List.map_cons, the_words_append, theWords_cons, wordExp]
  cases ha : theWords (A.map (fun a => wordExp s a)) with
  | none => rw [ha] at hA; simp at hA
  | some wa =>
      rw [ha] at hA
      simp only [Option.map_some, Option.some.injEq, WordLocW.word.injEq] at hA
      cases theWords (B.map (fun a => wordExp s a)) with
      | none => rfl
      | some wb =>
          simp only [Option.map_some, List.foldr_append, List.foldr_cons]
          rw [foldr_opFold_split op _ wb, hA, opFold_comm]

/-- Exact HOL local `EVERY_is_const_word_exp` (`word_instProofScript.sml:207-212`);
    HOL's free `s` is the outer binder. -/
@[hol "cakeml/compiler/backend/proofs/word_instProofScript.sml" "EVERY_is_const_word_exp"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem EVERY_is_const_word_exp {width : Nat} [NeZero width] {C : Type} {F : Type}
    (s : WordSemStateFiniteExact width C F) :
    ∀ ls : List (WordLangExpHOL (BitVec width)),
      (∀ e ∈ ls, isConst e = true) → ∀ o ∈ ls.map (fun a => wordExp s a), o.isSome = true := by
  intro ls h o ho
  obtain ⟨e, he, rfl⟩ := List.mem_map.mp ho
  have := h e he
  cases e <;> simp_all [isConst, wordExp]

/-- Exact HOL local `all_consts_simp` (`word_instProofScript.sml:214-232`); HOL's
    free `op` and `s` are the outer binders. -/
@[hol "cakeml/compiler/backend/proofs/word_instProofScript.sml" "all_consts_simp"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem all_consts_simp {width : Nat} [NeZero width] {C : Type} {F : Type}
    (op : BinOp) (s : WordSemStateFiniteExact width C F) :
    op ≠ .sub →
      ∀ ls : List (WordLangExpHOL (BitVec width)),
        (∀ e ∈ ls, isConst e = true) →
          wordExp s (.op op ls) = some (.word (holThe (wordOpHOL op (ls.map rmConst)))) := by
  intro hop ls hc
  have hw : theWords (ls.map (fun a => wordExp s a)) = some (ls.map rmConst) := by
    clear hop
    induction ls with
    | nil => rfl
    | cons e ls ih =>
        have he := hc e (List.mem_cons_self ..)
        cases e <;> simp only [isConst, Bool.false_eq_true] at he
        simp only [List.map_cons, theWords_cons, wordExp, rmConst,
          ih (fun e' h' => hc e' (List.mem_cons_of_mem _ h')), Option.map_some]
  rw [wordExp_op_fold s hop, hw, wordOpHOL_fold hop]
  rfl

/-- Exact HOL local `word_exp_reduce_const` (`word_instProofScript.sml:234-241`);
    HOL's free variables are explicit binders. -/
@[hol "cakeml/compiler/backend/proofs/word_instProofScript.sml" "word_exp_reduce_const"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem word_exp_reduce_const {width : Nat} [NeZero width] {C : Type} {F : Type}
    (op : BinOp) (s : WordSemStateFiniteExact width C F) (w : BitVec width)
    (rest : List (WordLangExpHOL (BitVec width))) (x : WordLocW width) :
    wordExp s (.op op (.const w :: rest)) = some x →
      wordExp s (reduceConst op w rest) = some x := by
  intro h
  unfold reduceConst
  by_cases hw : w = 0
  · subst hw
    rw [if_pos rfl]
    by_cases hop : op = .add ∨ op = .or ∨ op = .xor
    · rw [if_pos hop]
      have hns : op ≠ .sub := by rcases hop with rfl | rfl | rfl <;> decide
      rw [wordExp_op_fold s hns] at h
      simp only [List.map_cons, theWords_cons, wordExp, Option.map_map] at h
      have hu : opUnit op = (0 : BitVec width) := by
        rcases hop with rfl | rfl | rfl <;> rfl
      match rest, h with
      | [], h =>
          simp only [List.map_nil, theWords, Option.map_some, Function.comp, List.foldr_cons,
            List.foldr_nil, Option.some.injEq] at h
          rw [← h, hu]
          simp only [wordExp, Option.some.injEq, WordLocW.word.injEq]
          rw [← hu, opFold_unit]
      | [y], h =>
          simp only [List.map_cons, List.map_nil, theWords_cons] at h
          rcases hy : wordExp s y with _ | (a | _) <;> rw [hy] at h
          · simp at h
          · simp only [theWords, Option.map_some, Function.comp, List.foldr_cons, List.foldr_nil,
              Option.some.injEq] at h
            rw [← h, ← hu, opFold_unit, opFold_comm, opFold_unit]
          · simp at h
      | y :: z :: rest', h =>
          rw [wordExp_op_fold s hns]
          cases ht : theWords ((y :: z :: rest').map (fun a => wordExp s a)) with
          | none => rw [ht] at h; simp at h
          | some ws =>
              rw [ht] at h
              simp only [Option.map_some, Function.comp, List.foldr_cons, Option.some.injEq] at h ⊢
              rw [← h, ← hu, opFold_unit]
    · rw [if_neg hop]
      by_cases hand : op = .and
      · rw [if_pos hand]
        subst hand
        rw [wordExp_op_fold s (by decide)] at h
        simp only [List.map_cons, theWords_cons, wordExp, Option.map_map] at h
        cases ht : theWords (rest.map (fun a => wordExp s a)) with
        | none => rw [ht] at h; simp at h
        | some ws =>
            rw [ht] at h
            simp only [Option.map_some, Function.comp, List.foldr_cons, Option.some.injEq] at h
            rw [← h]
            simp only [wordExp, Option.some.injEq, WordLocW.word.injEq]
            show (0 : BitVec width) = 0 &&& _
            simp
      · rw [if_neg hand]
        exact h
  · rw [if_neg hw]
    exact h

/-- Exact HOL local `optimize_consts_ok` (`word_instProofScript.sml:243-270`); HOL's
    free variables are explicit binders. -/
@[hol "cakeml/compiler/backend/proofs/word_instProofScript.sml" "optimize_consts_ok"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem optimize_consts_ok {width : Nat} [NeZero width] {C : Type} {F : Type}
    (op : BinOp) (s : WordSemStateFiniteExact width C F)
    (ls : List (WordLangExpHOL (BitVec width))) (x : WordLocW width) :
    op ≠ .sub ∧ wordExp s (.op op ls) = some x →
      wordExp s (optimizeConsts op ls) = some x := by
  rintro ⟨hop, h⟩
  unfold optimizeConsts
  rcases hp : holPartition (fun e => isConst e) ls with ⟨cl, ncl⟩
  have hperm := permPartitionMisc (fun e => isConst e) ls cl ncl hp.symm
  have hcl := (holPartsHaveProp (fun e => isConst e) ls cl ncl [] []
    ⟨hp.symm, by simp, by simp⟩).1
  simp only
  cases cl with
  | nil =>
      rw [← h]
      exact (word_exp_op_permute_lem op s hop _ _ hperm).symm
  | cons c ct =>
      simp only
      apply word_exp_reduce_const
      have hall := all_consts_simp op s hop (c :: ct) hcl
      rw [← word_exp_swap_head op s (c :: ct) _ ncl hop hall, ← h]
      refine word_exp_op_permute_lem op s hop _ _ ?_
      rw [holPerm_iff] at hperm ⊢
      exact (hperm.trans List.perm_append_comm).symm

/-! ## `pull_exp` correctness (`word_instProofScript.sml:272-317`) -/

/-- Unfold one `pull_exp` clause, discharging the earlier-clause exclusions. -/
local macro "pull_exp_rw" : tactic =>
  `(tactic| (rw [pullExp]; all_goals (first | (intros; simp_all; done) | skip)))

/-- Exact HOL local `pull_exp_ok` (`word_instProofScript.sml:272-317`), by
    recursion on the expression as HOL's `pull_exp_ind`. -/
@[hol "cakeml/compiler/backend/proofs/word_instProofScript.sml" "pull_exp_ok"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem pull_exp_ok {width : Nat} [NeZero width] {C : Type} {F : Type} :
    ∀ (exp : WordLangExpHOL (BitVec width)) (s : WordSemStateFiniteExact width C F)
      (x : WordLocW width),
      wordExp s exp = some x → wordExp s (pullExp exp) = some x
  | .op op ls, s, x, h => by
      have ih : ∀ e ∈ ls, ∀ v, wordExp s e = some v → wordExp s (pullExp e) = some v :=
        fun e he v hv => pull_exp_ok e s v hv
      by_cases hsub : op = .sub
      · subst hsub
        pull_exp_rw
        simp only [List.map_attach_eq_pmap, List.pmap_eq_map]
        rw [convert_sub_ok, wordExp_op]
        rw [wordExp_op] at h
        cases hw : theWords (ls.map (fun a => wordExp s a)) with
        | none => rw [hw] at h; simp at h
        | some ws =>
            rw [hw] at h
            have := theWords_map_of_some s pullExp ls ih ws hw
            simp only [List.map_map, Function.comp_def]
            rw [this]
            exact h
      · rcases ls with _ | ⟨a, _ | ⟨b, rest⟩⟩
        · pull_exp_rw
          rw [wordExp_op_fold s hsub] at h
          simp only [List.map_nil, theWords, Option.map_some, List.foldr_nil,
            Option.some.injEq] at h
          subst h
          cases op <;> first | exact absurd rfl hsub | simp [opConsts, opUnit, wordExp]
        · pull_exp_rw
          rw [wordExp_op_fold s hsub] at h
          simp only [List.map_cons, List.map_nil, theWords_cons] at h
          rcases ha : wordExp s a with _ | (w | _) <;> rw [ha] at h
          · simp at h
          · simp only [theWords, Option.map_some, List.foldr_cons, List.foldr_nil,
              Option.some.injEq] at h
            rw [opFold_comm, opFold_unit] at h
            subst h
            exact ih a (List.mem_cons_self ..) _ ha
          · simp at h
        · pull_exp_rw
          simp only [List.map_attach_eq_pmap, List.pmap_eq_map]
          refine optimize_consts_ok op s _ x ⟨hsub, ?_⟩
          rw [pull_ops_ok op s hsub, wordExp_op_fold s hsub]
          rw [wordExp_op_fold s hsub] at h
          cases hw : theWords ((a :: b :: rest).map (fun a => wordExp s a)) with
          | none => rw [hw] at h; simp at h
          | some ws =>
              rw [hw] at h
              have := theWords_map_of_some s pullExp _ ih ws hw
              simp only [List.map_map, Function.comp_def]
              rw [this]
              exact h
  | .load e, s, x, h => by
      pull_exp_rw
      simp only [wordExp] at h ⊢
      rcases he : wordExp s e with _ | (w | _) <;> rw [he] at h
      · simp at h
      · rw [pull_exp_ok e s _ he]
        exact h
      · simp at h
  | .shift sh e1 e2, s, x, h => by
      pull_exp_rw
      simp only [wordExp] at h ⊢
      rcases h1 : wordExp s e1 with _ | (w1 | _) <;> rcases h2 : wordExp s e2 with _ | (w2 | _) <;>
        rw [h1, h2] at h <;> try (simp at h; done)
      rw [pull_exp_ok e1 s _ h1, pull_exp_ok e2 s _ h2]
      exact h
  | .const _, _, _, h | .var _, _, _, h | .lookup _, _, _, h => by pull_exp_rw
termination_by exp => sizeOf exp
decreasing_by
  all_goals simp_wf
  all_goals first
    | (have := List.sizeOf_lt_of_mem ‹_ ∈ _›; omega)
    | omega

/-! ## `pull_exp` syntax (`word_instProofScript.sml:319-361`) -/

/-- Exact HOL local `convert_sub_every_var_exp` (`word_instProofScript.sml:320-327`);
    HOL's free `P` is the outer binder. -/
@[hol "cakeml/compiler/backend/proofs/word_instProofScript.sml" "convert_sub_every_var_exp"
  (words_as_type_indexed_bitvec)]
theorem convert_sub_every_var_exp {width : Nat} [NeZero width] (P : Nat → Bool) :
    ∀ ls : List (WordLangExpHOL (BitVec width)),
      (∀ x ∈ ls, everyVarExpHOL P x = true) → everyVarExpHOL P (convertSub ls) = true := by
  intro ls h
  rw [convertSub.eq_def]
  split
  · simp [everyVarExpHOL]
  · rename_i x w _
    rw [everyVarExpHOL_op]
    intro y hy
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
    rcases hy with rfl | rfl
    · simp [everyVarExpHOL]
    · exact h y (List.mem_cons_self ..)
  · exact (everyVarExpHOL_op P _ _).mpr h

/-- Exact HOL local `optimize_consts_every_var_exp` (`word_instProofScript.sml:329-339`);
    HOL's free `P` and `op` are the outer binders. -/
@[hol "cakeml/compiler/backend/proofs/word_instProofScript.sml" "optimize_consts_every_var_exp"
  (words_as_type_indexed_bitvec)]
theorem optimize_consts_every_var_exp {width : Nat} [NeZero width] (P : Nat → Bool) (op : BinOp) :
    ∀ ls : List (WordLangExpHOL (BitVec width)),
      (∀ x ∈ ls, everyVarExpHOL P x = true) →
        everyVarExpHOL P (optimizeConsts op ls) = true := by
  intro ls h
  unfold optimizeConsts
  rcases hp : holPartition (fun e => isConst e) ls with ⟨cl, ncl⟩
  have hperm := (holPerm_iff _ _).mp (permPartitionMisc (fun e => isConst e) ls cl ncl hp.symm)
  have hn : ∀ x ∈ ncl, everyVarExpHOL P x = true :=
    fun x hx => h x (hperm.symm.subset (List.mem_append_right _ hx))
  simp only
  cases cl with
  | nil => exact (everyVarExpHOL_op P _ _).mpr hn
  | cons c ct =>
      simp only
      unfold reduceConst
      have hcons : ∀ w, everyVarExpHOL P (.op op (.const w :: ncl)) = true := by
        intro w
        rw [everyVarExpHOL_op]
        intro y hy
        rcases List.mem_cons.mp hy with rfl | hy
        · simp [everyVarExpHOL]
        · exact hn y hy
      split
      · split
        · split
          · simp [everyVarExpHOL]
          · exact hn _ (List.mem_singleton_self _)
          · exact (everyVarExpHOL_op P _ _).mpr hn
        · split
          · simp [everyVarExpHOL]
          · exact hcons _
      · exact hcons _

/-- HOL's anonymous `pull_ops_every_var_exp` (`word_instProofScript.sml:341-346`,
    a `val` bound by `Q.prove`, not a stored theorem), in its `EVERY_MEM`
    rewritten form. Flapjack infrastructure. -/
theorem pull_ops_every_var_exp {width : Nat} [NeZero width] (P : Nat → Bool) (op : BinOp) :
    ∀ ls acc : List (WordLangExpHOL (BitVec width)),
      (∀ x ∈ acc, everyVarExpHOL P x = true) ∧ (∀ x ∈ ls, everyVarExpHOL P x = true) →
        ∀ x ∈ pullOps op ls acc, everyVarExpHOL P x = true
  | [], acc, ⟨ha, _⟩ => ha
  | e :: ls, acc, ⟨ha, hl⟩ => by
      have he := hl e (List.mem_cons_self ..)
      have hl' : ∀ x ∈ ls, everyVarExpHOL P x = true := fun x hx => hl x (List.mem_cons_of_mem _ hx)
      have hother : ∀ x ∈ pullOps op ls (e :: acc), everyVarExpHOL P x = true :=
        pull_ops_every_var_exp P op ls (e :: acc)
          ⟨fun x hx => (List.mem_cons.mp hx).elim (fun h => h ▸ he) (ha x), hl'⟩
      cases e with
      | op op' l =>
          simp only [pullOps]
          split
          · refine pull_ops_every_var_exp P op ls (l ++ acc) ⟨?_, hl'⟩
            intro x hx
            rcases List.mem_append.mp hx with hx | hx
            · exact (everyVarExpHOL_op P _ _).mp he x hx
            · exact ha x hx
          · exact hother
      | _ => exact hother

/-- Exact HOL local `pull_exp_every_var_exp` (`word_instProofScript.sml:348-360`);
    HOL's free `P` is the outer binder. -/
@[hol "cakeml/compiler/backend/proofs/word_instProofScript.sml" "pull_exp_every_var_exp"
  (words_as_type_indexed_bitvec)]
theorem pull_exp_every_var_exp {width : Nat} [NeZero width] (P : Nat → Bool) :
    ∀ exp : WordLangExpHOL (BitVec width),
      everyVarExpHOL P exp = true → everyVarExpHOL P (pullExp exp) = true
  | .op op ls, h => by
      have hl := (everyVarExpHOL_op P op ls).mp h
      have ih : ∀ e ∈ ls, everyVarExpHOL P (pullExp e) = true :=
        fun e he => pull_exp_every_var_exp P e (hl e he)
      have hm : ∀ x ∈ ls.map pullExp, everyVarExpHOL P x = true := by
        intro x hx
        obtain ⟨e, he, rfl⟩ := List.mem_map.mp hx
        exact ih e he
      by_cases hsub : op = .sub
      · subst hsub
        pull_exp_rw
        simp only [List.map_attach_eq_pmap, List.pmap_eq_map]
        exact convert_sub_every_var_exp P _ hm
      · rcases ls with _ | ⟨a, _ | ⟨b, rest⟩⟩
        · pull_exp_rw
          all_goals (cases op <;> simp [opConsts, everyVarExpHOL])
        · pull_exp_rw
          all_goals exact ih a (List.mem_cons_self ..)
        · pull_exp_rw
          simp only [List.map_attach_eq_pmap, List.pmap_eq_map]
          exact optimize_consts_every_var_exp P op _
            (pull_ops_every_var_exp P op _ [] ⟨by simp, hm⟩)
  | .load e, h => by
      pull_exp_rw
      simp only [everyVarExpHOL] at h ⊢
      exact pull_exp_every_var_exp P e h
  | .shift sh e1 e2, h => by
      pull_exp_rw
      simp only [everyVarExpHOL, Bool.and_eq_true] at h ⊢
      exact ⟨pull_exp_every_var_exp P e1 h.1, pull_exp_every_var_exp P e2 h.2⟩
  | .const _, h | .var _, h | .lookup _, h => by pull_exp_rw
termination_by exp => sizeOf exp
decreasing_by
  all_goals simp_wf
  all_goals first
    | (have := List.sizeOf_lt_of_mem ‹_ ∈ _›; omega)
    | omega

/-! ## `flatten_exp` correctness and syntax (`word_instProofScript.sml:362-428`) -/

/-- Unfold one `flatten_exp` clause, discharging the earlier-clause exclusions. -/
local macro "flatten_exp_rw" : tactic =>
  `(tactic| (rw [flattenExp]; all_goals (first | (intros; simp_all; done) | skip)))

/-- The `Sub` clause of `flatten_exp_ok`, given the result for every operand. -/
theorem flatten_exp_ok_sub {width : Nat} [NeZero width] {C : Type} {F : Type}
    (s : WordSemStateFiniteExact width C F) (ls : List (WordLangExpHOL (BitVec width)))
    (ih : ∀ e ∈ ls, ∀ v, wordExp s e = some v → wordExp s (flattenExp e) = some v)
    (x : WordLocW width) (h : wordExp s (.op .sub ls) = some x) :
    wordExp s (flattenExp (.op .sub ls)) = some x := by
  flatten_exp_rw
  simp only [List.map_attach_eq_pmap, List.pmap_eq_map]
  rw [wordExp_op]
  rw [wordExp_op] at h
  cases hw : theWords (ls.map (fun a => wordExp s a)) with
  | none => rw [hw] at h; simp at h
  | some ws =>
      rw [hw] at h
      have := theWords_map_of_some s flattenExp ls ih ws hw
      simp only [List.map_map, Function.comp_def]
      rw [this]
      exact h

/-- Exact HOL local `flatten_exp_ok` (`word_instProofScript.sml:363-394`), by
    recursion on the expression as HOL's `flatten_exp_ind`. -/
@[hol "cakeml/compiler/backend/proofs/word_instProofScript.sml" "flatten_exp_ok"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem flatten_exp_ok {width : Nat} [NeZero width] {C : Type} {F : Type} :
    ∀ (exp : WordLangExpHOL (BitVec width)) (s : WordSemStateFiniteExact width C F)
      (x : WordLocW width),
      wordExp s exp = some x → wordExp s (flattenExp exp) = some x
  | .op op [], s, x, h => by
      by_cases hsub : op = .sub
      · subst hsub
        exact flatten_exp_ok_sub s [] (fun e he => by simp at he) x h
      · flatten_exp_rw
        rw [wordExp_op_fold s hsub] at h
        simp only [List.map_nil, theWords, Option.map_some, List.foldr_nil,
          Option.some.injEq] at h
        subst h
        all_goals (cases op <;> first | exact absurd rfl hsub | simp [opConsts, opUnit, wordExp])
  | .op op [a], s, x, h => by
      by_cases hsub : op = .sub
      · subst hsub
        exact flatten_exp_ok_sub s [a] (fun e he v hv => flatten_exp_ok e s v hv) x h
      · flatten_exp_rw
        rw [wordExp_op_fold s hsub] at h
        simp only [List.map_cons, List.map_nil, theWords_cons] at h
        rcases ha : wordExp s a with _ | (w | _) <;> rw [ha] at h
        · simp at h
        · simp only [theWords, Option.map_some, List.foldr_cons, List.foldr_nil,
            Option.some.injEq] at h
          rw [opFold_comm, opFold_unit] at h
          subst h
          exact flatten_exp_ok a s _ ha
        · simp at h
  | .op op (a :: b :: rest), s, x, h => by
      by_cases hsub : op = .sub
      · subst hsub
        exact flatten_exp_ok_sub s _ (fun e he v hv => flatten_exp_ok e s v hv) x h
      · flatten_exp_rw
        rw [wordExp_op_fold s hsub] at h
        rw [wordExp_op_fold s hsub]
        rw [List.map_cons, theWords_cons] at h
        rcases ha : wordExp s a with _ | (w | _) <;> rw [ha] at h
        · simp at h
        · simp only at h
          cases hw : theWords ((b :: rest).map (fun a => wordExp s a)) with
          | none => rw [hw] at h; simp at h
          | some ws =>
              rw [hw] at h
              simp only [Option.map_some, List.foldr_cons, Option.some.injEq] at h
              have hrest : wordExp s (.op op (b :: rest)) =
                  some (.word (ws.foldr (opFold op) (opUnit op))) := by
                rw [wordExp_op_fold s hsub, hw]
                rfl
              have h1 := flatten_exp_ok (.op op (b :: rest)) s _ hrest
              have h2 := flatten_exp_ok a s _ ha
              simp only [List.map_cons, List.map_nil, theWords_cons, h1, h2, theWords,
                Option.map_some, List.foldr_cons, List.foldr_nil]
              rw [← h, opFold_unit_right, opFold_comm]
        · simp at h
  | .load e, s, x, h => by
      flatten_exp_rw
      simp only [wordExp] at h ⊢
      rcases he : wordExp s e with _ | (w | _) <;> rw [he] at h
      · simp at h
      · rw [flatten_exp_ok e s _ he]
        exact h
      · simp at h
  | .shift sh e1 e2, s, x, h => by
      flatten_exp_rw
      simp only [wordExp] at h ⊢
      rcases h1 : wordExp s e1 with _ | (w1 | _) <;> rcases h2 : wordExp s e2 with _ | (w2 | _) <;>
        rw [h1, h2] at h <;> try (simp at h; done)
      rw [flatten_exp_ok e1 s _ h1, flatten_exp_ok e2 s _ h2]
      exact h
  | .const _, _, _, h | .var _, _, _, h | .lookup _, _, _, h => by flatten_exp_rw
termination_by exp => sizeOf exp
decreasing_by
  all_goals simp_wf
  all_goals first
    | (have := List.sizeOf_lt_of_mem ‹_ ∈ _›; simp_all; omega)
    | omega

/-- Exact HOL `binary_branch_exp_def` (`word_instProofScript.sml:397-409`); HOL's
    `EVERY` over the operands is `List.all`, attached for termination. -/
@[hol "cakeml/compiler/backend/proofs/word_instProofScript.sml" "binary_branch_exp_def"
  (words_as_type_indexed_bitvec)]
def binaryBranchExp {width : Nat} [NeZero width] : WordLangExpHOL (BitVec width) → Bool
  | .op .sub exps => exps.attach.all (fun ⟨e, _⟩ => binaryBranchExp e)
  | .op _ xs => decide (xs.length = 2) && xs.attach.all (fun ⟨e, _⟩ => binaryBranchExp e)
  | .load exp => binaryBranchExp exp
  | .shift _ exp nexp => binaryBranchExp exp && binaryBranchExp nexp
  | _ => true
termination_by e => sizeOf e
decreasing_by
  all_goals (try subst_vars)
  all_goals simp_wf
  all_goals first
    | (have := List.sizeOf_lt_of_mem ‹_ ∈ _›; omega)
    | omega

theorem binaryBranchExp_sub {width : Nat} [NeZero width] (ls : List (WordLangExpHOL (BitVec width)))
    (ih : ∀ e ∈ ls, binaryBranchExp (flattenExp e) = true) :
    binaryBranchExp (flattenExp (.op .sub ls)) = true := by
  flatten_exp_rw
  rw [binaryBranchExp]
  simp only [List.all_eq_true]
  intro x _
  obtain ⟨e, he⟩ := x
  obtain ⟨e', _, rfl⟩ := List.mem_map.mp he
  exact ih e'.1 e'.2

theorem binaryBranchExp_pair {width : Nat} [NeZero width] (op : BinOp) (hsub : op ≠ .sub)
    (a b : WordLangExpHOL (BitVec width)) (ha : binaryBranchExp a = true)
    (hb : binaryBranchExp b = true) : binaryBranchExp (.op op [a, b]) = true := by
  rw [binaryBranchExp]
  · simp only [List.length_cons, List.length_nil, decide_true, Bool.true_and,
      List.all_eq_true, List.mem_attach, true_implies]
    intro ⟨e, he⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl
    · exact ha
    · exact hb
  · intro h; exact hsub h

/-- Exact HOL local `flatten_exp_binary_branch_exp` (`word_instProofScript.sml:412-417`). -/
@[hol "cakeml/compiler/backend/proofs/word_instProofScript.sml" "flatten_exp_binary_branch_exp"
  (words_as_type_indexed_bitvec)]
theorem flatten_exp_binary_branch_exp {width : Nat} [NeZero width] :
    ∀ exp : WordLangExpHOL (BitVec width), binaryBranchExp (flattenExp exp) = true
  | .op op [] => by
      by_cases hsub : op = .sub
      · subst hsub
        exact binaryBranchExp_sub [] (fun e he => by simp at he)
      · flatten_exp_rw
        all_goals (cases op <;> simp [opConsts, binaryBranchExp])
  | .op op [a] => by
      by_cases hsub : op = .sub
      · subst hsub
        exact binaryBranchExp_sub [a] (fun e _ => flatten_exp_binary_branch_exp e)
      · flatten_exp_rw
        all_goals exact flatten_exp_binary_branch_exp a
  | .op op (a :: b :: rest) => by
      by_cases hsub : op = .sub
      · subst hsub
        exact binaryBranchExp_sub _ (fun e _ => flatten_exp_binary_branch_exp e)
      · flatten_exp_rw
        exact binaryBranchExp_pair op hsub _ _ (flatten_exp_binary_branch_exp (.op op (b :: rest)))
          (flatten_exp_binary_branch_exp a)
  | .load e => by
      flatten_exp_rw
      rw [binaryBranchExp]
      exact flatten_exp_binary_branch_exp e
  | .shift sh e1 e2 => by
      flatten_exp_rw
      rw [binaryBranchExp]
      simp only [Bool.and_eq_true]
      exact ⟨flatten_exp_binary_branch_exp e1, flatten_exp_binary_branch_exp e2⟩
  | .const _ | .var _ | .lookup _ => by flatten_exp_rw; all_goals simp [binaryBranchExp]
termination_by exp => sizeOf exp
decreasing_by
  all_goals simp_wf
  all_goals first
    | (have := List.sizeOf_lt_of_mem ‹_ ∈ _›; simp_all; omega)
    | omega

theorem flatten_exp_every_var_exp_sub {width : Nat} [NeZero width] (P : Nat → Bool)
    (ls : List (WordLangExpHOL (BitVec width)))
    (ih : ∀ e ∈ ls, everyVarExpHOL P e = true → everyVarExpHOL P (flattenExp e) = true)
    (h : everyVarExpHOL P (.op .sub ls) = true) :
    everyVarExpHOL P (flattenExp (.op .sub ls)) = true := by
  have hl := (everyVarExpHOL_op P _ ls).mp h
  flatten_exp_rw
  rw [everyVarExpHOL_op]
  intro y hy
  obtain ⟨e, _, rfl⟩ := List.mem_map.mp hy
  exact ih e.1 e.2 (hl e.1 e.2)

/-- Exact HOL local `flatten_exp_every_var_exp` (`word_instProofScript.sml:419-425`);
    HOL's free `P` is the outer binder. -/
@[hol "cakeml/compiler/backend/proofs/word_instProofScript.sml" "flatten_exp_every_var_exp"
  (words_as_type_indexed_bitvec)]
theorem flatten_exp_every_var_exp {width : Nat} [NeZero width] (P : Nat → Bool) :
    ∀ exp : WordLangExpHOL (BitVec width),
      everyVarExpHOL P exp = true → everyVarExpHOL P (flattenExp exp) = true
  | .op op [], h => by
      by_cases hsub : op = .sub
      · subst hsub
        exact flatten_exp_every_var_exp_sub P [] (fun e he => by simp at he) h
      · flatten_exp_rw
        all_goals (cases op <;> simp [opConsts, everyVarExpHOL])
  | .op op [a], h => by
      by_cases hsub : op = .sub
      · subst hsub
        exact flatten_exp_every_var_exp_sub P [a] (fun e _ he => flatten_exp_every_var_exp P e he) h
      · have hl := (everyVarExpHOL_op P op _).mp h
        flatten_exp_rw
        all_goals exact flatten_exp_every_var_exp P a (hl a (List.mem_cons_self ..))
  | .op op (a :: b :: rest), h => by
      by_cases hsub : op = .sub
      · subst hsub
        exact flatten_exp_every_var_exp_sub P _ (fun e _ he => flatten_exp_every_var_exp P e he) h
      · have hl := (everyVarExpHOL_op P op _).mp h
        have h1 := flatten_exp_every_var_exp P (.op op (b :: rest))
          ((everyVarExpHOL_op P _ _).mpr (fun z hz => hl z (List.mem_cons_of_mem _ hz)))
        have h2 := flatten_exp_every_var_exp P a (hl a (List.mem_cons_self ..))
        flatten_exp_rw
        rw [everyVarExpHOL_op]
        intro y hy
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
        rcases hy with rfl | rfl
        · exact h1
        · exact h2
  | .load e, h => by
      flatten_exp_rw
      simp only [everyVarExpHOL] at h ⊢
      exact flatten_exp_every_var_exp P e h
  | .shift sh e1 e2, h => by
      flatten_exp_rw
      simp only [everyVarExpHOL, Bool.and_eq_true] at h ⊢
      exact ⟨flatten_exp_every_var_exp P e1 h.1, flatten_exp_every_var_exp P e2 h.2⟩
  | .const _, h | .var _, h | .lookup _, h => by flatten_exp_rw
termination_by exp => sizeOf exp
decreasing_by
  all_goals simp_wf
  all_goals first
    | (have := List.sizeOf_lt_of_mem ‹_ ∈ _›; simp_all; omega)
    | omega

end Compiler.Backend.WordInst

end Flapjack
