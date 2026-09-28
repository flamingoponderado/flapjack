import Flapjack.Pancake.CrepToLoop.StateRel
import Flapjack.Pancake.CrepToLoop.Proofs.LocalListHelpers

/-!
# crep_to_loop `make_funcs` / `compile_prog` list lemmas

Exact ports of `cakeml/pancake/proofs/crep_to_loopProofScript.sml`'s
`distinct_make_funcs` (3757), `map_map2_fst` (3799),
`first_compile_prog_all_distinct` (3832), `make_funcs_domain_compile_prog`
(3908), `alookup_el_pair_eq_el` (3921), `initial_prog_make_funcs_el` (3942)
(bead `flapjack-pxn.18.5.6.33.20`) and `crep_to_loop_compile_prog_lab_min` (4398)
(bead `flapjack-pxn.18.5.6.33.21`).

`make_funcs` is the tagged polymorphic `crepToLoopMakeFuncsHOL`
(`make_funcs_def`, HOL equality as `[BEq α] [LawfulBEq α]`), `compile_prog` the
tagged `compileProgHOLExact` (`compile_prog_def`), `MAP2` is `List.zipWith`,
`GENLIST I (LENGTH p)` is `List.range p.length`, `ALOOKUP` is `holAlookup`,
`fromAList` is `sptFromAList`, `k ∈ domain t` is `sptMem k t`, `ALL_DISTINCT` is
`List.Nodup`, and `EL n xs` under `n < LENGTH xs` is the bounds-checked `xs[n]`.
-/

namespace Flapjack

/-- `FUPDATE_LIST FEMPTY l.reverse` (the `alist_to_fmap` rendering used by
    `crepToLoopMakeFuncsHOL`) only returns bindings of `l` (HOL `ALOOKUP_MEM`). -/
private theorem flookup_fupdateList_reverse_mem {α β : Type} [BEq α] [LawfulBEq α] :
    ∀ (l : List (α × β)) (k : α) (v : β),
      FLOOKUP (FUPDATE_LIST FEMPTY l.reverse) k = some v → (k, v) ∈ l
  | [], k, v, h => by simp [FUPDATE_LIST, FLOOKUP, FEMPTY] at h
  | a :: t, k, v, h => by
      simp only [List.reverse_cons, FUPDATE_LIST, List.foldl_append, List.foldl_cons,
        List.foldl_nil] at h
      simp only [FLOOKUP, FUPDATE] at h
      split at h
      · rename_i hk
        cases h
        have : a.1 = k := LawfulBEq.eq_of_beq hk
        subst this
        exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (flookup_fupdateList_reverse_mem t k v h)

/-- Entries of the `make_funcs` association list: the `i`-th entry is
    `(FST (EL i prog), (i + first_name, LENGTH params))`. -/
private theorem makeFuncs_entry_mem {α β γ : Type}
    (prog : List (α × List β × γ)) (x : α) (n rm : Nat)
    (h : (x, (n, rm)) ∈ (prog.zip (List.range prog.length)).map
      (fun entry => (entry.1.1, (firstLoopName + entry.2, entry.1.2.1.length)))) :
    ∃ (i : Nat) (hi : i < prog.length), x = (prog[i]'hi).1 ∧ n = firstLoopName + i ∧
      rm = (prog[i]'hi).2.1.length := by
  obtain ⟨⟨e, i⟩, he, hf⟩ := List.mem_map.mp h
  obtain ⟨k, hk, hke⟩ := List.mem_iff_getElem.mp he
  simp only [List.length_zip, List.length_range, Nat.min_self] at hk
  simp only [List.getElem_zip, List.getElem_range, Prod.mk.injEq] at hke
  obtain ⟨rfl, rfl⟩ := hke
  simp only [Prod.mk.injEq] at hf
  obtain ⟨rfl, rfl, rfl⟩ := hf
  exact ⟨k, hk, rfl, rfl, rfl⟩

/-- Exact HOL `distinct_make_funcs` (`crep_to_loopProofScript.sml:3757-3758`):
    `!crep_code. distinct_funcs (make_funcs crep_code)`. -/
@[hol "cakeml/pancake/proofs/crep_to_loopProofScript.sml" "distinct_make_funcs"]
theorem distinct_make_funcs {α β γ : Type} [BEq α] [LawfulBEq α] :
    ∀ (crep_code : List (α × List β × γ)),
      crepToLoopDistinctFuncs (crepToLoopMakeFuncsHOL crep_code) := by
  intro crep_code x y n m rm rm' hx hy hnm
  obtain ⟨i, hi, rfl, rfl, _⟩ := makeFuncs_entry_mem crep_code x n rm
    (flookup_fupdateList_reverse_mem _ _ _ hx)
  obtain ⟨j, hj, rfl, hm, _⟩ := makeFuncs_entry_mem crep_code y m rm'
    (flookup_fupdateList_reverse_mem _ _ _ hy)
  have : i = j := by omega
  subst this
  rfl

/-- Exact HOL `map_map2_fst` (`crep_to_loopProofScript.sml:3799-3803`):
    `!xs ys h. LENGTH xs = LENGTH ys ==>
      MAP FST (MAP2 (λx (n,p,b). (x,GENLIST I (LENGTH p),h p b)) xs ys) = xs`. -/
@[hol "cakeml/pancake/proofs/crep_to_loopProofScript.sml" "map_map2_fst"]
theorem map_map2_fst {α β γ δ ε : Type} :
    ∀ (xs : List α) (ys : List (β × List γ × δ)) (h : List γ → δ → ε),
      xs.length = ys.length →
      (List.zipWith (fun x (e : β × List γ × δ) => match e with
          | (_, p, b) => (x, List.range p.length, h p b)) xs ys).map Prod.fst = xs
  | [], _, _, _ => by simp
  | _ :: _, [], _, hl => by simp at hl
  | x :: xs, (_, _, _) :: ys, h, hl => by
      simp only [List.zipWith_cons_cons, List.map_cons, List.cons.injEq, true_and]
      exact map_map2_fst xs ys h (by simpa using hl)

private theorem map_fst_zipWith_pair {α β γ : Type} (g : α → β → γ) :
    ∀ (xs : List α) (ys : List β), xs.length = ys.length →
      (List.zipWith (fun x y => (x, g x y)) xs ys).map Prod.fst = xs
  | [], _, _ => by simp
  | _ :: _, [], h => by simp at h
  | x :: xs, _ :: ys, h => by
      simp only [List.zipWith_cons_cons, List.map_cons, List.cons.injEq, true_and]
      exact map_fst_zipWith_pair g xs ys (by simpa using h)

/-- Exact HOL `first_compile_prog_all_distinct` (`crep_to_loopProofScript.sml:3832-3834`):
    `!c crep_code. ALL_DISTINCT (MAP FST (compile_prog c crep_code))`. -/
@[hol "cakeml/pancake/proofs/crep_to_loopProofScript.sml" "first_compile_prog_all_distinct"
  (words_as_type_indexed_bitvec)]
theorem first_compile_prog_all_distinct {width : Nat} [NeZero width] :
    ∀ (c : Compiler.Encoders.Asm.AsmArchitecture) (crep_code : List (Basis.Pure.MlString.MlString × List Nat × CrepProgHOL width)),
      ((compileProgHOLExact c crep_code).map Prod.fst).Nodup := by
  intro c crep_code
  have hfst : ((compileProgHOLExact c crep_code).map Prod.fst) =
      (List.range crep_code.length).map (fun n => n + firstLoopName) := by
    simp only [compileProgHOLExact]
    exact map_fst_zipWith_pair _ _ _ (by simp)
  rw [hfst]
  exact List.Pairwise.map _ (fun a b (h : a ≠ b) (e : a + firstLoopName = b + firstLoopName) => h (by omega))
    List.nodup_range

private theorem sptMem_sptFromAList_of_mem {α : Type} :
    ∀ (l : List (Nat × α)) (k : Nat), k ∈ l.map Prod.fst → sptMem k (sptFromAList l)
  | [], _, h => by simp at h
  | (k', v) :: l, k, h => by
      simp only [sptFromAList]
      rw [sptMem_sptInsert]
      rcases List.mem_cons.mp h with h | h
      · exact Or.inl h
      · exact Or.inr (sptMem_sptFromAList_of_mem l k h)

/-- Exact HOL `make_funcs_domain_compile_prog` (`crep_to_loopProofScript.sml:3908-3910`):
    `!start lc crep_code c. FLOOKUP (make_funcs crep_code) start = SOME (lc,0) ==>
      lc ∈ domain (fromAList (compile_prog c crep_code))`. -/
@[hol "cakeml/pancake/proofs/crep_to_loopProofScript.sml" "make_funcs_domain_compile_prog"
  (words_as_type_indexed_bitvec)]
theorem make_funcs_domain_compile_prog {width : Nat} [NeZero width] :
    ∀ (start : Basis.Pure.MlString.MlString) (lc : Nat)
      (crep_code : List (Basis.Pure.MlString.MlString × List Nat × CrepProgHOL width))
      (c : Compiler.Encoders.Asm.AsmArchitecture),
      FLOOKUP (crepToLoopMakeFuncsHOL crep_code) start = some (lc, 0) →
      sptMem lc (sptFromAList (compileProgHOLExact c crep_code)) := by
  intro start lc crep_code c h
  obtain ⟨i, hi, _, rfl, _⟩ := makeFuncs_entry_mem crep_code start lc 0
    (flookup_fupdateList_reverse_mem _ _ _ h)
  apply sptMem_sptFromAList_of_mem
  have hfst : ((compileProgHOLExact c crep_code).map Prod.fst) =
      (List.range crep_code.length).map (fun n => n + firstLoopName) := by
    simp only [compileProgHOLExact]
    exact map_fst_zipWith_pair _ _ _ (by simp)
  rw [hfst, List.mem_map]
  exact ⟨i, List.mem_range.mpr hi, by omega⟩

/-- Exact HOL `alookup_el_pair_eq_el` (`crep_to_loopProofScript.sml:3921-3925`):
    `!prog start cp n. EL n prog = (start, [], SND(SND(EL n prog))) /\
      ALL_DISTINCT (MAP FST prog) /\ n < LENGTH prog /\
      ALOOKUP prog start = SOME ([],cp) ==> EL n prog = (start, [], cp)`.
    HOL's `n < LENGTH prog` conjunct is the bound `hn` of the bounds-checked
    `prog[n]` (as for the tagged `ALOOKUP_EQ_EL`); the other conjuncts keep
    their order. -/
@[hol "cakeml/pancake/proofs/crep_to_loopProofScript.sml" "alookup_el_pair_eq_el"]
theorem alookup_el_pair_eq_el {α β γ : Type} [DecidableEq α] :
    ∀ (prog : List (α × List β × γ)) (start : α) (cp : γ) (n : Nat) (hn : n < prog.length),
      prog[n]'hn = (start, [], (prog[n]'hn).2.2) ∧ (prog.map Prod.fst).Nodup ∧
        holAlookup prog start = some ([], cp) →
      prog[n]'hn = (start, [], cp) := by
  intro prog start cp n hn ⟨he, hd, hl⟩
  have h1 : (prog[n]'hn).1 = start := by rw [he]
  have := ALOOKUP_EQ_EL n prog start (prog[n]'hn).2 hn h1 hd rfl
  rw [hl, Option.some.injEq] at this
  rw [he, ← this]

/-- Exact HOL `initial_prog_make_funcs_el` (`crep_to_loopProofScript.sml:3942-3945`):
    `!prog start n. FLOOKUP (make_funcs prog) start = SOME (n + first_name,0) ==>
      (start, [], (SND o SND) (EL n prog)) = EL n prog /\ n < LENGTH prog`.
    HOL's second conjunct `n < LENGTH prog` is the witness of the existential
    bound under which the first conjunct's `EL n prog` is the bounds-checked
    `prog[n]`; the two formulations are equivalent because that conjunct pins
    `n` in range. -/
@[hol "cakeml/pancake/proofs/crep_to_loopProofScript.sml" "initial_prog_make_funcs_el"]
theorem initial_prog_make_funcs_el {α β γ : Type} [BEq α] [LawfulBEq α] :
    ∀ (prog : List (α × List β × γ)) (start : α) (n : Nat),
      FLOOKUP (crepToLoopMakeFuncsHOL prog) start = some (n + firstLoopName, 0) →
      ∃ hn : n < prog.length, (start, [], (prog[n]'hn).2.2) = prog[n]'hn := by
  intro prog start n h
  obtain ⟨i, hi, hs, hn, hr⟩ := makeFuncs_entry_mem prog start _ 0
    (flookup_fupdateList_reverse_mem _ _ _ h)
  have : i = n := by omega
  subst this
  refine ⟨hi, ?_⟩
  have hnil : (prog[i]'hi).2.1 = [] := List.eq_nil_of_length_eq_zero hr.symm
  rw [hs]
  generalize prog[i]'hi = e at hnil ⊢
  obtain ⟨a, b, c⟩ := e
  simp only at hnil ⊢
  rw [hnil]

/-- Exact HOL `crep_to_loop_compile_prog_lab_min` (`crep_to_loopProofScript.sml:4398-4400`):
    `crep_to_loop$compile_prog c cprog = lprog ⇒ EVERY (λprog. 60 ≤ FST prog) lprog`,
    with its free variables universally quantified and `EVERY` as `∀ x ∈ lprog`. -/
@[hol "cakeml/pancake/proofs/crep_to_loopProofScript.sml" "crep_to_loop_compile_prog_lab_min"
  (words_as_type_indexed_bitvec)]
theorem crep_to_loop_compile_prog_lab_min {width : Nat} [NeZero width] :
    ∀ (c : Compiler.Encoders.Asm.AsmArchitecture)
      (cprog : List (Basis.Pure.MlString.MlString × List Nat × CrepProgHOL width))
      (lprog : List (Nat × List Nat × HolLoopProg width)),
      compileProgHOLExact c cprog = lprog → ∀ prog ∈ lprog, 60 ≤ prog.1 := by
  intro c cprog lprog h prog hp
  subst h
  have hfst : prog.1 ∈ (compileProgHOLExact c cprog).map Prod.fst := List.mem_map_of_mem hp
  have e : ((compileProgHOLExact c cprog).map Prod.fst) =
      (List.range cprog.length).map (fun n => n + firstLoopName) := by
    simp only [compileProgHOLExact]
    exact map_fst_zipWith_pair _ _ _ (by simp)
  rw [e, List.mem_map] at hfst
  obtain ⟨n, _, hn⟩ := hfst
  rw [← hn]
  simp [firstLoopName]

end Flapjack
