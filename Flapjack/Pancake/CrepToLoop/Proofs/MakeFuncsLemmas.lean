import Flapjack.Pancake.CrepToLoop.ContextExact
import Flapjack.Pancake.CrepToLoop.StateRel
import Flapjack.Pancake.CrepToLoop.Proofs.LocalListHelpers

/-!
# crep_to_loop `crep_to_loop_compile_prog_lab_min`

Exact port of `cakeml/pancake/proofs/crep_to_loopProofScript.sml`'s
`crep_to_loop_compile_prog_lab_min` (4398-4400) (bead `flapjack-pxn.18.5.6.33.21`).

The `distinct_make_funcs` slice (bead
`flapjack-pxn.18.5.6.33.20.1`) uses the corrected exact finite-support
`make_funcs` result. Other `make_funcs`/`compile_prog` list lemmas are tracked
as commit-sized children of `flapjack-pxn.18.5.6.33.20`.

`compile_prog` is the tagged `compileProgHOLExact` (`compile_prog_def`) and
`first_name` the tagged `firstLoopName` (`first_name_def`, 64).
-/

namespace Flapjack

private theorem map_fst_zipWith_pair {α β γ : Type} (g : α → β → γ) :
    ∀ (xs : List α) (ys : List β), xs.length = ys.length →
      (List.zipWith (fun x y => (x, g x y)) xs ys).map Prod.fst = xs
  | [], _, _ => by simp
  | _ :: _, [], h => by simp at h
  | x :: xs, _ :: ys, h => by
      simp only [List.zipWith_cons_cons, List.map_cons, List.cons.injEq, true_and]
      exact map_fst_zipWith_pair g xs ys (by simpa using h)

/-- Exact HOL `map_map2_fst` (`crep_to_loopProofScript.sml:3799-3803`):
    `!xs ys h. LENGTH xs = LENGTH ys ==> MAP FST (MAP2 (λx (n,p,b).
    (x, GENLIST I (LENGTH p), h p b)) xs ys) = xs`. Its fully polymorphic
    HOL carrier has `xs : 'a list`, `ys : ('b # 'c list # 'd) list`, and
    `h : 'c list -> 'd -> 'e`; only `p` is constrained to be a list. The
    right-associated Lean triple is the HOL triple, and `panMap2` preserves
    HOL `MAP2` truncation behavior. -/
@[hol "cakeml/pancake/proofs/crep_to_loopProofScript.sml" "map_map2_fst"]
theorem mapMap2FstHOL {α β γ δ ε : Type} :
    ∀ (xs : List α) (ys : List (β × List γ × δ))
      (h : List γ → δ → ε),
      xs.length = ys.length →
        (panMap2
          (fun x y => (x, List.range y.2.1.length, h y.2.1 y.2.2)) xs ys).map
          Prod.fst = xs := by
  intro xs ys h hlen
  exact panMap2_fst_eq
    (fun _ y => (List.range y.2.1.length, h y.2.1 y.2.2)) xs ys hlen

/-- Flapjack-only list infrastructure: mapping an injective function preserves
    `List.Nodup`. This generic helper has no standalone HOL declaration. -/
private theorem nodupMapInjective {α β : Type} (f : α → β)
    (hf : Function.Injective f) : ∀ xs : List α, xs.Nodup → (xs.map f).Nodup
  | [], _ => by simp
  | head :: tail, h => by
      have hcons := List.nodup_cons.mp h
      simp only [List.map_cons, List.nodup_cons]
      constructor
      · intro hmem
        rcases List.mem_map.mp hmem with ⟨other, hother, heq⟩
        have hsame : head = other := hf heq.symm
        cases hsame
        exact hcons.1 hother
      · exact nodupMapInjective f hf tail hcons.2

/-- Exact HOL `first_compile_prog_all_distinct`
    (`crep_to_loopProofScript.sml:3832-3838`): every compiled program label is
    distinct. The binders `c, crep_code` and the unqualified conclusion are
    preserved over `compileProgHOLExact`; only its positive word width uses the
    reviewed width-indexed BitVec translation. -/
@[hol "cakeml/pancake/proofs/crep_to_loopProofScript.sml" "first_compile_prog_all_distinct"
  (words_as_type_indexed_bitvec)]
theorem firstCompileProgAllDistinctExact {width : Nat} [NeZero width] :
    ∀ (c : Compiler.Encoders.Asm.AsmArchitecture)
      (crep_code : List (Basis.Pure.MlString.MlString × List Nat × CrepProgHOL width)),
      ((compileProgHOLExact c crep_code).map Prod.fst).Nodup := by
  intro c crep_code
  have hkeys : (compileProgHOLExact c crep_code).map Prod.fst =
      (List.range crep_code.length).map (fun i => i + firstLoopName) := by
    simp only [compileProgHOLExact]
    exact map_fst_zipWith_pair _ _ _ (by simp)
  rw [hkeys]
  apply nodupMapInjective (fun i : Nat => i + firstLoopName)
  · intro i j hij
    exact Nat.add_right_cancel hij
  · exact List.nodup_range

/-- A successful lookup in the HOL equality fold over a reversed association
list must come from an entry in the original list. This is local infrastructure
for the exact `make_funcs` lemma below. -/
private theorem flookup_fupdateListHOL_reverse_mem {α β : Type} [DecidableEq α] :
    ∀ (entries : List (α × β)) (key : α) (value : β),
      FLOOKUP (FUPDATE_LIST_HOL (FEMPTY : FiniteMap α β) entries.reverse) key =
        some value → (key, value) ∈ entries
  | [], key, value, h => by
      simp [FUPDATE_LIST_HOL, FLOOKUP, FEMPTY] at h
  | entry :: entries, key, value, h => by
      simp only [List.reverse_cons, FUPDATE_LIST_HOL, List.foldl_append,
        List.foldl_cons, List.foldl_nil] at h
      change (if key = entry.1 then some entry.2 else
        FLOOKUP (FUPDATE_LIST_HOL (FEMPTY : FiniteMap α β) entries.reverse) key) =
          some value at h
      by_cases heq : key = entry.1
      · simp [heq] at h
        cases h
        subst key
        exact List.mem_cons_self
      · simp [heq] at h
        exact List.mem_cons_of_mem _ (flookup_fupdateListHOL_reverse_mem
          entries key value h)

/-- Each association produced by the exact `make_funcs` list construction has
the key, label, and parameter count of one source program entry. -/
private theorem makeFuncsExact_entry_mem {α β γ : Type}
    (prog : List (α × List β × γ)) (key : α) (label arity : Nat)
    (h : (key, (label, arity)) ∈ (prog.zip (List.range prog.length)).map
      (fun entry => (entry.1.1, (firstLoopName + entry.2,
        entry.1.2.1.length)))) :
    ∃ (i : Nat) (hi : i < prog.length), key = (prog[i]'hi).1 ∧
      label = firstLoopName + i ∧ arity = (prog[i]'hi).2.1.length := by
  obtain ⟨⟨e, i⟩, he, hf⟩ := List.mem_map.mp h
  obtain ⟨k, hk, hke⟩ := List.mem_iff_getElem.mp he
  simp only [List.length_zip, List.length_range, Nat.min_self] at hk
  simp only [List.getElem_zip, List.getElem_range, Prod.mk.injEq] at hke
  obtain ⟨rfl, rfl⟩ := hke
  simp only [Prod.mk.injEq] at hf
  obtain ⟨rfl, rfl, rfl⟩ := hf
  exact ⟨k, hk, rfl, rfl, rfl⟩

/-- Exact HOL `distinct_make_funcs` (`crep_to_loopProofScript.sml:3757-3758`):
    `!crep_code. distinct_funcs (make_funcs crep_code)`. The exact tagged
    `make_funcs_def` dependency carries the reviewed finite-support result
    translation and lookup witness. Its map is consumed by the exact tagged
    `crepToLoopDistinctFuncsExact`, whose standalone finite-support parameter
    has its own canonical roundtrip witness. All three program tuple components
    remain polymorphic and no equality typeclass or other premise is added. -/
@[hol "cakeml/pancake/proofs/crep_to_loopProofScript.sml" "distinct_make_funcs"]
theorem distinct_make_funcs {α β γ : Type} :
    ∀ (crep_code : List (α × List β × γ)),
      crepToLoopDistinctFuncsExact (crepToLoopMakeFuncsExactHOL crep_code) := by
  letI : DecidableEq α := fun a b => Classical.propDecidable (a = b)
  intro crep_code x y n m rm rm' hx hy hnm
  change (crepToLoopMakeFuncsExactHOL crep_code).lookup x = some (n, rm) at hx
  change (crepToLoopMakeFuncsExactHOL crep_code).lookup y = some (m, rm') at hy
  rw [holFmapAsFiniteSupportResultWitness_crepToLoopMakeFuncsExactHOL crep_code x] at hx
  rw [holFmapAsFiniteSupportResultWitness_crepToLoopMakeFuncsExactHOL crep_code y] at hy
  obtain ⟨i, hi, rfl, rfl, _⟩ := makeFuncsExact_entry_mem crep_code x n rm
    (flookup_fupdateListHOL_reverse_mem _ _ _ hx)
  obtain ⟨j, hj, rfl, hm, _⟩ := makeFuncsExact_entry_mem crep_code y m rm'
    (flookup_fupdateListHOL_reverse_mem _ _ _ hy)
  have : i = j := by omega
  subst this
  rfl

/-- Flapjack proof infrastructure: a key occurring in an association list's
    first projections occurs in the domain of its `sptFromAList` tree. HOL's
    `make_funcs_domain_compile_prog` is the result theorem below; this generic
    list-to-tree membership step has no standalone HOL declaration. -/
private theorem sptFromAList_mem_key {β : Type} :
    ∀ (entries : List (Nat × β)) (key : Nat),
      key ∈ entries.map Prod.fst → sptMem key (sptFromAList entries)
  | [], _, h => by simp at h
  | (headKey, headValue) :: entries, key, h => by
      simp only [List.map_cons, List.mem_cons] at h
      change sptMem key (sptInsert headKey headValue (sptFromAList entries))
      rw [sptMem_sptInsert]
      rcases h with hhead | htail
      · exact Or.inl hhead
      · exact Or.inr (sptFromAList_mem_key entries key htail)

/-- Exact HOL `make_funcs_domain_compile_prog`
    (`crep_to_loopProofScript.sml:3908-3918`): if `make_funcs` maps `start` to
    label `lc` with zero parameters, then that label is in the domain of the
    association-list tree built from `compile_prog`. The map result uses the
    canonical finite-support `make_funcs` port; `domain`/`fromAList` are the
    exact `sptMem`/`sptFromAList` rendering, and `compile_prog` is the tagged
    `compileProgHOLExact`. -/
@[hol "cakeml/pancake/proofs/crep_to_loopProofScript.sml" "make_funcs_domain_compile_prog"
  (words_as_type_indexed_bitvec)]
theorem makeFuncsDomainCompileProgExact {width : Nat} [NeZero width] :
    ∀ (start : Basis.Pure.MlString.MlString) (lc : Nat)
      (crep_code : List (Basis.Pure.MlString.MlString × List Nat × CrepProgHOL width))
      (c : Compiler.Encoders.Asm.AsmArchitecture),
      (crepToLoopMakeFuncsExactHOL crep_code).lookup start = some (lc, 0) →
        sptMem lc (sptFromAList (compileProgHOLExact c crep_code)) := by
  intro start lc crep_code c h
  letI : DecidableEq Basis.Pure.MlString.MlString :=
    fun a b => Classical.propDecidable (a = b)
  rw [holFmapAsFiniteSupportResultWitness_crepToLoopMakeFuncsExactHOL crep_code start] at h
  have hentry : (start, (lc, 0)) ∈
      (crep_code.zip (List.range crep_code.length)).map
        (fun entry => (entry.1.1, (firstLoopName + entry.2, entry.1.2.1.length))) :=
    flookup_fupdateListHOL_reverse_mem _ _ _ h
  obtain ⟨i, hi, _, hlc, _⟩ := makeFuncsExact_entry_mem crep_code start lc 0 hentry
  have hkeys : (compileProgHOLExact c crep_code).map Prod.fst =
      (List.range crep_code.length).map (fun i => i + firstLoopName) := by
    simp only [compileProgHOLExact]
    exact map_fst_zipWith_pair _ _ _ (by simp)
  have hkey : lc ∈ (compileProgHOLExact c crep_code).map Prod.fst := by
    rw [hkeys]
    apply List.mem_map.mpr
    refine ⟨i, List.mem_range.mpr hi, ?_⟩
    calc
      i + firstLoopName = firstLoopName + i := Nat.add_comm _ _
      _ = lc := hlc.symm
  exact sptFromAList_mem_key (compileProgHOLExact c crep_code) lc hkey

/-- Local total rendering of HOL `EL` on a fully polymorphic triple list. HOL
    `EL` unfolds via `HD`/`TL` (`listScript.sml:225-228`), so for an
    out-of-range index it is `HD [] = ARB`: HOL's `ARB` is a *fixed*
    Hilbert-choice element `@x. T` of the (necessarily nonempty) HOL type, not a
    universally quantified one. This rendering therefore returns the type's
    canonical Lean inhabitant `default` out of range, discharging HOL's implicit
    type nonemptiness with the standard `Inhabited` instance (the same
    translation used for `dimindex` positivity elsewhere via `[NeZero]`). The
    two agree exactly on in-range indices, and the exact theorem below proves
    its own index is in range, so the default is never observed here. This
    helper is proof infrastructure, not a separately tagged HOL declaration. -/
private def initialProgEL {α β γ : Type} [Inhabited (α × List β × γ)]
    (prog : List (α × List β × γ)) (n : Nat) : α × List β × γ :=
  (prog[n]?).getD default

private theorem initialProgEL_eq_getElem {α β γ : Type} [Inhabited (α × List β × γ)]
    (prog : List (α × List β × γ)) (n : Nat) (hn : n < prog.length) :
    initialProgEL prog n = prog[n]'hn := by
  simp [initialProgEL, hn]

/-- Exact HOL `initial_prog_make_funcs_el`
    (`crep_to_loopProofScript.sml:3942-3945`). HOL binds `prog : ('a # 'b list #
    'c) list`, `start : 'a`, `n : num` — all three tuple components and the key
    are fully polymorphic — assumes `FLOOKUP (make_funcs prog) start = SOME
    (n + first_name,0)`, and concludes `(start,[],(SND o SND) (EL n prog)) =
    EL n prog /\ n < LENGTH prog`. Lean keeps HOL's leading binder order
    `prog, start, n` and the conclusion order over the same right-associated
    triple, with `make_funcs` the tagged exact finite-support
    `crepToLoopMakeFuncsExactHOL` and `first_name` the tagged `firstLoopName`.
    HOL `EL` is rendered by `initialProgEL prog n`, which returns the type's
    canonical Lean inhabitant `default` only out of range (HOL's `ARB` is the
    fixed Hilbert-choice element of the nonempty HOL type, translated by the
    standard `Inhabited` instance, not by a universally quantified fallback
    binder); the conclusion itself establishes `n < prog.length`, and
    `initialProgEL_eq_getElem` shows the two agree on that in-range index, so
    the default is never observed. Lean's only extra binder is that `Inhabited`
    instance, the standard discharge of HOL's implicit type nonemptiness. No
    representation qualifier is needed: no word, finite-map or fixed-name
    carrier appears in the statement. -/
@[hol "cakeml/pancake/proofs/crep_to_loopProofScript.sml" "initial_prog_make_funcs_el"]
theorem initialProgMakeFuncsElExact {α β γ : Type} [Inhabited (α × List β × γ)] :
    ∀ (prog : List (α × List β × γ)) (start : α) (n : Nat),
      (crepToLoopMakeFuncsExactHOL prog).lookup start =
          some (n + firstLoopName, 0) →
        (start, [], (initialProgEL prog n).2.2) =
            initialProgEL prog n ∧
          n < prog.length := by
  intro prog start n hlookup
  letI : DecidableEq α := fun a b => Classical.propDecidable (a = b)
  rw [holFmapAsFiniteSupportResultWitness_crepToLoopMakeFuncsExactHOL prog start]
    at hlookup
  have hentry : (start, (n + firstLoopName, 0)) ∈
      (prog.zip (List.range prog.length)).map
        (fun entry => (entry.1.1, (firstLoopName + entry.2,
          entry.1.2.1.length))) :=
    flookup_fupdateListHOL_reverse_mem _ _ _ hlookup
  obtain ⟨i, hi, hname, hlabel, hparamsLength⟩ :=
    makeFuncsExact_entry_mem prog start (n + firstLoopName) 0 hentry
  have hindex : i = n := by omega
  have hn : n < prog.length := by omega
  have hnameN : start = (prog[n]'hn).1 := by
    simpa [hindex] using hname
  have hparamsLengthN : ((prog[n]'hn).2.1).length = 0 := by
    simpa [hindex] using hparamsLength.symm
  have hparamsN : (prog[n]'hn).2.1 = [] := List.eq_nil_of_length_eq_zero hparamsLengthN
  have hshape : (start, [], (prog[n]'hn).2.2) = prog[n]'hn := by
    apply Prod.ext
    · exact hnameN
    · apply Prod.ext
      · exact hparamsN.symm
      · rfl
  rw [initialProgEL_eq_getElem prog n hn]
  exact ⟨hshape, hn⟩

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
