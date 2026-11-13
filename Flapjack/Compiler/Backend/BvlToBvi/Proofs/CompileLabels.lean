module
public import Flapjack.Compiler.Backend.BvlToBvi.Proofs.CodeLabels
public import Flapjack.Compiler.Backend.BvlToBvi.SourceProgram
import all Flapjack.Compiler.Backend.BvlToBvi.Stubs
public import Flapjack.Compiler.Backend.BviLet.Proofs.CodeLabels
import all Flapjack.Compiler.Backend.BvlToBvi.SourceSing
public import Flapjack.Compiler.Backend.BvlToBvi.Proofs.AuxNameRange
import Flapjack.Compiler.Backend.Semantics.BvlProps.CodeLabels
import Lean.Elab.Tactic.Omega

@[expose] public section

/-! Full code-label bounds for BVL-to-BVI expression compilation. -/
namespace Flapjack.Compiler.Backend.BvlToBvi.Proofs
open Flapjack.Compiler.Backend.BviLet.Proofs

private def auxLabels (aux : AppList (Nat × Nat × Bvi.Exp)) : Set Nat :=
  ⋃₀ (BviProps.getCodeLabels '' {e | e ∈ (appListAppend aux).map (fun p => p.2.2)})

private theorem auxLabels_fresh (n arity : Nat) (body : Bvi.Exp) :
    auxLabels (compileAuxSource (n, arity, body)) = BviProps.getCodeLabels body := by
  ext label
  simp [auxLabels, compileAuxSource, appListAppend, appendAux, ← BviLet.compileExp_eq,
    compileExp_codeLabels]

private theorem auxLabels_append (a b : AppList (Nat × Nat × Bvi.Exp)) :
    auxLabels (smartAppend a b) = auxLabels a ∪ auxLabels b := by
  ext label
  simp [auxLabels, appListAppend_smartAppend, or_and_right, exists_or]

private def labelBound (start finish : Nat) (source : Set Nat) (x y : Nat) : Set Nat :=
  ((fun n => bvlNumStubs + n * bvlToBviNamespaces) '' source) ∪
  {label | ∃ k, label = bvlNumStubs + (k * bvlToBviNamespaces + 1) ∧ start ≤ k ∧ k < finish} ∪
  {label | label ∈ (stubs x y).map Prod.fst}

private theorem labelBound_mono {s t u v : Nat} {a b : Set Nat} {x y : Nat}
    (lower : s ≤ t) (upper : u ≤ v) (included : a ⊆ b) :
    labelBound t u a x y ⊆ labelBound s v b x y := by
  intro label member
  simp only [labelBound, Set.mem_union, Set.mem_image, Set.mem_ofPred_eq] at member ⊢
  rcases member with (⟨k, mem, eq⟩ | ⟨k, eq, lo, hi⟩) | stub
  · exact Or.inl (Or.inl ⟨k, included mem, eq⟩)
  · exact Or.inl (Or.inr ⟨k, eq, by omega, by omega⟩)
  · exact Or.inr stub

private theorem auxLabels_nil : auxLabels (.nil : AppList (Nat × Nat × Bvi.Exp)) = ∅ := by
  ext label
  simp [auxLabels, appListAppend, appendAux]

mutual
private theorem singBound (start : Nat) (exp : Bvl.Exp) (x y : Nat) :
    BviProps.getCodeLabels (compileSingSource start exp).1 ∪
      auxLabels (compileSingSource start exp).2.1 ⊆
    labelBound start (compileSingSource start exp).2.2 (BvlProps.getCodeLabels exp) x y := by
  cases exp with
  | var v => simp [compileSingSource.eq_1, BviProps.getCodeLabels, BvlProps.getCodeLabels, auxLabels_nil]
  | force loc v =>
    simp [compileSingSource.eq_2, BviProps.getCodeLabels, BvlProps.getCodeLabels, auxLabels_nil,
      labelBound, Nat.mul_comm]
  | raise e =>
    rcases h : compileSingSource start e with ⟨out, aux, next⟩
    have ih := singBound start e x y
    simpa [compileSingSource.eq_4, h, BviProps.getCodeLabels, BvlProps.getCodeLabels] using ih
  | tick e =>
    rcases h : compileSingSource start e with ⟨out, aux, next⟩
    have ih := singBound start e x y
    simpa [compileSingSource.eq_5, h, BviProps.getCodeLabels, BvlProps.getCodeLabels] using ih
  | ifThenElse a b c =>
    rcases ha : compileSingSource start a with ⟨a', aa, n1⟩
    rcases hb : compileSingSource n1 b with ⟨b', ab, n2⟩
    rcases hc : compileSingSource n2 c with ⟨c', ac, n3⟩
    have ia := singBound start a x y
    have ib := singBound n1 b x y
    have ic := singBound n2 c x y
    simp only [ha] at ia
    simp only [hb] at ib
    simp only [hc] at ic
    have h1 := auxNameRange_mono (compileSingSource_auxNameRange start a)
    have h2 := auxNameRange_mono (compileSingSource_auxNameRange n1 b)
    have h3 := auxNameRange_mono (compileSingSource_auxNameRange n2 c)
    simp only [ha] at h1
    simp only [hb] at h2
    simp only [hc] at h3
    let src := BvlProps.getCodeLabels a ∪ BvlProps.getCodeLabels b ∪ BvlProps.getCodeLabels c
    have ba := (labelBound_mono (s := start) (t := start) (u := n1) (v := n3)
      (a := BvlProps.getCodeLabels a) (b := src) (by omega) (by omega)
      (by intro l h; exact Or.inl (Or.inl h))).trans' ia
    have bb := (labelBound_mono (s := start) (t := n1) (u := n2) (v := n3)
      (a := BvlProps.getCodeLabels b) (b := src) (by omega) (by omega)
      (by intro l h; exact Or.inl (Or.inr h))).trans' ib
    have bc := (labelBound_mono (s := start) (t := n2) (u := n3) (v := n3)
      (a := BvlProps.getCodeLabels c) (b := src) (by omega) (by omega)
      (by intro l h; exact Or.inr h)).trans' ic
    simp only [compileSingSource.eq_3, ha, hb, hc, BviProps.getCodeLabels,
      BvlProps.getCodeLabels, auxLabels_append]
    change _ ⊆ labelBound start n3 src x y
    intro label member
    rcases member with ((pa | pb) | pc) | ((qa | qb) | qc)
    · exact ba (Or.inl pa)
    · exact bb (Or.inl pb)
    · exact bc (Or.inl pc)
    · exact ba (Or.inr qa)
    · exact bb (Or.inr qb)
    · exact bc (Or.inr qc)
  | «let» xs body =>
    cases xs with
    | nil =>
      rcases ha : compileListSource start (destLet body).1 with ⟨args, a, n1⟩
      rcases hb : compileSingSource n1 (destLet body).2 with ⟨inner, b, n2⟩
      have ia := listBound start (destLet body).1 x y
      have ib := singBound n1 (destLet body).2 x y
      simp only [ha] at ia
      simp only [hb] at ib
      have h1 := auxNameRange_mono (compileListSource_auxNameRange start (destLet body).1)
      have h2 := auxNameRange_mono (compileSingSource_auxNameRange n1 (destLet body).2)
      simp only [ha] at h1
      simp only [hb] at h2
      have dest := destLet_codeLabels body (destLet body).1 (destLet body).2 (by cases h : destLet body; rfl)
      rw [← BvlProps.getCodeLabelsList_eq] at dest
      have ba := (labelBound_mono (s := start) (t := start) (u := n1) (v := n2 + 1)
        (a := BvlProps.getCodeLabelsList (destLet body).1) (b := BvlProps.getCodeLabels body)
        (by omega) (by omega) (by intro l h; exact dest (Or.inl h))).trans' ia
      have bb := (labelBound_mono (s := start) (t := n1) (u := n2) (v := n2 + 1)
        (a := BvlProps.getCodeLabels (destLet body).2) (b := BvlProps.getCodeLabels body)
        (by omega) (by omega) (by intro l h; exact dest (Or.inr h))).trans' ib
      simp only [compileSingSource.eq_8, List.isEmpty_nil, ↓reduceIte, ha, hb,
        BviProps.getCodeLabels, BvlProps.getCodeLabels, BvlProps.getCodeLabelsList,
        Set.empty_union, Set.union_empty, auxLabels_append, auxLabels_fresh]
      intro label member
      rcases member with (fresh | arg) | ((auxa | auxb) | innerLabel)
      · simp only [Set.mem_singleton_iff] at fresh
        subst label
        simp only [labelBound, Set.mem_union, Set.mem_ofPred_eq]
        exact Or.inl (Or.inr ⟨n2, by simp [Nat.mul_comm, Nat.add_assoc], by omega, by omega⟩)
      · exact ba (Or.inl arg)
      · exact ba (Or.inr auxa)
      · exact bb (Or.inr auxb)
      · exact bb (Or.inl innerLabel)
    | cons e es =>
      rcases ha : compileListSource start (e :: es) with ⟨args, a, n1⟩
      rcases hb : compileSingSource n1 body with ⟨body', b, n2⟩
      have ia := listBound start (e :: es) x y
      have ib := singBound n1 body x y
      simp only [ha] at ia
      simp only [hb] at ib
      have h1 := auxNameRange_mono (compileListSource_auxNameRange start (e :: es))
      have h2 := auxNameRange_mono (compileSingSource_auxNameRange n1 body)
      simp only [ha] at h1
      simp only [hb] at h2
      let src := BvlProps.getCodeLabelsList (e :: es) ∪ BvlProps.getCodeLabels body
      have ba := (labelBound_mono (s := start) (t := start) (u := n1) (v := n2)
        (a := BvlProps.getCodeLabelsList (e :: es)) (b := src) (by omega) (by omega)
        Set.subset_union_left).trans' ia
      have bb := (labelBound_mono (s := start) (t := n1) (u := n2) (v := n2)
        (a := BvlProps.getCodeLabels body) (b := src) (by omega) (by omega)
        Set.subset_union_right).trans' ib
      simp only [compileSingSource.eq_8, List.isEmpty_cons, Bool.false_eq_true, ↓reduceIte,
        ha, hb, BviProps.getCodeLabels, BvlProps.getCodeLabels, auxLabels_append]
      change _ ⊆ labelBound start n2 src x y
      intro label member
      rcases member with (pa | pb) | (qa | qb)
      · exact ba (Or.inl pa)
      · exact bb (Or.inl pb)
      · exact ba (Or.inr qa)
      · exact bb (Or.inr qb)
  | handle body handler =>
    rcases ha : compileListSource start (destLet body).1 with ⟨args, a, n1⟩
    rcases hb : compileSingSource n1 (destLet body).2 with ⟨inner, b, n2⟩
    rcases hc : compileSingSource n2 handler with ⟨hand, c, n3⟩
    have ia := listBound start (destLet body).1 x y
    have ib := singBound n1 (destLet body).2 x y
    have ic := singBound n2 handler x y
    simp only [ha] at ia
    simp only [hb] at ib
    simp only [hc] at ic
    have h1 := auxNameRange_mono (compileListSource_auxNameRange start (destLet body).1)
    have h2 := auxNameRange_mono (compileSingSource_auxNameRange n1 (destLet body).2)
    have h3 := auxNameRange_mono (compileSingSource_auxNameRange n2 handler)
    simp only [ha] at h1
    simp only [hb] at h2
    simp only [hc] at h3
    have dest := destLet_codeLabels body (destLet body).1 (destLet body).2 (by cases h : destLet body; rfl)
    rw [← BvlProps.getCodeLabelsList_eq] at dest
    let src := BvlProps.getCodeLabels body ∪ BvlProps.getCodeLabels handler
    have ba := (labelBound_mono (s := start) (t := start) (u := n1) (v := n3 + 1)
      (a := BvlProps.getCodeLabelsList (destLet body).1) (b := src)
      (by omega) (by omega) (by intro l h; exact Or.inl (dest (Or.inl h)))).trans' ia
    have bb := (labelBound_mono (s := start) (t := n1) (u := n2) (v := n3 + 1)
      (a := BvlProps.getCodeLabels (destLet body).2) (b := src)
      (by omega) (by omega) (by intro l h; exact Or.inl (dest (Or.inr h)))).trans' ib
    have bc := (labelBound_mono (s := start) (t := n2) (u := n3) (v := n3 + 1)
      (a := BvlProps.getCodeLabels handler) (b := src)
      (by omega) (by omega) Set.subset_union_right).trans' ic
    simp only [compileSingSource.eq_9, ha, hb, hc, BviProps.getCodeLabels,
      BvlProps.getCodeLabels, auxLabels_append, auxLabels_fresh]
    change _ ⊆ labelBound start (n3 + 1) src x y
    intro label member
    rcases member with ((fresh | handLabel) | arg) | (((auxa | auxb) | auxc) | innerLabel)
    · simp only [Set.mem_singleton_iff] at fresh
      subst label
      simp only [labelBound, Set.mem_union, Set.mem_ofPred_eq]
      exact Or.inl (Or.inr ⟨n3, by simp [Nat.mul_comm, Nat.add_assoc], by omega, by omega⟩)
    · exact bc (Or.inl handLabel)
    · exact ba (Or.inl arg)
    · exact ba (Or.inr auxa)
    · exact bb (Or.inr auxb)
    · exact bc (Or.inr auxc)
    · exact bb (Or.inl innerLabel)
  | op op xs =>
    rcases hc : compileListSource start xs with ⟨out, aux, next⟩
    have ih := listBound start xs x y
    simp only [hc] at ih
    have lifted := (labelBound_mono (s := start) (t := start) (u := next) (v := next)
      (a := BvlProps.getCodeLabelsList xs)
      (b := ClosLang.assignGetCodeLabel op ∪ BvlProps.getCodeLabelsList xs)
      (by omega) (by omega) Set.subset_union_right).trans' ih
    have oper := compileOp_codeLabels op out x y
    rw [← BviProps.getCodeLabelsList_eq] at oper
    simp only [compileSingSource.eq_6, hc, BvlProps.getCodeLabels]
    intro label member
    rcases member with labelOp | labelAux
    · rcases oper labelOp with (inArgs | inOp) | inStub
      · exact lifted (Or.inl inArgs)
      · simp only [labelBound, Set.mem_union, Set.mem_image] at *
        obtain ⟨n, hn, rfl⟩ := inOp
        exact Or.inl (Or.inl ⟨n, Or.inl hn, rfl⟩)
      · exact Or.inr inStub
    · exact lifted (Or.inr labelAux)
  | call ticks dest xs =>
    rcases hc : compileListSource start xs with ⟨out, aux, next⟩
    have ih := listBound start xs x y
    simp only [hc] at ih
    cases dest with
    | none =>
      simp only [compileSingSource.eq_7, hc, Option.map_none,
        BviProps.getCodeLabels, BvlProps.getCodeLabels, Set.empty_union]
      exact ih
    | some loc =>
      have lifted := (labelBound_mono (s := start) (t := start) (u := next) (v := next)
        (a := BvlProps.getCodeLabelsList xs)
        (b := {loc} ∪ BvlProps.getCodeLabelsList xs)
        (by omega) (by omega) Set.subset_union_right).trans' ih
      simp only [compileSingSource.eq_7, hc, Option.map_some, BviProps.getCodeLabels,
        BvlProps.getCodeLabels, Set.union_empty]
      intro label member
      rcases member with (destLabel | argLabel) | auxLabel
      · simp only [Set.mem_singleton_iff] at destLabel
        subst label
        simp only [labelBound, Set.mem_union, Set.mem_image, Set.mem_singleton_iff]
        exact Or.inl (Or.inl ⟨loc, Or.inl rfl, by simp [Nat.mul_comm]⟩)
      · exact lifted (Or.inl argLabel)
      · exact lifted (Or.inr auxLabel)
termination_by expBudget exp
decreasing_by
  all_goals try simp only [expBudget.eq_3, expBudget.eq_4,
    expBudget.eq_5, expBudget.eq_6, expBudget.eq_7, expBudget.eq_8, expBudget.eq_9]
  all_goals try (have := destLetBudget body)
  all_goals omega

private theorem listBound (start : Nat) (xs : List Bvl.Exp) (x y : Nat) :
    BviProps.getCodeLabelsList (compileListSource start xs).1 ∪
      auxLabels (compileListSource start xs).2.1 ⊆
    labelBound start (compileListSource start xs).2.2 (BvlProps.getCodeLabelsList xs) x y := by
  cases xs with
  | nil => simp [compileListSource.eq_1, BviProps.getCodeLabelsList, BvlProps.getCodeLabelsList, auxLabels_nil]
  | cons e es =>
    rcases hx : compileSingSource start e with ⟨out, a, mid⟩
    rcases ht : compileListSource mid es with ⟨outs, b, finish⟩
    have ihx := singBound start e x y
    have iht := listBound mid es x y
    simp only [hx] at ihx
    simp only [ht] at iht
    have lo := auxNameRange_mono (compileSingSource_auxNameRange start e)
    have hi := auxNameRange_mono (compileListSource_auxNameRange mid es)
    simp only [hx] at lo
    simp only [ht] at hi
    have bx := (labelBound_mono (s := start) (t := start) (u := mid) (v := finish)
      (a := BvlProps.getCodeLabels e)
      (b := BvlProps.getCodeLabels e ∪ BvlProps.getCodeLabelsList es)
      (by omega) hi (Set.subset_union_left)).trans' ihx
    have bt := (labelBound_mono (s := start) (t := mid) (u := finish) (v := finish)
      (a := BvlProps.getCodeLabelsList es)
      (b := BvlProps.getCodeLabels e ∪ BvlProps.getCodeLabelsList es)
      lo (by omega) (Set.subset_union_right)).trans' iht
    simp only [compileListSource.eq_2, hx, ht, BviProps.getCodeLabelsList,
      BvlProps.getCodeLabelsList, auxLabels_append]
    intro label member
    simp only [Set.mem_union] at member bx bt
    rcases member with (p | q) | (r | s)
    · exact bx (Or.inl p)
    · exact bt (Or.inl q)
    · exact bx (Or.inr r)
    · exact bt (Or.inr s)
termination_by listBudget xs
decreasing_by all_goals simp only [listBudget.eq_2]; omega
end

/-- Compiled expressions and auxiliary bodies reference only translated source
labels, freshly allocated auxiliary labels, and stub labels. -/
@[hol "cakeml/compiler/backend/proofs/bvl_to_bviProofScript.sml" "compile_exps_get_code_labels"]
theorem compileExps_getCodeLabels (n : Nat) (xs : List Bvl.Exp) (ys : List Bvi.Exp)
    (aux : AppList (Nat × Nat × Bvi.Exp)) (m x y : Nat)
    (compiled : compileListSource n xs = (ys, aux, m)) :
    (⋃₀ (BviProps.getCodeLabels '' {e | e ∈ ys})) ∪
      (⋃₀ (BviProps.getCodeLabels '' {e | e ∈ (appListAppend aux).map (fun p => p.2.2)})) ⊆
    ((fun k => bvlNumStubs + k * bvlToBviNamespaces) ''
      (⋃₀ (BvlProps.getCodeLabels '' {e | e ∈ xs}))) ∪
    {label | ∃ k, label = bvlNumStubs + (k * bvlToBviNamespaces + 1) ∧ n ≤ k ∧ k < m} ∪
    {label | label ∈ (stubs x y).map Prod.fst} := by
  rw [← BviProps.getCodeLabelsList_eq, ← BvlProps.getCodeLabelsList_eq]
  have result := listBound n xs x y
  simp only [compiled] at result
  exact result

/-- Compiling a labeled function references only translated source labels,
emitted code labels, and stub labels. -/
@[hol "cakeml/compiler/backend/proofs/bvl_to_bviProofScript.sml" "compile_single_get_code_labels"]
theorem compileSingle_getCodeLabels (n : Nat) (p : Nat × Nat × Bvl.Exp)
    (code : AppList (Nat × Nat × Bvi.Exp)) (m x y : Nat)
    (compiled : compileSingleSource n p = (code, m)) :
    (⋃₀ (BviProps.getCodeLabels '' {e | e ∈ (appListAppend code).map (fun q => q.2.2)})) ⊆
      ((fun k => bvlNumStubs + k * bvlToBviNamespaces) '' BvlProps.getCodeLabels p.2.2) ∪
      {label | label ∈ (appListAppend code).map Prod.fst} ∪
      {label | label ∈ (stubs x y).map Prod.fst} := by
  rcases p with ⟨name, arity, body⟩
  rcases h : compileSingSource n body with ⟨out, aux, next⟩
  have singleton : compileListSource n [body] = ([out], aux, next) := by
    simp only [compileListSource.eq_2, h, compileListSource.eq_1]
    cases aux <;> rfl
  have bound := compileExps_getCodeLabels n [body] [out] aux next x y singleton
  have fresh := compileExps_auxContains n [body] [out] aux next singleton
  simp only [compileSingleSource, h, Prod.mk.injEq] at compiled
  rcases compiled with ⟨rfl, rfl⟩
  simp only [appListAppend_smartAppend] at *
  simp [appListAppend, appendAux, ← BviLet.compileExp_eq, compileExp_codeLabels] at *
  constructor
  · intro label member
    have result := bound.1 member
    simp only [Set.mem_union, Set.mem_ofPred_eq] at result ⊢
    rcases result with (src | ⟨k, eq, lo, hi⟩) | stub
    · exact Or.inl (Or.inl src)
    · exact Or.inl (Or.inr (Or.inr (fresh label k eq lo hi)))
    · exact Or.inr stub
  · intro i i1 i2 member label inside
    have result := bound.2 i i1 i2 member inside
    simp only [Set.mem_union, Set.mem_ofPred_eq] at result ⊢
    rcases result with (src | ⟨k, eq, lo, hi⟩) | stub
    · exact Or.inl (Or.inl src)
    · exact Or.inl (Or.inr (Or.inr (fresh label k eq lo hi)))
    · exact Or.inr stub

/-- Compiling a list preserves label closure and does not decrease the
fresh-name counter. -/
@[hol "cakeml/compiler/backend/proofs/bvl_to_bviProofScript.sml" "compile_list_get_code_labels"]
theorem compileList_getCodeLabels (n : Nat) (p : List (Nat × Nat × Bvl.Exp))
    (code : AppList (Nat × Nat × Bvi.Exp)) (m x y : Nat)
    (compiled : compileProgramsSource n p = (code, m)) :
    n ≤ m ∧
    (⋃₀ (BviProps.getCodeLabels '' {e | e ∈ (appListAppend code).map (fun q => q.2.2)})) ⊆
      {label | label ∈ (appListAppend code).map Prod.fst} ∪
      ((fun k => bvlNumStubs + k * bvlToBviNamespaces) ''
        (⋃₀ (BvlProps.getCodeLabels '' {e | e ∈ p.map (fun q => q.2.2)}))) ∪
      {label | label ∈ (stubs x y).map Prod.fst} := by
  have monotone := (compileProgramsSource_nameRange n p).1
  simp only [compiled] at monotone
  refine ⟨monotone, ?_⟩
  induction p generalizing n code m with
  | nil =>
    simp [compileProgramsSource, Prod.mk.injEq] at compiled
    obtain ⟨rfl, rfl⟩ := compiled
    simp [appListAppend, appendAux]
  | cons entry rest ih =>
    rcases h1 : compileSingleSource n entry with ⟨first, mid⟩
    rcases h2 : compileProgramsSource mid rest with ⟨tail, finish⟩
    simp only [compileProgramsSource, h1, h2, Prod.mk.injEq] at compiled
    obtain ⟨rfl, rfl⟩ := compiled
    have one := compileSingle_getCodeLabels n entry first mid x y h1
    have tailMono := (compileProgramsSource_nameRange mid rest).1
    simp only [h2] at tailMono
    have later := ih mid tail finish h2 tailMono
    simp only [appListAppend_smartAppend] at *
    simp at *
    intro i member label inLabel
    simp only [Set.mem_union, Set.mem_image, Set.mem_ofPred_eq, Set.mem_iUnion] at *
    rcases member with ⟨a, b, member⟩ | ⟨a, b, member⟩
    · have h := one i a b member inLabel
      simp only [Set.mem_union, Set.mem_image, Set.mem_ofPred_eq] at h
      rcases h with (⟨k, hk, rfl⟩ | ⟨a, b, member⟩) | stub
      · exact Or.inl (Or.inr ⟨k, Or.inl hk, rfl⟩)
      · exact Or.inl (Or.inl (Or.inl ⟨a, b, member⟩))
      · exact Or.inr stub
    · have h := later i a b member inLabel
      simp only [Set.mem_union, Set.mem_image, Set.mem_ofPred_eq, Set.mem_iUnion] at h
      rcases h with (⟨a, b, member⟩ | ⟨k, hk, rfl⟩) | stub
      · exact Or.inl (Or.inl (Or.inr ⟨a, b, member⟩))
      · exact Or.inl (Or.inr ⟨k, Or.inr hk, rfl⟩)
      · exact Or.inr stub

private theorem stubsLabels (start count : Nat) :
    (⋃₀ (BviProps.getCodeLabels '' {e | e ∈ (stubs start count).map (fun q => q.2.2)})) ⊆
      {start} ∪ {label | label ∈ (stubs start count).map Prod.fst} := by
  simp [stubs, allocGlobalCode, copyGlobalsCode, initGlobalsCode, listLengthCode,
    fromListByteCode, toListByteCode, sumListLengthCode, concatByteCode,
    BviProps.getCodeLabels, BviProps.getCodeLabelsList, ClosLang.assignGetCodeLabel,
    int, el, add, sub]
  simp only [Set.subset_def, Set.mem_insert_iff, Set.mem_ofPred_eq]; aesop

/-- The whole-program compiler references only emitted code labels, translated
source labels, and its entry label. -/
@[hol "cakeml/compiler/backend/proofs/bvl_to_bviProofScript.sml" "compile_prog_get_code_labels"]
theorem compileProg_getCodeLabels (s n : Nat) (p : List (Nat × Nat × Bvl.Exp))
    (t : Nat) (q : List (Nat × Nat × Bvi.Exp)) (m : Nat)
    (compiled : compileProgSource s n p = (t, q, m)) :
    (⋃₀ (BviProps.getCodeLabels '' {e | e ∈ q.map (fun z => z.2.2)})) ⊆
      insert (bvlNumStubs + s * bvlToBviNamespaces)
        ({label | label ∈ q.map Prod.fst} ∪
          ((fun k => bvlNumStubs + k * bvlToBviNamespaces) ''
            (⋃₀ (BvlProps.getCodeLabels '' {e | e ∈ p.map (fun z => z.2.2)})))) := by
  rw [← Set.insert_union]
  rcases h : compileProgramsSource n p with ⟨code, next⟩
  have tail := (compileList_getCodeLabels n p code next
    (bvlNumStubs + bvlToBviNamespaces * s) (allocGlobCount (p.map fun z => z.2.2)) h).2
  have stub := stubsLabels (bvlNumStubs + bvlToBviNamespaces * s) (allocGlobCount (p.map fun z => z.2.2))
  simp only [compileProgSource, h, Prod.mk.injEq] at compiled
  rcases compiled with ⟨rfl, rfl, rfl⟩
  simp at *
  intro i member label inside
  simp only [Set.mem_union, Set.mem_insert_iff, Set.mem_ofPred_eq] at *
  rcases member with ⟨a, b, member⟩ | ⟨a, b, member⟩
  · have h := stub i a b member inside
    simp only [Set.mem_insert_iff, Set.mem_ofPred_eq] at h
    rcases h with h | ⟨a, b, h⟩
    · exact Or.inl (Or.inl (by simpa [Nat.mul_comm] using h))
    · exact Or.inl (Or.inr (Or.inl ⟨a, b, h⟩))
  · have h := tail i a b member inside
    simp only [Set.mem_union, Set.mem_ofPred_eq] at h
    rcases h with (⟨a, b, h⟩ | source) | ⟨a, b, h⟩
    · exact Or.inl (Or.inr (Or.inr ⟨a, b, h⟩))
    · exact Or.inr source
    · exact Or.inl (Or.inr (Or.inl ⟨a, b, h⟩))

end Flapjack.Compiler.Backend.BvlToBvi.Proofs
