import Flapjack.HolRef
import Flapjack.Compiler.Backend.LinearScan.Proofs.Bijection
import Flapjack.Compiler.Backend.LinearScan.Proofs.RegExchange

/-!
# linear_scanProof: checking a renamed clash tree

Ports of `linear_scanProofScript.sml:5565-6006`: colour checking commutes with
the register bijection, `extract_coloration` reads back the colouring,
and the checkers only depend on the colouring at the names they inspect.
Renderings as in `LiveTree` and `Bijection`; HOL free variables (`bijdom`,
`bijcodom`, `appbij`, `appinvbij`, `f`) are quantified first.
-/

namespace Flapjack.LinearScan

open Flapjack.RegAlloc Flapjack.Translator.Monadic.MonadBase

/-- The domain of a tree rebuilt by inserting `g` of every key (Flapjack
helper behind `domain_apply_bij_set`). -/
private theorem domainFoldiInsert {α : Type} (g : Nat → Nat) (s : Spt α) :
    sptDomain (sptFoldiGen (fun r _ acc => sptInsert (g r) () acc) 0 .ln s) =
      fun y => ∃ x, sptDomain s x ∧ g x = y := by
  rw [sptFoldiGenFoldrToAList]
  have key : ∀ (l : List (Nat × α)),
      sptDomain (l.foldr (fun p acc => sptInsert (g p.1) () acc) (.ln : NumSet)) =
        fun y => ∃ p, p ∈ l ∧ g p.1 = y := by
    intro l
    induction l with
    | nil => funext y; simp [sptDomain]
    | cons p l ih =>
        rw [List.foldr_cons, sptDomainInsert, ih]
        funext y
        apply propext
        constructor
        · rintro (rfl | ⟨q, hq, rfl⟩)
          · exact ⟨p, List.mem_cons_self, rfl⟩
          · exact ⟨q, List.mem_cons_of_mem _ hq, rfl⟩
        · rintro ⟨q, hq, rfl⟩
          rcases List.mem_cons.mp hq with rfl | hq
          · exact Or.inl rfl
          · exact Or.inr ⟨q, hq, rfl⟩
  rw [key]
  funext y
  apply propext
  constructor
  · rintro ⟨⟨k, v⟩, hp, rfl⟩
    exact ⟨k, (sptMemMapFstToAList s k).mp (List.mem_map_of_mem (f := Prod.fst) hp), rfl⟩
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨⟨k, v⟩, hp, hk⟩ := List.mem_map.mp ((sptMemMapFstToAList s x).mpr hx)
    simp only at hk
    subst hk
    exact ⟨(k, v), hp, rfl⟩

/-- Exact HOL `check_col_apply_bijection` (`linear_scanProofScript.sml:5565-5599`). -/
@[hol "cakeml/compiler/backend/reg_alloc/proofs/linear_scanProofScript.sml"
  "check_col_apply_bijection"]
theorem checkColApplyBijection :
    ∀ (bijdom bijcodom : Nat → Prop) (appbij appinvbij : Nat → Nat) (cutset : NumSet)
      (livein flivein : NumSet) (f : Nat → Nat),
      (∀ r, bijdom r → bijcodom (appbij r) ∧ appinvbij (appbij r) = r) ∧
      (∀ r, bijcodom r → bijdom (appinvbij r) ∧ appbij (appinvbij r) = r) ∧
      (∀ x, sptDomain cutset x → bijdom x) ∧
      checkCol f (sptFoldiGen (fun r _ acc => sptInsert (appbij r) () acc) 0 .ln cutset) =
        some (livein, flivein) →
      ∃ livein' flivein', checkCol (fun r => f (appbij r)) cutset = some (livein', flivein') ∧
        sptDomain livein' = fun y => ∃ x, sptDomain livein x ∧ appinvbij x = y := by
  intro bijdom bijcodom appbij appinvbij cutset livein flivein f ⟨hb1, hb2, hsub, hc⟩
  have hdomT := domainFoldiInsert appbij cutset
  obtain ⟨hdT, hiT⟩ := checkColOutput f _ livein flivein hc
  have hlive : livein = sptFoldiGen (fun r _ acc => sptInsert (appbij r) () acc) 0 .ln cutset := by
    unfold checkCol at hc; dsimp only at hc; split at hc
    · simp only [Option.some.injEq, Prod.mk.injEq] at hc; exact hc.1.symm
    · cases hc
  have hinj : ∀ x y, sptDomain cutset x → sptDomain cutset y →
      f (appbij x) = f (appbij y) → x = y := by
    intro x y hx hy he
    have hx' : sptDomain livein (appbij x) := by rw [hlive, hdomT]; exact ⟨x, hx, rfl⟩
    have hy' : sptDomain livein (appbij y) := by rw [hlive, hdomT]; exact ⟨y, hy, rfl⟩
    have := hiT _ _ hx' hy' he
    rw [← (hb1 x (hsub x hx)).2, ← (hb1 y (hsub y hy)).2, this]
  obtain ⟨fl, hfl⟩ := checkColSuccess (fun r => f (appbij r)) cutset hinj
  refine ⟨cutset, fl, hfl, ?_⟩
  rw [hlive, hdomT]
  funext y
  apply propext
  constructor
  · intro hy; exact ⟨appbij y, ⟨y, hy, rfl⟩, (hb1 y (hsub y hy)).2⟩
  · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    rw [(hb1 x (hsub x hx)).2]; exact hx

/-- Exact HOL `check_partial_col_apply_bijection` (`linear_scanProofScript.sml:5602-5645`). -/
@[hol "cakeml/compiler/backend/reg_alloc/proofs/linear_scanProofScript.sml"
  "check_partial_col_apply_bijection"]
theorem checkPartialColApplyBijection :
    ∀ (bijdom bijcodom : Nat → Prop) (appbij appinvbij f : Nat → Nat) (l : List Nat)
      (live flive live' flive' livein flivein : NumSet),
      (∀ r, bijdom r → bijcodom (appbij r) ∧ appinvbij (appbij r) = r) ∧
      (∀ r, bijcodom r → bijdom (appinvbij r) ∧ appbij (appinvbij r) = r) ∧
      (∀ x, x ∈ l → bijdom x) ∧
      (∀ x, sptDomain live x → bijcodom x) ∧
      sptDomain flive = (fun y => ∃ x, sptDomain live x ∧ f x = y) ∧
      sptDomain flive' = (fun y => ∃ x, sptDomain live' x ∧ (f ∘ appbij) x = y) ∧
      sptDomain live' = (fun y => ∃ x, sptDomain live x ∧ appinvbij x = y) ∧
      (∀ x y, sptDomain live x → sptDomain live y → f x = f y → x = y) ∧
      checkPartialCol f (l.map appbij) live flive = some (livein, flivein) →
      ∃ livein' flivein', checkPartialCol (fun r => f (appbij r)) l live' flive' =
          some (livein', flivein') ∧
        sptDomain livein' = fun y => ∃ x, sptDomain livein x ∧ appinvbij x = y := by
  intro bijdom bijcodom appbij appinvbij f l
  induction l with
  | nil =>
      intro live flive live' flive' livein flivein ⟨_, _, _, _, _, _, hl', _, hc⟩
      simp only [List.map_nil, checkPartialCol, Option.some.injEq, Prod.mk.injEq] at hc
      obtain ⟨rfl, rfl⟩ := hc
      exact ⟨live', flive', rfl, hl'⟩
  | cons h l ih =>
      intro live flive live' flive' livein flivein
        ⟨hb1, hb2, hl, hlive, hfl, hfl', hl', hinj, hc⟩
      have hh := hb1 h (hl h List.mem_cons_self)
      have hfeq : sptDomain flive' = sptDomain flive := by
        rw [hfl', hfl, hl']
        funext y
        apply propext
        constructor
        · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
          exact ⟨x, hx, by simp [Function.comp, (hb2 x (hlive x hx)).2]⟩
        · rintro ⟨x, hx, rfl⟩
          exact ⟨appinvbij x, ⟨x, hx, rfl⟩, by simp [Function.comp, (hb2 x (hlive x hx)).2]⟩
      simp only [List.map_cons] at hc
      cases hlk : sptLookup (appbij h) live with
      | some u =>
          cases u
          have hc' : checkPartialCol f (l.map appbij) live flive = some (livein, flivein) := by
            simpa only [checkPartialCol, hlk] using hc
          have hd : sptDomain live' h := by
            rw [hl']; exact ⟨appbij h, by simp [sptDomain, hlk], hh.2⟩
          have hlk' : sptLookup h live' = some () := by
            unfold sptDomain at hd
            cases e : sptLookup h live' with
            | none => rw [e] at hd; simp at hd
            | some u => cases u; rfl
          obtain ⟨li, fli, hci, hdi⟩ := ih live flive live' flive' livein flivein
            ⟨hb1, hb2, fun x hx => hl x (List.mem_cons_of_mem h hx), hlive, hfl, hfl', hl', hinj, hc'⟩
          exact ⟨li, fli, by simpa only [checkPartialCol, hlk'] using hci, hdi⟩
      | none =>
          cases hfk : sptLookup (f (appbij h)) flive with
          | some _ => simp [checkPartialCol, hlk, hfk] at hc
          | none =>
              have hc' : checkPartialCol f (l.map appbij) (sptInsert (appbij h) () live)
                  (sptInsert (f (appbij h)) () flive) = some (livein, flivein) := by
                simpa only [checkPartialCol, hlk, hfk] using hc
              have hnd : ¬ sptDomain live' h := by
                rw [hl']
                rintro ⟨x, hx, rfl⟩
                have := (hb2 x (hlive x hx)).2
                rw [this] at hlk
                simp [sptDomain, hlk] at hx
              have hlk' : sptLookup h live' = none := by
                cases e : sptLookup h live' with
                | none => rfl
                | some _ => exact absurd (by simp [sptDomain, e]) hnd
              have hfnd : ¬ sptDomain flive' (f (appbij h)) := by
                rw [hfeq]; simp [sptDomain, hfk]
              have hfk' : sptLookup (f (appbij h)) flive' = none := by
                cases e : sptLookup (f (appbij h)) flive' with
                | none => rfl
                | some _ => exact absurd (by simp [sptDomain, e]) hfnd
              have p1 : ∀ x, sptDomain (sptInsert (appbij h) () live) x → bijcodom x := by
                intro x hx
                rw [sptDomainInsert] at hx
                rcases hx with rfl | hx
                · exact hh.1
                · exact hlive x hx
              have p2 : sptDomain (sptInsert (f (appbij h)) () flive) =
                  (fun y => ∃ x, sptDomain (sptInsert (appbij h) () live) x ∧ f x = y) := by
                rw [sptDomainInsert, sptDomainInsert, hfl]
                funext y
                apply propext
                constructor
                · rintro (rfl | ⟨x, hx, rfl⟩)
                  · exact ⟨appbij h, Or.inl rfl, rfl⟩
                  · exact ⟨x, Or.inr hx, rfl⟩
                · rintro ⟨x, hx | hx, rfl⟩
                  · rw [hx]; exact Or.inl rfl
                  · exact Or.inr ⟨x, hx, rfl⟩
              have p3 : sptDomain (sptInsert (f (appbij h)) () flive') =
                  (fun y => ∃ x, sptDomain (sptInsert h () live') x ∧ (f ∘ appbij) x = y) := by
                rw [sptDomainInsert, sptDomainInsert, hfl']
                funext y
                apply propext
                constructor
                · rintro (rfl | ⟨x, hx, rfl⟩)
                  · exact ⟨h, Or.inl rfl, rfl⟩
                  · exact ⟨x, Or.inr hx, rfl⟩
                · rintro ⟨x, hx | hx, rfl⟩
                  · rw [hx]; exact Or.inl rfl
                  · exact Or.inr ⟨x, hx, rfl⟩
              have p4 : sptDomain (sptInsert h () live') =
                  (fun y => ∃ x, sptDomain (sptInsert (appbij h) () live) x ∧ appinvbij x = y) := by
                rw [sptDomainInsert, sptDomainInsert, hl']
                funext y
                apply propext
                constructor
                · rintro (hy | ⟨x, hx, rfl⟩)
                  · exact ⟨appbij h, Or.inl rfl, by rw [hy]; exact hh.2⟩
                  · exact ⟨x, Or.inr hx, rfl⟩
                · rintro ⟨x, hx | hx, rfl⟩
                  · rw [hx, hh.2]; exact Or.inl rfl
                  · exact Or.inr ⟨x, hx, rfl⟩
              have p5 : ∀ x y, sptDomain (sptInsert (appbij h) () live) x →
                  sptDomain (sptInsert (appbij h) () live) y → f x = f y → x = y := by
                intro x y hx hy he
                rw [sptDomainInsert] at hx hy
                have hnf : ∀ z, sptDomain live z → f z ≠ f (appbij h) := by
                  intro z hz e
                  have : sptDomain flive (f (appbij h)) := by rw [hfl]; exact ⟨z, hz, e⟩
                  simp [sptDomain, hfk] at this
                rcases hx with hx | hx <;> rcases hy with hy | hy
                · rw [hx, hy]
                · rw [hx] at he; exact absurd he.symm (hnf y hy)
                · rw [hy] at he; exact absurd he (hnf x hx)
                · exact hinj x y hx hy he
              obtain ⟨li, fli, hci, hdi⟩ := ih (sptInsert (appbij h) () live)
                (sptInsert (f (appbij h)) () flive) (sptInsert h () live')
                (sptInsert (f (appbij h)) () flive') livein flivein
                ⟨hb1, hb2, fun x hx => hl x (List.mem_cons_of_mem h hx), p1, p2, p3, p4, p5, hc'⟩
              exact ⟨li, fli, by simpa only [checkPartialCol, hlk', hfk'] using hci, hdi⟩

/-- Exact HOL `check_clash_tree_output_subset` (`linear_scanProofScript.sml:5647-5674`). -/
@[hol "cakeml/compiler/backend/reg_alloc/proofs/linear_scanProofScript.sml"
  "check_clash_tree_output_subset"]
theorem checkClashTreeOutputSubset :
    ∀ (f : Nat → Nat) (ct : ClashTree) (live flive livein flivein : NumSet),
      checkClashTree f ct live flive = some (livein, flivein) →
      ∀ x, sptDomain livein x → sptDomain live x ∨ inClashTree ct x := by
  intro f ct
  induction ct with
  | delta w r =>
      intro live flive livein flivein hc x hx
      cases hp : checkPartialCol f w live flive with
      | none => simp [checkClashTree, hp] at hc
      | some v =>
          simp only [checkClashTree, hp] at hc
          rw [checkPartialColDomain _ f _ _ (livein, flivein) hc, RegAlloc.domainNumsetListDelete] at hx
          rcases hx with hx | ⟨hx, _⟩
          · exact Or.inr (Or.inr hx)
          · exact Or.inl hx
  | set tree =>
      intro live flive livein flivein hc x hx
      unfold checkClashTree checkCol at hc; dsimp only at hc; split at hc
      · simp only [Option.some.injEq, Prod.mk.injEq] at hc
        rw [← hc.1] at hx; exact Or.inr hx
      · cases hc
  | branch o ct1 ct2 ih1 ih2 =>
      intro live flive livein flivein hc x hx
      cases h1 : checkClashTree f ct1 live flive with
      | none => simp [checkClashTree, h1] at hc
      | some p1 =>
          obtain ⟨l1, f1⟩ := p1
          cases h2 : checkClashTree f ct2 live flive with
          | none => simp [checkClashTree, h1, h2] at hc
          | some p2 =>
              obtain ⟨l2, f2⟩ := p2
              simp only [checkClashTree, h1, h2] at hc
              cases o with
              | none =>
                  simp only at hc
                  rw [checkPartialColBranchDomain f l1 l2 f1 livein flivein hc] at hx
                  rcases hx with hx | hx
                  · rcases ih1 _ _ _ _ h1 x hx with h | h
                    · exact Or.inl h
                    · exact Or.inr (Or.inl h)
                  · rcases ih2 _ _ _ _ h2 x hx with h | h
                    · exact Or.inl h
                    · exact Or.inr (Or.inr (Or.inl h))
              | some cut =>
                  simp only at hc
                  unfold checkCol at hc; dsimp only at hc; split at hc
                  · simp only [Option.some.injEq, Prod.mk.injEq] at hc
                    rw [← hc.1] at hx; exact Or.inr (Or.inr (Or.inr hx))
                  · cases hc
  | seq ct1 ct2 ih1 ih2 =>
      intro live flive livein flivein hc x hx
      cases h2 : checkClashTree f ct2 live flive with
      | none => simp [checkClashTree, h2] at hc
      | some p2 =>
          obtain ⟨l2, f2⟩ := p2
          simp only [checkClashTree, h2] at hc
          rcases ih1 _ _ _ _ hc x hx with h | h
          · rcases ih2 _ _ _ _ h2 x h with h | h
            · exact Or.inl h
            · exact Or.inr (Or.inr h)
          · exact Or.inr (Or.inl h)

/-- Exact HOL `domain_apply_bij_set` (`linear_scanProofScript.sml:5676-5690`). -/
@[hol "cakeml/compiler/backend/reg_alloc/proofs/linear_scanProofScript.sml"
  "domain_apply_bij_set"]
theorem domainApplyBijSet {α : Type} :
    ∀ (s : Spt α) (bij : Spt Nat),
      sptDomain (sptFoldiGen (fun r _ acc => sptInsert (miscThe 0 (sptLookup r bij)) () acc) 0 .ln s) =
        fun y => ∃ x, sptDomain s x ∧ miscThe 0 (sptLookup x bij) = y :=
  fun s bij => domainFoldiInsert (fun r => miscThe 0 (sptLookup r bij)) s

/-- Exact HOL `in_clash_tree_apply_bij` (`linear_scanProofScript.sml:5692-5708`). -/
@[hol "cakeml/compiler/backend/reg_alloc/proofs/linear_scanProofScript.sml"
  "in_clash_tree_apply_bij"]
theorem inClashTreeApplyBij :
    ∀ (bij : Spt Nat) (ct : ClashTree),
      (∀ x, inClashTree ct x → sptDomain bij x) →
      inClashTree (applyBijOnClashTree ct bij) =
        fun y => ∃ x, inClashTree ct x ∧ miscThe 0 (sptLookup x bij) = y := by
  intro bij ct hsub
  clear hsub
  induction ct with
  | delta w r =>
      funext y
      apply propext
      simp only [applyBijOnClashTree, inClashTree, List.mem_map]
      constructor
      · rintro (⟨x, hx, rfl⟩ | ⟨x, hx, rfl⟩)
        · exact ⟨x, Or.inl hx, rfl⟩
        · exact ⟨x, Or.inr hx, rfl⟩
      · rintro ⟨x, hx | hx, rfl⟩
        · exact Or.inl ⟨x, hx, rfl⟩
        · exact Or.inr ⟨x, hx, rfl⟩
  | set s =>
      show sptDomain _ = _
      rw [domainApplyBijSet]
      rfl
  | branch o ct1 ct2 ih1 ih2 =>
      funext y
      apply propext
      have e1 := congrFun ih1 y; have e2 := congrFun ih2 y
      simp only [applyBijOnClashTree, inClashTree]
      rw [e1, e2]
      cases o with
      | none =>
          simp only [Option.map]
          constructor
          · rintro (⟨x, hx, rfl⟩ | ⟨x, hx, rfl⟩ | h)
            · exact ⟨x, Or.inl hx, rfl⟩
            · exact ⟨x, Or.inr (Or.inl hx), rfl⟩
            · exact h.elim
          · rintro ⟨x, hx | hx | hx, rfl⟩
            · exact Or.inl ⟨x, hx, rfl⟩
            · exact Or.inr (Or.inl ⟨x, hx, rfl⟩)
            · exact hx.elim
      | some cut =>
          simp only [Option.map]
          rw [domainApplyBijSet]
          constructor
          · rintro (⟨x, hx, rfl⟩ | ⟨x, hx, rfl⟩ | ⟨x, hx, rfl⟩)
            · exact ⟨x, Or.inl hx, rfl⟩
            · exact ⟨x, Or.inr (Or.inl hx), rfl⟩
            · exact ⟨x, Or.inr (Or.inr hx), rfl⟩
          · rintro ⟨x, hx | hx | hx, rfl⟩
            · exact Or.inl ⟨x, hx, rfl⟩
            · exact Or.inr (Or.inl ⟨x, hx, rfl⟩)
            · exact Or.inr (Or.inr ⟨x, hx, rfl⟩)
  | seq ct1 ct2 ih1 ih2 =>
      funext y
      apply propext
      have e1 := congrFun ih1 y; have e2 := congrFun ih2 y
      simp only [applyBijOnClashTree, inClashTree]
      rw [e1, e2]
      constructor
      · rintro (⟨x, hx, rfl⟩ | ⟨x, hx, rfl⟩)
        · exact ⟨x, Or.inl hx, rfl⟩
        · exact ⟨x, Or.inr hx, rfl⟩
      · rintro ⟨x, hx | hx, rfl⟩
        · exact Or.inl ⟨x, hx, rfl⟩
        · exact Or.inr ⟨x, hx, rfl⟩

/-- Exact HOL `LENGTH_toAList` (`linear_scanProofScript.sml:5922-5930`). -/
@[hol "cakeml/compiler/backend/reg_alloc/proofs/linear_scanProofScript.sml" "LENGTH_toAList"]
theorem lengthToAList {α : Type} : ∀ (s : Spt α), (sptToAList s).length = sptSize s := by
  have key : ∀ (s : Spt α) (n : Nat) (l : List (Nat × α)),
      (sptFoldi (fun k v a => (k, v) :: a) n l s).length = sptSize s + l.length := by
    intro s
    induction s with
    | ln => intro n l; simp [sptFoldi]
    | ls v => intro n l; simp [sptFoldi]; omega
    | bn t1 t2 ih1 ih2 => intro n l; simp only [sptFoldi, ih2, ih1, sptSize]; omega
    | bs t1 v t2 ih1 ih2 =>
        intro n l; simp only [sptFoldi, ih2, ih1, sptSize, List.length_cons]; omega
  intro s
  simpa [sptToAList] using key s 0 []

/-- Exact HOL `check_col_equal_col` (`linear_scanProofScript.sml:5932-5942`). -/
@[hol "cakeml/compiler/backend/reg_alloc/proofs/linear_scanProofScript.sml" "check_col_equal_col"]
theorem checkColEqualCol {α : Type} :
    ∀ (s : Spt α) (f1 f2 : Nat → Nat), (∀ r, sptDomain s r → f1 r = f2 r) →
      checkCol f1 s = checkCol f2 s := by
  intro s f1 f2 h
  have hm : (sptToAList s).map (fun entry => f1 entry.1) =
      (sptToAList s).map (fun entry => f2 entry.1) := by
    apply List.map_congr_left
    intro p hp
    exact h p.1 ((sptMemMapFstToAList s p.1).mp (List.mem_map_of_mem hp))
  unfold checkCol
  dsimp only
  rw [hm]

/-- Exact HOL `check_partial_col_equal_col` (`linear_scanProofScript.sml:5944-5952`). -/
@[hol "cakeml/compiler/backend/reg_alloc/proofs/linear_scanProofScript.sml"
  "check_partial_col_equal_col"]
theorem checkPartialColEqualCol :
    ∀ (l : List Nat) (live flive : NumSet) (f1 f2 : Nat → Nat), (∀ r, r ∈ l → f1 r = f2 r) →
      checkPartialCol f1 l live flive = checkPartialCol f2 l live flive := by
  intro l
  induction l with
  | nil => intro _ _ _ _ _; rfl
  | cons h l ih =>
      intro live flive f1 f2 hf
      have hh := hf h List.mem_cons_self
      have ht : ∀ r, r ∈ l → f1 r = f2 r := fun r hr => hf r (List.mem_cons_of_mem h hr)
      simp only [checkPartialCol, hh]
      split
      · exact ih _ _ f1 f2 ht
      · split
        · exact ih _ _ f1 f2 ht
        · rfl

/-- Exact HOL `check_clash_tree_equal_col` (`linear_scanProofScript.sml:5954-6006`). -/
@[hol "cakeml/compiler/backend/reg_alloc/proofs/linear_scanProofScript.sml"
  "check_clash_tree_equal_col"]
theorem checkClashTreeEqualCol :
    ∀ (f1 f2 : Nat → Nat) (ct : ClashTree) (live flive : NumSet),
      (∀ r, inClashTree ct r → f1 r = f2 r) ∧ (∀ r, sptDomain live r → f1 r = f2 r) →
      checkClashTree f1 ct live flive = checkClashTree f2 ct live flive := by
  intro f1 f2 ct
  induction ct with
  | delta w r =>
      intro live flive ⟨hct, _⟩
      have hw : ∀ x, x ∈ w → f1 x = f2 x := fun x hx => hct x (Or.inl hx)
      have hr : ∀ x, x ∈ r → f1 x = f2 x := fun x hx => hct x (Or.inr hx)
      have hmap : w.map f1 = w.map f2 := List.map_congr_left hw
      simp only [checkClashTree]
      rw [checkPartialColEqualCol w live flive f1 f2 hw, hmap]
      split
      · rfl
      · exact checkPartialColEqualCol r _ _ f1 f2 hr
  | set tree =>
      intro live flive ⟨hct, _⟩
      exact checkColEqualCol tree f1 f2 hct
  | branch o ct1 ct2 ih1 ih2 =>
      intro live flive ⟨hct, hlive⟩
      have e1 := ih1 live flive ⟨fun x hx => hct x (Or.inl hx), hlive⟩
      have e2 := ih2 live flive ⟨fun x hx => hct x (Or.inr (Or.inl hx)), hlive⟩
      simp only [checkClashTree]
      rw [e1, e2]
      cases h1 : checkClashTree f2 ct1 live flive with
      | none => rfl
      | some p1 =>
          obtain ⟨l1, fl1⟩ := p1
          cases h2 : checkClashTree f2 ct2 live flive with
          | none => rfl
          | some p2 =>
              obtain ⟨l2, fl2⟩ := p2
              simp only
              cases o with
              | none =>
                  apply checkPartialColEqualCol
                  intro x hx
                  rw [sptMemMapFstToAList, sptDomainDifference] at hx
                  rcases checkClashTreeOutputSubset f2 ct2 live flive l2 fl2 h2 x hx.1 with h | h
                  · exact hlive x h
                  · exact hct x (Or.inr (Or.inl h))
              | some cut =>
                  exact checkColEqualCol cut f1 f2 (fun x hx => hct x (Or.inr (Or.inr hx)))
  | seq ct1 ct2 ih1 ih2 =>
      intro live flive ⟨hct, hlive⟩
      have e2 := ih2 live flive ⟨fun x hx => hct x (Or.inr hx), hlive⟩
      simp only [checkClashTree]
      rw [e2]
      cases h2 : checkClashTree f2 ct2 live flive with
      | none => rfl
      | some p2 =>
          obtain ⟨l2, fl2⟩ := p2
          simp only
          apply ih1
          refine ⟨fun x hx => hct x (Or.inl hx), fun x hx => ?_⟩
          rcases checkClashTreeOutputSubset f2 ct2 live flive l2 fl2 h2 x hx with h | h
          · exact hlive x h
          · exact hct x (Or.inr h)

/-- The names a successful check returns lie in the domain of the inverse
bijection when its inputs do (Flapjack helper for
`check_clash_tree_apply_bijection`). -/
private theorem outputInCodomain (bij invbij : Spt Nat) (f : Nat → Nat) (ct : ClashTree)
    (live flive out fout : NumSet)
    (hb1 : ∀ r, sptDomain bij r → sptDomain invbij (miscThe 0 (sptLookup r bij)))
    (hct : ∀ x, inClashTree ct x → sptDomain bij x)
    (hlive : ∀ x, sptDomain live x → sptDomain invbij x)
    (hc : checkClashTree f (applyBijOnClashTree ct bij) live flive = some (out, fout)) :
    ∀ x, sptDomain out x → sptDomain invbij x := by
  intro x hx
  rcases checkClashTreeOutputSubset f _ live flive out fout hc x hx with h | h
  · exact hlive x h
  · rw [inClashTreeApplyBij bij ct hct] at h
    obtain ⟨y, hy, rfl⟩ := h
    exact hb1 y (hct y hy)

/-- Exact HOL `check_clash_tree_apply_bijection` (`linear_scanProofScript.sml:5710-5865`). -/
@[hol "cakeml/compiler/backend/reg_alloc/proofs/linear_scanProofScript.sml"
  "check_clash_tree_apply_bijection"]
theorem checkClashTreeApplyBijection :
    ∀ (bij invbij : Spt Nat) (f : Nat → Nat) (ct : ClashTree)
      (live flive live' flive' livein flivein : NumSet),
      spInverts bij invbij ∧ spInverts invbij bij ∧
      (∀ x, inClashTree ct x → sptDomain bij x) ∧
      (∀ x, sptDomain live x → sptDomain invbij x) ∧
      sptDomain flive = (fun y => ∃ x, sptDomain live x ∧ f x = y) ∧
      sptDomain flive' = (fun y => ∃ x, sptDomain live' x ∧
        (fun r => f (miscThe 0 (sptLookup r bij))) x = y) ∧
      sptDomain live' = (fun y => ∃ x, sptDomain live x ∧
        (fun r => miscThe 0 (sptLookup r invbij)) x = y) ∧
      (∀ x y, sptDomain live x → sptDomain live y → f x = f y → x = y) ∧
      checkClashTree f (applyBijOnClashTree ct bij) live flive = some (livein, flivein) →
      ∃ livein' flivein',
        checkClashTree (fun r => f (miscThe 0 (sptLookup r bij))) ct live' flive' =
          some (livein', flivein') ∧
        sptDomain livein' = (fun y => ∃ x, sptDomain livein x ∧
          (fun r => miscThe 0 (sptLookup r invbij)) x = y) := by
  intro bij invbij f ct
  -- the bijection facts used throughout
  have mk : ∀ (a b : Spt Nat), spInverts a b → ∀ r, sptDomain a r →
      sptDomain b (miscThe 0 (sptLookup r a)) ∧
        miscThe 0 (sptLookup (miscThe 0 (sptLookup r a)) b) = r := by
    intro a b hab r hr
    unfold sptDomain at hr
    cases hl : sptLookup r a with
    | none => rw [hl] at hr; simp at hr
    | some v =>
        have := hab r v hl
        simp only [miscThe]
        exact ⟨by simp [sptDomain, this], by rw [this]⟩
  induction ct with
  | delta w r =>
      intro live flive live' flive' livein flivein
        ⟨hi1, hi2, hct, hlive, hfl, hfl', hl', hinj, hc⟩
      have hb1 := mk bij invbij hi1
      have hb2 := mk invbij bij hi2
      let ab := fun r => miscThe 0 (sptLookup r bij)
      let ai := fun r => miscThe 0 (sptLookup r invbij)
      simp only [applyBijOnClashTree, checkClashTree] at hc
      cases hp : checkPartialCol f (w.map ab) live flive with
      | none => rw [hp] at hc; cases hc
      | some v =>
          rw [hp] at hc
          simp only at hc
          obtain ⟨v1, v2⟩ := v
          obtain ⟨v1', v2', hp', -⟩ := checkPartialColApplyBijection (sptDomain bij)
            (sptDomain invbij) ab ai f w live flive live' flive' v1 v2
            ⟨hb1, hb2, fun x hx => hct x (Or.inl hx), hlive, hfl, hfl', hl', hinj, hp⟩
          have hinj' : ∀ x y, sptDomain live' x → sptDomain live' y →
              (fun r => f (ab r)) x = (fun r => f (ab r)) y → x = y := by
            intro x y hx hy he
            rw [hl'] at hx hy
            obtain ⟨a, ha, rfl⟩ := hx
            obtain ⟨b, hb, rfl⟩ := hy
            simp only [ab, (hb2 a (hlive a ha)).2, (hb2 b (hlive b hb)).2] at he
            rw [hinj a b ha hb he]
          have hd1 := numsetListDeleteImage f (w.map ab) live flive (v1, v2) hfl hinj hp
          have hd1' := numsetListDeleteImage (fun r => f (ab r)) w live' flive' (v1', v2') hfl' hinj' hp'
          have q1 : ∀ x, sptDomain (numsetListDelete (w.map ab) live) x → sptDomain invbij x := by
            intro x hx
            rw [RegAlloc.domainNumsetListDelete] at hx
            exact hlive x hx.1
          have q2 : sptDomain (numsetListDelete (w.map (fun r => f (ab r))) flive') =
              (fun y => ∃ x, sptDomain (numsetListDelete w live') x ∧ (f ∘ ab) x = y) := by
            rw [hd1']; rfl
          have q3 : sptDomain (numsetListDelete w live') =
              (fun y => ∃ x, sptDomain (numsetListDelete (w.map ab) live) x ∧ ai x = y) := by
            rw [RegAlloc.domainNumsetListDelete, RegAlloc.domainNumsetListDelete, hl']
            funext y
            apply propext
            constructor
            · rintro ⟨⟨a, ha, rfl⟩, hn⟩
              refine ⟨a, ⟨ha, fun hm => hn ?_⟩, rfl⟩
              obtain ⟨z, hz, hza⟩ := List.mem_map.mp hm
              rw [← hza]
              dsimp only [ab]
              rw [(hb1 z (hct z (Or.inl hz))).2]
              exact hz
            · rintro ⟨a, ⟨ha, hn⟩, rfl⟩
              refine ⟨⟨a, ha, rfl⟩, fun hm => hn ?_⟩
              have := (hb2 a (hlive a ha)).2
              dsimp only [ab, ai] at hm ⊢
              rw [← this]
              exact List.mem_map_of_mem hm
          have q4 : ∀ x y, sptDomain (numsetListDelete (w.map ab) live) x →
              sptDomain (numsetListDelete (w.map ab) live) y → f x = f y → x = y := by
            intro x y hx hy he
            rw [RegAlloc.domainNumsetListDelete] at hx hy
            exact hinj x y hx.1 hy.1 he
          have q5 : checkPartialCol f (r.map ab) (numsetListDelete (w.map ab) live)
              (numsetListDelete ((w.map ab).map f) flive) = some (livein, flivein) := by
            rw [List.map_map] at hc ⊢
            exact hc
          obtain ⟨li, fli, hc2, hdi⟩ := checkPartialColApplyBijection (sptDomain bij)
            (sptDomain invbij) ab ai f r (numsetListDelete (w.map ab) live)
            (numsetListDelete ((w.map ab).map f) flive) (numsetListDelete w live')
            (numsetListDelete (w.map (fun r => f (ab r))) flive') livein flivein
            ⟨hb1, hb2, fun x hx => hct x (Or.inr hx), q1, hd1, q2, q3, q4, q5⟩
          refine ⟨li, fli, ?_, hdi⟩
          simp only [checkClashTree]
          simp only [ab] at hp' hc2
          rw [hp']
          all_goals exact hc2
  | set s =>
      intro live flive live' flive' livein flivein
        ⟨hi1, hi2, hct, _, _, _, _, _, hc⟩
      simp only [applyBijOnClashTree, checkClashTree] at hc
      obtain ⟨li, fli, hci, hdi⟩ := checkColApplyBijection (sptDomain bij) (sptDomain invbij)
        (fun r => miscThe 0 (sptLookup r bij)) (fun r => miscThe 0 (sptLookup r invbij)) s
        livein flivein f ⟨mk bij invbij hi1, mk invbij bij hi2, hct, hc⟩
      exact ⟨li, fli, by simp only [checkClashTree]; exact hci, hdi⟩
  | branch o ct1 ct2 ih1 ih2 =>
      intro live flive live' flive' livein flivein
        ⟨hi1, hi2, hct, hlive, hfl, hfl', hl', hinj, hc⟩
      have hb1 := mk bij invbij hi1
      have hb2 := mk invbij bij hi2
      have hct1 : ∀ x, inClashTree ct1 x → sptDomain bij x := fun x hx => hct x (Or.inl hx)
      have hct2 : ∀ x, inClashTree ct2 x → sptDomain bij x := fun x hx => hct x (Or.inr (Or.inl hx))
      simp only [applyBijOnClashTree, checkClashTree] at hc
      cases h1 : checkClashTree f (applyBijOnClashTree ct1 bij) live flive with
      | none => rw [h1] at hc; cases hc
      | some p1 =>
          obtain ⟨t1, ft1⟩ := p1
          cases h2 : checkClashTree f (applyBijOnClashTree ct2 bij) live flive with
          | none => rw [h1, h2] at hc; cases hc
          | some p2 =>
              obtain ⟨t2, ft2⟩ := p2
              rw [h1, h2] at hc
              simp only at hc
              obtain ⟨l1, fl1, hc1, hd1⟩ := ih1 live flive live' flive' t1 ft1
                ⟨hi1, hi2, hct1, hlive, hfl, hfl', hl', hinj, h1⟩
              obtain ⟨l2, fl2, hc2, hd2⟩ := ih2 live flive live' flive' t2 ft2
                ⟨hi1, hi2, hct2, hlive, hfl, hfl', hl', hinj, h2⟩
              cases o with
              | some cut =>
                  simp only [Option.map] at hc
                  obtain ⟨li, fli, hci, hdi⟩ := checkColApplyBijection (sptDomain bij)
                    (sptDomain invbij) (fun r => miscThe 0 (sptLookup r bij))
                    (fun r => miscThe 0 (sptLookup r invbij)) cut livein flivein f
                    ⟨hb1, hb2, fun x hx => hct x (Or.inr (Or.inr hx)), hc⟩
                  exact ⟨li, fli, by simp only [checkClashTree, hc1, hc2]; exact hci, hdi⟩
              | none =>
                  simp only [Option.map] at hc
                  let ab := fun r => miscThe 0 (sptLookup r bij)
                  let ai := fun r => miscThe 0 (sptLookup r invbij)
                  have ht1 := outputInCodomain bij invbij f ct1 live flive t1 ft1
                    (fun r hr => (hb1 r hr).1) hct1 hlive h1
                  have ht2 := outputInCodomain bij invbij f ct2 live flive t2 ft2
                    (fun r hr => (hb1 r hr).1) hct2 hlive h2
                  obtain ⟨hdt1, hit1⟩ := checkClashTreeOutput f _ live flive t1 ft1 ⟨hfl, hinj, h1⟩
                  have hinj' : ∀ x y, sptDomain live' x → sptDomain live' y →
                      (fun r => f (ab r)) x = (fun r => f (ab r)) y → x = y := by
                    intro x y hx hy he
                    rw [hl'] at hx hy
                    obtain ⟨a, ha, rfl⟩ := hx
                    obtain ⟨b, hb, rfl⟩ := hy
                    simp only [ab, (hb2 a (hlive a ha)).2, (hb2 b (hlive b hb)).2] at he
                    rw [hinj a b ha hb he]
                  obtain ⟨hdl1, -⟩ := checkClashTreeOutput (fun r => f (ab r)) ct1 live' flive' l1 fl1
                    ⟨hfl', hinj', hc1⟩
                  -- names checked at the join, before and after renaming
                  have hunion := (checkPartialColSuccessInj livein flivein _ t1 ft1 f
                    ⟨hdt1, hit1, hc⟩).1
                  have keysEq : ∀ x, (x ∈ ((sptToAList (sptDifference l2 l1)).map Prod.fst).map ab ∨
                      sptDomain t1 x) ↔ (sptDomain t1 x ∨ sptDomain t2 x) := by
                    intro x
                    rw [List.map_map]
                    constructor
                    · rintro (hx | hx)
                      · obtain ⟨⟨k, v⟩, hk, rfl⟩ := List.mem_map.mp hx
                        have hkd := (sptMemMapFstToAList _ k).mp (List.mem_map_of_mem (f := Prod.fst) hk)
                        rw [sptDomainDifference, hd1, hd2] at hkd
                        obtain ⟨⟨a, ha, rfl⟩, -⟩ := hkd
                        simp only [Function.comp, ab]
                        rw [(hb2 a (ht2 a ha)).2]
                        exact Or.inr ha
                      · exact Or.inl hx
                    · rintro (hx | hx)
                      · exact Or.inr hx
                      · by_cases h1x : sptDomain t1 x
                        · exact Or.inr h1x
                        · left
                          have hk : sptDomain (sptDifference l2 l1) (ai x) := by
                            rw [sptDomainDifference, hd1, hd2]
                            refine ⟨⟨x, hx, rfl⟩, ?_⟩
                            rintro ⟨y, hy, hyx⟩
                            have := congrArg ab hyx
                            simp only [ab, ai, (hb2 y (ht1 y hy)).2, (hb2 x (ht2 x hx)).2] at this
                            exact h1x (this ▸ hy)
                          obtain ⟨⟨k, v⟩, hkm, hkk⟩ :=
                            List.mem_map.mp ((sptMemMapFstToAList _ (ai x)).mpr hk)
                          simp only at hkk
                          refine List.mem_map.mpr ⟨(k, v), hkm, ?_⟩
                          simp only [Function.comp, ab]
                          rw [hkk]
                          exact (hb2 x (ht2 x hx)).2
                  have hbranch := branchDomainIff t1 t2
                  obtain ⟨br, fbr, hbr, hdbr⟩ := checkPartialColSuccess
                    (((sptToAList (sptDifference l2 l1)).map Prod.fst).map ab) t1 ft1 f
                    ⟨hdt1, fun x y hx hy he => hunion x y ((hbranch x).mpr ((keysEq x).mp hx))
                      ((hbranch y).mpr ((keysEq y).mp hy)) he⟩
                  have hkeys : ∀ x, x ∈ (sptToAList (sptDifference l2 l1)).map Prod.fst →
                      sptDomain bij x := by
                    intro x hx
                    have hkd := (sptMemMapFstToAList _ x).mp hx
                    rw [sptDomainDifference, hd2] at hkd
                    obtain ⟨⟨a, ha, rfl⟩, -⟩ := hkd
                    exact (hb2 a (ht2 a ha)).1
                  obtain ⟨li, fli, hci, hdi⟩ := checkPartialColApplyBijection (sptDomain bij)
                    (sptDomain invbij) ab ai f ((sptToAList (sptDifference l2 l1)).map Prod.fst)
                    t1 ft1 l1 fl1 br fbr ⟨hb1, hb2, hkeys, ht1, hdt1, hdl1, hd1, hit1, hbr⟩
                  refine ⟨li, fli, by simp only [checkClashTree, hc1, hc2]; exact hci, ?_⟩
                  rw [hdi]
                  have e1 := checkPartialColDomain _ f t1 ft1 (br, fbr) hbr
                  have e2 := checkPartialColDomain _ f t1 ft1 (livein, flivein) hc
                  have : sptDomain br = sptDomain livein := by
                    rw [e1, e2]
                    funext x
                    exact propext ((keysEq x).trans (hbranch x).symm)
                  rw [this]
  | seq ct1 ct2 ih1 ih2 =>
      intro live flive live' flive' livein flivein
        ⟨hi1, hi2, hct, hlive, hfl, hfl', hl', hinj, hc⟩
      have hb1 := mk bij invbij hi1
      have hb2 := mk invbij bij hi2
      have hct1 : ∀ x, inClashTree ct1 x → sptDomain bij x := fun x hx => hct x (Or.inl hx)
      have hct2 : ∀ x, inClashTree ct2 x → sptDomain bij x := fun x hx => hct x (Or.inr hx)
      simp only [applyBijOnClashTree, checkClashTree] at hc
      cases h2 : checkClashTree f (applyBijOnClashTree ct2 bij) live flive with
      | none => rw [h2] at hc; cases hc
      | some p2 =>
          obtain ⟨t2, ft2⟩ := p2
          rw [h2] at hc
          simp only at hc
          let ab := fun r => miscThe 0 (sptLookup r bij)
          let ai := fun r => miscThe 0 (sptLookup r invbij)
          obtain ⟨l2, fl2, hc2, hd2⟩ := ih2 live flive live' flive' t2 ft2
            ⟨hi1, hi2, hct2, hlive, hfl, hfl', hl', hinj, h2⟩
          have ht2 := outputInCodomain bij invbij f ct2 live flive t2 ft2
            (fun r hr => (hb1 r hr).1) hct2 hlive h2
          obtain ⟨hdt2, hit2⟩ := checkClashTreeOutput f _ live flive t2 ft2 ⟨hfl, hinj, h2⟩
          have hinj' : ∀ x y, sptDomain live' x → sptDomain live' y →
              (fun r => f (ab r)) x = (fun r => f (ab r)) y → x = y := by
            intro x y hx hy he
            rw [hl'] at hx hy
            obtain ⟨a, ha, rfl⟩ := hx
            obtain ⟨b, hb, rfl⟩ := hy
            simp only [ab, (hb2 a (hlive a ha)).2, (hb2 b (hlive b hb)).2] at he
            rw [hinj a b ha hb he]
          obtain ⟨hdl2, -⟩ := checkClashTreeOutput (fun r => f (ab r)) ct2 live' flive' l2 fl2
            ⟨hfl', hinj', hc2⟩
          obtain ⟨li, fli, hc1, hd1⟩ := ih1 t2 ft2 l2 fl2 livein flivein
            ⟨hi1, hi2, hct1, ht2, hdt2, hdl2, hd2, hit2, hc⟩
          exact ⟨li, fli, by simp only [checkClashTree, hc2]; exact hc1, hd1⟩

/-- HOL `extract_coloration_output` (`linear_scanProofScript.sml:5867-5919`).

HOL `EL` is the exact `holEl`. -/
@[hol "cakeml/compiler/backend/reg_alloc/proofs/linear_scanProofScript.sml" "extract_coloration_output"]
theorem extractColorationOutput :
    ∀ (bij invbij : Spt Nat) (sth : LinearScanHiddenState) (l : List Nat) (acc : Spt Nat),
      spInverts bij invbij ∧ spInverts invbij bij ∧
      (∀ r, r ∈ l → sptDomain invbij r) ∧ (∀ r, r ∈ l → r < sth.colors.length) →
      ∃ col, extractColoration invbij l acc sth = (.success col, sth) ∧
        (∀ r, sptDomain bij r →
          if miscThe 0 (sptLookup r bij) ∈ l then
            sptLookup r col = some (holEl (miscThe 0 (sptLookup r bij)) sth.colors)
          else sptLookup r col = sptLookup r acc) ∧
        (∀ x, sptDomain col x → sptDomain bij x ∨ sptDomain acc x) := by
  intro bij invbij sth l
  induction l with
  | nil =>
      intro acc _
      refine ⟨acc, rfl, fun r _ => by simp, fun x hx => Or.inr hx⟩
  | cons h l ih =>
      intro acc ⟨hi1, hi2, hdom, hlen⟩
      have hh : h < sth.colors.length := hlen h List.mem_cons_self
      obtain ⟨ih', hih⟩ : ∃ ih', sptLookup h invbij = some ih' := by
        have := hdom h List.mem_cons_self
        unfold sptDomain at this
        cases e : sptLookup h invbij with
        | none => rw [e] at this; simp at this
        | some v => exact ⟨v, rfl⟩
      have hbij : sptLookup ih' bij = some h := hi2 h ih' hih
      let acc' := sptInsert (miscThe 0 (sptLookup h invbij)) (holEl h sth.colors) acc
      obtain ⟨col, hrun, hcol, hdcol⟩ := ih acc'
        ⟨hi1, hi2, fun r hr => hdom r (List.mem_cons_of_mem h hr),
          fun r hr => hlen r (List.mem_cons_of_mem h hr)⟩
      refine ⟨col, ?_, ?_, ?_⟩
      · show Translator.Monadic.MonadBase.bind (colorsSub h) _ sth = _
        unfold Translator.Monadic.MonadBase.bind
        rw [colorsSubEqn, if_pos hh]
        exact hrun
      · intro r hr
        have hc := hcol r hr
        obtain ⟨br, hbr⟩ : ∃ br, sptLookup r bij = some br := by
          unfold sptDomain at hr
          cases e : sptLookup r bij with
          | none => rw [e] at hr; simp at hr
          | some v => exact ⟨v, rfl⟩
        simp only [hbr, miscThe] at hc ⊢
        have hkey : (r = ih') ↔ br = h := by
          constructor
          · rintro rfl; rw [hbij] at hbr; cases hbr; rfl
          · rintro rfl
            have := hi1 r br hbr
            rw [this] at hih; cases hih; rfl
        by_cases hm : br ∈ l
        · rw [if_pos hm] at hc
          rw [if_pos (List.mem_cons_of_mem h hm)]
          exact hc
        · rw [if_neg hm] at hc
          by_cases hbh : br = h
          · rw [if_pos (by rw [hbh]; exact List.mem_cons_self), hc]
            show sptLookup r (sptInsert (miscThe 0 (sptLookup h invbij)) _ acc) = _
            rw [hih]
            simp only [miscThe]
            rw [hkey.mpr hbh, sptLookup_sptInsert_same, hbh]
          · have hne : r ≠ ih' := fun e => hbh (hkey.mp e)
            rw [if_neg (by simp [hm, hbh]), hc]
            show sptLookup r (sptInsert (miscThe 0 (sptLookup h invbij)) _ acc) = _
            rw [hih]
            simp only [miscThe]
            rw [sptLookup_sptInsert_ne ih' r _ acc hne]
      · intro x hx
        rcases hdcol x hx with h1 | h1
        · exact Or.inl h1
        · show sptDomain bij x ∨ sptDomain acc x
          change sptDomain (sptInsert (miscThe 0 (sptLookup h invbij)) _ acc) x at h1
          rw [sptDomainInsert, hih] at h1
          rcases h1 with rfl | h1
          · left; simp [sptDomain, hbij]
          · exact Or.inr h1

end Flapjack.LinearScan
