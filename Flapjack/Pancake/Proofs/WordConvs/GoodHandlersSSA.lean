import Flapjack.Pancake.Proofs.WordConvs.NotCreatedSSA
import Flapjack.Pancake.WordConvs

/-!
# `wordConvsProof`: `word_good_handlers` through SSA

`word_good_handlers_fake_moves`, `word_good_handlers_ssa_cc_trans` and
`word_good_handlers_full_ssa_cc_trans` of
`cakeml/compiler/backend/proofs/wordConvsProofScript.sml` (1310-1385): SSA renaming keeps
the handler-ownership predicate exactly. HOL's free label `n` (and `prio`) lead.
-/

namespace Flapjack.WordConvs

open Flapjack Flapjack.Compiler.Backend.WordAlloc Flapjack.WordAlloc

/-- HOL `word_good_handlers_fake_moves` (`wordConvsProofScript.sml:1310-1321`, `[local]`);
    HOL's free `n prio` lead. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem goodHandlers_fakeMoves {width : Nat} [NeZero width] (n : Nat)
    (prio : Option (Unit ⊕ Unit)) :
    ∀ (a : List Nat) (b c : Spt Nat) (d : Nat) (e f : WordLangProgHOL (BitVec width)) (g : Nat)
      (h i : Spt Nat),
      fakeMoves prio a b c d = (e, f, g, h, i) →
      goodHandlersHOL n e = true ∧ goodHandlersHOL n f = true := by
  intro a b c d e f g h i hm
  have all : ∀ (ls : List Nat) (l r : Spt Nat) (na : Nat),
      let (x, y, _, _, _) := fakeMoves (width := width) prio ls l r na
      goodHandlersHOL n x = true ∧ goodHandlersHOL n y = true := by
    intro ls
    induction ls with
    | nil => intro l r na; simp [fakeMoves, goodHandlersHOL]
    | cons x xs ih =>
        intro l r na
        generalize he : fakeMoves (width := width) prio xs l r na = result
        rcases result with ⟨x1, y1, count, treeL, treeR⟩
        have previous := ih l r na
        rw [he] at previous
        simp only [fakeMoves, he]
        cases hl : sptLookup x treeL <;> cases hr : sptLookup x treeR <;>
          simp_all [goodHandlersHOL, fakeMove]
  have result := all a b c d
  rw [hm] at result
  exact result

private theorem fixGood {width : Nat} [NeZero width] (n : Nat)
    (prio : Option (Unit ⊕ Unit)) (l r : Spt Nat) (next : Nat) :
    let out := fixInconsistencies (width := width) prio l r next
    goodHandlersHOL n out.1 = true ∧ goodHandlersHOL n out.2.1 = true := by
  unfold fixInconsistencies
  generalize hm : mergeMoves ((sptToAList (sptUnion l r)).map Prod.fst) l r next = merged
  rcases merged with ⟨lmov, rmov, count, left, right⟩
  generalize hf : fakeMoves (width := width) prio ((sptToAList (sptUnion l r)).map Prod.fst)
    left right count = result
  rcases result with ⟨a, b, final, leftOut, rightOut⟩
  have facts := goodHandlers_fakeMoves n prio _ left right count a b final leftOut rightOut hf
  simpa [hm, hf, goodHandlersHOL] using facts

/-- HOL `ssa_reconcile_good_handlers` (`wordConvsProofScript.sml:1029-1033`, `[local]`). HOL's free
    `n cur_ssa tgt_ssa ns` are explicit; `ns` keeps its independent value type `β`. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem reconcileGood {width : Nat} [NeZero width] (n : Nat) {β : Type}
    (current target : Spt Nat) (names : Spt β) :
    goodHandlersHOL n (ssaReconcile current target names : WordLangProgHOL (BitVec width)) = true := by
  unfold ssaReconcile
  dsimp only
  split <;> simp [goodHandlersHOL]

/-- HOL `fake_seq_good_handlers` (`wordConvsProofScript.sml:999-1003`, `[local]`). HOL's free `n`
    leads; `ls` stays universally quantified. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem fakeSeqGood {width : Nat} [NeZero width] (n : Nat) :
    ∀ ls : List Nat, goodHandlersHOL n
      ((ls.map (fakeMove : Nat → WordLangProgHOL (BitVec width))).foldr .seq .skip) = true := by
  intro ls
  induction ls with
  | nil => simp [goodHandlersHOL]
  | cons name names ih => simpa [goodHandlersHOL, fakeMove] using ih

/-- HOL `loop_setup_good_handlers` (`wordConvsProofScript.sml:1069-1078`, `[local]`). HOL's free
    variables are explicit (`n` first); the premise and conclusion are kept. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem loopSetupGood {width : Nat} [NeZero width] (n : Nat)
    (names exitNames : Spt Unit) (ssa : Spt Nat) (na : Nat)
    (setupProg : WordLangProgHOL (BitVec width)) (ssaRefreshed : Spt Nat) (naRefreshed : Nat)
    (setup : loopSetup names exitNames ssa na = (setupProg, ssaRefreshed, naRefreshed)) :
    goodHandlersHOL n setupProg = true := by
  unfold loopSetup at setup
  generalize hr : listNextVarRename
    (((sptToAList (sptUnion names exitNames)).map Prod.fst).filter
      fun v => (sptLookup v ssa).isNone) ssa na = renamed at setup
  rcases renamed with ⟨fresh, extended, next⟩
  generalize hm : listNextVarRenameMove (width := width) extended next
    (((sptToAList (sptUnion names exitNames)).map Prod.fst).filter
      fun v => (sptLookup v ssa).isSome) = moved at setup
  rcases moved with ⟨moves, refreshed, nextOut⟩
  simp only [hr, hm] at setup
  have fake := fakeSeqGood (width := width) n fresh
  have moveConvention : goodHandlersHOL n moves = true := by
    unfold listNextVarRenameMove at hm
    have projected := congrArg Prod.fst hm
    simp only at projected
    rw [← projected]
    simp [goodHandlersHOL]
  have output := congrArg Prod.fst setup
  simp only at output
  rw [← output]
  simp only [goodHandlersHOL, fake, moveConvention, Bool.and_self]

private theorem fixGood1 {width : Nat} [NeZero width] (n : Nat)
    (prio : Option (Unit ⊕ Unit)) (l r : Spt Nat) (next : Nat) :
    goodHandlersHOL n (fixInconsistencies (width := width) prio l r next).1 = true :=
  (fixGood n prio l r next).1

private theorem fixGood2 {width : Nat} [NeZero width] (n : Nat)
    (prio : Option (Unit ⊕ Unit)) (l r : Spt Nat) (next : Nat) :
    goodHandlersHOL n (fixInconsistencies (width := width) prio l r next).2.1 = true :=
  (fixGood n prio l r next).2

private theorem loopSetupGood' {width : Nat} [NeZero width] (n : Nat)
    (names exitNames : Spt Unit) (ssa : Spt Nat) (na : Nat) :
    goodHandlersHOL n (loopSetup (width := width) names exitNames ssa na).1 = true :=
  loopSetupGood n names exitNames ssa na _ _ _ rfl

private def programGood {width : Nat} [NeZero width] (n : Nat)
    (prog : WordLangProgHOL (BitVec width)) : Prop :=
  ∀ ssa next tables, goodHandlersHOL n (ssaCcTrans prog ssa next tables).1 = goodHandlersHOL n prog

/-- `ssa_cc_trans` keeps `word_good_handlers` of the program component exactly (Flapjack
    restatement of the HOL lemma below). -/
theorem goodHandlers_ssaCcTrans_fst {width : Nat} [NeZero width] (n : Nat) :
    ∀ (prog : WordLangProgHOL (BitVec width)) (ssa : Spt Nat) (next : Nat)
      (lt : List (Spt Nat × Spt Unit × Spt Unit)),
      goodHandlersHOL n (ssaCcTrans prog ssa next lt).1 = goodHandlersHOL n prog := by
  intro p
  apply WordLangProgHOL.rec
    (motive_1 := programGood n)
    (motive_2 := fun ret => match ret with | none => True | some r => programGood n r.2.2.1)
    (motive_3 := fun exc => match exc with | none => True | some r => programGood n r.2.1)
    (motive_4 := fun r => programGood n r.2.2.1)
    (motive_5 := fun r => programGood n r.2.1)
    (motive_6 := fun r => programGood n r.2.1)
    (motive_7 := fun r => programGood n r.1) (t := p)
  all_goals dsimp only [programGood]
  all_goals intros
  all_goals try simp_all [ssaCcTrans, goodHandlersHOL, nextVarRename, listNextVarRenameMove]
  case inst =>
    rename_i instruction ssa next tables
    fun_cases ssaCcTransInst instruction ssa next <;> simp [goodHandlersHOL]
  case ite =>
    simp only [fixGood1, fixGood2, Bool.and_true]
  case loop =>
    rename_i names body exits bodyIH ssa next tables
    simp only [loopSetupGood', Bool.true_and]
    split
    · exact bodyIH _ _ _
    · simp only [goodHandlersHOL, reconcileGood, Bool.and_true]
      exact bodyIH _ _ _
  case «break» | «continue» =>
    split
    · rfl
    · dsimp only
      split
      · rfl
      · simp only [goodHandlersHOL, reconcileGood, Bool.and_true]
  case shareInst =>
    split <;> simp [goodHandlersHOL]
  case call =>
    rename_i returns target arguments handler retIH excIH ssa next tables
    cases returns with
    | none =>
      cases handler with
      | none => simp_all [ssaCcTrans, goodHandlersHOL]
      | some exc =>
        rcases exc with ⟨excName, excBody, e1, e2⟩
        simp_all [ssaCcTrans, goodHandlersHOL]
    | some ret =>
      rcases ret with ⟨retNames, cutsets, retBody, l1, l2⟩
      cases handler with
      | none =>
        simp_all [ssaCcTrans, goodHandlersHOL, listNextVarRenameMove]
      | some exc =>
        rcases exc with ⟨excName, excBody, e1, e2⟩
        simp_all [ssaCcTrans, goodHandlersHOL, listNextVarRenameMove, nextVarRename,
          fixGood1, fixGood2]

/-- HOL `word_good_handlers_ssa_cc_trans` (`wordConvsProofScript.sml:1323-1372`, `[local]`). -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem goodHandlers_ssaCcTrans {width : Nat} [NeZero width] (n : Nat) :
    ∀ (x : WordLangProgHOL (BitVec width)) (y : Spt Nat) (z : Nat)
      (lt : List (Spt Nat × Spt Unit × Spt Unit)) (a : WordLangProgHOL (BitVec width))
      (b : Spt Nat) (c : Nat),
      ssaCcTrans x y z lt = (a, b, c) → goodHandlersHOL n a = goodHandlersHOL n x := by
  intro x y z lt a b c h
  have := goodHandlers_ssaCcTrans_fst n x y z lt
  rw [h] at this
  exact this

/-- HOL `word_good_handlers_full_ssa_cc_trans` (`wordConvsProofScript.sml:1374-1385`,
    `[local]`). -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem goodHandlers_fullSsaCcTrans {width : Nat} [NeZero width] (n : Nat) :
    ∀ (m : Nat) (p : WordLangProgHOL (BitVec width)),
      goodHandlersHOL n (fullSsaCcTrans m p) = true ↔ goodHandlersHOL n p = true := by
  intro m p
  generalize produced : setupSSA (outputWidth := width) m (limitVar p) p = result
  rcases result with ⟨move, ssa, next⟩
  have hm : goodHandlersHOL n move = true := by
    unfold setupSSA at produced
    generalize listNextVarRename (evenList m) .ln (limitVar p) = renamed at produced
    rcases renamed with ⟨names, tree, counter⟩
    cases produced
    simp [goodHandlersHOL]
  have hb := goodHandlers_ssaCcTrans_fst n p ssa next []
  generalize bodyEq : ssaCcTrans p ssa next [] = bodyResult
  rcases bodyResult with ⟨body, finalMap, finalNext⟩
  rw [bodyEq] at hb
  simp only [fullSsaCcTrans, produced, bodyEq, goodHandlersHOL, hm, hb, Bool.true_and]

end Flapjack.WordConvs
