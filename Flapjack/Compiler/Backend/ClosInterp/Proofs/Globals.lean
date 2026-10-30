import Flapjack.Compiler.Backend.ClosInterp.Optimise
import Flapjack.Compiler.Backend.Semantics.ClosProps.Globals
import Flapjack.Compiler.Backend.FlatProps.GlobalBagProperties

/-! Global-write preservation for incremental interpreter insertion. -/
namespace Flapjack.Compiler.Backend.ClosInterp
open ClosLang ClosProps
open FlatProps (emptyGlobalBag unionGlobalBag_eq_empty)

private theorem interpretableOp_noWrites (op : Op) (len : Nat)
    (valid : canInterpretOp op len = true) : opGlobalBag op = emptyGlobalBag := by
  cases op <;> simp [canInterpretOp, opGlobalBag] at valid ⊢
  case globOp op =>
    cases op <;> simp_all

private theorem interpretable_safe (e : Exp) :
    canInterpret e = true → setGlobals e = emptyGlobalBag ∧ esgcFree e := by
  induction e using canInterpret.induct
      (motive_2 := fun es => canInterpretList es = true →
        elistGlobals es = emptyGlobalBag ∧ esgcFreeList es) with
  | case1 t n => simp [canInterpret, setGlobals, esgcFree]
  | case2 t a b c ia ib ic =>
    simp only [canInterpret, Bool.and_eq_true]
    intro ⟨⟨ha, hb⟩, hc⟩
    obtain ⟨ga, sa⟩ := ia ha
    obtain ⟨gb, sb⟩ := ib hb
    obtain ⟨gc, sc⟩ := ic hc
    simp [setGlobals, esgcFree, unionGlobalBag_eq_empty, ga, gb, gc, sa, sb, sc]
  | case3 t es e ie ies =>
    simp only [canInterpret, Bool.and_eq_true]
    intro ⟨he, hs⟩
    obtain ⟨ge, se⟩ := ie he
    obtain ⟨gs, ss⟩ := ies hs
    simp [setGlobals, esgcFree, unionGlobalBag_eq_empty, ge, se, gs, ss]
  | case4 t op es ies =>
    simp only [canInterpret, Bool.and_eq_true]
    intro ⟨ho, hs⟩
    obtain ⟨gs, ss⟩ := ies hs
    simp [setGlobals, esgcFree, unionGlobalBag_eq_empty, interpretableOp_noWrites op es.length ho, gs, ss]
  | case5 t e ih | case6 t e ih =>
    simpa [canInterpret, setGlobals, esgcFree] using ih
  | case7 t a b ia ib =>
    simp only [canInterpret, Bool.and_eq_true]
    intro ⟨ha, hb⟩
    obtain ⟨ga, sa⟩ := ia ha
    obtain ⟨gb, sb⟩ := ib hb
    simp [setGlobals, esgcFree, unionGlobalBag_eq_empty, ga, gb, sa, sb]
  | case8 t opt e es ie ies =>
    simp only [canInterpret, Bool.and_eq_true]
    intro ⟨⟨⟨_, he⟩, hs⟩, _⟩
    obtain ⟨ge, se⟩ := ie he
    obtain ⟨gs, ss⟩ := ies hs
    simp [setGlobals, esgcFree, unionGlobalBag_eq_empty, ge, gs, se, ss]
  | case9 | case10 | case11 => simp [canInterpret]
  | case12 => simp [elistGlobals, esgcFreeList]
  | case13 e es ie ies =>
    rename_i h
    simp only [canInterpretList, Bool.and_eq_true] at h
    obtain ⟨he, hs⟩ := h
    obtain ⟨ge, se⟩ := ie he
    obtain ⟨gs, ss⟩ := ies hs
    simp [elistGlobals, esgcFreeList, unionGlobalBag_eq_empty, ge, gs, se, ss]

private theorem optInterp_safe (e e' : Exp) (h : optInterp e = some e') :
    setGlobals e' = emptyGlobalBag ∧ setGlobals e = emptyGlobalBag ∧
      esgcFree e ∧ esgcFree e' := by
  unfold optInterp at h
  split at h
  · rename_i test
    simp only [Bool.and_eq_true] at test
    have source := interpretable_safe e test.1
    simp only [Option.some.injEq] at h
    subst e'
    simp [setGlobals, elistGlobals, opGlobalBag, esgcFree, esgcFreeList,
      unionGlobalBag_eq_empty, source.1, source.2]
  · simp at h

private theorem optInterp1_safe (e : Exp) : esgcFree (optInterp1 e) ↔ esgcFree e := by
  cases h : optInterp e with
  | none => simp [optInterp1, h]
  | some e' =>
    have safe := optInterp_safe e e' h
    simp [optInterp1, h, safe.2.2.1, safe.2.2.2]

private theorem optInterp1_globals (e : Exp) : setGlobals (optInterp1 e) = setGlobals e := by
  cases h : optInterp e with
  | none => simp [optInterp1, h]
  | some e' =>
    have safe := optInterp_safe e e' h
    simp [optInterp1, h, safe.1, safe.2.1]

private theorem mappedOpt_safe (es : List Exp) :
    esgcFreeList (es.map optInterp1) ↔ esgcFreeList es := by
  induction es with
  | nil => simp [esgcFreeList]
  | cons e es ih => simp [esgcFreeList, optInterp1_safe, ih]

private theorem mappedOpt_globals (es : List Exp) :
    elistGlobals (es.map optInterp1) = elistGlobals es := by
  induction es with
  | nil => rfl
  | cons e es ih => simp [elistGlobals, optInterp1_globals, ih]

private theorem insertInterp1_safe (e : Exp) : esgcFree (insertInterp1 e) ↔ esgcFree e := by
  cases h : optInterp e with
  | some e' =>
    have safe := optInterp_safe e e' h
    simp [insertInterp1, h, safe.2.2.1, safe.2.2.2]
  | none =>
    cases e <;> simp [insertInterp1, h, esgcFree, mappedOpt_safe]

private theorem insertInterp1_globals (e : Exp) : setGlobals (insertInterp1 e) = setGlobals e := by
  cases h : optInterp e with
  | some e' =>
    have safe := optInterp_safe e e' h
    simp [insertInterp1, h, safe.1, safe.2.1]
  | none =>
    cases e <;> simp [insertInterp1, h, setGlobals, mappedOpt_globals]

/-- Incremental interpreter insertion preserves the bag of global writes. -/
@[hol "cakeml/compiler/backend/proofs/clos_interpProofScript.sml" "elist_globals_insert_interp"]
theorem elistGlobals_insertInterp (es : List Exp) :
    elistGlobals (insertInterp es) = elistGlobals es := by
  induction es with
  | nil => rfl
  | cons e es ih =>
    simp only [insertInterp] at ih
    simp [insertInterp, elistGlobals, insertInterp1_globals, ih]

/-- Incremental interpreter insertion preserves closure safety in both directions. -/
@[hol "cakeml/compiler/backend/proofs/clos_interpProofScript.sml" "insert_interp_esgc_free"]
theorem insertInterp_esgcFree (es : List Exp) :
    (∀ e ∈ insertInterp es, esgcFree e) ↔ ∀ e ∈ es, esgcFree e := by
  simp [insertInterp, insertInterp1_safe]

end Flapjack.Compiler.Backend.ClosInterp
