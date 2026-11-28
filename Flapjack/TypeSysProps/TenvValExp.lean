module

public import Flapjack.TypeSoundInvariants
public import Flapjack.FiniteMap.AlistExact.Lookup
public import Flapjack.TypeSysProps.Freevars

@[expose] public section

/-!
# Local type-variable environments

The `tenv_val_exp` operations from `typeSysPropsScript.sml`: substitution over
local environments, merging two environments, and the lookup lemmas used by the
declarative type system's metatheory. `ALOOKUP` is the reviewed propositional
association-list lookup `holALookup`.
-/

namespace Flapjack.TypeSysProps

open Flapjack.TypeSystemHOL Flapjack.Basis.Pure.MlString Flapjack.TypeSoundInvariants

noncomputable local instance instDecidableEq_tenvValExp (α : Type) : DecidableEq α :=
  Classical.typeDecidableEq α

/-- Original `deBruijn_subst_tenvE_def`: substitute type arguments through a
local environment, shifting by the bound variables seen so far. -/
@[hol "cakeml/semantics/proofs/typeSysPropsScript.sml" "deBruijn_subst_tenvE_def"]
def deBruijnSubstTenvE (targs : List SemanticT) : TenvValExp → TenvValExp
  | .empty => .empty
  | .bindTvar tvs env => .bindTvar tvs (deBruijnSubstTenvE targs env)
  | .bindName x tvs t env =>
    .bindName x tvs
      (deBruijnSubst (tvs + numTvs env) (targs.map (deBruijnInc 0 (tvs + numTvs env))) t)
      (deBruijnSubstTenvE targs env)

/-- Original `db_merge_def`: append one local environment beneath another,
keeping the bound-variable counts of both. -/
@[hol "cakeml/semantics/proofs/typeSysPropsScript.sml" "db_merge_def"]
def dbMerge : TenvValExp → TenvValExp → TenvValExp
  | .empty, e => e
  | .bindTvar tvs e1, e2 => .bindTvar tvs (dbMerge e1 e2)
  | .bindName x tvs t e1, e2 => .bindName x tvs t (dbMerge e1 e2)

/-- Original `bind_tvar_rewrites`: the eight source rewrites for
`bind_tvar` over merging, counting, lookup, well-formedness and substitution. -/
@[hol "cakeml/semantics/proofs/typeSysPropsScript.sml" "bind_tvar_rewrites"]
theorem bindTvar_rewrites :
    (∀ (tvs : Nat) (e1 e2 : TenvValExp),
        dbMerge (bindTvar tvs e1) e2 = bindTvar tvs (dbMerge e1 e2)) ∧
      (∀ (tvs : Nat) (e : TenvValExp), numTvs (bindTvar tvs e) = tvs + numTvs e) ∧
      (∀ (tvs : Nat) (e : TenvValExp), numTvs (.bindTvar tvs e) = tvs + numTvs e) ∧
      (∀ (tvs : Nat) (n : MlString) (t : SemanticT) (e : TenvValExp),
        numTvs (.bindName n tvs t e) = numTvs e) ∧
      numTvs (.empty : TenvValExp) = 0 ∧
      (∀ (n : MlString) (inc : Nat) (tvs : Nat) (e : TenvValExp),
        tveLookup n inc (bindTvar tvs e) = tveLookup n (inc + tvs) e) ∧
      (∀ (tvs : Nat) (e : TenvValExp), tenvValExpOk (bindTvar tvs e) ↔ tenvValExpOk e) ∧
      ∀ (targs : List SemanticT) (tvs : Nat) (e : TenvValExp),
        deBruijnSubstTenvE targs (bindTvar tvs e) =
          bindTvar tvs (deBruijnSubstTenvE targs e) := by
  simp only [bindTvar]
  refine ⟨?_, ?_, fun tvs e => rfl, fun tvs n t e => rfl, rfl, ?_, ?_, ?_⟩
  · intro tvs e1 e2
    by_cases zero : tvs = 0
    · simp [zero]
    · simp [dbMerge, zero]
  · intro tvs e
    by_cases zero : tvs = 0
    · simp [zero]
    · simp [numTvs, zero]
  · intro n inc tvs e
    by_cases zero : tvs = 0
    · simp [zero]
    · simp [tveLookup, zero]
  · intro tvs e
    by_cases zero : tvs = 0
    · simp [zero]
    · simp [tenvValExpOk, zero]
  · intro targs tvs e
    by_cases zero : tvs = 0
    · simp [zero]
    · simp [deBruijnSubstTenvE, zero]

/-- Original `bind_tvar0`: binding zero type variables leaves the environment
unchanged. -/
@[hol "cakeml/semantics/proofs/typeSysPropsScript.sml" "bind_tvar0"]
theorem bindTvar_zero (x : TenvValExp) : bindTvar 0 x = x := by
  simp [bindTvar]

/-- Original `tveLookup_subst_none`: substituting type arguments preserves
whether a lookup fails. -/
@[hol "cakeml/semantics/proofs/typeSysPropsScript.sml" "tveLookup_subst_none"]
theorem tveLookup_subst_none (n : MlString) :
    ∀ (inc : Nat) (e : TenvValExp) (targs : List SemanticT),
      tveLookup n inc (deBruijnSubstTenvE targs e) = none ↔ tveLookup n inc e = none := by
  intro inc e targs
  induction e generalizing inc with
  | empty => simp [deBruijnSubstTenvE, tveLookup]
  | bindTvar tvs e ih => simp [deBruijnSubstTenvE, tveLookup, ih]
  | bindName x tvs t e ih =>
    by_cases same : x = n
    · simp [deBruijnSubstTenvE, tveLookup, same]
    · simp [deBruijnSubstTenvE, tveLookup, same, ih]

/-- Original `tveLookup_db_merge_none`: a lookup in a merged environment fails
exactly when it fails in the outer part and, shifted by that part's bound
variables, in the inner part. -/
@[hol "cakeml/semantics/proofs/typeSysPropsScript.sml" "tveLookup_db_merge_none"]
theorem tveLookup_dbMerge_none (n : MlString) :
    ∀ (inc : Nat) (e1 e2 : TenvValExp),
      tveLookup n inc (dbMerge e1 e2) = none ↔
        tveLookup n inc e1 = none ∧ tveLookup n (numTvs e1 + inc) e2 = none := by
  intro inc e1
  induction e1 generalizing inc with
  | empty => simp [dbMerge, tveLookup, numTvs]
  | bindTvar tvs e1 ih =>
    intro e2
    simp only [dbMerge, tveLookup, numTvs]
    rw [show tvs + numTvs e1 + inc = numTvs e1 + (inc + tvs) by omega]
    exact ih (inc + tvs) e2
  | bindName x tvs t e1 ih =>
    intro e2
    by_cases same : x = n
    · simp [dbMerge, tveLookup, numTvs, same]
    · simp only [dbMerge, tveLookup, numTvs, same, if_false]
      exact ih inc e2

/-- Original `tveLookup_inc_none`: a lookup fails at every increment exactly
when it fails at increment zero. -/
@[hol "cakeml/semantics/proofs/typeSysPropsScript.sml" "tveLookup_inc_none"]
theorem tveLookup_inc_none (n : MlString) :
    ∀ (inc : Nat) (e : TenvValExp), tveLookup n inc e = none ↔ tveLookup n 0 e = none := by
  intro inc e
  induction e generalizing inc with
  | empty => simp [tveLookup]
  | bindTvar tvs e ih =>
    simp only [tveLookup, Nat.zero_add]
    rw [ih (inc + tvs), ih tvs]
  | bindName x tvs t e ih =>
    by_cases same : x = n
    · simp [tveLookup, same]
    · simp [tveLookup, same, ih]

/-- Original `bind_var_list_append`: binding an appended list binds the two
parts in order. -/
@[hol "cakeml/semantics/proofs/typeSysPropsScript.sml" "bind_var_list_append"]
theorem bindVarList_append (n : Nat) :
    ∀ (te1 te2 : List (MlString × SemanticT)) (te3 : TenvValExp),
      bindVarList n (te1 ++ te2) te3 = bindVarList n te1 (bindVarList n te2 te3) := by
  intro te1
  induction te1 with
  | nil =>
    intro te2 te3
    simp [bindVarList]
  | cons p te1 ih =>
    intro te2 te3
    obtain ⟨name, t⟩ := p
    simp [bindVarList, ih te2 te3]

/-- Original `num_tvs_bind_var_list`: binding a variable list does not change
the bound-variable count. -/
@[hol "cakeml/semantics/proofs/typeSysPropsScript.sml" "num_tvs_bind_var_list"]
theorem numTvs_bindVarList (tvs : Nat) :
    ∀ (env : List (MlString × SemanticT)) (tenvE : TenvValExp),
      numTvs (bindVarList tvs env tenvE) = numTvs tenvE := by
  intro env
  induction env with
  | nil =>
    intro tenvE
    simp [bindVarList]
  | cons p env ih =>
    intro tenvE
    obtain ⟨name, t⟩ := p
    simp [bindVarList, numTvs, ih]

/-- Original `tveLookup_bvl`: looking a name up in a bound variable list
either finds its type at the list's bound-variable count or falls through to
the underlying environment. -/
@[hol "cakeml/semantics/proofs/typeSysPropsScript.sml" "tveLookup_bvl"]
theorem tveLookup_bvl (x : MlString) :
    ∀ (tvs tvs' : Nat) (bindings : List (MlString × SemanticT)) (tenvE : TenvValExp),
      tveLookup x tvs (bindVarList tvs' bindings tenvE) =
        match Flapjack.holALookup bindings x with
        | none => tveLookup x tvs tenvE
        | some t => some (tvs', deBruijnInc tvs' tvs t) := by
  intro tvs tvs' bindings
  induction bindings with
  | nil =>
    intro tenvE
    simp [bindVarList, Flapjack.holALookup]
  | cons p bindings ih =>
    intro tenvE
    obtain ⟨name, t⟩ := p
    by_cases same : name = x
    · have flip : x = name := same.symm
      rw [bindVarList, Flapjack.holALookup, tveLookup, if_pos same, if_pos flip]
    · have flip : ¬ x = name := fun h => same h.symm
      rw [bindVarList, Flapjack.holALookup, tveLookup, if_neg same, if_neg flip]
      exact ih tenvE

/-- Original `num_tvs_db_merge`: merging adds the bound-variable counts. -/
@[hol "cakeml/semantics/proofs/typeSysPropsScript.sml" "num_tvs_db_merge"]
theorem numTvs_dbMerge (e1 e2 : TenvValExp) :
    numTvs (dbMerge e1 e2) = numTvs e1 + numTvs e2 := by
  induction e1 with
  | empty => simp [dbMerge, numTvs]
  | bindTvar tvs e1 ih =>
    simp [dbMerge, numTvs, ih]
    omega
  | bindName x tvs t e1 ih => simp [dbMerge, numTvs, ih]

/-- Original `num_tvs_deBruijn_subst_tenvE`: substituting type arguments does
not change the bound-variable count. -/
@[hol "cakeml/semantics/proofs/typeSysPropsScript.sml" "num_tvs_deBruijn_subst_tenvE"]
theorem numTvs_deBruijnSubstTenvE (targs : List SemanticT) (env : TenvValExp) :
    numTvs (deBruijnSubstTenvE targs env) = numTvs env := by
  induction env with
  | empty => rfl
  | bindTvar tvs env ih => simp [deBruijnSubstTenvE, numTvs, ih]
  | bindName x tvs t env ih => simp [deBruijnSubstTenvE, numTvs, ih]

/-- Original `tenv_val_exp_ok_db_merge`: a well-formed merged environment has a
well-formed inner part. -/
@[hol "cakeml/semantics/proofs/typeSysPropsScript.sml" "tenv_val_exp_ok_db_merge"]
theorem tenvValExpOk_dbMerge (e1 e2 : TenvValExp) :
    tenvValExpOk (dbMerge e1 e2) → tenvValExpOk e2 := by
  induction e1 with
  | empty => simp [dbMerge]
  | bindTvar tvs e1 ih =>
    intro h
    apply ih
    exact h
  | bindName x tvs t e1 ih =>
    intro h
    apply ih
    exact h.2

/-- Merging beneath a bound variable list keeps the list structure. -/
@[hol "cakeml/semantics/proofs/typeSysPropsScript.sml" "db_merge_bvl"]
theorem dbMerge_bvl (tenv1 : List (MlString × SemanticT)) (tenv2 tenv3 : TenvValExp)
    (tvs : Nat) :
    dbMerge (bindVarList tvs tenv1 tenv2) tenv3 =
      bindVarList tvs tenv1 (dbMerge tenv2 tenv3) := by
  induction tenv1 generalizing tenv2 with
  | nil => simp [bindVarList]
  | cons entry rest ih =>
    rcases entry with ⟨name, ty⟩
    simp only [bindVarList, dbMerge, ih]

/-- Raising the lookup increment shifts the stored type by the difference. -/
@[hol "cakeml/semantics/proofs/typeSysPropsScript.sml" "tveLookup_add_inc"]
theorem tveLookup_add_inc (x : MlString) (inc inc2 : Nat) (localEnv : TenvValExp)
    (tvs : Nat) (t : SemanticT) :
    tveLookup x inc localEnv = some (tvs, t) →
      tveLookup x (inc2 + inc) localEnv = some (tvs, deBruijnInc tvs inc2 t) := by
  intro found
  induction localEnv generalizing inc tvs t with
  | empty => cases found
  | bindTvar bound rest ih =>
    simp only [tveLookup] at found ⊢
    have shifted := ih _ _ _ found
    rw [Nat.add_assoc]
    exact shifted
  | bindName name bound ty rest ih =>
    simp only [tveLookup] at found ⊢
    split at found
    · rename_i same
      obtain ⟨rfl, rfl⟩ := Option.some.inj found
      simp only [same, ↓reduceIte]
      rw [deBruijnInc_deBruijnInc]
    · rename_i different
      simp only [different, ↓reduceIte]
      exact ih _ _ _ found

/-- A successful lookup in a merged environment is either a lookup in the outer
environment or a lookup in the inner one shifted by the outer bound. -/
@[hol "cakeml/semantics/proofs/typeSysPropsScript.sml" "tveLookup_db_merge_some"]
theorem tveLookup_dbMerge_some (n : MlString) (inc : Nat) (tenvE1 tenvE2 : TenvValExp)
    (tvs : Nat) (t : SemanticT) :
    tveLookup n inc (dbMerge tenvE1 tenvE2) = some (tvs, t) ↔
      tveLookup n inc tenvE1 = some (tvs, t) ∨
        (tveLookup n inc tenvE1 = none ∧
          tveLookup n (numTvs tenvE1 + inc) tenvE2 = some (tvs, t)) := by
  induction tenvE1 generalizing inc tvs t with
  | empty => simp [dbMerge, tveLookup, numTvs]
  | bindTvar bound rest ih =>
    simp only [dbMerge, tveLookup, numTvs]
    rw [ih (inc + bound)]
    have idx : bound + numTvs rest + inc = numTvs rest + (inc + bound) := by omega
    rw [idx]
  | bindName name bound ty rest ih =>
    simp only [dbMerge, tveLookup, numTvs]
    by_cases same : name = n
    · simp [same]
    · simp only [same, ↓reduceIte]
      rw [ih inc tvs t]

/-- A successful lookup in a well-formed zero-bound local environment returns a
type satisfying the lookup bound. -/
@[hol "cakeml/semantics/proofs/typeSysPropsScript.sml" "tveLookup_freevars" 704]
theorem tveLookup_freevars (n : MlString) (tvs : Nat) (localEnv : TenvValExp) (tvs' : Nat)
    (t : SemanticT) :
    tenvValExpOk localEnv ∧ numTvs localEnv = 0 ∧ tveLookup n tvs localEnv = some (tvs', t) →
      checkFreevars tvs' [] t = true := by
  intro h
  induction localEnv generalizing tvs tvs' t with
  | empty => cases h.2.2
  | bindTvar bound rest ih =>
    simp only [tenvValExpOk, numTvs, tveLookup] at h ⊢
    obtain ⟨hok, hnum, hfound⟩ := h
    have zero : bound = 0 := by omega
    exact ih _ _ _ ⟨hok, by omega, hfound⟩
  | bindName name bound ty rest ih =>
    simp only [tenvValExpOk, numTvs, tveLookup] at h ⊢
    obtain ⟨head1, hnum, hfound⟩ := h
    obtain ⟨hfree, hok⟩ := head1
    split at hfound
    · rename_i same
      obtain ⟨rfl, rfl⟩ := Option.some.inj hfound
      have freeHere : checkFreevars bound [] ty = true := by simpa [hnum] using hfree
      rw [nil_deBruijnInc bound tvs ty (Or.inl freeHere)]
      exact freeHere
    · rename_i different
      exact ih _ _ _ ⟨hok, hnum, hfound⟩

/-- A successful lookup exposes a base type that every increment shifts, so any
other increment can be recovered from the same base. -/
@[hol "cakeml/semantics/proofs/typeSysPropsScript.sml" "tveLookup_inc_some"]
theorem tveLookup_inc_some (n : MlString) (inc : Nat) (localEnv : TenvValExp) (tvs : Nat)
    (t : SemanticT) (inc2 : Nat) :
    tveLookup n inc localEnv = some (tvs, t) →
      ∃ t', t = deBruijnInc tvs inc t' ∧
        tveLookup n inc2 localEnv = some (tvs, deBruijnInc tvs inc2 t') := by
  intro found
  induction localEnv generalizing inc tvs t inc2 with
  | empty => cases found
  | bindTvar bound rest ih =>
    simp only [tveLookup] at found
    obtain ⟨t', eq, found2⟩ := ih (inc + bound) tvs t (inc2 + bound) found
    refine ⟨deBruijnInc tvs bound t', ?_, ?_⟩
    · rw [deBruijnInc_deBruijnInc]
      exact eq
    · rw [deBruijnInc_deBruijnInc]
      exact found2
  | bindName name bound ty rest ih =>
    simp only [tveLookup] at found ⊢
    by_cases same : name = n
    · rw [if_pos same] at found
      obtain ⟨rfl, rfl⟩ := Option.some.inj found
      rw [if_pos same]
      exact ⟨ty, rfl, rfl⟩
    · rw [if_neg same] at found
      rw [if_neg same]
      exact ih inc tvs t inc2 found

/-- In a well-formed zero-bound local environment, the lookup increment does not
change the result. -/
@[hol "cakeml/semantics/proofs/typeSysPropsScript.sml" "tveLookup_no_tvs"]
theorem tveLookup_no_tvs (tvs : Nat) (l : Nat) (localEnv : TenvValExp) (n : MlString)
    (t : SemanticT) :
    tenvValExpOk localEnv ∧ numTvs localEnv = 0 →
      (tveLookup n tvs localEnv = some (l, t) ↔ tveLookup n 0 localEnv = some (l, t)) := by
  intro h
  induction localEnv generalizing tvs l t with
  | empty => simp [tveLookup]
  | bindTvar bound rest ih =>
    simp only [tenvValExpOk, numTvs, tveLookup] at h ⊢
    obtain ⟨hok, hnum⟩ := h
    have zero : bound = 0 := by omega
    rw [zero]
    exact ih tvs l t ⟨hok, by omega⟩
  | bindName name bound ty rest ih =>
    simp only [tenvValExpOk, numTvs, tveLookup] at h ⊢
    obtain ⟨head1, hnum⟩ := h
    obtain ⟨hfree, hok⟩ := head1
    by_cases same : name = n
    · rw [if_pos same, if_pos same]
      have freeHere : checkFreevars bound [] ty = true := by simpa [hnum] using hfree
      have incEq : deBruijnInc bound tvs ty = deBruijnInc bound 0 ty := by
        rw [nil_deBruijnInc bound tvs ty (Or.inl freeHere), deBruijnInc_zero.1]
      rw [incEq]
    · rw [if_neg same, if_neg same]
      exact ih tvs l t ⟨hok, hnum⟩

/-- Substituting through a bound variable list keeps the list structure. -/
@[hol "cakeml/semantics/proofs/typeSysPropsScript.sml" "deBruijn_subst_E_bvl"]
theorem deBruijnSubstTenvE_bvl (tenv1 : List (MlString × SemanticT))
    (tenv2 : TenvValExp) (tvs : Nat) (targs : List SemanticT) :
    deBruijnSubstTenvE targs (bindVarList tvs tenv1 tenv2) =
      bindVarList tvs
        (tenv1.map fun (x, t) => (x, deBruijnSubst (tvs + numTvs tenv2)
          (targs.map (deBruijnInc 0 (tvs + numTvs tenv2))) t))
        (deBruijnSubstTenvE targs tenv2) := by
  induction tenv1 generalizing tenv2 with
  | nil => simp [bindVarList]
  | cons entry rest ih =>
    rcases entry with ⟨x, t⟩
    simp only [bindVarList, List.map_cons, deBruijnSubstTenvE, numTvs_bindVarList, ih]

end Flapjack.TypeSysProps
