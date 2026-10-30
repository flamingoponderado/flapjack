import Flapjack.Compiler.Backend.SourceToFlat.CompileExp
import Flapjack.Compiler.Backend.FlatProps.GlobalBagProperties

/-! Global-initialization invariants for source-to-flat expression compilation.
The untagged supporting lemmas are Flapjack proof infrastructure; the two
source theorems below carry their original references. -/
namespace Flapjack.Compiler.Backend.SourceToFlat
open Flapjack.AstHOL Flapjack.NamespaceHOL Flapjack.Basis.Pure.MlString
open Flapjack.Compiler.Backend.FlatProps

/-- Translating a source primitive never creates a global initialization. -/
@[hol "cakeml/compiler/backend/proofs/source_to_flatProofScript.sml" "op_gbag_astOp_to_flatOp"]
theorem opGlobalBag_astOpToFlatOp (op : AstHOL.Op) :
    opGlobalBag (astOpToFlatOp op) = emptyGlobalBag := by
  cases op <;> rfl

private theorem unionEmpty : unionGlobalBag emptyGlobalBag emptyGlobalBag = emptyGlobalBag := by
  funext key
  simp [unionGlobalBag, emptyGlobalBag]

/-- Safety of one compiled expression with respect to global writes. -/
def CompiledGlobalSafe (e : FlatLang.Exp) : Prop := esgcFree e ∧ setGlobals e = emptyGlobalBag

private theorem esgcFreeList_iff (xs : List FlatLang.Exp) :
    esgcFreeList xs ↔ ∀ x ∈ xs, esgcFree x := by
  induction xs with
  | nil => simp [esgcFreeList]
  | cons x xs ih => simp [esgcFreeList, ih]

private theorem reverse_safe (xs : List FlatLang.Exp) (hfree : esgcFreeList xs)
    (hbag : elistGlobals xs = emptyGlobalBag) :
    esgcFreeList xs.reverse ∧ elistGlobals xs.reverse = emptyGlobalBag := by
  constructor
  · apply (esgcFreeList_iff _).mpr
    intro x hx
    exact (esgcFreeList_iff xs).mp hfree x (List.mem_reverse.mp hx)
  · apply (elistGlobals_eq_empty _).mpr
    intro x hx
    exact (elistGlobals_eq_empty xs).mp hbag x (List.mem_reverse.mp hx)

private theorem foldLets_safe (xs : List FlatLang.Exp) (body : FlatLang.Exp)
    (hfree : esgcFreeList xs) (hbag : elistGlobals xs = emptyGlobalBag)
    (hbody : CompiledGlobalSafe body) :
    CompiledGlobalSafe (xs.foldr (FlatLang.Exp.let_ .none none) body) := by
  induction xs with
  | nil => exact hbody
  | cons x xs ih =>
    simp only [esgcFreeList] at hfree
    simp only [elistGlobals] at hbag
    have hx : esgcFree x := hfree.1
    have hs : esgcFreeList xs := hfree.2
    have bags : setGlobals x = emptyGlobalBag ∧ elistGlobals xs = emptyGlobalBag :=
      unionGlobalBag_eq_empty _ _ |>.mp hbag
    have rest := ih hs bags.2
    simpa [CompiledGlobalSafe, esgcFree, setGlobals, bags.1, rest.1, rest.2, unionEmpty] using hx

mutual
/-- Compiled expressions introduce no global initialization. -/
theorem compileExp_globalSafe (t : List MlString) (env : Environment) :
    (e : AstHOL.Exp) → CompiledGlobalSafe (compileExp t env e)
  | .raise e => by
      have h := compileExp_globalSafe t env e
      simpa [CompiledGlobalSafe, compileExp, esgcFree, setGlobals] using h
  | .handle e rows => by
      have h := compileExp_globalSafe t env e
      have hs := compilePes_globalSafe t env rows
      simp [CompiledGlobalSafe, compileExp, esgcFree, setGlobals, h.1, h.2, hs.1, hs.2, unionEmpty]
  | .lit _ => by simp [CompiledGlobalSafe, compileExp, esgcFree, setGlobals]
  | .con name es => by
      have h := compileExps_globalSafe t env es
      simp [CompiledGlobalSafe, compileExp, esgcFree, setGlobals, h.1, h.2]
  | .var id => by
      cases lookup : nsLookup env.v id with
      | none => simp [CompiledGlobalSafe, compileExp, lookup, esgcFree, setGlobals]
      | some name => cases name <;> simp [CompiledGlobalSafe, compileExp, lookup, compileVar, esgcFree, esgcFreeList, setGlobals, elistGlobals, opGlobalBag, unionEmpty]
  | .fn x body => by
      have h := compileExp_globalSafe t { env with v := nsBind x (.localName .none x) env.v } body
      simp [CompiledGlobalSafe, compileExp, esgcFree, setGlobals, h.2]
  | .app op es => by
      have hs := compileExps_globalSafe t env es
      by_cases empty : op = .aallocEmpty
      · subst op
        simp only [compileExp, ↓reduceIte]
        have rev := reverse_safe (compileExps t env es) hs.1 hs.2
        apply foldLets_safe _ _ rev.1 rev.2
        simp [CompiledGlobalSafe, esgcFree, esgcFreeList, setGlobals, elistGlobals, opGlobalBag, unionEmpty]
      · by_cases eval : op = .eval
        · subst op
          simp [CompiledGlobalSafe, compileExp, esgcFree, esgcFreeList, esgcFreeRows, setGlobals,
            rowGlobals, elistGlobals, opGlobalBag, hs.1, hs.2, unionEmpty]
        · by_cases envId : op = .envId
          · subst op
            cases es with
            | nil => simp [CompiledGlobalSafe, compileExp, compileExps, esgcFree, esgcFreeList, setGlobals, elistGlobals, opGlobalBag, unionEmpty]
            | cons e es =>
              cases es with
              | nil => simpa [compileExp, compileExps] using compileExp_globalSafe t env e
              | cons e' rest =>
                simp [CompiledGlobalSafe, compileExp, esgcFree, setGlobals, opGlobalBag, hs.1, hs.2, unionEmpty]
          · simp [CompiledGlobalSafe, compileExp, empty, eval, envId, esgcFree, setGlobals,
              opGlobalBag_astOpToFlatOp, hs.1, hs.2, unionEmpty]
  | .log op a b => by
      have ha := compileExp_globalSafe t env a
      have hb := compileExp_globalSafe t env b
      cases op <;> simp [CompiledGlobalSafe, compileExp, esgcFree, esgcFreeList, setGlobals, FlatLang.mkBool,
        elistGlobals, ha.1, ha.2, hb.1, hb.2, unionEmpty]
  | .if_ a b c => by
      have ha := compileExp_globalSafe t env a
      have hb := compileExp_globalSafe t env b
      have hc := compileExp_globalSafe t env c
      simp [CompiledGlobalSafe, compileExp, esgcFree, setGlobals, ha.1, ha.2, hb.1, hb.2, hc.1, hc.2, unionEmpty]
  | .mat e rows => by
      have h := compileExp_globalSafe t env e
      have hs := compilePes_globalSafe t env rows
      simp [CompiledGlobalSafe, compileExp, esgcFree, setGlobals, h.1, h.2, hs.1, hs.2, unionEmpty]
  | .let_ name a b => by
      cases name with
      | none =>
        have ha := compileExp_globalSafe t env a
        have hb := compileExp_globalSafe t env b
        simp [CompiledGlobalSafe, compileExp, esgcFree, setGlobals, ha.1, ha.2, hb.1, hb.2, unionEmpty]
      | some x =>
        have ha := compileExp_globalSafe (x :: t) env a
        have hb := compileExp_globalSafe t { env with v := nsBind x (.localName .none x) env.v } b
        simp [CompiledGlobalSafe, compileExp, esgcFree, setGlobals, ha.1, ha.2, hb.1, hb.2, unionEmpty]
  | .letrec funs body => by
      let names := funs.map Prod.fst
      let newEnv := nsBindList (names.map fun x => (x, VarName.localName .none x)) env.v
      have hf := compileFuns_globalSafe t { env with v := newEnv } funs
      have hb := compileExp_globalSafe t { env with v := newEnv } body
      simp only [newEnv, names, List.map_map] at hf hb
      simp [CompiledGlobalSafe, compileExp, esgcFree, setGlobals, hf.2, hb.1, hb.2, unionEmpty]
  | .tannot e _ => compileExp_globalSafe t env e
  | .lannot e (.locs _ _) => compileExp_globalSafe t env e
termination_by e => sizeOf e
decreasing_by all_goals simp_wf <;> omega

theorem compileExps_globalSafe (t : List MlString) (env : Environment) :
    (es : List AstHOL.Exp) → esgcFreeList (compileExps t env es) ∧
      elistGlobals (compileExps t env es) = emptyGlobalBag
  | [] => by simp [compileExps, esgcFreeList, elistGlobals]
  | e :: es => by
      have h := compileExp_globalSafe t env e
      have hs := compileExps_globalSafe t env es
      simp [compileExps, esgcFreeList, elistGlobals, h.1, h.2, hs.1, hs.2, unionEmpty]
termination_by es => sizeOf es
decreasing_by all_goals simp_wf <;> omega

theorem compilePes_globalSafe (t : List MlString) (env : Environment) :
    (rows : List (AstHOL.Pat × AstHOL.Exp)) → esgcFreeRows (compilePes t env rows) ∧
      rowGlobals (compilePes t env rows) = emptyGlobalBag
  | [] => by simp [compilePes, esgcFreeRows, rowGlobals]
  | (p, e) :: rows => by
      have h := compileExp_globalSafe t { env with v := nsBindList (patTups .none (AstHOL.patBindings p)) env.v } e
      have hs := compilePes_globalSafe t env rows
      simp [compilePes, esgcFreeRows, rowGlobals, h.1, h.2, hs.1, hs.2, unionEmpty]
termination_by rows => sizeOf rows
decreasing_by all_goals simp_wf <;> omega

theorem compileFuns_globalSafe (t : List MlString) (env : Environment) :
    (funs : List (VarN × VarN × AstHOL.Exp)) →
      esgcFreeList ((compileFuns t env funs).map (fun (_, _, e) => e)) ∧
      funGlobals (compileFuns t env funs) = emptyGlobalBag
  | [] => by simp [compileFuns, esgcFreeList, funGlobals]
  | (f, x, e) :: funs => by
      have h := compileExp_globalSafe (f :: t) { env with v := nsBind x (.localName .none x) env.v } e
      have hs := compileFuns_globalSafe t env funs
      simp [compileFuns, esgcFreeList, funGlobals, h.1, h.2, hs.1, hs.2, unionEmpty]
termination_by funs => sizeOf funs
decreasing_by all_goals simp_wf <;> omega
end

private theorem rowGlobals_eq_elist (rows : List (FlatLang.Pat × FlatLang.Exp)) :
    rowGlobals rows = elistGlobals (rows.map Prod.snd) := by
  induction rows with
  | nil => simp [rowGlobals, elistGlobals]
  | cons row rows ih =>
    obtain ⟨p, e⟩ := row
    simp [rowGlobals, elistGlobals, ih]

private theorem funGlobals_eq_elist (funs : List (VarN × VarN × FlatLang.Exp)) :
    funGlobals funs = elistGlobals (funs.map (fun (_, _, e) => e)) := by
  induction funs with
  | nil => simp [funGlobals, elistGlobals]
  | cons fn funs ih =>
    obtain ⟨name, arg, body⟩ := fn
    simp [funGlobals, elistGlobals, ih]

private theorem esgcFreeRows_iff (rows : List (FlatLang.Pat × FlatLang.Exp)) :
    esgcFreeRows rows ↔ esgcFreeList (rows.map Prod.snd) := by
  induction rows with
  | nil => simp [esgcFreeRows, esgcFreeList]
  | cons row rows ih =>
    obtain ⟨p, e⟩ := row
    simp [esgcFreeRows, esgcFreeList, ih]

/-- Compiled expressions, lists, pattern rows and recursive function bodies
are free of global-initialization effects. -/
@[hol "cakeml/compiler/backend/proofs/source_to_flatProofScript.sml" "compile_exp_esgc_free"]
theorem compileExp_esgcFree :
    (∀ t env e, esgcFree (compileExp t env e) ∧ setGlobals (compileExp t env e) = emptyGlobalBag) ∧
    (∀ t env es, (∀ e ∈ compileExps t env es, esgcFree e) ∧
      elistGlobals (compileExps t env es) = emptyGlobalBag) ∧
    (∀ t env rows, (∀ e ∈ (compilePes t env rows).map Prod.snd, esgcFree e) ∧
      elistGlobals ((compilePes t env rows).map Prod.snd) = emptyGlobalBag) ∧
    (∀ t env funs, (∀ e ∈ (compileFuns t env funs).map (fun (_, _, e) => e), esgcFree e) ∧
      elistGlobals ((compileFuns t env funs).map (fun (_, _, e) => e)) = emptyGlobalBag) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro t env e
    exact compileExp_globalSafe t env e
  · intro t env es
    obtain ⟨free, bag⟩ := compileExps_globalSafe t env es
    exact ⟨(esgcFreeList_iff _).mp free, bag⟩
  · intro t env rows
    obtain ⟨free, bag⟩ := compilePes_globalSafe t env rows
    exact ⟨(esgcFreeList_iff _).mp ((esgcFreeRows_iff _).mp free),
      (rowGlobals_eq_elist _).symm.trans bag⟩
  · intro t env funs
    obtain ⟨free, bag⟩ := compileFuns_globalSafe t env funs
    exact ⟨(esgcFreeList_iff _).mp free, (funGlobals_eq_elist _).symm.trans bag⟩

end Flapjack.Compiler.Backend.SourceToFlat
