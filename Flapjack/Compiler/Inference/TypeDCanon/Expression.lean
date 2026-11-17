module

public import Flapjack.Compiler.Inference.TypeDCanon.LocalEnv
public import Flapjack.Compiler.Inference.TypeDCanon.Operator

@[expose] public section

/-! Expression typing under good type-identifier renamings. -/
namespace Flapjack.Compiler.Inference.TypeDCanon
open Flapjack Flapjack.Basis.Pure.MlString Flapjack.NamespaceHOL Flapjack.AstHOL Flapjack.TypeSystemHOL
  Flapjack.Compiler.Inference.InferProps Flapjack.Compiler.Inference.TypeDCanon

/-- List-map identity supplies the fixed IDs used in the source proof. -/
private theorem fixed {α : Type} (f : α → α) (xs : List α) (h : xs.map f = xs) : ∀ x ∈ xs, f x = x := by
  induction xs with
  | nil => simp
  | cons y ys ih =>
    simp only [List.map_cons, List.cons.injEq] at h
    intro x mem
    rcases List.mem_cons.mp mem with rfl | mem
    · exact h.1
    · exact ih h.2 x mem

/-- The function-list rule's name lookup is unchanged by renaming binding types. -/
private theorem lookupMapNone (name : MlString) (bindings : List (MlString × SemanticT)) (f : Nat → Nat) :
    bindings.lookup name = none →
      (bindings.map (fun entry => (entry.1, tsTidRename f entry.2))).lookup name = none := by
  induction bindings with
  | nil => simp
  | cons entry rest ih =>
    rcases entry with ⟨key, value⟩
    by_cases same : name = key
    · subst key; simp
    · have different : (name == key) = false := by simp [same]
      simpa [List.lookup, different] using ih

/-- Good renamings preserve expression, expression-list, and function typing. -/
@[hol "cakeml/compiler/inference/proofs/type_dCanonScript.sml" "type_e_ts_tid_rename"]
theorem typeETsTidRename (f : Nat → Nat) : goodRemap f →
    (∀ env bvs e t, TypeE env bvs e t → TypeE (remapTenv f env) (remapTenvE f bvs) e (tsTidRename f t)) ∧
    (∀ env bvs es ts, TypeEs env bvs es ts → TypeEs (remapTenv f env) (remapTenvE f bvs) es (ts.map (tsTidRename f))) ∧
    (∀ env bvs funs bindings, TypeFuns env bvs funs bindings → TypeFuns (remapTenv f env) (remapTenvE f bvs) funs (bindings.map (fun entry => (entry.1, tsTidRename f entry.2)))) := by
  intro good
  have fixed := fixed f (TlistNum :: TboolNum :: primTypeNums) good
  have fint : f TintNum = TintNum := fixed TintNum (by simp [primTypeNums])
  have fchar : f TcharNum = TcharNum := fixed TcharNum (by simp [primTypeNums])
  have fstr : f TstringNum = TstringNum := fixed TstringNum (by simp [primTypeNums])
  have fw8 : f Tword8Num = Tword8Num := fixed Tword8Num (by simp [primTypeNums])
  have fw64 : f Tword64Num = Tword64Num := fixed Tword64Num (by simp [primTypeNums])
  have fdouble : f TdoubleNum = TdoubleNum := fixed TdoubleNum (by simp [primTypeNums])
  have fexn : f TexnNum = TexnNum := fixed TexnNum (by simp [primTypeNums])
  have fbool : f TboolNum = TboolNum := fixed TboolNum (by simp)
  have ftup : f TtupNum = TtupNum := fixed TtupNum (by simp [primTypeNums])
  have ffn : f TfnNum = TfnNum := fixed TfnNum (by simp [primTypeNums])
  refine ⟨?_, ?_, ?_⟩
  all_goals
    intro env bvs es ts h
    let P := fun bvs e t (_ : TypeE env bvs e t) => TypeE (remapTenv f env) (remapTenvE f bvs) e (tsTidRename f t)
    let Ps := fun bvs es ts (_ : TypeEs env bvs es ts) => TypeEs (remapTenv f env) (remapTenvE f bvs) es (ts.map (tsTidRename f))
    let Pf := fun bvs funs ts (_ : TypeFuns env bvs funs ts) => TypeFuns (remapTenv f env) (remapTenvE f bvs) funs (ts.map (fun entry => (entry.1, tsTidRename f entry.2)))
    let Pb := fun bvs input output clauses (_ : TypeBranches env bvs input output clauses) => TypeBranches (remapTenv f env) (remapTenvE f bvs) (tsTidRename f input) (tsTidRename f output) clauses
    first
    | refine TypeE.rec (motive_1 := P) (motive_2 := Ps) (motive_3 := Pf) (motive_4 := Pb)
        ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ h
    | refine TypeEs.rec (motive_1 := P) (motive_2 := Ps) (motive_3 := Pf) (motive_4 := Pb)
        ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ h
    | refine TypeFuns.rec (motive_1 := P) (motive_2 := Ps) (motive_3 := Pf) (motive_4 := Pb)
        ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ h
    all_goals dsimp only [P, Ps, Pf, Pb] at *
    case refine_1 =>
      intro b n
      simpa [tsTidRename, tsTidRenameList, Tint, fint] using TypeE.intLit (remapTenv f env) (remapTenvE f b) n
    case refine_2 =>
      intro b c
      simpa [tsTidRename, tsTidRenameList, Tchar, fchar] using TypeE.charLit (remapTenv f env) (remapTenvE f b) c
    case refine_3 =>
      intro b s
      simpa [tsTidRename, tsTidRenameList, Tstring, fstr] using TypeE.stringLit (remapTenv f env) (remapTenvE f b) s
    case refine_4 =>
      intro b w
      simpa [tsTidRename, tsTidRenameList, Tword8, fw8] using TypeE.word8Lit (remapTenv f env) (remapTenvE f b) w
    case refine_5 =>
      intro b w
      simpa [tsTidRename, tsTidRenameList, Tword64, fw64] using TypeE.word64Lit (remapTenv f env) (remapTenvE f b) w
    case refine_6 =>
      intro b w
      simpa [tsTidRename, tsTidRenameList, Tdouble, fdouble] using TypeE.float64Lit (remapTenv f env) (remapTenvE f b) w
    case refine_7 =>
      intro b e t free typed ih
      apply TypeE.raise (remapTenv f env) (remapTenvE f b) e (tsTidRename f t)
      · simpa [numTvsRemapTenvE] using (checkFreevarsTsTidRename (numTvs b) [] t f).2 free
      · simpa [tsTidRename, tsTidRenameList, Texn, fexn] using ih
    case refine_8 =>
      intro b e clauses t typed nonempty branches ih ihBranches
      apply TypeE.handle (remapTenv f env) (remapTenvE f b) e clauses (tsTidRename f t) ih nonempty
      simpa [tsTidRename, tsTidRenameList, Texn, fexn] using ihBranches
    case refine_9 =>
      intro b name es params id args types free arity typed lookup ih
      have lookupPrime : nsLookup (remapTenv f env).c name =
          some (params, types.map (tsTidRename f), f id) := by
        simp [remapTenv, nsLookup_nsMap, lookup]
      have typedPrime := ih
      rw [mapSubstRename] at typedPrime
      have freePrime : ((args.map (tsTidRename f)).all (checkFreevars (numTvs (remapTenvE f b)) [])) = true := by
        simpa [numTvsRemapTenvE] using checkFreevarsMapRename (numTvs b) args f free
      simpa [tsTidRename, tsTidRenameList_eq_map] using
        TypeE.constructor (remapTenv f env) (remapTenvE f b) name es params (f id)
          (args.map (tsTidRename f)) (types.map (tsTidRename f)) freePrime
          (by simpa using arity) typedPrime lookupPrime
    case refine_10 =>
      intro b es types typed ih
      simpa [tsTidRename, tsTidRenameList_eq_map, Ttup, ftup] using TypeE.tuple (remapTenv f env) (remapTenvE f b) es (types.map (tsTidRename f)) ih
    case refine_11 =>
      intro b name t args tvs arity free lookup
      have lookupPrime : lookupVar name (remapTenvE f b) (remapTenv f env) = some (tvs, tsTidRename f t) := by
        have localLookup := lookupVarERemapTenvE name b f
        cases localResult : lookupVarE name b with
        | none =>
          simp [lookupVar, localResult] at lookup
          simp [lookupVar, localLookup, localResult, remapTenv, nsLookup_nsMap, lookup]
        | some value =>
          simp [lookupVar, localResult] at lookup
          cases value
          simp_all [lookupVar]
      have freePrime : ((args.map (tsTidRename f)).all (checkFreevars (numTvs (remapTenvE f b)) [])) = true := by
        simpa [numTvsRemapTenvE] using checkFreevarsMapRename (numTvs b) args f free
      simpa [tsTidRenameDeBruijnSubst] using
        TypeE.var (remapTenv f env) (remapTenvE f b) name (tsTidRename f t) (args.map (tsTidRename f)) tvs
          (by simpa using arity) freePrime lookupPrime
    case refine_12 =>
      intro b name body t1 t2 free typed ih
      have freePrime : checkFreevars (numTvs (remapTenvE f b)) [] (tsTidRename f t1) = true := by
        simpa [numTvsRemapTenvE] using (checkFreevarsTsTidRename (numTvs b) [] t1 f).2 free
      simpa [tsTidRename, tsTidRenameList, Tfn, ffn, remapTenvE] using TypeE.fn (remapTenv f env) (remapTenvE f b) name body (tsTidRename f t1) (tsTidRename f t2) freePrime ih
    case refine_13 =>
      intro b op es ts t typed operator free ih
      apply TypeE.app (remapTenv f env) (remapTenvE f b) op es (ts.map (tsTidRename f)) (tsTidRename f t) ih (typeOpTsTidRename f good op ts t operator)
      simpa [numTvsRemapTenvE] using (checkFreevarsTsTidRename (numTvs b) [] t f).2 free
    case refine_14 =>
      intro b op e1 e2 first second ih1 ih2
      have firstPrime := ih1
      have secondPrime := ih2
      simp [tsTidRename, tsTidRenameList, fbool] at firstPrime secondPrime ⊢
      exact TypeE.log (remapTenv f env) (remapTenvE f b) op e1 e2 firstPrime secondPrime
    case refine_15 =>
      intro b guard yes no t condition yesT noT ih1 ih2 ih3
      apply TypeE.if_ (remapTenv f env) (remapTenvE f b) guard yes no (tsTidRename f t)
      · simpa [tsTidRename, tsTidRenameList, Tbool, fbool] using ih1
      · exact ih2
      · exact ih3
    case refine_16 =>
      intro b e clauses t1 t2 typed nonempty branches ih ihBranches
      exact .match_ (remapTenv f env) (remapTenvE f b) e clauses _ _ ih nonempty ihBranches
    case refine_17 =>
      intro b name e1 e2 t1 t2 value body ih1 ih2
      apply TypeE.let_ (remapTenv f env) (remapTenvE f b) name e1 e2 (tsTidRename f t1) (tsTidRename f t2) ih1
      cases name <;> simpa [optBindName, remapTenvE] using ih2
    case refine_18 =>
      intro b funs e t bindings functions body ihF ihE
      apply TypeE.letrec (remapTenv f env) (remapTenvE f b) funs e (tsTidRename f t)
        (bindings.map (fun entry => (entry.1, tsTidRename f entry.2)))
      · simpa [remapTenvEBindVarList] using ihF
      · simpa [remapTenvEBindVarList] using ihE
    case refine_19 =>
      intro b e t free names typed ih
      have namesPrime := (checkTypeNamesTsTidRename env.t t f).1 names
      have subst := tsTidRenameTypeNameSubst env.t t f () ⟨good, names⟩
      rw [subst] at ih ⊢
      exact .annotation (remapTenv f env) (remapTenvE f b) e t free namesPrime ih
    case refine_20 =>
      intro b e loc t typed ih
      exact .location (remapTenv f env) (remapTenvE f b) e loc _ ih
    case refine_21 =>
      intro b
      exact .nil (remapTenv f env) (remapTenvE f b)
    case refine_22 =>
      intro b e es t ts head tail ihH ihT
      exact .cons (remapTenv f env) (remapTenvE f b) e es _ _ ihH ihT
    case refine_23 =>
      intro b
      exact .nil (remapTenv f env) (remapTenvE f b)
    case refine_24 =>
      intro b name arg body funs bindings t1 t2 free typed tail unique ihH ihT
      have freePrime : checkFreevars (numTvs (remapTenvE f b)) []
          (.app [tsTidRename f t1, tsTidRename f t2] 4) = true := by
        simpa [tsTidRename, tsTidRenameList, Tfn, ffn, numTvsRemapTenvE] using
          (checkFreevarsTsTidRename (numTvs b) [] (.app [t1, t2] 4) f).2 free
      have uniquePrime := lookupMapNone name bindings f unique
      have headPrime : TypeE (remapTenv f env)
          (.bindName arg 0 (tsTidRename f t1) (remapTenvE f b)) body (tsTidRename f t2) := by
        simpa [remapTenvE] using ihH
      simpa [tsTidRename, tsTidRenameList, Tfn, ffn, remapTenvE] using
        TypeFuns.cons (remapTenv f env) (remapTenvE f b) name arg body funs
          (bindings.map (fun entry => (entry.1, tsTidRename f entry.2)))
          (tsTidRename f t1) (tsTidRename f t2) freePrime headPrime ihT uniquePrime
    case refine_25 =>
      intro b input output
      exact .nil (remapTenv f env) (remapTenvE f b) _ _
    case refine_26 =>
      intro b input output p body rest bindings distinct pattern expression tail ihE ihT
      apply TypeBranches.cons (remapTenv f env) (remapTenvE f b) (tsTidRename f input) (tsTidRename f output)
        p body rest (bindings.map (fun entry => (entry.1, tsTidRename f entry.2))) distinct
      · simpa [numTvsRemapTenvE] using (typePTsTidRename f good).1 (numTvs b) env p input bindings pattern
      · simpa [remapTenvEBindVarList] using ihE
      · exact ihT

end Flapjack.Compiler.Inference.TypeDCanon
