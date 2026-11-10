import Flapjack.Compiler.Backend.FlatElim.Proofs.ValueGlobals

/-! Global dependencies of mapped recursive closures. -/
namespace Flapjack.Compiler.Backend.FlatElim

@[hol "cakeml/compiler/backend/proofs/flat_elimProofScript.sml" "find_v_globals_MAP_Recclosure"]
theorem findValueGlobals_map_recclosure {α β : Type}
    (env : FlatSem.Environment FlatSem.Value) (f : α → Flapjack.AstHOL.VarN) :
    ∀ (funs : List α) (_v : β)
      (l : List (Flapjack.AstHOL.VarN × Flapjack.AstHOL.VarN × FlatLang.Exp)),
      sptDomain (findValuesGlobals (funs.map (fun x => .recclosure env l (f x)))) =
        if funs.isEmpty then (fun _ => False) else
          (fun key => sptMem key (findValuesGlobals (env.v.map Prod.snd)) ∨
            sptMem key (findGlobalsList destGlobalVarLookup (l.map (fun (_, _, body) => body)))) := by
  intro funs _ l
  funext key
  apply propext
  induction funs with
  | nil => simp [findValuesGlobals, sptDomain]
  | cons x xs ih =>
    change sptMem key (findValuesGlobals ((x :: xs).map (fun z => .recclosure env l (f z)))) ↔ _
    change sptMem key (findValuesGlobals (xs.map (fun z => .recclosure env l (f z)))) ↔ _ at ih
    cases env with
    | mk bindings =>
      simp [findValuesGlobals, findValueGlobals, findBindingsGlobals_eq_map,
        findFunctionGlobals_eq_map, sptMem_sptUnion] at *
      cases xs <;> simp_all

end Flapjack.Compiler.Backend.FlatElim
