import Flapjack.Compiler.Backend.SourceToFlat.Proofs.GlobalEnvConditions
import Flapjack.Compiler.Backend.SourceToFlat.Proofs.OracleStep
import Flapjack.Compiler.Backend.SourceToFlat.CompileProg
import Flapjack.PanToCrepMaxList

/-! Initial environments for source-to-flat compilation. -/
namespace Flapjack.Compiler.Backend.SourceToFlat
open Flapjack.AstHOL Flapjack.SemanticPrimitivesHOL Flapjack.Basis.Pure.MlString
open Flapjack.Compiler.Backend.BackendCommon

/-- The initial Eval state has either no Eval machinery or one empty oracle
  generation. The EvalDecs mode is not admitted by this precondition. -/
@[hol "cakeml/compiler/backend/proofs/source_to_flatProofScript.sml" "init_eval_state_ok_def"]
def initEvalStateOk : Option EvalState → Prop
  | none => True
  | some (.evalDecs _) => False
  | some (.evalOracle state) => state.generation = 0 ∧ state.envs = [[]]

/-- Initial Boolean and list constructor entries, in original order. -/
@[hol "cakeml/compiler/backend/proofs/source_to_flatProofScript.sml" "init_genv_ty_els_def"]
def initGenvTyEntries : List (Nat × List (Nat × Nat × Stamp)) :=
  [(FlatLang.boolId, [(falseTag, 0, .typeStamp (ofString "False") boolTypeNum),
                     (trueTag, 0, .typeStamp (ofString "True") boolTypeNum)]),
   (FlatSem.listId, [(consTag, 2, .typeStamp (ofString "::") listTypeNum),
                     (nilTag, 0, .typeStamp (ofString "[]") listTypeNum)].reverse)]

/-- Initial typed and exception constructor entries. -/
@[hol "cakeml/compiler/backend/proofs/source_to_flatProofScript.sml" "init_genv_els_def"]
def initGenvEntries : List (ConstructorKey × Stamp) :=
  initGenvTyEntries.flatMap (fun (id, entries) =>
    entries.map (fun (tag, arity, stamp) => (((tag, some id), arity), stamp))) ++
  [(((divTag, none), 0), divStamp), (((chrTag, none), 0), chrStamp),
   (((subscriptTag, none), 0), subscriptStamp), (((bindTag, none), 0), bindStamp)]

/-- Initial source-to-flat global environment, with the original finite maps. -/
@[hol "cakeml/compiler/backend/proofs/source_to_flatProofScript.sml" "init_genv_def"
  (fmap_as_finite_support := [c, tys])]
def initGenv : GlobalEnv :=
  { v := [], c := HolFiniteMapExact.updateListEq HolFiniteMapExact.empty initGenvEntries,
    tys := HolFiniteMapExact.updateListEq HolFiniteMapExact.empty
      (initGenvTyEntries.map (fun (id, entries) => (id, entries.map (fun (tag, arity, _) => (tag, arity))))) }

namespace Initialization
/-- Canonical finite-map representation witness for the initial environment. -/
theorem holFmapAsFiniteSupportWitness (env : GlobalEnv) : GlobalEnv.ofBroad (GlobalEnv.toBroad env) = env :=
  GlobalEnv.holFmapAsFiniteSupportWitness env
end Initialization

/-- First unused global, type, and exception indices for the initial map. -/
@[hol "cakeml/compiler/backend/proofs/source_to_flatProofScript.sml" "init_genv_next"]
def initGenvNext : NextIndices :=
  { vidx := 0,
    tidx := maxList (initGenvEntries.map (fun (_, stamp) => match stamp with
      | .typeStamp _ n => n | .exnStamp _ => 0)) + 1,
    eidx := maxList (initGenvEntries.map (fun (_, stamp) => match stamp with
      | .typeStamp _ _ => 0 | .exnStamp n => n)) + 1 }

/-- The initial next-index calculation evaluates to the original constants. -/
theorem initGenvNext_values : initGenvNext = ⟨0, 2, 4⟩ := by
  rfl

/-- The initial constructor map supplies the Boolean, list, and exception
constructors needed by the source-to-flat value invariant. -/
theorem initGenv_requiredConstructors : hasBools initGenv.c ∧ hasLists initGenv.c ∧ hasExns initGenv.c := by
  simp [hasBools, hasLists, hasExns, initGenv, initGenvEntries, initGenvTyEntries,
    HolFiniteMapExact.updateListEq, HolFiniteMapExact.empty, FUPDATE_LIST_HOL, FUPDATE_HOL,
    FlatLang.boolId, FlatSem.listId, boolTypeNum, listTypeNum, trueTag, falseTag, consTag, nilTag,
    divTag, chrTag, subscriptTag, bindTag]

/-- A finite update list can return only an inserted entry or an entry from
the original lookup function. -/
private theorem updateList_lookup_mem {α β : Type} [DecidableEq α]
    (entries : List (α × β)) (base : α → Option β) (key : α) (value : β)
    (found : FUPDATE_LIST_HOL base entries key = some value) :
    (key, value) ∈ entries ∨ base key = some value := by
  induction entries generalizing base with
  | nil => exact Or.inr found
  | cons entry entries ih =>
    rw [FUPDATE_LIST_HOL_cons] at found
    rcases ih (FUPDATE_HOL base entry) found with member | previous
    · exact Or.inl (List.mem_cons_of_mem entry member)
    · simp only [FUPDATE_HOL] at previous
      split at previous
      · rename_i equal
        rcases entry with ⟨entryKey, entryValue⟩
        simp only at equal previous
        cases equal
        cases previous
        exact Or.inl List.mem_cons_self
      · exact Or.inr previous

/-- Every entry in the initial constructor map comes from the original eight
constructor entries. -/
theorem initGenv_lookup_mem (key : ConstructorKey) (stamp : Stamp)
    (found : initGenv.c.lookup key = some stamp) : (key, stamp) ∈ initGenvEntries := by
  change FUPDATE_LIST_HOL (fun _ => none) initGenvEntries key = some stamp at found
  rcases updateList_lookup_mem initGenvEntries (fun _ => none) key stamp found with member | impossible
  · exact member
  · cases impossible

/-- Every typed constructor in the initial map belongs to its initial
constructor group. -/
theorem initGenv_typesOk : genvCTysOk initGenv.c initGenv.tys := by
  intro cn tyId arity present
  cases lookup : initGenv.c.lookup ((cn, some tyId), arity) with
  | none => simp [lookup] at present
  | some stamp =>
    have member := initGenv_lookup_mem ((cn, some tyId), arity) stamp lookup
    simp [initGenvEntries, initGenvTyEntries, FlatLang.boolId, FlatSem.listId,
      trueTag, falseTag, consTag, nilTag, divTag, chrTag, subscriptTag, bindTag] at member
    rcases member with first | second | third | fourth
    all_goals simp_all [initGenv, initGenvTyEntries, HolFiniteMapExact.updateListEq,
      HolFiniteMapExact.empty, FUPDATE_LIST_HOL, FUPDATE_HOL, FlatLang.boolId, FlatSem.listId,
      trueTag, falseTag, consTag, nilTag]

/-- The initial constructor map has the required constructors and preserves
constructor-type comparison and injectivity. -/
theorem initGenv_constructorsOk : genvCOk initGenv.c := by
  have boolNames : ofString "False" ≠ ofString "True" := by decide
  have listNames : ofString "[]" ≠ ofString "::" := by decide
  obtain ⟨bools, lists, exceptions⟩ := initGenv_requiredConstructors
  refine ⟨bools, exceptions, lists, ?_, ?_⟩
  · intro cn1 cn2 arity1 arity2 stamp1 stamp2 lookup1 lookup2
    have mem1 := initGenv_lookup_mem (cn1, arity1) stamp1 lookup1
    have mem2 := initGenv_lookup_mem (cn2, arity2) stamp2 lookup2
    simp [initGenvEntries, initGenvTyEntries, FlatLang.boolId, FlatSem.listId,
      trueTag, falseTag, consTag, nilTag, divTag, chrTag, subscriptTag, bindTag] at mem1 mem2
    rcases mem1 with h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1 <;>
      rcases mem2 with h2 | h2 | h2 | h2 | h2 | h2 | h2 | h2 <;>
      simp_all [SemanticPrimitivesHOL.ctorSameType, SemanticPrimitivesHOL.sameType,
        FlatSem.ctorSameType, boolTypeNum, listTypeNum, divStamp, chrStamp, subscriptStamp, bindStamp]
  · intro cn1 cn2 arity1 arity2 stamp lookup1 lookup2
    have mem1 := initGenv_lookup_mem (cn1, arity1) stamp lookup1
    have mem2 := initGenv_lookup_mem (cn2, arity2) stamp lookup2
    simp [initGenvEntries, initGenvTyEntries, FlatLang.boolId, FlatSem.listId,
      trueTag, falseTag, consTag, nilTag, divTag, chrTag, subscriptTag, bindTag] at mem1 mem2
    rcases mem1 with h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1 <;>
      rcases mem2 with h2 | h2 | h2 | h2 | h2 | h2 | h2 | h2 <;>
      simp_all [boolTypeNum, listTypeNum, divStamp, chrStamp, subscriptStamp, bindStamp,
        Ne.symm boolNames, Ne.symm listNames]

/-- The original initial-evaluation precondition supplies the initial
generation relation needed by the declaration simulation. -/
theorem initEvalStateOk_envGenRel (evalState : Option EvalState)
    (initial : initEvalStateOk evalState) :
    OracleInvariant.envGenRel ⟨0, 0, .ln⟩ evalState := by
  cases evalState with
  | none => trivial
  | some state =>
    cases state with
    | evalDecs state => exact False.elim initial
    | evalOracle state =>
      obtain ⟨generation, envs⟩ := initial
      simp [OracleInvariant.envGenRel, generation, envs]

/-- When the next oracle configuration is the result of compiling this
program, the compiled generation is retained in that configuration. This
discharges the future-generation premise of the declaration simulation. -/
theorem compileProg_envGenFutureRel {C : Type}
    (interp : Option (Value → Option (Config × C))) (evalState : Option EvalState)
    (config : Config) (decs : List Dec) (n : Nat) (next : NextIndices)
    (outEnv : Environment) (outGen : EnvironmentGenerationStore) (body : List FlatLang.Exp)
    (compiled : compileDecs [] 1 { config.next with vidx := config.next.vidx + 1 } config.modEnv
      ⟨0, config.envs.next, .ln⟩ decs = (n, next, outEnv, outGen, body))
    (oracleConfig : match OracleInvariant.srcOracNextCfg interp evalState with
      | none => True
      | some nextConfig => nextConfig = (compileProg config decs).1) :
    OracleInvariant.envGenFutureRel interp outGen evalState := by
  have generation := OracleInvariant.compileDecs_generation [] 1
    { config.next with vidx := config.next.vidx + 1 } config.modEnv
    ⟨0, config.envs.next, .ln⟩ decs n next outEnv outGen body compiled
  unfold OracleInvariant.envGenFutureRel
  cases eq : OracleInvariant.srcOracNextCfg interp evalState with
  | none => trivial
  | some nextConfig =>
    simp only [eq] at oracleConfig ⊢
    subst nextConfig
    refine ⟨outGen.envs, ?_, ?_⟩
    · simpa [compileProg, compiled, generation] using
        (Flapjack.sptLookup_sptInsert_same config.envs.next outGen.envs config.envs.envGens)
    · intro key member
      exact ⟨member, rfl⟩

end Flapjack.Compiler.Backend.SourceToFlat
