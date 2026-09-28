import Flapjack.Pancake.CrepToLoop
import Flapjack.Pancake.CrepToLoop.ContextExact
import Flapjack.Pancake.LoopLive
import Flapjack.Pancake.Semantics.CrepSem.HOLState
import Flapjack.Misc.Sptree

namespace Flapjack

open Flapjack.Basis.Pure.MlString
open Flapjack.Compiler.Encoders.Asm

/-! The broad projection is local to this standalone map-parameter witness. -/
private def CompFuncMapParam.toBroadlookup (map : HolFiniteMapExact α β) :
    α → Option β := map.lookup

private def CompFuncMapParam.ofBroad (lookup : α → Option β)
    (support : ∃ keys : List α, ∀ key, lookup key ≠ none → key ∈ keys) :
    HolFiniteMapExact α β := ⟨lookup, support⟩

/-- Canonical lookup/support roundtrip witness for the exact comp-func `fs`
parameter qualifier. -/
theorem holFmapAsFiniteSupportParamWitness_compFuncHOLExact_fs
    (fs : HolFiniteMapExact MlString (Nat × Nat)) :
    CompFuncMapParam.ofBroad (CompFuncMapParam.toBroadlookup fs)
      fs.finiteSupport = fs := by
  cases fs
  rfl

/-! ## Exact source compiler wrapper -/

/-- Exact HOL `crep_to_loop$comp_func_def` (`crep_to_loopScript.sml:235`)
over the faithful finite-map, Crep, and Loop carriers. HOL constructs its
variable map with `FEMPTY |++ ZIP (params, GENLIST I (LENGTH params))`, its
initial live set with `list_to_num_set (GENLIST I (LENGTH params))`, sets
`vmax = LENGTH params - 1`, and calls the unoptimized `compile` definition.
`updateList` renders the finite-map `|++`, `List.range` renders the indexed
`GENLIST`, and `sptListInsert` renders `list_to_num_set`. The target, function
map, word width, and program carriers are the reviewed HOL counterparts. This
tag does not claim that the String/list-backed production `crepCompFunc` has
been routed through this exact definition; that projection and routing remains
tracked by `flapjack-pxn.18.5.6.28.1`. -/
@[hol "cakeml/pancake/crep_to_loopScript.sml" "comp_func_def"
  (fmap_as_finite_support_parameters := [fs]) (words_as_type_indexed_bitvec)]
def compFuncHOLExact {width : Nat} [NeZero width]
    (target : AsmArchitecture)
    (fs : HolFiniteMapExact MlString (Nat × Nat))
    (params : List Nat) (body : CrepProgHOL width) : HolLoopProg width :=
  let vmap := HolFiniteMapExact.empty.updateList
    (params.zip (List.range params.length))
  let live := sptListInsert (List.range params.length) (.ln : NumSet)
  compileHOLExact
    (mkCtxtExact target vmap fs (params.length - 1)) live body

/-! The optimised Crepe-to-Loop entry point corresponding to
    `crep_to_loop$ocompile` (`crep_to_loopScript.sml:216`). -/
def oCompile [OfNat α 0] [OfNat α 1]
    (context : LoopContext α) (live : List Nat) (program : CrepProg α) :
    LoopProg α :=
  loopLiveOptimise (compileCrepToLoop context live program)

/-! Production helper corresponding to the shape of CakeML Pancake's
    `comp_func_def` (`crep_to_loopScript.sml:235`). It is intentionally
    untagged: it uses RISC-V `Architecture`, String-keyed production function
    maps, and the generic executable `LoopProg`, while HOL uses `asm$architecture`,
    `mlstring` keys, and `HolLoopProg`; moreover it calls the production
    `compileCrepToLoop`/`loopLiveOptimise`, not an exact `compile_def` port.
    The exact `comp_func_def` remains blocked on the faithful program compiler
    tracked by `flapjack-pxn.18.5.6.28`. -/
def crepCompFunc [OfNat α 0] [OfNat α 1]
    (target : RiscV.Architecture) (functions : InfoMap (Nat × Nat))
    (params : List Nat) (body : CrepProg α) : LoopProg α :=
  let context : LoopContext α := crepMkCtxt target (crepMakeVmap params)
    functions (params.length - 1)
  oCompile context (List.range params.length) body

theorem oCompile_skip [OfNat α 0] [OfNat α 1]
    (context : LoopContext α) (live : List Nat) :
    oCompile context live (.skip : CrepProg α) = .mark .skip := by
  simp [oCompile, compileCrepToLoop, loopCompileProg, loopLiveOptimise,
    loopLiveComp, loopShrink, loopShrinkLeaf, loopMarkAll, LoopCall.comp]

end Flapjack
