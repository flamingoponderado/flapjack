import Flapjack.Pancake.CrepToLoop
import Flapjack.Pancake.CrepLang.Exp
import Flapjack.Pancake.Semantics.CrepSem.HOLState
import Flapjack.Basis.Pure.MlString
import Flapjack.Compiler.Encoders.Asm
import Flapjack.Pancake.LoopLive

/-!
Exact finite-map carrier and context helpers for `crep_to_loopScript.sml`.
Production `LoopContext` remains list/String-backed; these declarations model
the HOL `context` datatype over its actual finite-map and mlstring carriers.
-/

namespace Flapjack

open Flapjack.Basis.Pure.MlString
open Flapjack.Compiler.Encoders.Asm

/-- Function-backed view with explicit finite-support evidence for the
    canonical finite-map carrier witness. -/
structure CrepToLoopContextBroad where
  varsLookup : Nat → Option Nat
  varsFiniteSupport : ∃ keys : List Nat, ∀ key, varsLookup key ≠ none → key ∈ keys
  funcsLookup : MlString → Option (Nat × Nat)
  funcsFiniteSupport : ∃ keys : List MlString,
    ∀ key, funcsLookup key ≠ none → key ∈ keys
  vmax : Nat
  target : AsmArchitecture

/-- Exact HOL `crep_to_loop$context` (`crep_to_loopScript.sml:11-18`). Both
    `|->` fields use the canonical finite-support carrier; function names use
    HOL `mlstring`; and `target` uses the exact `asm$architecture` datatype. -/
@[hol "cakeml/pancake/crep_to_loopScript.sml" "context"
  (fmap_as_finite_support := [vars, funcs])]
structure CrepToLoopContextExact where
  vars : HolFiniteMapExact Nat Nat
  funcs : HolFiniteMapExact MlString (Nat × Nat)
  vmax : Nat
  target : AsmArchitecture

namespace CrepToLoopContextExact

/-- Forget the finite-map wrapper while retaining the support witnesses. -/
def toBroad (context : CrepToLoopContextExact) : CrepToLoopContextBroad where
  varsLookup := context.vars.lookup
  varsFiniteSupport := context.vars.finiteSupport
  funcsLookup := context.funcs.lookup
  funcsFiniteSupport := context.funcs.finiteSupport
  vmax := context.vmax
  target := context.target

/-- Reconstruct the canonical finite-support maps from their lookup/support
    pairs. -/
def ofBroad (context : CrepToLoopContextBroad) : CrepToLoopContextExact where
  vars := ⟨context.varsLookup, context.varsFiniteSupport⟩
  funcs := ⟨context.funcsLookup, context.funcsFiniteSupport⟩
  vmax := context.vmax
  target := context.target

/-- Canonical finite-support witness required by the `context` qualifier. -/
theorem holFmapAsFiniteSupportWitness (context : CrepToLoopContextExact) :
    ofBroad (toBroad context) = context := by
  cases context
  rfl

end CrepToLoopContextExact

private def CrepToLoopFiniteMap.toBroadlookup (map : HolFiniteMapExact α β) :
    α → Option β := map.lookup

private def CrepToLoopFiniteMap.ofBroad (lookup : α → Option β)
    (support : ∃ keys : List α, ∀ key, lookup key ≠ none → key ∈ keys) :
    HolFiniteMapExact α β := ⟨lookup, support⟩

/-- Checked finite-map parameter translation for `mk_ctxt_def.vmap`. -/
theorem holFmapAsFiniteSupportParamWitness_mkCtxtExact_vmap
    (vmap : HolFiniteMapExact Nat Nat) :
    CrepToLoopFiniteMap.ofBroad (CrepToLoopFiniteMap.toBroadlookup vmap)
      vmap.finiteSupport = vmap := by
  cases vmap
  rfl

/-- Checked finite-map parameter translation for `mk_ctxt_def.fs`. -/
theorem holFmapAsFiniteSupportParamWitness_mkCtxtExact_fs
    (fs : HolFiniteMapExact MlString (Nat × Nat)) :
    CrepToLoopFiniteMap.ofBroad (CrepToLoopFiniteMap.toBroadlookup fs)
      fs.finiteSupport = fs := by
  cases fs
  rfl

/-- Exact HOL `mk_ctxt_def` (`crep_to_loopScript.sml:221-228`), preserving
    source argument and field order. -/
@[hol "cakeml/pancake/crep_to_loopScript.sml" "mk_ctxt_def"
  (fmap_as_finite_support_parameters := [vmap, fs])]
def mkCtxtExact (target : AsmArchitecture)
    (vmap : HolFiniteMapExact Nat Nat)
    (fs : HolFiniteMapExact MlString (Nat × Nat)) (vmax : Nat) :
    CrepToLoopContextExact :=
  { vars := vmap, funcs := fs, vmax := vmax, target := target }

/-- Exact HOL `find_lab_def` (`crep_to_loopScript.sml:27-32`). -/
@[hol "cakeml/pancake/crep_to_loopScript.sml" "find_lab_def"
  (fmap_as_finite_support := [funcs])]
def findLabExact (context : CrepToLoopContextExact) (function : MlString) : Nat :=
  match context.funcs.lookup function with
  | some (label, _) => label
  | none => 0

/-- Exact HOL `compile_crepop_def`, including the ARMv7 two-result case. -/
@[hol "cakeml/pancake/crep_to_loopScript.sml" "compile_crepop_def"
  (words_as_type_indexed_bitvec)]
def compileCrepopHOLExact {width : Nat} [NeZero width]
    (operator : CrepOp) (target : AsmArchitecture)
    (left right tmp : Nat) (_live : NumSet) : List (HolLoopProg width) × Nat :=
  match operator with
  | .mul =>
      if target = .armv7 then
        ([.arith (.longMul tmp (tmp + 1) left right)], tmp + 1)
      else
        ([.arith (.longMul tmp tmp left right)], tmp)

/-- Exact HOL `prog_if_def`: materialize both expressions, branch on the
comparison, and insert both temporaries into the HOL `num_set`. -/
@[hol "cakeml/pancake/crep_to_loopScript.sml" "prog_if_def"
  (words_as_type_indexed_bitvec)]
def progIfHOLExact {width : Nat} [NeZero width]
    (operator : Cmp) (first second : List (HolLoopProg width))
    (left right : HolLoopExp width) (condition rightRegister : Nat)
    (live : NumSet) : List (HolLoopProg width) :=
  first ++ second ++
    [.assign condition left,
     .assign rightRegister right,
     .ite operator condition (.reg rightRegister)
       (.assign condition (.const 1))
       (.assign condition (.const 0))
       (sptListInsert [condition, rightRegister] live)]

mutual
  /-- Exact HOL `compile_exp_def` over the source Crep and Loop carriers. This
  is proof-side exact infrastructure for now: production `loopCompileExp`
  consumes generic `CrepExp`/list-backed `LoopContext` and emits the
  String-capable, list-live `LoopProg`, whereas this definition consumes
  `CrepExpHOL`, the `MlString`/finite-map context, and emits `HolLoopProg` with
  `NumSet`. No production-routing or material-performance exception is
  claimed. The exact compiler-path bridge is open work linked to
  `flapjack-pxn.18.5.6.28`. -/
  @[hol "cakeml/pancake/crep_to_loopScript.sml" "compile_exp_def"
    (fmap_as_finite_support := [vars, funcs]) (words_as_type_indexed_bitvec)]
  def compileExpHOLExact {width : Nat} [NeZero width]
      (context : CrepToLoopContextExact) (tmp : Nat) (live : NumSet) :
      CrepExpHOL width → List (HolLoopProg width) × HolLoopExp width × Nat × NumSet
    | .baseAddr => ([], .baseAddr, tmp, live)
    | .topAddr => ([], .topAddr, tmp, live)
    | .const value => ([], .const value, tmp, live)
    | .var name =>
        ([], .var (match context.vars.lookup name with | some value => value | none => 0), tmp, live)
    | .load address =>
        let (code, value, next, outLive) := compileExpHOLExact context tmp live address
        (code, .load value, next, outLive)
    | .load32 address =>
        let (code, value, next, outLive) := compileExpHOLExact context tmp live address
        (code ++ [.assign next value, .load32 next next], .var next,
          next + 1, sptInsert next () outLive)
    | .loadByte address =>
        let (code, value, next, outLive) := compileExpHOLExact context tmp live address
        (code ++ [.assign next value, .loadByte next next], .var next,
          next + 1, sptInsert next () outLive)
    | .loadGlob address => ([], .lookup address, tmp, live)
    | .op operator expressions =>
        let (code, values, next, outLive) := compileExpsHOLExact context tmp live expressions
        (code, .op operator values, next, outLive)
    | .crepOp operator expressions =>
        let (code, values, next, outLive) := compileExpsHOLExact context tmp live expressions
        let (operationCode, destination) :=
          compileCrepopHOLExact operator context.target next (next + 1)
            (next + values.length)
            (sptListInsert ((List.range values.length).map (fun offset => next + offset)) outLive)
        let valueAssignments := (List.range values.length).zipWith
          (fun offset value => HolLoopProg.assign (next + offset) value) values
        (code ++ valueAssignments ++ operationCode, .var destination,
          destination + 1,
          sptInsert destination ()
            (sptListInsert
              ((List.range (destination - next)).map (fun offset => next + offset))
              outLive))
    | .cmp operator left right =>
        let (leftCode, leftValue, leftNext, leftLive) :=
          compileExpHOLExact context tmp live left
        let (rightCode, rightValue, rightNext, rightLive) :=
          compileExpHOLExact context leftNext leftLive right
        let condition := rightNext + 1
        let rightRegister := rightNext + 2
        (progIfHOLExact operator leftCode rightCode leftValue rightValue
            condition rightRegister rightLive,
          .var condition, rightNext + 3,
          sptListInsert [condition, rightRegister] rightLive)
    | .shift operator left right =>
        let (leftCode, leftValue, leftNext, leftLive) :=
          compileExpHOLExact context tmp live left
        let (rightCode, rightValue, rightNext, rightLive) :=
          compileExpHOLExact context leftNext leftLive right
        (leftCode ++ rightCode, .shift operator leftValue rightValue, rightNext, rightLive)
  termination_by expression => sizeOf expression
  decreasing_by
    all_goals simp_wf
    all_goals first
      | decreasing_trivial
      | (rename_i h; simp_all only [CrepExpHOL.op.sizeOf_spec, CrepExpHOL.crepOp.sizeOf_spec];
         have := List.sizeOf_lt_of_mem h; omega)

  /-- Flapjack-only helper for the mutual list recursion in `compile_exp_def`;
  HOL's `compile_exps` is local to the source script. -/
  def compileExpsHOLExact {width : Nat} [NeZero width]
      (context : CrepToLoopContextExact) (tmp : Nat) (live : NumSet) :
      List (CrepExpHOL width) →
        List (HolLoopProg width) × List (HolLoopExp width) × Nat × NumSet
    | [] => ([], [], tmp, live)
    | expression :: expressions =>
        let (code, value, next, outLive) := compileExpHOLExact context tmp live expression
        let (tailCode, tailValues, finalTemp, finalLive) :=
          compileExpsHOLExact context next outLive expressions
        (code ++ tailCode, value :: tailValues, finalTemp, finalLive)
  termination_by expressions => sizeOf expressions
  decreasing_by
    all_goals first | sizeOf_list_dec | decreasing_trivial
end

/-- Exact HOL `compile_def` (`crep_to_loopScript.sml:120-213`) over the
width-indexed `CrepProgHOL` and `HolLoopProg` carriers. The context's two map
fields use the reviewed canonical finite-support translation, and word fields
use positive-width `BitVec`. This is proof-side exact infrastructure: the
executed compiler still uses `CrepProg`/`LoopProg` with generic words, String
names and list-backed live sets. No executable routing or performance
exception is claimed; the production bridge is tracked separately. -/
@[hol "cakeml/pancake/crep_to_loopScript.sml" "compile_def"
  (fmap_as_finite_support := [vars, funcs]) (words_as_type_indexed_bitvec)]
def compileHOLExact {width : Nat} [NeZero width]
    (context : CrepToLoopContextExact) (live : NumSet) :
    CrepProgHOL width → HolLoopProg width
  | .skip => .skip
  | .break label => .break label
  | .continue label => .continue label
  | .tick => .tick
  | .return expressions =>
      let (code, values, nextTemporary, _) :=
        compileExpsHOLExact context (context.vmax + 1) live expressions
      let destinations := genTemps nextTemporary values.length
      loopNestedSeqHOL
        (code ++ destinations.zipWith HolLoopProg.assign values ++ [.return destinations])
  | .raise exception =>
      .seq (.assign (context.vmax + 1) (.const exception)) (.raise (context.vmax + 1))
  | .shMem operator name address =>
      match context.vars.lookup name with
      | none => .skip
      | some mappedName =>
          let (code, compiledAddress, _, _) :=
            compileExpHOLExact context (context.vmax + 1) live address
          loopNestedSeqHOL (code ++ [.shMem operator mappedName compiledAddress])
  | .store destination source =>
      let (destinationCode, address, nextTemporary, nextLive) :=
        compileExpHOLExact context (context.vmax + 1) live destination
      let (sourceCode, value, finalTemporary, _) :=
        compileExpHOLExact context nextTemporary nextLive source
      loopNestedSeqHOL
        (destinationCode ++ sourceCode ++
          [.assign finalTemporary value, .store address finalTemporary])
  | .store32 destination source =>
      let (destinationCode, address, nextTemporary, nextLive) :=
        compileExpHOLExact context (context.vmax + 1) live destination
      let (sourceCode, value, finalTemporary, _) :=
        compileExpHOLExact context nextTemporary nextLive source
      loopNestedSeqHOL
        (destinationCode ++ sourceCode ++
          [.assign finalTemporary address,
           .assign (finalTemporary + 1) value,
           .store32 finalTemporary (finalTemporary + 1)])
  | .storeByte destination source =>
      let (destinationCode, address, nextTemporary, nextLive) :=
        compileExpHOLExact context (context.vmax + 1) live destination
      let (sourceCode, value, finalTemporary, _) :=
        compileExpHOLExact context nextTemporary nextLive source
      loopNestedSeqHOL
        (destinationCode ++ sourceCode ++
          [.assign finalTemporary address,
           .assign (finalTemporary + 1) value,
           .storeByte finalTemporary (finalTemporary + 1)])
  | .storeGlob address value =>
      let (code, compiledValue, _, _) :=
        compileExpHOLExact context (context.vmax + 1) live value
      loopNestedSeqHOL (code ++ [.setGlobal address compiledValue])
  | .seq first second =>
      .seq (compileHOLExact context live first) (compileHOLExact context live second)
  | .assign name value =>
      match context.vars.lookup name with
      | none => .skip
      | some mappedName =>
          let (code, compiledValue, _, _) :=
            compileExpHOLExact context (context.vmax + 1) live value
          loopNestedSeqHOL (code ++ [.assign mappedName compiledValue])
  | .primitive destinations operator arguments =>
      match destinations.mapM context.vars.lookup, arguments.mapM context.vars.lookup with
      | some mappedDestinations, some mappedArguments =>
          .primitive mappedDestinations operator mappedArguments
      | _, _ => .skip
  | .dec name value body =>
      let (code, compiledValue, temporary, _) :=
        compileExpHOLExact context (context.vmax + 1) live value
      let bodyContext :=
        { context with vars := context.vars.updateEq (name, temporary), vmax := temporary }
      let bodyLive := sptInsert temporary () live
      .seq (loopNestedSeqHOL code)
        (.seq (.assign temporary compiledValue) (compileHOLExact bodyContext bodyLive body))
  | .ite condition thenBranch elseBranch =>
      let (code, compiledCondition, temporary, _) :=
        compileExpHOLExact context (context.vmax + 1) live condition
      let compiledThen := compileHOLExact context live thenBranch
      let compiledElse := compileHOLExact context live elseBranch
      loopNestedSeqHOL
        (code ++
          [.assign temporary compiledCondition,
           .ite .notEqual temporary (.imm (0 : BitVec width))
             compiledThen compiledElse live])
  | .while condition body =>
      let (code, compiledCondition, temporary, _) :=
        compileExpHOLExact context (context.vmax + 1) live condition
      let compiledBody := compileHOLExact context live body
      .loop live
        (loopNestedSeqHOL
          (code ++
            [.assign temporary compiledCondition,
             .ite .notEqual temporary (.imm (0 : BitVec width))
               (.seq compiledBody (.continue 0)) (.break 0) live]))
        live
  | .call returnInfo name arguments =>
      let label := findLabExact context name
      let (code, compiledArguments, nextTemporary, _) :=
        compileExpsHOLExact context (context.vmax + 1) live arguments
      let argumentNames := genTemps nextTemporary compiledArguments.length
      let (returns, handler) :=
        match returnInfo with
        | none => (none, none)
        | some (returnVariables, maybeHandler) =>
            let returnNames :=
              match returnVariables.mapM context.vars.lookup with
              | none => [context.vmax + 2]
              | some names => names
            let exceptionName := context.vmax + 1
            let handlerBody : HolLoopProg width :=
              match maybeHandler with
              | none => .raise exceptionName
              | some (exception, handlerProgram) =>
                  let compiledHandler := compileHOLExact context live handlerProgram
                  .ite .notEqual exceptionName (.imm exception)
                    (.raise exceptionName) (.seq .tick compiledHandler) live
            (some (returnNames, live),
              some (exceptionName, handlerBody, .skip, live))
      loopNestedSeqHOL
        (code ++ argumentNames.zipWith HolLoopProg.assign compiledArguments ++
          [HolLoopProg.call returns (some label) argumentNames handler])
  | .extCall function configuration configurationLength array arrayLength =>
      match context.vars.lookup configuration,
        context.vars.lookup configurationLength, context.vars.lookup array,
        context.vars.lookup arrayLength with
      | some mappedConfiguration, some mappedConfigurationLength,
          some mappedArray, some mappedArrayLength =>
          .ffi function mappedConfiguration mappedConfigurationLength mappedArray
            mappedArrayLength live
      | _, _, _, _ => .skip
termination_by program => sizeOf program
decreasing_by
  simp_wf
  all_goals first
    | decreasing_trivial
    | (simp_all only [CrepProgHOL.dec.sizeOf_spec, CrepProgHOL.seq.sizeOf_spec,
        CrepProgHOL.ite.sizeOf_spec, CrepProgHOL.while.sizeOf_spec,
        CrepProgHOL.call.sizeOf_spec]; omega)

/-- Exact HOL `ocompile_def` (`crep_to_loopScript.sml:216-219`):
`ocompile ctxt l p = (loop_live$optimise o compile ctxt l) p`.  Composes the
reviewed exact `compileHOLExact` (`compile_def`) with the reviewed exact
`optimiseHOL` (`loop_liveScript.sml` `optimise_def`).  Exact-carrier
infrastructure, validated by the direct original-HOL EVAL rows in
`scripts/hol-probes/crep_to_loop_ocompile_probe.out` (6 rows:
skip/tick/assign/primitive/return/call) replayed by
`Flapjack/Test/CrepToLoopOcompileHOLParity.lean`. -/
@[hol "cakeml/pancake/crep_to_loopScript.sml" "ocompile_def"
  (fmap_as_finite_support := [vars, funcs]) (words_as_type_indexed_bitvec)]
def ocompileHOLExact {width : Nat} [NeZero width]
    (context : CrepToLoopContextExact) (live : NumSet)
    (prog : CrepProgHOL width) : HolLoopProg width :=
  optimiseHOL (compileHOLExact context live prog)

end Flapjack
