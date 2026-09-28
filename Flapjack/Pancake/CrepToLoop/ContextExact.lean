import Flapjack.Pancake.CrepToLoop
import Flapjack.Pancake.CrepLang.Exp
import Flapjack.Pancake.Semantics.CrepSem.HOLState
import Flapjack.Basis.Pure.MlString
import Flapjack.Compiler.Encoders.Asm

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
        (leftCode ++ rightCode ++
          [.assign condition leftValue,
           .assign rightRegister rightValue,
           .ite operator condition (.reg rightRegister)
             (.assign condition (.const 1))
             (.assign condition (.const 0))
             (sptListInsert [condition, rightRegister] rightLive)],
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

end Flapjack
