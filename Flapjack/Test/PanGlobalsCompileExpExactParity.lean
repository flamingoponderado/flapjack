import Flapjack.Pancake.PanGlobals
import Flapjack.Pancake.PanGlobals.CompileExpExact
import Flapjack.Pancake.PanGlobals.CompileExpExactRoute

namespace Flapjack.Test.PanGlobalsCompileExpExactParity

/-! Direct parity for the exact `pan_globals$compile_exp_def` port
    (`pan_globalsScript.sml:18-46`) over the exact `ExpHOL`/`MlS`/`ShapeHOL`
    carrier and the finite-support `PanGlobalsContextExact`.

    Replays the five direct HOL-EVAL rows of
    `scripts/hol-probes/pan_globals_compile_exp_probe.out`
    (`local`, `global_hit`, `global_miss`, `top_addr`, `nested`) at width 8 with
    the probe context `globals = {g := (One, 8w)}`, `globals_size = 1w`,
    `max_globals_size = 16w`. -/

open Flapjack
open Flapjack.Pancake.PanLang
  (MlS ShapeHOL ExpHOL expToHOL expOfHOL ExpByteRanged ListExpByteRanged ShapeByteRanged
    shapeOfHOL NameRanged DeclByteRanged)
open Flapjack.Basis.Pure.MlString (ofString toStringOfBytes)

/-- The probe context of `pan_globals_compile_exp_probeScript.sml` at width 8:
    `globals = FEMPTY |+ («g», (One, 8w))`, `globals_size = 1w`,
    `max_globals_size = 16w`. -/
def exactProbeContext : PanGlobalsContextExact 8 where
  globals :=
    { lookup := fun key => if key = ofString "g" then some (.one, 8) else none
      finiteSupport := by
        refine ⟨[ofString "g"], ?_⟩
        intro key hkey
        by_cases h : key = ofString "g"
        · simp [h]
        · simp [h] at hkey }
  globalsSize := 1
  maxGlobalsSize := 16

/-- The `local` probe row: `Var Local «x»` is the identity. -/
@[simp] theorem global_compile_exp_exact_local :
    compileExpExactHOL exactProbeContext
        (.var .local (ofString "x") : ExpHOL 8) =
      .var .local (ofString "x") :=
  compileExpExactHOL.eq_2 _ _

/-- The `global_hit` probe row:
    `Load One (Op Sub [TopAddr; Const 8w])`. -/
@[simp] theorem global_compile_exp_exact_global_hit :
    compileExpExactHOL exactProbeContext
        (.var .global (ofString "g") : ExpHOL 8) =
      .load .one (.op .sub [.topAddr, .const (8 : BitVec 8)]) := by
  rw [compileExpExactHOL.eq_3]
  rfl

/-- The `global_miss` probe row: `Const 0w`. -/
@[simp] theorem global_compile_exp_exact_global_miss :
    compileExpExactHOL exactProbeContext
        (.var .global (ofString "missing") : ExpHOL 8) =
      .const (0 : BitVec 8) := by
  rw [compileExpExactHOL.eq_3]
  rfl

/-- The `top_addr` probe row: `Op Sub [TopAddr; Const 16w]`. -/
@[simp] theorem global_compile_exp_exact_top_addr :
    compileExpExactHOL exactProbeContext (.topAddr : ExpHOL 8) =
      .op .sub [.topAddr, .const (16 : BitVec 8)] :=
  compileExpExactHOL.eq_16 _

/-- The `nested` probe row:
    `Op Add [Load One (Op Sub [TopAddr; Const 8w]); Op Sub [TopAddr; Const 16w]]`. -/
@[simp] theorem global_compile_exp_exact_nested :
    compileExpExactHOL exactProbeContext
        (.op .add [.var .global (ofString "g"), .topAddr] : ExpHOL 8) =
      .op .add
        [.load .one (.op .sub [.topAddr, .const (8 : BitVec 8)]),
         .op .sub [.topAddr, .const (16 : BitVec 8)]] := by
  rw [compileExpExactHOL.eq_11]
  rw [compileExpExactHOLList.eq_2]
  rw [compileExpExactHOLList.eq_2]
  rw [compileExpExactHOLList.eq_1]
  rw [compileExpExactHOL.eq_3]
  rw [compileExpExactHOL.eq_16]
  rfl

/-- The five `pan_globals_compile_exp_probe.out` rows evaluated through the
    exact carrier, as a single Bool fixture. -/
def parityGuard : Bool :=
  (match compileExpExactHOL exactProbeContext
      (.var .local (ofString "x") : ExpHOL 8) with
   | .var .local name => toStringOfBytes name == "x"
   | _ => false) &&
  (match compileExpExactHOL exactProbeContext
      (.var .global (ofString "g") : ExpHOL 8) with
   | .load .one (.op .sub [.topAddr, .const address]) =>
       address == (8 : BitVec 8)
   | _ => false) &&
  (match compileExpExactHOL exactProbeContext
      (.var .global (ofString "missing") : ExpHOL 8) with
   | .const value => value == (0 : BitVec 8)
   | _ => false) &&
  (match compileExpExactHOL exactProbeContext (.topAddr : ExpHOL 8) with
   | .op .sub [.topAddr, .const address] => address == (16 : BitVec 8)
   | _ => false) &&
  (match compileExpExactHOL exactProbeContext
      (.op .add [.var .global (ofString "g"), .topAddr] : ExpHOL 8) with
   | .op .add [.load .one (.op .sub [.topAddr, .const first]),
               .op .sub [.topAddr, .const second]] =>
       first == (8 : BitVec 8) && second == (16 : BitVec 8)
   | _ => false)

#eval parityGuard
#guard parityGuard

/-- The production `CakeContext` induced by the exact probe context through the
    checked `cakeContextOfExact` adapter. -/
def productionProbeContext : CakeContext 8 :=
  PanGlobalsContextExact.cakeContextOfExact exactProbeContext

/-- The `global_hit` row through the executed production `compileExpCake`,
    obtained from the exact row by the kernel-checked
    `compileExpCake_cakeContextOfExact` bridge. -/
theorem bridge_global_hit :
    compileExpCake productionProbeContext (.var .global "g") =
      .load .one (.op .sub [.topAddr, .const (8 : BitVec 8)]) := by
  unfold productionProbeContext
  rw [compileExpCake_cakeContextOfExact exactProbeContext _
    (by simp [ExpByteRanged])]
  simp only [expToHOL, expOfHOL, shapeOfHOL, List.map_cons, List.map_nil,
    global_compile_exp_exact_global_hit]

/-- The `top_addr` row through the executed production `compileExpCake`. -/
theorem bridge_top_addr :
    compileExpCake productionProbeContext (.topAddr : Exp (BitVec 8)) =
      .op .sub [.topAddr, .const (16 : BitVec 8)] := by
  unfold productionProbeContext
  rw [compileExpCake_cakeContextOfExact exactProbeContext _
    (by simp [ExpByteRanged])]
  simp only [expToHOL, expOfHOL, List.map_cons, List.map_nil,
    global_compile_exp_exact_top_addr]

/-- The five `pan_globals_compile_exp_probe.out` rows replayed through the
    executed String-backed `compileExpCake`, as a single Bool fixture. -/
def productionGuard : Bool :=
  (match compileExpCake productionProbeContext (.var .local "x") with
   | .var .local name => name == "x"
   | _ => false) &&
  (match compileExpCake productionProbeContext (.var .global "g") with
   | .load .one (.op .sub [.topAddr, .const address]) =>
       address == (8 : BitVec 8)
   | _ => false) &&
  (match compileExpCake productionProbeContext (.var .global "missing") with
   | .const value => value == (0 : BitVec 8)
   | _ => false) &&
  (match compileExpCake productionProbeContext (.topAddr : Exp (BitVec 8)) with
   | .op .sub [.topAddr, .const address] => address == (16 : BitVec 8)
   | _ => false) &&
  (match compileExpCake productionProbeContext
      (.op .add [.var .global "g", .topAddr]) with
   | .op .add [.load .one (.op .sub [.topAddr, .const first]),
               .op .sub [.topAddr, .const second]] =>
       first == (8 : BitVec 8) && second == (16 : BitVec 8)
   | _ => false)

#eval productionGuard
#guard productionGuard

/-! ### Routing the executed `cakeContextOfPass` path through `compileExpExactHOL` -/

/-- The probe's production `GlobalPassContext`: the association-list analogue of
    `exactProbeContext` with `globals = «g» ↦ (One, 8w)`, `globals_size = 1w`,
    `max_globals_size = 16w`, and the canonical word operations. -/
def productionPassContext : GlobalPassContext (BitVec 8) where
  globals := [("g", (Shape.one, 8))]
  globalsSize := 1
  maxGlobalsSize := 16
  bytesInWord := 1
  fromNat := fun value => BitVec.ofNat 8 value

/-- The probe context's stored shapes are byte-ranged, as the routing equality
    `compileExpCake_ofPass_eq` requires. -/
theorem productionPassContext_shapes :
    ∀ entry ∈ productionPassContext.globals, ShapeByteRanged entry.2.1 := by
  intro entry hmem
  simp only [productionPassContext, List.mem_singleton] at hmem
  subst hmem
  simp only [ShapeByteRanged]

/-- The `global_hit` row through the executed `cakeContextOfPass` production
    path, routed through the reviewed `compileExpExactHOL` by
    `compileExpCake_ofPass_eq`. -/
theorem routed_global_hit :
    compileExpCake (cakeContextOfPass productionPassContext) (.var .global "g")
      = .load .one (.op .sub [.topAddr, .const (8 : BitVec 8)]) := by
  rw [compileExpCake_ofPass_eq productionPassContext productionPassContext_shapes _
    (by simp [ExpByteRanged])]
  simp only [expToHOL]
  rw [compileExpExactHOL.eq_3]
  simp only [PanGlobalsContextExact.ofPass_globals_lookup]
  rw [Flapjack.Basis.Pure.MlString.toStringOfBytes_ofString_of_bytes "g" (by decide)]
  simp only [productionPassContext, lookupInfo, List.map_cons, List.map_nil,
    beq_self_eq_true, if_true, Option.map_some, expOfHOL]
  rw [Flapjack.Pancake.PanLang.shapeOfHOL_shapeToHOL Shape.one (by simp [ShapeByteRanged])]

/-- The `top_addr` row through the executed `cakeContextOfPass` production path,
    routed through the reviewed `compileExpExactHOL`. -/
theorem routed_top_addr :
    compileExpCake (cakeContextOfPass productionPassContext) (.topAddr : Exp (BitVec 8))
      = .op .sub [.topAddr, .const (16 : BitVec 8)] := by
  rw [compileExpCake_ofPass_eq productionPassContext productionPassContext_shapes _
    (by simp [ExpByteRanged])]
  simp only [expToHOL]
  rw [compileExpExactHOL.eq_16]
  simp only [PanGlobalsContextExact.ofPass, expOfHOL, List.map_cons, List.map_nil]
  rfl

/-- The five `pan_globals_compile_exp_probe.out` rows replayed through the
    executed `cakeContextOfPass` production context (the finite-support
    association-list view), as a single Bool fixture. -/
def routedProductionGuard : Bool :=
  (match compileExpCake (cakeContextOfPass productionPassContext)
      (.var .local "x") with
   | .var .local name => name == "x"
   | _ => false) &&
  (match compileExpCake (cakeContextOfPass productionPassContext)
      (.var .global "g") with
   | .load .one (.op .sub [.topAddr, .const address]) => address == (8 : BitVec 8)
   | _ => false) &&
  (match compileExpCake (cakeContextOfPass productionPassContext)
      (.var .global "missing") with
   | .const value => value == (0 : BitVec 8)
   | _ => false) &&
  (match compileExpCake (cakeContextOfPass productionPassContext)
      (.topAddr : Exp (BitVec 8)) with
   | .op .sub [.topAddr, .const address] => address == (16 : BitVec 8)
   | _ => false) &&
  (match compileExpCake (cakeContextOfPass productionPassContext)
      (.op .add [.var .global "g", .topAddr]) with
   | .op .add [.load .one (.op .sub [.topAddr, .const first]),
               .op .sub [.topAddr, .const second]] =>
       first == (8 : BitVec 8) && second == (16 : BitVec 8)
   | _ => false)

#eval routedProductionGuard
#guard routedProductionGuard

/-! ### Routing the executed decl/prog compiler through `compileExpExactHOL`

The `nestedSeqCake`-routed entry point executes the routed siblings
`compileDecsCakeOfExact`/`compileProgCakeOfExact`, whose expression call sites
textually invoke the reviewed `compileExpExactHOL` through `compileExpRouteCake`.
The rows below replay the five direct HOL probe expressions through the routed
program compiler and the routed declaration compiler, and the equality theorems
record that the routed decl/prog compiler computes the production output. -/

/-- Canonical-word hypothesis of the probe production context. -/
theorem productionPassContext_canonical :
    productionPassContext.IsCakeCanonical := ⟨rfl, fun _ => rfl⟩

/-- The `local` probe row through the executed routed program compiler. -/
theorem routed_prog_local :
    compileProgCakeOfExact productionPassContext (.return (.var .local "x")) =
      .return (.var .local "x") := by
  rw [compileProgCakeOfExact,
    ← compileExpCake_eq_route productionPassContext productionPassContext_shapes _
      (by simp [ExpByteRanged])]
  simp only [compileExpCake]

/-- The `global_hit` probe row through the executed routed program compiler. -/
theorem routed_prog_global_hit :
    compileProgCakeOfExact productionPassContext (.return (.var .global "g")) =
      .return (.load .one (.op .sub [.topAddr, .const (8 : BitVec 8)])) := by
  rw [compileProgCakeOfExact,
    ← compileExpCake_eq_route productionPassContext productionPassContext_shapes _
      (by simp [ExpByteRanged])]
  rw [routed_global_hit]

/-- The `global_miss` probe row through the executed routed program compiler. -/
theorem routed_prog_global_miss :
    compileProgCakeOfExact productionPassContext (.return (.var .global "missing")) =
      .return (.const (0 : BitVec 8)) := by
  rw [compileProgCakeOfExact,
    ← compileExpCake_eq_route productionPassContext productionPassContext_shapes _
      (by simp [ExpByteRanged])]
  have hmiss : ("g" == "missing") = false := by decide
  simp only [compileExpCake, cakeContextOfPass, productionPassContext, lookupInfo,
    FLOOKUP, hmiss, Bool.false_eq_true, if_false, Option.map_none, List.map_nil]
  rfl

/-- The `top_addr` probe row through the executed routed program compiler. -/
theorem routed_prog_top_addr :
    compileProgCakeOfExact productionPassContext (.return (.topAddr : Exp (BitVec 8))) =
      .return (.op .sub [.topAddr, .const (16 : BitVec 8)]) := by
  rw [compileProgCakeOfExact,
    ← compileExpCake_eq_route productionPassContext productionPassContext_shapes _
      (by simp [ExpByteRanged])]
  rw [routed_top_addr]

/-- The `nested` probe row through the executed `cakeContextOfPass` production
    context, routed through the reviewed `compileExpExactHOL`. -/
theorem routed_nested :
    compileExpCake (cakeContextOfPass productionPassContext)
        (.op .add [.var .global "g", .topAddr]) =
      .op .add
        [.load .one (.op .sub [.topAddr, .const (8 : BitVec 8)]),
         .op .sub [.topAddr, .const (16 : BitVec 8)]] := by
  rw [compileExpCake_ofPass_eq productionPassContext productionPassContext_shapes _
    (by simp [ExpByteRanged, ListExpByteRanged])]
  simp only [expToHOL, List.map_cons, List.map_nil]
  rw [compileExpExactHOL.eq_11, compileExpExactHOLList.eq_2,
    compileExpExactHOLList.eq_2, compileExpExactHOLList.eq_1,
    compileExpExactHOL.eq_3, compileExpExactHOL.eq_16]
  simp only [PanGlobalsContextExact.ofPass_globals_lookup]
  rw [Flapjack.Basis.Pure.MlString.toStringOfBytes_ofString_of_bytes "g" (by decide)]
  simp only [productionPassContext, lookupInfo, List.map_cons, List.map_nil,
    beq_self_eq_true, if_true, Option.map_some]
  simp only [expOfHOL, List.map_cons, List.map_nil]
  rw [Flapjack.Pancake.PanLang.shapeOfHOL_shapeToHOL Shape.one (by simp [ShapeByteRanged])]
  simp only [PanGlobalsContextExact.ofPass, productionPassContext, List.map_cons, List.map_nil]

/-- The `nested` probe row through the executed routed program compiler. -/
theorem routed_prog_nested :
    compileProgCakeOfExact productionPassContext
        (.return (.op .add [.var .global "g", .topAddr])) =
      .return (.op .add
        [.load .one (.op .sub [.topAddr, .const (8 : BitVec 8)]),
         .op .sub [.topAddr, .const (16 : BitVec 8)]]) := by
  rw [compileProgCakeOfExact,
    ← compileExpCake_eq_route productionPassContext productionPassContext_shapes _
      (by simp [ExpByteRanged, ListExpByteRanged])]
  rw [routed_nested]

/-- A `.decl` initializer replaying the `global_hit` probe row through the
    executed routed declaration compiler. -/
theorem routed_decs_global_hit :
    (compileDecsCakeOfExact productionPassContext
        [.decl Shape.one "y" (.var .global "g")]).initializers =
      [.store (.op .sub [.topAddr, .const (cakeAddress (cakeContextOfPass productionPassContext) Shape.one)])
        (.load .one (.op .sub [.topAddr, .const (8 : BitVec 8)]))] := by
  simp only [compileDecsCakeOfExact]
  rw [← compileExpCake_eq_route productionPassContext productionPassContext_shapes _
      (by simp [ExpByteRanged])]
  rw [routed_global_hit]

/-- The routed declaration compiler agrees with the production `compileDecsCake`
    on the probe declaration list, by the kernel-checked routing equality. -/
theorem routed_decs_eq_production :
    compileDecsCakeOfExact productionPassContext [.decl Shape.one "y" (.var .global "g")] =
      compileDecsCake (cakeContextOfPass productionPassContext)
        [.decl Shape.one "y" (.var .global "g")] :=
  compileDecsCakeOfExact_eq _ productionPassContext productionPassContext_canonical
    productionPassContext_shapes
    (by
      intro declaration hdeclaration
      simp only [List.mem_singleton] at hdeclaration
      subst hdeclaration
      simp only [DeclByteRanged]
      exact ⟨by simp [ShapeByteRanged], by decide, by simp [ExpByteRanged]⟩)

/-- The five `pan_globals_compile_exp_probe.out` rows replayed through the
    executed routed `compileProgCakeOfExact` (whose expression call sites invoke
    `compileExpExactHOL`), as a single Bool fixture. -/
def routedProgramGuard : Bool :=
  (match compileProgCakeOfExact productionPassContext (.return (.var .local "x")) with
   | .return (.var .local name) => name == "x"
   | _ => false) &&
  (match compileProgCakeOfExact productionPassContext (.return (.var .global "g")) with
   | .return (.load .one (.op .sub [.topAddr, .const address])) =>
       address == (8 : BitVec 8)
   | _ => false) &&
  (match compileProgCakeOfExact productionPassContext (.return (.var .global "missing")) with
   | .return (.const value) => value == (0 : BitVec 8)
   | _ => false) &&
  (match compileProgCakeOfExact productionPassContext (.return (.topAddr : Exp (BitVec 8))) with
   | .return (.op .sub [.topAddr, .const address]) => address == (16 : BitVec 8)
   | _ => false) &&
  (match compileProgCakeOfExact productionPassContext
      (.return (.op .add [.var .global "g", .topAddr])) with
   | .return (.op .add [.load .one (.op .sub [.topAddr, .const first]),
                        .op .sub [.topAddr, .const second]]) =>
       first == (8 : BitVec 8) && second == (16 : BitVec 8)
   | _ => false)

#eval routedProgramGuard
#guard routedProgramGuard

def runChecks : IO Bool := do
  let exactResult := parityGuard
  let productionResult := productionGuard
  let routedResult := routedProductionGuard
  let routedProgramResult := routedProgramGuard
  IO.println (if exactResult then
    "PASS pan_globals compile_exp_def exact-carrier parity (5 HOL rows)"
    else "FAIL pan_globals compile_exp_def exact-carrier parity (5 HOL rows)")
  IO.println (if productionResult then
    "PASS pan_globals compileExpCake/cakeContextOfExact bridge parity (5 HOL rows)"
    else "FAIL pan_globals compileExpCake/cakeContextOfExact bridge parity (5 HOL rows)")
  IO.println (if routedResult then
    "PASS pan_globals compileExpCake/ofPass routed parity (5 HOL rows)"
    else "FAIL pan_globals compileExpCake/ofPass routed parity (5 HOL rows)")
  IO.println (if routedProgramResult then
    "PASS pan_globals routed decl/prog compiler parity (5 HOL rows)"
    else "FAIL pan_globals routed decl/prog compiler parity (5 HOL rows)")
  pure (exactResult && productionResult && routedResult && routedProgramResult)

end Flapjack.Test.PanGlobalsCompileExpExactParity
