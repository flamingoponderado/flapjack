import Flapjack.Pancake.PanGlobals.CompileExpExactRoute
import Flapjack.Pancake.PanLang.Prog.FreeVarIdsCodec

namespace Flapjack

open Flapjack.Basis.Pure.MlString Flapjack.Pancake.PanLang

/-- The generated initializer uses only zero constants and records. This
    Flapjack codec lemma has no separate HOL original. -/
private theorem cakeShapeVal_decode {width : Nat} [NeZero width]
    (context : CakeContext width) (shape : Shape) :
    cakeShapeVal context shape = expOfHOL (shapeValHOL (shapeToHOL shape)) := by
  fun_induction cakeShapeVal context shape <;>
    simp_all [shapeValHOL, shapeValsHOL_eq_map, shapeToHOL, expOfHOL, List.map_map]

/-- Global handled Call codec case, comparing both lookup outcomes and the
    generated result/flag names with pan_globalsScript.sml:102-125. The only
    recursive premise is the actual handler commuting induction hypothesis.
    This cross-carrier routing lemma has no separate HOL original. -/
theorem compileProgCakeOfExact_call_global_handler_exact_bridge
    [LawfulBEq String] {width : Nat} [NeZero width]
    (context : GlobalPassContext (BitVec width))
    (name function exception handlerVar : String)
    (arguments : List (Exp (BitVec width))) (handler : Prog (BitVec width))
    (hname : NameRanged name) (hfunction : NameRanged function)
    (hexception : NameRanged exception) (hhandlerVar : NameRanged handlerVar)
    (hshapes : GlobalContextListShapesByteRanged context)
    (hhandler : compileProgCakeOfExact context handler =
      progOfHOL (compileProgExactHOL (PanGlobalsContextExact.ofPass context)
        (progToHOL handler))) :
    compileProgCakeOfExact context
      (.call (some (some (.global, name), some (exception, handlerVar, handler)))
        function arguments) =
      progOfHOL (compileProgExactHOL (PanGlobalsContextExact.ofPass context)
        (progToHOL (.call (some (some (.global, name),
          some (exception, handlerVar, handler))) function arguments))) := by
  have hnameDecode := toStringOfBytes_ofString_of_bytes name hname
  have hfunctionDecode := toStringOfBytes_ofString_of_bytes function hfunction
  have hexceptionDecode := toStringOfBytes_ofString_of_bytes exception hexception
  have hhandlerVarDecode := toStringOfBytes_ofString_of_bytes handlerVar hhandlerVar
  have hempty := toStringOfBytes_ofString_of_bytes "" (by decide)
  have hflag := toStringOfBytes_ofString_of_bytes "vn'" (by decide)
  cases hlookup : lookupInfo name context.globals with
  | none =>
      simp [compileProgCakeOfExact, compileProgExactHOL, progToHOL, progOfHOL,
        PanGlobalsContextExact.ofPass_globals_lookup, FLOOKUP,
        FLOOKUP_cakeContextOfPass_globals, hlookup, hnameDecode, hfunctionDecode,
        hexceptionDecode, hhandlerVarDecode, hhandler, compileExpRouteCakeArgs_eq_exact]
  | some entry =>
      obtain ⟨shape, address⟩ := entry
      have hshape : ShapeByteRanged shape := hshapes (name, (shape, address))
        (lookupInfo_eq_some_mem name context.globals hlookup)
      have hvars := freeVarIdsHOL_map_toStringOfBytes
        (compileProgExactHOL (PanGlobalsContextExact.ofPass context) (progToHOL handler))
      rw [← hhandler] at hvars
      simp [compileProgCakeOfExact, compileProgExactHOL, progToHOL, progOfHOL,
        PanGlobalsContextExact.ofPass_globals_lookup, FLOOKUP,
        FLOOKUP_cakeContextOfPass_globals, hlookup, hnameDecode, hfunctionDecode,
        hexceptionDecode, hhandlerVarDecode, hhandler, compileExpRouteCakeArgs_eq_exact,
        toStringOfBytes_freshNameMlS, List.map_append, List.map_cons, hempty, hflag,
        hvars, exactArgumentNames_decode, hshape, expOfHOL,
        cakeShapeVal_decode, shapeOfHOL]

end Flapjack
