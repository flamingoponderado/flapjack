module

public import Flapjack.Compiler.Backend.DataLang.Syntax
public import Flapjack.Compiler.Backend.BviToData.Assign

@[expose] public section

/-! Backward liveness for the data-language optimizer. -/
namespace Flapjack.Compiler.Backend.DataLive
open DataLang

/-- Classify operations whose unused results may be removed. -/
@[hol "cakeml/compiler/backend/data_liveScript.sml" "is_pure_def"]
def isPure : ClosLang.Op → Bool
  | .ffi _ | .intOp .add | .intOp .sub | .intOp .mult | .intOp .div | .intOp .mod
  | .intOp .less | .intOp .lessEq | .wordOp (.wordOpw .w64 _) | .wordOp (.wordShift .w64 _ _)
  | .wordOp .wordFromInt | .wordOp .wordToInt | .wordOp (.wordFromWord _)
  | .wordOp (.fpUop _) | .wordOp (.fpBop _) | .wordOp (.fpTop _)
  | .blockOp (.build _) | .blockOp (.cons _) | .blockOp (.consExtend _)
  | .blockOp (.fromList _) | .blockOp .listAppend | .blockOp .equal
  | .globOp (.setGlobal _) | .globOp .setGlobalsPtr | .memOp .ref
  | .memOp (.refByte _) | .memOp .refArray | .memOp .update | .memOp (.mutCons _ _)
  | .memOp .updateCons | .memOp .finaliseCons | .memOp .updateByte
  | .memOp .fromListByte | .memOp (.copyByte _) | .memOp .xorByte | .memOp .configGC
  | .install | .thunkOp _ => false
  | _ => true

/-- The source-order pattern match for the purity classifier. -/
@[hol "cakeml/compiler/backend/data_liveScript.sml" "is_pure_pmatch"]
theorem isPure_pmatch (op : ClosLang.Op) :
    isPure op = match op with
      | .ffi _ => false
      | .globOp (.setGlobal _) => false
      | .globOp .setGlobalsPtr => false
      | .wordOp (.wordOpw .w64 _) => false
      | .wordOp (.wordShift .w64 _ _) => false
      | .wordOp .wordFromInt => false
      | .wordOp .wordToInt => false
      | .wordOp (.wordFromWord _) => false
      | .wordOp (.fpUop _) => false
      | .wordOp (.fpBop _) => false
      | .wordOp (.fpTop _) => false
      | .blockOp (.build _) => false
      | .blockOp (.cons _) => false
      | .blockOp (.consExtend _) => false
      | .blockOp (.fromList _) => false
      | .blockOp .listAppend => false
      | .blockOp .equal => false
      | .memOp .ref => false
      | .memOp (.refByte _) => false
      | .memOp .refArray => false
      | .memOp .update => false
      | .memOp (.mutCons _ _) => false
      | .memOp .updateCons => false
      | .memOp .finaliseCons => false
      | .memOp .updateByte => false
      | .memOp .fromListByte => false
      | .memOp (.copyByte _) => false
      | .memOp .xorByte => false
      | .intOp .add => false
      | .intOp .sub => false
      | .intOp .mult => false
      | .intOp .div => false
      | .intOp .mod => false
      | .intOp .less => false
      | .intOp .lessEq => false
      | .install => false
      | .memOp .configGC => false
      | .thunkOp _ => false
      | _ => true := by
  cases op with
  | ffi name => rfl
  | label n => rfl
  | intOp op => cases op <;> rfl
  | wordOp op =>
    cases op <;> try rfl
    case wordOpw size operation => cases size <;> rfl
    case wordShift size operation amount => cases size <;> rfl
  | blockOp op => cases op <;> rfl
  | globOp op => cases op <;> rfl
  | memOp op => cases op <;> rfl
  | install => rfl
  | thunkOp op => rfl

/-- Rewrite live-name annotations and remove unused pure assignments. -/
@[hol "cakeml/compiler/backend/data_liveScript.sml" "compile_def"]
def compile : Prog → NumSet → Prog × NumSet
  | .skip, live => (.skip, live)
  | .return ns, _ => (.return ns, sptListInsert ns .ln)
  | .raise n, _ => (.raise n, sptInsert n () .ln)
  | .move dst src, live => (.move dst src, sptInsert src () (sptDelete dst live))
  | .seq x y, live =>
      let (y, live) := compile y live
      let (x, live) := compile x live
      (.seq x y, live)
  | .tick, live => (.tick, live)
  | .makeSpace k names, live =>
      let names := sptInter names live
      (.makeSpace k names, names)
  | .assign v op vs none, live =>
      if (sptLookup v live).isNone && isPure op then (.skip, live)
      else (.assign v op vs none, sptListInsert vs (sptDelete v live))
  | .assign v op vs (some names), live =>
      let names := sptInter names (sptDelete v live)
      (.assign v op vs (some names), sptListInsert vs names)
  | .ifThenElse n x y, live =>
      let (y, ly) := compile y live
      let (x, lx) := compile x live
      (.ifThenElse n x y, sptInsert n () (sptUnion lx ly))
  | .force none loc src, _ => (.force none loc src, sptInsert src () .ln)
  | .force (some (n, names)) loc src, live =>
      let names := sptInter names (sptDelete n live)
      (.force (some (n, names)) loc src, sptInsert src () names)
  | .call none dest vs handler, _ =>
      (.call none dest vs handler, BviToData.namesOfList vs)
  | .call (some (ns, names)) dest vs none, live =>
      let names := sptInter names (sptListDelete ns live)
      (.call (some (ns, names)) dest vs none, sptListInsert vs names)
  | .call (some (ns, names)) dest vs (some (v, handler)), live =>
      let (handler, handlerLive) := compile handler live
      let names := sptInter names (sptUnion (sptListDelete ns live) (sptDelete v handlerLive))
      (.call (some (ns, names)) dest vs (some (v, handler)), sptListInsert vs names)

end Flapjack.Compiler.Backend.DataLive
