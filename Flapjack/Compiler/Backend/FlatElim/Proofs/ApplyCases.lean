module
public import Flapjack.Compiler.Backend.Semantics.FlatSem.ApplyArithmeticSource
public import Flapjack.Compiler.Backend.Semantics.FlatSem.ApplyCompareSource
public import Flapjack.Compiler.Backend.Semantics.FlatSem.ApplyCopySource
public import Flapjack.Compiler.Backend.Semantics.FlatSem.ApplyDataSource
public import Flapjack.Compiler.Backend.Semantics.FlatSem.ApplyFlatSource
public import Flapjack.Compiler.Backend.Semantics.FlatSem.ApplyMemorySource
public import Flapjack.Misc.ListEl
public import Flapjack.Misc.Option
import Aesop
@[expose] public section

/-! Complete primitive-application case analysis for flat elimination. -/
namespace Flapjack.Compiler.Backend.FlatSem
open Flapjack Flapjack.AstHOL Flapjack.SemanticPrimitivesHOL
open Flapjack.Basis.Pure.MlString
/-- Flapjack proof infrastructure abbreviating the source-operator case of
the generated application analysis. It has no separate HOL declaration. -/
noncomputable def independentSrcRhs {C F : Type} (s : State C F) (op : AstHOL.Op) (vs : List Value) :
    Option (State C F × Result Value Value) :=
  match op with
  | .arith action typ =>
      let sourceValues := vs.map flatToValue
      if sourceValues.all (SemanticPrimitivesHOL.checkType typ) then
        match SemanticPrimitivesHOL.doArith action typ sourceValues with
        | none => none
        | some (.inl _) => some (s, .err (.raise divExnV))
        | some (.inr result) => some (s, .val (valueToFlat result))
      else none
  | .fromTo source target =>
      match vs with
      | [value] =>
        let sourceValue := flatToValue value
        if SemanticPrimitivesHOL.checkType source sourceValue then
          match SemanticPrimitivesHOL.doConversion sourceValue source target with
          | none => none
          | some (.inl _) => some (s, .err (.raise chrExnV))
          | some (.inr result) => some (s, .val (valueToFlat result))
        else none
      | _ => none
  | .shift width shift n =>
      match vs with
      | [.litv lit] =>
        match Flapjack.SemanticPrimitivesProps.doShift shift n width lit with
        | none => none
        | some result => some (s, .val (.litv result))
      | _ => none
  | .equality =>
      match vs with
           | [x, y] => match doEq x y with
             | .typeError => none
             | .val b => some (s, .val (boolValue b))
           | _ => none
  | .test test typ =>
      match vs with
           | [x, y] => match doTest test typ x y with
             | .typeError => none
             | .val b => some (s, .val (boolValue b))
           | _ => none
  | .copyStrStr =>
      match vs with
           | [.litv (.strLit str), .litv (.intLit offset), .litv (.intLit length)] =>
             match copyArray (str.explode, offset) length none with
             | none => some (s, .err (.raise subscriptExnV))
             | some chars => some (s, .val (.litv (.strLit (.implode chars))))
           | _ => none
  | .copyStrAw8 =>
      match vs with
           | [.litv (.strLit str), .litv (.intLit off), .litv (.intLit len), .loc _ dst, .litv (.intLit dstOff)] =>
             match storeLookup dst s.refs with
             | some (.w8array bytes) => match copyArray (str.explode, off) len (some (bytes, dstOff)) with
               | none => some (s, .err (.raise subscriptExnV))
               | some copied => (storeAssign dst (.w8array copied) s.refs).map fun refs => ({ s with refs := refs }, .val unitValue)
             | _ => none
           | _ => none
  | .copyAw8Str =>
      match vs with
           | [.loc _ src, .litv (.intLit off), .litv (.intLit len)] =>
             match storeLookup src s.refs with
             | some (.w8array bytes) => match copyArray (bytes, off) len none with
               | none => some (s, .err (.raise subscriptExnV))
               | some copied => some (s, .val (.litv (.strLit (.implode copied))))
             | _ => none
           | _ => none
  | .copyAw8Aw8 =>
      match vs with
           | [.loc _ src, .litv (.intLit off), .litv (.intLit len), .loc _ dst, .litv (.intLit dstOff)] =>
             match storeLookup src s.refs, storeLookup dst s.refs with
             | some (.w8array bytes), some (.w8array output) =>
               match copyArray (bytes, off) len (some (output, dstOff)) with
               | none => some (s, .err (.raise subscriptExnV))
               | some copied => (storeAssign dst (.w8array copied) s.refs).map fun refs => ({ s with refs := refs }, .val unitValue)
             | _, _ => none
           | _ => none
  | .xorAw8StrUnsafe =>
      match vs with
           | [.loc _ dst, .litv (.strLit str)] => match storeLookup dst s.refs with
             | some (.w8array bytes) => match xorBytes str.explode bytes with
               | none => none
               | some output => (storeAssign dst (.w8array output) s.refs).map fun refs => ({ s with refs := refs }, .val unitValue)
             | _ => none
           | _ => none
  | .implode =>
      match vs with
           | [v] => (valueToCharList v).map fun chars => (s, .val (.litv (.strLit (.implode chars))))
           | _ => none
  | .explode =>
      match vs with
           | [.litv (.strLit str)] => some (s, .val (listToValue (str.explode.map (.litv ∘ Lit.char))))
           | _ => none
  | .strsub =>
      match vs with
           | [.litv (.strLit str), .litv (.intLit i)] =>
             if i < 0 then some (s, .err (.raise subscriptExnV)) else
             match str.explode[i.toNat]? with
             | none => some (s, .err (.raise subscriptExnV))
             | some c => some (s, .val (.litv (.char c)))
           | _ => none
  | .strlen =>
      match vs with
           | [.litv (.strLit str)] => some (s, .val (.litv (.intLit str.explode.length)))
           | _ => none
  | .strcat =>
      match vs with
           | [v] => do
             let parts ← valueToList v
             let str ← valuesToString parts
             some (s, .val (.litv (.strLit str)))
           | _ => none
  | .vfromList =>
      match vs with
           | [v] => (valueToList v).map fun values => (s, .val (.vectorv values))
           | _ => none
  | .vsub =>
      match vs with
           | [.vectorv xs, .litv (.intLit i)] => if i < 0 then some (s, .err (.raise subscriptExnV)) else
             match xs[i.toNat]? with | none => some (s, .err (.raise subscriptExnV)) | some v => some (s, .val v)
           | _ => none
  | .vsubUnsafe =>
      match vs with
           | [.vectorv xs, .litv (.intLit i)] => if i < 0 then none else
             match xs[i.toNat]? with | none => none | some v => some (s, .val v)
           | _ => none
  | .vlength =>
      match vs with
           | [.vectorv xs] => some (s, .val (.litv (.intLit xs.length)))
           | _ => none
  | .listAppend =>
      match vs with
           | [x, y] => do
             let left ← valueToList x
             let right ← valueToList y
             some (s, .val (listToValue (left ++ right)))
           | _ => none
  | .configGC =>
      match vs with
           | [.litv (.intLit _), .litv (.intLit _)] => some (s, .val unitValue)
           | _ => none
  | .thunkOp op =>
      match op, vs with
           | .allocThunk mode, [v] =>
             if badThunkUpdate mode v s.refs then none else
             let (refs, n) := storeAlloc (.thunk mode v) s.refs
             some ({ s with refs := refs }, .val (.loc false n))
           | .updateThunk mode, [.loc false n, v] =>
             if badThunkUpdate mode v s.refs then none else
             (storeAssign n (.thunk mode v) s.refs).map fun refs => ({ s with refs := refs }, .val unitValue)
           | _, _ => none
  | .ffi name =>
      match vs with
           | [.litv (.strLit conf), .loc _ n] => match storeLookup n s.refs with
             | some (.w8array bytes) => match callFFIHOL s.ffi (.extCall name) conf.explode bytes with
               | .final event => some (s, .err (.abort (.ffiError event)))
               | .ret ffi output => (storeAssign n (.w8array output) s.refs).map fun refs =>
                   ({ s with refs := refs, ffi := ffi }, .val unitValue)
             | _ => none
           | _ => none
  | .opapp =>
      none
  | .eval =>
      none
  | .opref =>
      match vs with
           | [v] => let (refs, n) := storeAlloc (.refv v) s.refs
                    some ({ s with refs := refs }, .val (.loc true n))
           | _ => none
  | .opassign =>
      match vs with
           | [.loc _ n, v] => (storeAssign n (.refv v) s.refs).map fun refs => ({ s with refs := refs }, .val unitValue)
           | _ => none
  | .aallocFixed =>
      let (refs, n) := storeAlloc (.varray vs) s.refs
      some ({ s with refs := refs }, .val (.loc true n))
  | .aalloc =>
      match vs with
           | [.litv (.intLit n), v] => if n < 0 then some (s, .err (.raise subscriptExnV)) else
             let (refs, address) := storeAlloc (.varray (List.replicate n.toNat v)) s.refs
             some ({ s with refs := refs }, .val (.loc true address))
           | _ => none
  | .aw8alloc =>
      match vs with
           | [.litv (.intLit n), .litv (.word8 v)] => if n < 0 then some (s, .err (.raise subscriptExnV)) else
             let (refs, address) := storeAlloc (.w8array (List.replicate n.toNat v)) s.refs
             some ({ s with refs := refs }, .val (.loc true address))
           | _ => none
  | .alength =>
      match vs with
           | [.loc _ n] => match storeLookup n s.refs with
             | some (.varray xs) => some (s, .val (.litv (.intLit xs.length)))
             | _ => none
           | _ => none
  | .aw8length =>
      match vs with
           | [.loc _ n] => match storeLookup n s.refs with
             | some (.w8array xs) => some (s, .val (.litv (.intLit xs.length)))
             | _ => none
           | _ => none
  | .asub =>
      match vs with
           | [.loc _ n, .litv (.intLit i)] => match storeLookup n s.refs with
             | some (.varray xs) => if i < 0 then some (s, .err (.raise subscriptExnV)) else
               match xs[i.toNat]? with
               | none => some (s, .err (.raise subscriptExnV))
               | some v => some (s, .val v)
             | _ => none
           | _ => none
  | .aupdate =>
      match vs with
           | [.loc _ n, .litv (.intLit i), v] => match storeLookup n s.refs with
             | some (.varray xs) => if i < 0 ∨ xs.length ≤ i.toNat then some (s, .err (.raise subscriptExnV)) else
               (storeAssign n (.varray (xs.set i.toNat v)) s.refs).map fun refs => ({ s with refs := refs }, .val unitValue)
             | _ => none
           | _ => none
  | .asubUnsafe =>
      match vs with
           | [.loc _ n, .litv (.intLit i)] => match storeLookup n s.refs with
             | some (.varray xs) => if i < 0 then none else
               match xs[i.toNat]? with | none => none | some v => some (s, .val v)
             | _ => none
           | _ => none
  | .aupdateUnsafe =>
      match vs with
           | [.loc _ n, .litv (.intLit i), v] => match storeLookup n s.refs with
             | some (.varray xs) => if i < 0 ∨ xs.length ≤ i.toNat then none else
               (storeAssign n (.varray (xs.set i.toNat v)) s.refs).map fun refs => ({ s with refs := refs }, .val unitValue)
             | _ => none
           | _ => none
  | .aw8sub =>
      match vs with
           | [.loc _ n, .litv (.intLit i)] => match storeLookup n s.refs with
             | some (.w8array xs) => if i < 0 then some (s, .err (.raise subscriptExnV)) else
               match xs[i.toNat]? with
               | none => some (s, .err (.raise subscriptExnV))
               | some v => some (s, .val (.litv (.word8 v)))
             | _ => none
           | _ => none
  | .aw8subUnsafe =>
      match vs with
           | [.loc _ n, .litv (.intLit i)] => match storeLookup n s.refs with
             | some (.w8array xs) => if i < 0 then none else
               match xs[i.toNat]? with | none => none | some v => some (s, .val (.litv (.word8 v)))
             | _ => none
           | _ => none
  | .aw8update =>
      match vs with
           | [.loc _ n, .litv (.intLit i), .litv (.word8 v)] => match storeLookup n s.refs with
             | some (.w8array xs) => if i < 0 ∨ xs.length ≤ i.toNat then some (s, .err (.raise subscriptExnV)) else
               (storeAssign n (.w8array (xs.set i.toNat v)) s.refs).map fun refs => ({ s with refs := refs }, .val unitValue)
             | _ => none
           | _ => none
  | .aw8updateUnsafe =>
      match vs with
           | [.loc _ n, .litv (.intLit i), .litv (.word8 v)] => match storeLookup n s.refs with
             | some (.w8array xs) => if i < 0 ∨ xs.length ≤ i.toNat then none else
               (storeAssign n (.w8array (xs.set i.toNat v)) s.refs).map fun refs => ({ s with refs := refs }, .val unitValue)
             | _ => none
           | _ => none
  | .opderef | .aallocEmpty | .envId => none
/-- The source-operator abbreviation agrees with flat primitive application.
This is Flapjack proof infrastructure, not a separate HOL theorem. -/
private theorem independentSrcRhs_eq {C F : Type} (s : State C F) (op : AstHOL.Op) (vs : List Value) :
    doApp s (.src op) vs = independentSrcRhs s op vs := by
  cases op <;> simp only [independentSrcRhs, doApp_arith_source, doApp_conversion_source, doApp_shift_source, doApp_equality_source, doApp_test_source, doApp_copyStrStr_source, doApp_copyStrAw8_source, doApp_copyAw8Str_source, doApp_copyAw8Aw8_source, doApp_xorAw8StrUnsafe_source, doApp_implode_source, doApp_explode_source, doApp_strsub_source, doApp_strlen_source, doApp_strcat_source, doApp_vfromList_source, doApp_vsub_source, doApp_vsubUnsafe_source, doApp_vlength_source, doApp_listAppend_source, doApp_configGC_source, doApp_thunk_source, doApp_ffi_source, doApp_opapp_source, doApp_eval_source, doApp_opref_source, doApp_opassign_source, doApp_aallocFixed_source, doApp_aalloc_source, doApp_aw8alloc_source, doApp_alength_source, doApp_aw8length_source, doApp_asub_source, doApp_aupdate_source, doApp_asubUnsafe_source, doApp_aupdateUnsafe_source, doApp_aw8sub_source, doApp_aw8subUnsafe_source, doApp_aw8update_source, doApp_aw8updateUnsafe_source] <;> rfl

open Classical in
/-- Complete generated application case analysis; floating-point dependencies
inherit the rational-cut assumption recorded in SOUNDNESS item 8. -/
@[hol "cakeml/compiler/backend/proofs/flat_elimProofScript.sml" "do_app_cases"]
theorem doAppCases {C F : Type} (st : State C F) (op : FlatLang.Op)
    (vs : List Value) (st' : State C F) (v : Result Value Value) :
    doApp st op vs = some (st', v) ↔
      (∃ a, op = .src a ∧ independentSrcRhs st a vs = some (st', v)) ∨
      (∃ n, op = .globalVarAlloc n ∧ vs = [] ∧
        { st with globals := st.globals ++ List.replicate n none } = st' ∧ v = .val unitValue) ∨
      (∃ n, op = .globalVarInit n ∧
        ((¬ n < st.globals.length ∨ Flapjack.holEl n st.globals ≠ none) ∨
          ∃ value, vs = [value] ∧ { st with globals := st.globals.set n (some value) } = st' ∧ v = .val unitValue) ∧
        n < st.globals.length ∧ Flapjack.holEl n st.globals = none) ∨
      (∃ n, op = .globalVarLookup n ∧
        ((¬ n < st.globals.length ∨ Flapjack.holEl n st.globals = none) ∨
          vs = [] ∧ st = st' ∧ .val (@Flapjack.holThe Value ⟨unitValue⟩ (Flapjack.holEl n st.globals)) = v) ∧
        n < st.globals.length ∧ (Flapjack.holEl n st.globals).isSome = true) ∨
      (∃ n l xs tag opt, op = .tagLenEq n l ∧ vs = [.conv (some (tag,opt)) xs] ∧
        st = st' ∧ .val (boolValue (decide (tag = n ∧ xs.length = l))) = v) ∨
      (∃ l opt xs, op = .lenEq l ∧ vs = [.conv opt xs] ∧ st = st' ∧
        .val (boolValue (decide (xs.length = l))) = v) ∨
      (∃ n, op = .el n ∧
        (n = 0 ∨ ∃ opt xs, vs = [.conv opt xs] ∧ n < xs.length ∧ st = st' ∧
          .val (@Flapjack.holEl Value ⟨unitValue⟩ n xs) = v) ∧
        (n ≠ 0 ∨ ∃ x, vs = [x] ∧
          ((∃ opt xs, x = .conv opt xs ∧ 0 < xs.length ∧ st = st' ∧
              .val (@Flapjack.holHd Value ⟨unitValue⟩ xs) = v) ∨
           ∃ flag p value, x = .loc flag p ∧ storeLookup p st.refs = some (.refv value) ∧
              st = st' ∧ .val value = v))) ∨
      ∃ value, op = .id ∧ vs = [value] ∧ st = st' ∧ .val value = v := by
  classical
  cases op <;> simp [independentSrcRhs_eq, doApp_globalAlloc_source, doApp_globalInit_source,
    doApp_globalLookup_source, doApp_tagLenEq_source, doApp_lenEq_source, doApp_el_source, doApp_id_source]
  case globalVarAlloc => cases vs <;> simp_all [eq_comm]
  case globalVarInit n =>
    by_cases bound : n < st.globals.length
    · rw [Flapjack.holEl_eq_getElem n _ bound, List.getElem?_eq_getElem bound]
      cases vs with
      | nil => simp_all [Nat.not_le_of_gt bound]
      | cons head tail =>
        cases tail with
        | cons _ _ => simp_all [Nat.not_le_of_gt bound]
        | nil =>
          cases entry : st.globals[n] with
          | none => simp_all [Nat.not_le_of_gt bound, eq_comm]
          | some value =>
            have ne : st.globals[n] ≠ none := by rw [entry]; simp
            simp_all [Nat.not_le_of_gt bound, eq_comm]
    · have absent : st.globals[n]? = none := List.getElem?_eq_none_iff.mpr (by omega)
      simp_all
      omega
  case globalVarLookup n =>
    by_cases bound : n < st.globals.length
    · rw [Flapjack.holEl_eq_getElem n _ bound, List.getElem?_eq_getElem bound]
      cases vs <;> cases entry : st.globals[n] <;> simp_all [Flapjack.holThe]
      all_goals omega
    · have absent : st.globals[n]? = none := List.getElem?_eq_none_iff.mpr (by omega)
      simp_all
      omega
  case id => cases vs with
    | nil => simp_all
    | cons head tail => cases tail <;> simp_all [eq_comm]
  case lenEq =>
    cases vs with
    | nil => simp_all
    | cons head tail =>
      cases tail with
      | cons _ _ => simp_all
      | nil =>
        cases head <;> simp_all [Bool.beq_eq_decide_eq]
        all_goals aesop
  case tagLenEq =>
    cases vs with
    | nil => simp_all
    | cons head tail =>
      cases tail with
      | cons _ _ => simp_all
      | nil =>
        cases head <;> simp_all
        case conv opt fields =>
          cases opt with
          | none => simp_all
          | some pair =>
            cases pair
            simp_all [Bool.beq_eq_decide_eq]
            all_goals aesop
  case el n =>
    cases n with
    | zero =>
      cases vs with
      | nil => simp_all
      | cons head tail =>
        cases tail with
        | cons _ _ => simp_all
        | nil =>
          cases head <;> simp_all
          case conv opt fields =>
            cases fields with
            | nil => simp_all [Flapjack.holHd]
            | cons first rest =>
              simp_all [Flapjack.holHd]
              constructor
              · rintro ⟨hs, hv⟩
                exact ⟨opt, first :: rest, ⟨rfl, rfl⟩, by simp, hs, hv⟩
              · rintro ⟨_, _, ⟨rfl, rfl⟩, _, hs, hv⟩
                exact ⟨hs, hv⟩
          case loc flag p =>
            cases found : storeLookup p st.refs with
            | none => cases flag <;> simp_all
            | some item => cases item <;> cases flag <;> simp_all
    | succ n =>
      cases vs with
      | nil => simp_all
      | cons head tail =>
        cases tail with
        | cons _ _ => simp_all
        | nil =>
          cases head <;> simp_all
          case conv opt fields =>
            by_cases bound : n + 1 < fields.length
            · rw [List.getElem?_eq_getElem bound]
              constructor
              · rintro ⟨value, hvalue, hs, hv⟩
                cases hvalue
                exact ⟨opt, fields, ⟨rfl, rfl⟩, bound, hs, by
                  simpa [@Flapjack.holEl_eq_getElem Value ⟨unitValue⟩ (n + 1) fields bound] using hv⟩
              · rintro ⟨_, _, ⟨rfl, rfl⟩, _, hs, hv⟩
                exact ⟨fields[n + 1], rfl, hs, by
                  simpa [@Flapjack.holEl_eq_getElem Value ⟨unitValue⟩ (n + 1) fields bound] using hv⟩
            · have absent : fields[n + 1]? = none := List.getElem?_eq_none_iff.mpr (by omega)
              simp_all
              omega

end Flapjack.Compiler.Backend.FlatSem
