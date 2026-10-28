import Flapjack.Compiler.Backend.SourceToFlat.Proofs.EvalApp
import Flapjack.Compiler.Backend.SourceToFlat.Proofs.EvaluateLocalBoundedArray
import Flapjack.Compiler.Backend.SourceToFlat.Proofs.EvaluateLocalBoundedData
import Flapjack.Compiler.Backend.SourceToFlat.Proofs.EvaluateLocalBoundedTree

/-! Bounded expression composition including arrays and function calls. -/
namespace Flapjack.Compiler.Backend.SourceToFlat
open Flapjack.AstHOL Flapjack.SemanticPrimitivesHOL Flapjack.NamespaceHOL
open OracleInvariant

inductive LocalEnvBoundedArrayExpression : AstHOL.Exp → Prop where
  | base (expr : AstHOL.Exp) : LocalEnvPrimitiveExpression expr → LocalEnvBoundedArrayExpression expr
  | eval (args : List AstHOL.Exp) : (∀ expr, expr ∈ args → LocalEnvBoundedArrayExpression expr) →
      LocalEnvBoundedArrayExpression (.app .eval args)
  | call (left right : AstHOL.Exp) : LocalEnvBoundedArrayExpression left → LocalEnvBoundedArrayExpression right →
      LocalEnvBoundedArrayExpression (.app .opapp [left, right])
  | arrayEmpty (body : AstHOL.Exp) : LocalEnvBoundedArrayExpression body →
      LocalEnvBoundedArrayExpression (.app .aallocEmpty [body])
  | arrayFixed (args : List AstHOL.Exp) : (∀ expr, expr ∈ args → LocalEnvBoundedArrayExpression expr) →
      LocalEnvBoundedArrayExpression (.app .aallocFixed args)
  | arrayAlloc (size value : AstHOL.Exp) : LocalEnvBoundedArrayExpression size → LocalEnvBoundedArrayExpression value →
      LocalEnvBoundedArrayExpression (.app .aalloc [size, value])
  | byteArrayAlloc (size value : AstHOL.Exp) : LocalEnvBoundedArrayExpression size → LocalEnvBoundedArrayExpression value →
      LocalEnvBoundedArrayExpression (.app .aw8alloc [size, value])
  | arrayUpdate (pointer index value : AstHOL.Exp) : LocalEnvBoundedArrayExpression pointer → LocalEnvBoundedArrayExpression index →
      LocalEnvBoundedArrayExpression value → LocalEnvBoundedArrayExpression (.app .aupdate [pointer, index, value])
  | arrayUpdateUnsafe (pointer index value : AstHOL.Exp) : LocalEnvBoundedArrayExpression pointer → LocalEnvBoundedArrayExpression index →
      LocalEnvBoundedArrayExpression value → LocalEnvBoundedArrayExpression (.app .aupdateUnsafe [pointer, index, value])
  | byteUpdate (pointer index value : AstHOL.Exp) : LocalEnvBoundedArrayExpression pointer → LocalEnvBoundedArrayExpression index →
      LocalEnvBoundedArrayExpression value → LocalEnvBoundedArrayExpression (.app .aw8update [pointer, index, value])
  | byteUpdateUnsafe (pointer index value : AstHOL.Exp) : LocalEnvBoundedArrayExpression pointer → LocalEnvBoundedArrayExpression index →
      LocalEnvBoundedArrayExpression value → LocalEnvBoundedArrayExpression (.app .aw8updateUnsafe [pointer, index, value])
  | arraySubscript (pointer index : AstHOL.Exp) : LocalEnvBoundedArrayExpression pointer → LocalEnvBoundedArrayExpression index →
      LocalEnvBoundedArrayExpression (.app .asub [pointer, index])
  | arraySubscriptUnsafe (pointer index : AstHOL.Exp) : LocalEnvBoundedArrayExpression pointer → LocalEnvBoundedArrayExpression index →
      LocalEnvBoundedArrayExpression (.app .asubUnsafe [pointer, index])
  | byteSubscript (pointer index : AstHOL.Exp) : LocalEnvBoundedArrayExpression pointer → LocalEnvBoundedArrayExpression index →
      LocalEnvBoundedArrayExpression (.app .aw8sub [pointer, index])
  | byteSubscriptUnsafe (pointer index : AstHOL.Exp) : LocalEnvBoundedArrayExpression pointer → LocalEnvBoundedArrayExpression index →
      LocalEnvBoundedArrayExpression (.app .aw8subUnsafe [pointer, index])
  | copyBytes (source offset length destination dstOffset : AstHOL.Exp) :
      LocalEnvBoundedArrayExpression source → LocalEnvBoundedArrayExpression offset →
      LocalEnvBoundedArrayExpression length → LocalEnvBoundedArrayExpression destination →
      LocalEnvBoundedArrayExpression dstOffset →
      LocalEnvBoundedArrayExpression (.app .copyAw8Aw8 [source, offset, length, destination, dstOffset])
  | stringToBytes (string offset length array dstOffset : AstHOL.Exp) :
      LocalEnvBoundedArrayExpression string → LocalEnvBoundedArrayExpression offset →
      LocalEnvBoundedArrayExpression length → LocalEnvBoundedArrayExpression array →
      LocalEnvBoundedArrayExpression dstOffset →
      LocalEnvBoundedArrayExpression (.app .copyStrAw8 [string, offset, length, array, dstOffset])
  | byteArraySlice (array offset length : AstHOL.Exp) :
      LocalEnvBoundedArrayExpression array → LocalEnvBoundedArrayExpression offset →
      LocalEnvBoundedArrayExpression length → LocalEnvBoundedArrayExpression (.app .copyAw8Str [array, offset, length])
  | stringSlice (string offset length : AstHOL.Exp) :
      LocalEnvBoundedArrayExpression string → LocalEnvBoundedArrayExpression offset →
      LocalEnvBoundedArrayExpression length → LocalEnvBoundedArrayExpression (.app .copyStrStr [string, offset, length])
  | stringSubscript (string index : AstHOL.Exp) : LocalEnvBoundedArrayExpression string → LocalEnvBoundedArrayExpression index →
      LocalEnvBoundedArrayExpression (.app .strsub [string, index])
  | vectorSubscript (vector index : AstHOL.Exp) : LocalEnvBoundedArrayExpression vector → LocalEnvBoundedArrayExpression index →
      LocalEnvBoundedArrayExpression (.app .vsub [vector, index])
  | vectorSubscriptUnsafe (vector index : AstHOL.Exp) : LocalEnvBoundedArrayExpression vector → LocalEnvBoundedArrayExpression index →
      LocalEnvBoundedArrayExpression (.app .vsubUnsafe [vector, index])
  | ffi (name : Basis.Pure.MlString.MlString) (left right : AstHOL.Exp) :
      LocalEnvBoundedArrayExpression left → LocalEnvBoundedArrayExpression right →
      LocalEnvBoundedArrayExpression (.app (.ffi name) [left, right])
  | configGC (left right : AstHOL.Exp) : LocalEnvBoundedArrayExpression left → LocalEnvBoundedArrayExpression right →
      LocalEnvBoundedArrayExpression (.app .configGC [left, right])
  | forceThunk (body : AstHOL.Exp) : LocalEnvBoundedArrayExpression body →
      LocalEnvBoundedArrayExpression (.app (.thunkOp .forceThunk) [body])
  | allocThunk (mode : ThunkMode) (body : AstHOL.Exp) : LocalEnvBoundedArrayExpression body →
      LocalEnvBoundedArrayExpression (.app (.thunkOp (.allocThunk mode)) [body])
  | updateThunk (mode : ThunkMode) (pointer value : AstHOL.Exp) :
      LocalEnvBoundedArrayExpression pointer → LocalEnvBoundedArrayExpression value →
      LocalEnvBoundedArrayExpression (.app (.thunkOp (.updateThunk mode)) [pointer, value])
  | byteXor (array string : AstHOL.Exp) : LocalEnvBoundedArrayExpression array → LocalEnvBoundedArrayExpression string →
      LocalEnvBoundedArrayExpression (.app .xorAw8StrUnsafe [array, string])
  | listAppend (left right : AstHOL.Exp) : LocalEnvBoundedArrayExpression left → LocalEnvBoundedArrayExpression right →
      LocalEnvBoundedArrayExpression (.app .listAppend [left, right])
  | envId (body : AstHOL.Exp) : LocalEnvBoundedArrayExpression body →
      LocalEnvBoundedArrayExpression (.app .envId [body])
  | vectorFromList (body : AstHOL.Exp) : LocalEnvBoundedArrayExpression body → LocalEnvBoundedArrayExpression (.app .vfromList [body])
  | stringImplode (body : AstHOL.Exp) : LocalEnvBoundedArrayExpression body → LocalEnvBoundedArrayExpression (.app .implode [body])
  | stringExplode (body : AstHOL.Exp) : LocalEnvBoundedArrayExpression body → LocalEnvBoundedArrayExpression (.app .explode [body])
  | stringConcat (body : AstHOL.Exp) : LocalEnvBoundedArrayExpression body → LocalEnvBoundedArrayExpression (.app .strcat [body])
  | stringLength (body : AstHOL.Exp) : LocalEnvBoundedArrayExpression body → LocalEnvBoundedArrayExpression (.app .strlen [body])
  | vectorLength (body : AstHOL.Exp) : LocalEnvBoundedArrayExpression body → LocalEnvBoundedArrayExpression (.app .vlength [body])
  | arrayLength (body : AstHOL.Exp) : LocalEnvBoundedArrayExpression body → LocalEnvBoundedArrayExpression (.app .alength [body])
  | byteArrayLength (body : AstHOL.Exp) : LocalEnvBoundedArrayExpression body → LocalEnvBoundedArrayExpression (.app .aw8length [body])
  | tuple (args : List AstHOL.Exp) : (∀ expr, expr ∈ args → LocalEnvBoundedArrayExpression expr) →
      LocalEnvBoundedArrayExpression (.con none args)
  | constructor (id : Ident ModN ConN) (args : List AstHOL.Exp) :
      (∀ expr, expr ∈ args → LocalEnvBoundedArrayExpression expr) → LocalEnvBoundedArrayExpression (.con (some id) args)
  | test (test : Test) (typ : PrimType) (left right : AstHOL.Exp) :
      LocalEnvBoundedArrayExpression left → LocalEnvBoundedArrayExpression right →
      LocalEnvBoundedArrayExpression (.app (.test test typ) [left, right])
  | equality (left right : AstHOL.Exp) : LocalEnvBoundedArrayExpression left → LocalEnvBoundedArrayExpression right →
      LocalEnvBoundedArrayExpression (.app .equality [left, right])
  | booleanNot (body : AstHOL.Exp) : LocalEnvBoundedArrayExpression body →
      LocalEnvBoundedArrayExpression (.app (.arith .not .boolT) [body])
  | floatUnary (action : Arith) (body : AstHOL.Exp) : LocalEnvBoundedArrayExpression body →
      LocalEnvBoundedArrayExpression (.app (.arith action .float64T) [body])
  | integerArith (action : Arith) (left right : AstHOL.Exp) :
      LocalEnvBoundedArrayExpression left → LocalEnvBoundedArrayExpression right →
      LocalEnvBoundedArrayExpression (.app (.arith action .intT) [left, right])
  | word8Arith (action : Arith) (left right : AstHOL.Exp) :
      LocalEnvBoundedArrayExpression left → LocalEnvBoundedArrayExpression right →
      LocalEnvBoundedArrayExpression (.app (.arith action (.wordT .w8)) [left, right])
  | word64Arith (action : Arith) (left right : AstHOL.Exp) :
      LocalEnvBoundedArrayExpression left → LocalEnvBoundedArrayExpression right →
      LocalEnvBoundedArrayExpression (.app (.arith action (.wordT .w64)) [left, right])
  | word8Shift (shift : Shift) (amount : Nat) (body : AstHOL.Exp) : LocalEnvBoundedArrayExpression body →
      LocalEnvBoundedArrayExpression (.app (.shift .w8 shift amount) [body])
  | word64Shift (shift : Shift) (amount : Nat) (body : AstHOL.Exp) : LocalEnvBoundedArrayExpression body →
      LocalEnvBoundedArrayExpression (.app (.shift .w64 shift amount) [body])
  | conversion (fromType toType : PrimType) (body : AstHOL.Exp) : LocalEnvBoundedArrayExpression body →
      LocalEnvBoundedArrayExpression (.app (.fromTo fromType toType) [body])
  | ref_ (body : AstHOL.Exp) : LocalEnvBoundedArrayExpression body →
      LocalEnvBoundedArrayExpression (.app .opref [body])
  | assign (left right : AstHOL.Exp) : LocalEnvBoundedArrayExpression left → LocalEnvBoundedArrayExpression right →
      LocalEnvBoundedArrayExpression (.app .opassign [left, right])
  | deref (body : AstHOL.Exp) : LocalEnvBoundedArrayExpression body →
      LocalEnvBoundedArrayExpression (.app .opderef [body])
  | mat (body : AstHOL.Exp) (rows : List (Pat × AstHOL.Exp)) : LocalEnvBoundedArrayExpression body →
      (∀ pattern rowBody, (pattern, rowBody) ∈ rows → LocalEnvBoundedArrayExpression rowBody) →
      LocalEnvBoundedArrayExpression (.mat body rows)
  | handle (body : AstHOL.Exp) (rows : List (Pat × AstHOL.Exp)) : LocalEnvBoundedArrayExpression body →
      (∀ pattern rowBody, (pattern, rowBody) ∈ rows → LocalEnvBoundedArrayExpression rowBody) →
      LocalEnvBoundedArrayExpression (.handle body rows)
  | letrec (funs : List (VarN × VarN × AstHOL.Exp)) (body : AstHOL.Exp) :
      LocalEnvBoundedArrayExpression body → LocalEnvBoundedArrayExpression (.letrec funs body)
  | letNamed (name : VarN) (first body : AstHOL.Exp) : LocalEnvBoundedArrayExpression first →
      LocalEnvBoundedArrayExpression body → LocalEnvBoundedArrayExpression (.let_ (some name) first body)
  | letAnonymous (first body : AstHOL.Exp) : LocalEnvBoundedArrayExpression first → LocalEnvBoundedArrayExpression body →
      LocalEnvBoundedArrayExpression (.let_ none first body)
  | if_ (cond yes no : AstHOL.Exp) : LocalEnvBoundedArrayExpression cond → LocalEnvBoundedArrayExpression yes →
      LocalEnvBoundedArrayExpression no → LocalEnvBoundedArrayExpression (.if_ cond yes no)
  | log (op : Lop) (left right : AstHOL.Exp) : LocalEnvBoundedArrayExpression left → LocalEnvBoundedArrayExpression right →
      LocalEnvBoundedArrayExpression (.log op left right)
  | raise_ (body : AstHOL.Exp) : LocalEnvBoundedArrayExpression body → LocalEnvBoundedArrayExpression (.raise body)
  | tannot (expr : AstHOL.Exp) (typ : AstT) : LocalEnvBoundedArrayExpression expr → LocalEnvBoundedArrayExpression (.tannot expr typ)
  | lannot (expr : AstHOL.Exp) (loc : Flapjack.Misc.Location.Locs) : LocalEnvBoundedArrayExpression expr →
      LocalEnvBoundedArrayExpression (.lannot expr loc)

/-- Covered expressions satisfy the preliminary arbitrary-local hypothesis;
the relations remain pending HOL correspondence review. -/
theorem localEnvBounded_arrayTree {C F : Type} [Nonempty C]
    (interp : Option (Value → Option (Config × C))) (transform : List Dec → List Dec)
    (limit : Nat) (calledIH : LocalEnvClockIH (F := F) interp transform limit)
    (decsIH : FactoredDecClockIH (F := F) interp transform limit)
    (expr : AstHOL.Exp) (covered : LocalEnvBoundedArrayExpression expr) : LocalEnvBoundedIH (F := F) interp transform limit expr := by
  induction covered with
  | base expr covered =>
    exact localEnvBounded_of_unbounded interp transform limit expr (localEnvIH_primitiveTree interp transform expr covered)
  | eval args _ ih => exact localEnvBounded_eval interp transform limit decsIH args ih
  | call left right _ _ leftIH rightIH =>
    exact localEnvBounded_opapp interp transform limit calledIH left right leftIH rightIH
  | arrayEmpty body _ ih => exact localEnvBounded_aallocEmpty interp transform limit body ih
  | arrayFixed args _ ih => exact localEnvBounded_aallocFixed interp transform limit args ih
  | arrayAlloc size value _ _ sizeIH valueIH => exact localEnvBounded_aalloc interp transform limit size value sizeIH valueIH
  | byteArrayAlloc size value _ _ sizeIH valueIH => exact localEnvBounded_aw8alloc interp transform limit size value sizeIH valueIH
  | arrayUpdate pointer index value _ _ _ pointerIH indexIH valueIH =>
    exact localEnvBounded_aupdate interp transform limit pointer index value pointerIH indexIH valueIH
  | arrayUpdateUnsafe pointer index value _ _ _ pointerIH indexIH valueIH =>
    exact localEnvBounded_aupdateUnsafe interp transform limit pointer index value pointerIH indexIH valueIH
  | byteUpdate pointer index value _ _ _ pointerIH indexIH valueIH =>
    exact localEnvBounded_aw8update interp transform limit pointer index value pointerIH indexIH valueIH
  | byteUpdateUnsafe pointer index value _ _ _ pointerIH indexIH valueIH =>
    exact localEnvBounded_aw8updateUnsafe interp transform limit pointer index value pointerIH indexIH valueIH
  | arraySubscript pointer index _ _ pointerIH indexIH =>
    exact localEnvBounded_asub interp transform limit pointer index pointerIH indexIH
  | arraySubscriptUnsafe pointer index _ _ pointerIH indexIH =>
    exact localEnvBounded_asubUnsafe interp transform limit pointer index pointerIH indexIH
  | byteSubscript pointer index _ _ pointerIH indexIH =>
    exact localEnvBounded_aw8sub interp transform limit pointer index pointerIH indexIH
  | byteSubscriptUnsafe pointer index _ _ pointerIH indexIH =>
    exact localEnvBounded_aw8subUnsafe interp transform limit pointer index pointerIH indexIH
  | copyBytes source offset length destination dstOffset _ _ _ _ _ sourceIH offsetIH lengthIH destinationIH dstOffsetIH =>
    exact localEnvBounded_copyAw8Aw8 interp transform limit source offset length destination dstOffset sourceIH offsetIH lengthIH destinationIH dstOffsetIH
  | stringToBytes string offset length array dstOffset _ _ _ _ _ stringIH offsetIH lengthIH arrayIH dstOffsetIH =>
    exact localEnvBounded_copyStrAw8 interp transform limit string offset length array dstOffset stringIH offsetIH lengthIH arrayIH dstOffsetIH
  | byteArraySlice array offset length _ _ _ arrayIH offsetIH lengthIH =>
    exact localEnvBounded_copyAw8Str interp transform limit array offset length arrayIH offsetIH lengthIH
  | stringSlice string offset length _ _ _ stringIH offsetIH lengthIH =>
    exact localEnvBounded_copyStrStr interp transform limit string offset length stringIH offsetIH lengthIH
  | stringSubscript string index _ _ stringIH indexIH =>
    exact localEnvBounded_strsub interp transform limit string index stringIH indexIH
  | vectorSubscript vector index _ _ vectorIH indexIH =>
    exact localEnvBounded_vsub interp transform limit vector index vectorIH indexIH
  | vectorSubscriptUnsafe vector index _ _ vectorIH indexIH =>
    exact localEnvBounded_vsubUnsafe interp transform limit vector index vectorIH indexIH
  | ffi name left right _ _ leftIH rightIH =>
    exact localEnvBounded_ffi interp transform limit name left right leftIH rightIH
  | configGC left right _ _ leftIH rightIH =>
    exact localEnvBounded_configGC interp transform limit left right leftIH rightIH
  | forceThunk body _ ih => exact localEnvBounded_forceThunk interp transform limit calledIH body ih
  | allocThunk mode body _ ih => exact localEnvBounded_allocThunk interp transform limit mode body ih
  | updateThunk mode pointer value _ _ pointerIH valueIH =>
    exact localEnvBounded_updateThunk interp transform limit mode pointer value pointerIH valueIH
  | byteXor array string _ _ arrayIH stringIH =>
    exact localEnvBounded_xorAw8StrUnsafe interp transform limit array string arrayIH stringIH
  | listAppend left right _ _ leftIH rightIH =>
    exact localEnvBounded_listAppend interp transform limit left right leftIH rightIH
  | envId body _ ih => exact localEnvBounded_envId interp transform limit body ih
  | vectorFromList body _ ih => exact localEnvBounded_vfromList interp transform limit body ih
  | stringImplode body _ ih => exact localEnvBounded_implode interp transform limit body ih
  | stringExplode body _ ih => exact localEnvBounded_explode interp transform limit body ih
  | stringConcat body _ ih => exact localEnvBounded_strcat interp transform limit body ih
  | stringLength body _ ih => exact localEnvBounded_strlen interp transform limit body ih
  | vectorLength body _ ih => exact localEnvBounded_vlength interp transform limit body ih
  | arrayLength body _ ih => exact localEnvBounded_alength interp transform limit body ih
  | byteArrayLength body _ ih => exact localEnvBounded_aw8length interp transform limit body ih
  | tuple args _ ih => exact localEnvBounded_tuple interp transform limit args ih
  | constructor id args _ ih => exact localEnvBounded_constructor interp transform limit id args ih
  | test test typ left right _ _ leftIH rightIH => exact localEnvBounded_test interp transform limit test typ left right leftIH rightIH
  | equality left right _ _ leftIH rightIH => exact localEnvBounded_equality interp transform limit left right leftIH rightIH
  | booleanNot body _ ih => exact localEnvBounded_booleanNot interp transform limit body ih
  | floatUnary action body _ ih => exact localEnvBounded_floatUnary interp transform limit body action ih
  | integerArith action left right _ _ leftIH rightIH =>
    exact localEnvBounded_integerArith interp transform limit action left right leftIH rightIH
  | word8Arith action left right _ _ leftIH rightIH =>
    exact localEnvBounded_word8Arith interp transform limit action left right leftIH rightIH
  | word64Arith action left right _ _ leftIH rightIH =>
    exact localEnvBounded_word64Arith interp transform limit action left right leftIH rightIH
  | word8Shift shift amount body _ ih => exact localEnvBounded_word8Shift interp transform limit body shift amount ih
  | word64Shift shift amount body _ ih => exact localEnvBounded_word64Shift interp transform limit body shift amount ih
  | conversion fromType toType body _ ih =>
    exact localEnvBounded_conversion interp transform limit body fromType toType ih
  | ref_ body _ ih => exact localEnvBounded_opref interp transform limit body ih
  | assign left right _ _ leftIH rightIH => exact localEnvBounded_opassign interp transform limit left right leftIH rightIH
  | deref body _ ih => exact localEnvBounded_opderef interp transform limit body ih
  | mat body rows _ _ bodyIH rowsIH => exact localEnvBounded_mat interp transform limit body rows bodyIH rowsIH
  | handle body rows _ _ bodyIH rowsIH => exact localEnvBounded_handle interp transform limit body rows bodyIH rowsIH
  | letrec funs body _ ih => exact localEnvBounded_letrec interp transform limit funs body ih
  | letNamed name first body _ _ firstIH bodyIH => exact localEnvBounded_let_named interp transform limit name first body firstIH bodyIH
  | letAnonymous first body _ _ firstIH bodyIH => exact localEnvBounded_let_anonymous interp transform limit first body firstIH bodyIH
  | if_ cond yes no _ _ _ condIH yesIH noIH => exact localEnvBounded_if interp transform limit cond yes no condIH yesIH noIH
  | log op left right _ _ leftIH rightIH => exact localEnvBounded_log interp transform limit op left right leftIH rightIH
  | raise_ body _ ih => exact localEnvBounded_raise interp transform limit body ih
  | tannot expr typ _ ih => exact localEnvBounded_tannot interp transform limit expr typ ih
  | lannot expr loc _ ih => exact localEnvBounded_lannot interp transform limit expr loc ih




/-- The covered expression proof can be invoked directly from the expression
and declaration induction hypotheses at smaller clocks. -/
theorem localEnvBounded_arrayTree_of_smaller {C F : Type} [Nonempty C]
    (interp : Option (Value → Option (Config × C))) (transform : List Dec → List Dec) (limit : Nat)
    (smallerExprs : ∀ n, n < limit → ∀ expr, LocalEnvBoundedIH (F := F) interp transform n expr)
    (smallerDecs : ∀ n, n < limit → ∀ decs, FactoredDecBoundedIH (F := F) interp transform n decs)
    (expr : AstHOL.Exp) (covered : LocalEnvBoundedArrayExpression expr) :
    LocalEnvBoundedIH (F := F) interp transform limit expr :=
  localEnvBounded_arrayTree interp transform limit
    (localEnvClockIH_of_smaller interp transform limit smallerExprs)
    (factoredDecClockIH_of_smaller interp transform limit smallerDecs) expr covered

/-- A value declaration with a covered initializer follows from the same
smaller-clock hypotheses as the initializer expression. -/
theorem factoredDecBoundedIH_dlet_arrayTree {C F : Type} [Nonempty C]
    (interp : Option (Value → Option (Config × C))) (transform : List Dec → List Dec) (limit : Nat)
    (smallerExprs : ∀ n, n < limit → ∀ expr, LocalEnvBoundedIH (F := F) interp transform n expr)
    (smallerDecs : ∀ n, n < limit → ∀ decs, FactoredDecBoundedIH (F := F) interp transform n decs)
    (location : Flapjack.Misc.Location.Locs) (pattern : Pat) (expr : AstHOL.Exp)
    (covered : LocalEnvBoundedArrayExpression expr) :
    FactoredDecBoundedIH (F := F) interp transform limit [.dlet location pattern expr] := by
  apply factoredDecBoundedIH_dlet_expression interp transform limit location pattern expr
  exact localEnvBounded_arrayTree_of_smaller interp transform limit smallerExprs smallerDecs expr covered

/-- Dynamic evaluation is simulated for covered operands, assuming the
declaration induction hypothesis for every decoded declaration list. -/
theorem localEnvBounded_eval_arrayTree {C F : Type} [Nonempty C]
    (interp : Option (Value → Option (Config × C))) (transform : List Dec → List Dec)
    (limit : Nat) (calledIH : LocalEnvClockIH (F := F) interp transform limit)
    (decsIH : FactoredDecClockIH (F := F) interp transform limit)
    (exprs : List AstHOL.Exp) (covered : ∀ expr, expr ∈ exprs → LocalEnvBoundedArrayExpression expr) :
    LocalEnvBoundedIH (F := F) interp transform limit (.app .eval exprs) := by
  apply localEnvBounded_eval interp transform limit decsIH exprs
  intro expr member
  exact localEnvBounded_arrayTree interp transform limit calledIH decsIH expr (covered expr member)

/-- At clock zero the smaller-clock function-call hypothesis is vacuous. -/
theorem localEnvClockIH_zero {C F : Type} [Nonempty C]
    (interp : Option (Value → Option (Config × C))) (transform : List Dec → List Dec) :
    LocalEnvClockIH (F := F) interp transform 0 := by
  intro expr genv start finish other source flat baseEnv sourceLocal flatEnv traces trace baseMap gen below
  omega

/-- At clock zero the smaller-clock declaration hypothesis is vacuous. -/
theorem factoredDecClockIH_zero {C F : Type} [Nonempty C]
    (interp : Option (Value → Option (Config × C))) (transform : List Dec → List Dec) :
    FactoredDecClockIH (F := F) interp transform 0 := by
  intro decs genv env nextEnv sourceEnv trace source sourceLast flat start finish next other n n' gen nextGen flatDecs result below
  omega

/-- Dynamic evaluation at clock zero is simulated when its operands are
covered by the bounded expression proof. -/
theorem localEnvBounded_eval_zero_arrayTree {C F : Type} [Nonempty C]
    (interp : Option (Value → Option (Config × C))) (transform : List Dec → List Dec)
    (exprs : List AstHOL.Exp) (covered : ∀ expr, expr ∈ exprs → LocalEnvBoundedArrayExpression expr) :
    LocalEnvBoundedIH (F := F) interp transform 0 (.app .eval exprs) := by
  apply localEnvBounded_eval_zero interp transform exprs
  intro expr member
  exact localEnvBounded_arrayTree interp transform 0 (localEnvClockIH_zero interp transform)
    (factoredDecClockIH_zero interp transform) expr (covered expr member)

end Flapjack.Compiler.Backend.SourceToFlat
