import Flapjack.Compiler.Backend.SourceToFlat.Proofs.EvaluateLocalBoundedArray
import Flapjack.Compiler.Backend.SourceToFlat.Proofs.EvaluateLocalBoundedTree

/-! Bounded expression composition including arrays and function calls. -/
namespace Flapjack.Compiler.Backend.SourceToFlat
open Flapjack.AstHOL Flapjack.SemanticPrimitivesHOL Flapjack.NamespaceHOL
open OracleInvariant

inductive LocalEnvBoundedArrayExpression : AstHOL.Exp → Prop where
  | base (expr : AstHOL.Exp) : LocalEnvPrimitiveExpression expr → LocalEnvBoundedArrayExpression expr
  | call (left right : AstHOL.Exp) : LocalEnvBoundedArrayExpression left → LocalEnvBoundedArrayExpression right →
      LocalEnvBoundedArrayExpression (.app .opapp [left, right])
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
    (expr : AstHOL.Exp) (covered : LocalEnvBoundedArrayExpression expr) : LocalEnvBoundedIH (F := F) interp transform limit expr := by
  induction covered with
  | base expr covered =>
    exact localEnvBounded_of_unbounded interp transform limit expr (localEnvIH_primitiveTree interp transform expr covered)
  | call left right _ _ leftIH rightIH =>
    exact localEnvBounded_opapp interp transform limit calledIH left right leftIH rightIH
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
  | arrayLength body _ ih => exact localEnvBounded_alength interp transform limit body ih
  | byteArrayLength body _ ih => exact localEnvBounded_aw8length interp transform limit body ih
  | tuple args _ ih => exact localEnvBounded_tuple interp transform limit args ih
  | constructor id args _ ih => exact localEnvBounded_constructor interp transform limit id args ih
  | test test typ left right _ _ leftIH rightIH => exact localEnvBounded_test interp transform limit test typ left right leftIH rightIH
  | equality left right _ _ leftIH rightIH => exact localEnvBounded_equality interp transform limit left right leftIH rightIH
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




end Flapjack.Compiler.Backend.SourceToFlat
