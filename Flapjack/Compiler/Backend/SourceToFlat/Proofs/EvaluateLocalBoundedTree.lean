import Flapjack.Compiler.Backend.SourceToFlat.Proofs.EvaluateLocalBoundedPrimitive
import Flapjack.Compiler.Backend.SourceToFlat.Proofs.EvaluateLocalBoundedMatch
import Flapjack.Compiler.Backend.SourceToFlat.Proofs.EvaluateLocalCall

/-! Composed clock-bounded expression cases over preliminary relations. -/
namespace Flapjack.Compiler.Backend.SourceToFlat
open Flapjack.AstHOL Flapjack.SemanticPrimitivesHOL Flapjack.NamespaceHOL
open OracleInvariant

inductive LocalEnvBoundedExpression : AstHOL.Exp → Prop where
  | base (expr : AstHOL.Exp) : LocalEnvPrimitiveExpression expr → LocalEnvBoundedExpression expr
  | call (left right : AstHOL.Exp) : LocalEnvBoundedExpression left → LocalEnvBoundedExpression right →
      LocalEnvBoundedExpression (.app .opapp [left, right])
  | tuple (args : List AstHOL.Exp) : (∀ expr, expr ∈ args → LocalEnvBoundedExpression expr) →
      LocalEnvBoundedExpression (.con none args)
  | constructor (id : Ident ModN ConN) (args : List AstHOL.Exp) :
      (∀ expr, expr ∈ args → LocalEnvBoundedExpression expr) → LocalEnvBoundedExpression (.con (some id) args)
  | test (test : Test) (typ : PrimType) (left right : AstHOL.Exp) :
      LocalEnvBoundedExpression left → LocalEnvBoundedExpression right →
      LocalEnvBoundedExpression (.app (.test test typ) [left, right])
  | equality (left right : AstHOL.Exp) : LocalEnvBoundedExpression left → LocalEnvBoundedExpression right →
      LocalEnvBoundedExpression (.app .equality [left, right])
  | integerArith (action : Arith) (left right : AstHOL.Exp) :
      LocalEnvBoundedExpression left → LocalEnvBoundedExpression right →
      LocalEnvBoundedExpression (.app (.arith action .intT) [left, right])
  | word8Arith (action : Arith) (left right : AstHOL.Exp) :
      LocalEnvBoundedExpression left → LocalEnvBoundedExpression right →
      LocalEnvBoundedExpression (.app (.arith action (.wordT .w8)) [left, right])
  | word64Arith (action : Arith) (left right : AstHOL.Exp) :
      LocalEnvBoundedExpression left → LocalEnvBoundedExpression right →
      LocalEnvBoundedExpression (.app (.arith action (.wordT .w64)) [left, right])
  | word8Shift (shift : Shift) (amount : Nat) (body : AstHOL.Exp) : LocalEnvBoundedExpression body →
      LocalEnvBoundedExpression (.app (.shift .w8 shift amount) [body])
  | word64Shift (shift : Shift) (amount : Nat) (body : AstHOL.Exp) : LocalEnvBoundedExpression body →
      LocalEnvBoundedExpression (.app (.shift .w64 shift amount) [body])
  | conversion (fromType toType : PrimType) (body : AstHOL.Exp) : LocalEnvBoundedExpression body →
      LocalEnvBoundedExpression (.app (.fromTo fromType toType) [body])
  | ref_ (body : AstHOL.Exp) : LocalEnvBoundedExpression body →
      LocalEnvBoundedExpression (.app .opref [body])
  | assign (left right : AstHOL.Exp) : LocalEnvBoundedExpression left → LocalEnvBoundedExpression right →
      LocalEnvBoundedExpression (.app .opassign [left, right])
  | deref (body : AstHOL.Exp) : LocalEnvBoundedExpression body →
      LocalEnvBoundedExpression (.app .opderef [body])
  | mat (body : AstHOL.Exp) (rows : List (Pat × AstHOL.Exp)) : LocalEnvBoundedExpression body →
      (∀ pattern rowBody, (pattern, rowBody) ∈ rows → LocalEnvBoundedExpression rowBody) →
      LocalEnvBoundedExpression (.mat body rows)
  | handle (body : AstHOL.Exp) (rows : List (Pat × AstHOL.Exp)) : LocalEnvBoundedExpression body →
      (∀ pattern rowBody, (pattern, rowBody) ∈ rows → LocalEnvBoundedExpression rowBody) →
      LocalEnvBoundedExpression (.handle body rows)
  | letrec (funs : List (VarN × VarN × AstHOL.Exp)) (body : AstHOL.Exp) :
      LocalEnvBoundedExpression body → LocalEnvBoundedExpression (.letrec funs body)
  | letNamed (name : VarN) (first body : AstHOL.Exp) : LocalEnvBoundedExpression first →
      LocalEnvBoundedExpression body → LocalEnvBoundedExpression (.let_ (some name) first body)
  | letAnonymous (first body : AstHOL.Exp) : LocalEnvBoundedExpression first → LocalEnvBoundedExpression body →
      LocalEnvBoundedExpression (.let_ none first body)
  | if_ (cond yes no : AstHOL.Exp) : LocalEnvBoundedExpression cond → LocalEnvBoundedExpression yes →
      LocalEnvBoundedExpression no → LocalEnvBoundedExpression (.if_ cond yes no)
  | log (op : Lop) (left right : AstHOL.Exp) : LocalEnvBoundedExpression left → LocalEnvBoundedExpression right →
      LocalEnvBoundedExpression (.log op left right)
  | raise_ (body : AstHOL.Exp) : LocalEnvBoundedExpression body → LocalEnvBoundedExpression (.raise body)
  | tannot (expr : AstHOL.Exp) (typ : AstT) : LocalEnvBoundedExpression expr → LocalEnvBoundedExpression (.tannot expr typ)
  | lannot (expr : AstHOL.Exp) (loc : Flapjack.Misc.Location.Locs) : LocalEnvBoundedExpression expr →
      LocalEnvBoundedExpression (.lannot expr loc)

/-- Covered expressions satisfy the preliminary arbitrary-local hypothesis;
the relations remain pending HOL correspondence review. -/
theorem localEnvBounded_tree {C F : Type} [Nonempty C]
    (interp : Option (Value → Option (Config × C))) (transform : List Dec → List Dec)
    (limit : Nat) (calledIH : LocalEnvClockIH (F := F) interp transform limit)
    (expr : AstHOL.Exp) (covered : LocalEnvBoundedExpression expr) : LocalEnvBoundedIH (F := F) interp transform limit expr := by
  induction covered with
  | base expr covered =>
    exact localEnvBounded_of_unbounded interp transform limit expr (localEnvIH_primitiveTree interp transform expr covered)
  | call left right _ _ leftIH rightIH =>
    exact localEnvBounded_opapp interp transform limit calledIH left right leftIH rightIH
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
