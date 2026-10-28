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
  | unaryBasicBadArity (op : Op) (args : List AstHOL.Exp) : UnaryBasicOp op → args.length ≠ 1 →
      (∀ expr, expr ∈ args → LocalEnvBoundedArrayExpression expr) → LocalEnvBoundedArrayExpression (.app op args)
  | binaryBasicBadArity (op : Op) (args : List AstHOL.Exp) : BinaryBasicOp op → args.length ≠ 2 →
      (∀ expr, expr ∈ args → LocalEnvBoundedArrayExpression expr) → LocalEnvBoundedArrayExpression (.app op args)
  | ternaryBasicBadArity (op : Op) (args : List AstHOL.Exp) : TernaryBasicOp op → args.length ≠ 3 →
      (∀ expr, expr ∈ args → LocalEnvBoundedArrayExpression expr) → LocalEnvBoundedArrayExpression (.app op args)
  | fiveArgBasicBadArity (op : Op) (args : List AstHOL.Exp) : FiveArgBasicOp op → args.length ≠ 5 →
      (∀ expr, expr ∈ args → LocalEnvBoundedArrayExpression expr) → LocalEnvBoundedArrayExpression (.app op args)
  | eval (args : List AstHOL.Exp) : (∀ expr, expr ∈ args → LocalEnvBoundedArrayExpression expr) →
      LocalEnvBoundedArrayExpression (.app .eval args)
  | call (left right : AstHOL.Exp) : LocalEnvBoundedArrayExpression left → LocalEnvBoundedArrayExpression right →
      LocalEnvBoundedArrayExpression (.app .opapp [left, right])
  | callBadArity (args : List AstHOL.Exp) : args.length ≠ 2 →
      (∀ expr, expr ∈ args → LocalEnvBoundedArrayExpression expr) → LocalEnvBoundedArrayExpression (.app .opapp args)
  | arrayEmpty (body : AstHOL.Exp) : LocalEnvBoundedArrayExpression body →
      LocalEnvBoundedArrayExpression (.app .aallocEmpty [body])
  | arrayEmptyBadArity (args : List AstHOL.Exp) : args.length ≠ 1 →
      (∀ expr, expr ∈ args → LocalEnvBoundedArrayExpression expr) → LocalEnvBoundedArrayExpression (.app .aallocEmpty args)
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
  | ffiBadArity (name : Basis.Pure.MlString.MlString) (args : List AstHOL.Exp) : args.length ≠ 2 →
      (∀ expr, expr ∈ args → LocalEnvBoundedArrayExpression expr) → LocalEnvBoundedArrayExpression (.app (.ffi name) args)
  | configGC (left right : AstHOL.Exp) : LocalEnvBoundedArrayExpression left → LocalEnvBoundedArrayExpression right →
      LocalEnvBoundedArrayExpression (.app .configGC [left, right])
  | forceThunk (body : AstHOL.Exp) : LocalEnvBoundedArrayExpression body →
      LocalEnvBoundedArrayExpression (.app (.thunkOp .forceThunk) [body])
  | forceThunkBadArity (args : List AstHOL.Exp) : args.length ≠ 1 →
      (∀ expr, expr ∈ args → LocalEnvBoundedArrayExpression expr) →
      LocalEnvBoundedArrayExpression (.app (.thunkOp .forceThunk) args)
  | allocThunk (mode : ThunkMode) (body : AstHOL.Exp) : LocalEnvBoundedArrayExpression body →
      LocalEnvBoundedArrayExpression (.app (.thunkOp (.allocThunk mode)) [body])
  | allocThunkBadArity (mode : ThunkMode) (args : List AstHOL.Exp) : args.length ≠ 1 →
      (∀ expr, expr ∈ args → LocalEnvBoundedArrayExpression expr) →
      LocalEnvBoundedArrayExpression (.app (.thunkOp (.allocThunk mode)) args)
  | updateThunk (mode : ThunkMode) (pointer value : AstHOL.Exp) :
      LocalEnvBoundedArrayExpression pointer → LocalEnvBoundedArrayExpression value →
      LocalEnvBoundedArrayExpression (.app (.thunkOp (.updateThunk mode)) [pointer, value])
  | updateThunkBadArity (mode : ThunkMode) (args : List AstHOL.Exp) : args.length ≠ 2 →
      (∀ expr, expr ∈ args → LocalEnvBoundedArrayExpression expr) →
      LocalEnvBoundedArrayExpression (.app (.thunkOp (.updateThunk mode)) args)
  | byteXor (array string : AstHOL.Exp) : LocalEnvBoundedArrayExpression array → LocalEnvBoundedArrayExpression string →
      LocalEnvBoundedArrayExpression (.app .xorAw8StrUnsafe [array, string])
  | listAppend (left right : AstHOL.Exp) : LocalEnvBoundedArrayExpression left → LocalEnvBoundedArrayExpression right →
      LocalEnvBoundedArrayExpression (.app .listAppend [left, right])
  | envId (body : AstHOL.Exp) : LocalEnvBoundedArrayExpression body →
      LocalEnvBoundedArrayExpression (.app .envId [body])
  | envIdBadArity (args : List AstHOL.Exp) : args.length ≠ 1 →
      (∀ expr, expr ∈ args → LocalEnvBoundedArrayExpression expr) → LocalEnvBoundedArrayExpression (.app .envId args)
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
  | equalityBadArity (args : List AstHOL.Exp) : args.length ≠ 2 →
      (∀ expr, expr ∈ args → LocalEnvBoundedArrayExpression expr) →
      LocalEnvBoundedArrayExpression (.app .equality args)
  | testBadArity (test : Test) (typ : PrimType) (args : List AstHOL.Exp) : args.length ≠ 2 →
      (∀ expr, expr ∈ args → LocalEnvBoundedArrayExpression expr) →
      LocalEnvBoundedArrayExpression (.app (.test test typ) args)
  | booleanNot (body : AstHOL.Exp) : LocalEnvBoundedArrayExpression body →
      LocalEnvBoundedArrayExpression (.app (.arith .not .boolT) [body])
  | floatFma (first second third : AstHOL.Exp) :
      LocalEnvBoundedArrayExpression first → LocalEnvBoundedArrayExpression second →
      LocalEnvBoundedArrayExpression third →
      LocalEnvBoundedArrayExpression (.app (.arith .fma .float64T) [first, second, third])
  | floatTernaryNonFma (action : Arith) (args : List AstHOL.Exp) :
      action ≠ .fma → args.length = 3 → (∀ expr, expr ∈ args → LocalEnvBoundedArrayExpression expr) →
      LocalEnvBoundedArrayExpression (.app (.arith action .float64T) args)
  | floatBinary (action : Arith) (left right : AstHOL.Exp) :
      LocalEnvBoundedArrayExpression left → LocalEnvBoundedArrayExpression right →
      LocalEnvBoundedArrayExpression (.app (.arith action .float64T) [left, right])
  | floatUnary (action : Arith) (body : AstHOL.Exp) : LocalEnvBoundedArrayExpression body →
      LocalEnvBoundedArrayExpression (.app (.arith action .float64T) [body])
  | arithExtremeArity (action : Arith) (typ : PrimType) (args : List AstHOL.Exp) :
      (args.length = 0 ∨ 3 < args.length) →
      (∀ expr, expr ∈ args → LocalEnvBoundedArrayExpression expr) →
      LocalEnvBoundedArrayExpression (.app (.arith action typ) args)
  | intWordArithBadArity (action : Arith) (size : Option WordSize) (args : List AstHOL.Exp) :
      args.length ≠ 2 → (∀ expr, expr ∈ args → LocalEnvBoundedArrayExpression expr) →
      LocalEnvBoundedArrayExpression
        (.app (.arith action (match size with | none => .intT | some w => .wordT w)) args)
  | boolArithBadArity (action : Arith) (args : List AstHOL.Exp) :
      args.length ≠ 1 → (∀ expr, expr ∈ args → LocalEnvBoundedArrayExpression expr) →
      LocalEnvBoundedArrayExpression (.app (.arith action .boolT) args)
  | arithRejectedType (action : Arith) (typ : PrimType) (args : List AstHOL.Exp) :
      (typ = .charT ∨ typ = .strT ∨ (typ = .boolT ∧ action ≠ .not)) →
      (∀ expr, expr ∈ args → LocalEnvBoundedArrayExpression expr) →
      LocalEnvBoundedArrayExpression (.app (.arith action typ) args)
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
  | shiftBadArity (size : WordSize) (shift : Shift) (amount : Nat) (args : List AstHOL.Exp) :
      args.length ≠ 1 → (∀ expr, expr ∈ args → LocalEnvBoundedArrayExpression expr) →
      LocalEnvBoundedArrayExpression (.app (.shift size shift amount) args)
  | conversion (fromType toType : PrimType) (body : AstHOL.Exp) : LocalEnvBoundedArrayExpression body →
      LocalEnvBoundedArrayExpression (.app (.fromTo fromType toType) [body])
  | conversionBadArity (fromType toType : PrimType) (args : List AstHOL.Exp) :
      args.length ≠ 1 → (∀ expr, expr ∈ args → LocalEnvBoundedArrayExpression expr) →
      LocalEnvBoundedArrayExpression (.app (.fromTo fromType toType) args)
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

/-- Arithmetic applications are covered whenever their operands are covered,
including operations that reject their type or arity. -/
theorem arithmeticExpression_covered (action : Arith) (typ : PrimType) (args : List AstHOL.Exp)
    (each : ∀ expr, expr ∈ args → LocalEnvBoundedArrayExpression expr) :
    LocalEnvBoundedArrayExpression (.app (.arith action typ) args) := by
  cases args with
  | nil => exact .arithExtremeArity action typ [] (Or.inl rfl) each
  | cons first rest =>
    have firstCovered := each first (by simp)
    cases rest with
    | nil =>
      cases typ with
      | boolT =>
        by_cases isNot : action = .not
        · subst action; exact .booleanNot first firstCovered
        · exact .arithRejectedType action .boolT [first] (Or.inr (Or.inr ⟨rfl, isNot⟩)) each
      | intT => exact .intWordArithBadArity action none [first] (by simp) each
      | charT => exact .arithRejectedType action .charT [first] (Or.inl rfl) each
      | strT => exact .arithRejectedType action .strT [first] (Or.inr (Or.inl rfl)) each
      | wordT size => exact .intWordArithBadArity action (some size) [first] (by simp) each
      | float64T => exact .floatUnary action first firstCovered
    | cons second rest =>
      have secondCovered := each second (by simp)
      cases rest with
      | nil =>
        cases typ with
        | boolT => exact .boolArithBadArity action [first, second] (by simp) each
        | intT => exact .integerArith action first second firstCovered secondCovered
        | charT => exact .arithRejectedType action .charT [first, second] (Or.inl rfl) each
        | strT => exact .arithRejectedType action .strT [first, second] (Or.inr (Or.inl rfl)) each
        | wordT size => cases size with
          | w8 => exact .word8Arith action first second firstCovered secondCovered
          | w64 => exact .word64Arith action first second firstCovered secondCovered
        | float64T => exact .floatBinary action first second firstCovered secondCovered
      | cons third rest =>
        have thirdCovered := each third (by simp)
        cases rest with
        | nil =>
          cases typ with
          | boolT => exact .boolArithBadArity action [first, second, third] (by simp) each
          | intT => exact .intWordArithBadArity action none [first, second, third] (by simp) each
          | charT => exact .arithRejectedType action .charT [first, second, third] (Or.inl rfl) each
          | strT => exact .arithRejectedType action .strT [first, second, third] (Or.inr (Or.inl rfl)) each
          | wordT size => exact .intWordArithBadArity action (some size) [first, second, third] (by simp) each
          | float64T =>
            by_cases isFma : action = .fma
            · subst action; exact .floatFma first second third firstCovered secondCovered thirdCovered
            · exact .floatTernaryNonFma action [first, second, third] isFma rfl each
        | cons fourth rest =>
          exact .arithExtremeArity action typ (first :: second :: third :: fourth :: rest) (Or.inr (by simp)) each

/-- All ordinary unary primitive forms are covered when their operands are. -/
theorem unaryBasicExpression_covered (op : Op) (args : List AstHOL.Exp) (unary : UnaryBasicOp op)
    (each : ∀ expr, expr ∈ args → LocalEnvBoundedArrayExpression expr) :
    LocalEnvBoundedArrayExpression (.app op args) := by
  cases args with
  | nil => exact .unaryBasicBadArity op [] unary (by simp) each
  | cons first rest =>
    have firstCovered := each first (by simp)
    cases rest with
    | cons second rest => exact .unaryBasicBadArity op (first :: second :: rest) unary (by simp) each
    | nil =>
      rcases unary with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact .ref_ first firstCovered
      · exact .deref first firstCovered
      · exact .byteArrayLength first firstCovered
      · exact .stringImplode first firstCovered
      · exact .stringExplode first firstCovered
      · exact .stringLength first firstCovered
      · exact .stringConcat first firstCovered
      · exact .vectorFromList first firstCovered
      · exact .vectorLength first firstCovered
      · exact .arrayLength first firstCovered

/-- All ordinary binary primitive forms are covered when their operands are. -/
theorem binaryBasicExpression_covered (op : Op) (args : List AstHOL.Exp) (binary : BinaryBasicOp op)
    (each : ∀ expr, expr ∈ args → LocalEnvBoundedArrayExpression expr) :
    LocalEnvBoundedArrayExpression (.app op args) := by
  cases args with
  | nil => exact .binaryBasicBadArity op [] binary (by simp) each
  | cons first rest =>
    have firstCovered := each first (by simp)
    cases rest with
    | nil => exact .binaryBasicBadArity op [first] binary (by simp) each
    | cons second rest =>
      have secondCovered := each second (by simp)
      cases rest with
      | cons third rest => exact .binaryBasicBadArity op (first :: second :: third :: rest) binary (by simp) each
      | nil =>
        rcases binary with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
        · exact .assign first second firstCovered secondCovered
        · exact .listAppend first second firstCovered secondCovered
        · exact .byteArrayAlloc first second firstCovered secondCovered
        · exact .byteSubscript first second firstCovered secondCovered
        · exact .byteSubscriptUnsafe first second firstCovered secondCovered
        · exact .byteXor first second firstCovered secondCovered
        · exact .stringSubscript first second firstCovered secondCovered
        · exact .vectorSubscript first second firstCovered secondCovered
        · exact .vectorSubscriptUnsafe first second firstCovered secondCovered
        · exact .arrayAlloc first second firstCovered secondCovered
        · exact .arraySubscript first second firstCovered secondCovered
        · exact .arraySubscriptUnsafe first second firstCovered secondCovered
        · exact .configGC first second firstCovered secondCovered

/-- All ordinary ternary primitive forms are covered when their operands are. -/
theorem ternaryBasicExpression_covered (op : Op) (args : List AstHOL.Exp) (ternary : TernaryBasicOp op)
    (each : ∀ expr, expr ∈ args → LocalEnvBoundedArrayExpression expr) :
    LocalEnvBoundedArrayExpression (.app op args) := by
  cases args with
  | nil => exact .ternaryBasicBadArity op [] ternary (by simp) each
  | cons first rest =>
    have firstCovered := each first (by simp)
    cases rest with
    | nil => exact .ternaryBasicBadArity op [first] ternary (by simp) each
    | cons second rest =>
      have secondCovered := each second (by simp)
      cases rest with
      | nil => exact .ternaryBasicBadArity op [first, second] ternary (by simp) each
      | cons third rest =>
        have thirdCovered := each third (by simp)
        cases rest with
        | cons fourth rest => exact .ternaryBasicBadArity op (first :: second :: third :: fourth :: rest) ternary (by simp) each
        | nil =>
          rcases ternary with rfl | rfl | rfl | rfl | rfl | rfl
          · exact .arrayUpdate first second third firstCovered secondCovered thirdCovered
          · exact .arrayUpdateUnsafe first second third firstCovered secondCovered thirdCovered
          · exact .byteUpdate first second third firstCovered secondCovered thirdCovered
          · exact .byteUpdateUnsafe first second third firstCovered secondCovered thirdCovered
          · exact .stringSlice first second third firstCovered secondCovered thirdCovered
          · exact .byteArraySlice first second third firstCovered secondCovered thirdCovered

/-- Both byte-copy primitives are covered for every operand count when each
operand is covered. -/
theorem fiveArgBasicExpression_covered (op : Op) (args : List AstHOL.Exp) (copy : FiveArgBasicOp op)
    (each : ∀ expr, expr ∈ args → LocalEnvBoundedArrayExpression expr) :
    LocalEnvBoundedArrayExpression (.app op args) := by
  by_cases arity : args.length = 5
  · cases args with
    | nil => simp at arity
    | cons first rest =>
      cases rest with
      | nil => simp at arity
      | cons second rest =>
        cases rest with
        | nil => simp at arity
        | cons third rest =>
          cases rest with
          | nil => simp at arity
          | cons fourth rest =>
            cases rest with
            | nil => simp at arity
            | cons fifth rest =>
              cases rest with
              | cons sixth rest => simp at arity
              | nil =>
                have firstCovered := each first (by simp)
                have secondCovered := each second (by simp)
                have thirdCovered := each third (by simp)
                have fourthCovered := each fourth (by simp)
                have fifthCovered := each fifth (by simp)
                rcases copy with rfl | rfl
                · exact .stringToBytes first second third fourth fifth firstCovered secondCovered thirdCovered fourthCovered fifthCovered
                · exact .copyBytes first second third fourth fifth firstCovered secondCovered thirdCovered fourthCovered fifthCovered
  · exact .fiveArgBasicBadArity op args copy arity each

/-- Foreign-call applications are covered for every operand count. -/
theorem ffiExpression_covered (name : Basis.Pure.MlString.MlString) (args : List AstHOL.Exp)
    (each : ∀ expr, expr ∈ args → LocalEnvBoundedArrayExpression expr) :
    LocalEnvBoundedArrayExpression (.app (.ffi name) args) := by
  cases args with
  | nil => exact .ffiBadArity name [] (by simp) each
  | cons first rest =>
    have firstCovered := each first (by simp)
    cases rest with
    | nil => exact .ffiBadArity name [first] (by simp) each
    | cons second rest =>
      have secondCovered := each second (by simp)
      cases rest with
      | nil => exact .ffi name first second firstCovered secondCovered
      | cons third rest => exact .ffiBadArity name (first :: second :: third :: rest) (by simp) each

/-- Thunk allocation is covered for every operand count. -/
theorem allocThunkExpression_covered (mode : ThunkMode) (args : List AstHOL.Exp)
    (each : ∀ expr, expr ∈ args → LocalEnvBoundedArrayExpression expr) :
    LocalEnvBoundedArrayExpression (.app (.thunkOp (.allocThunk mode)) args) := by
  cases args with
  | nil => exact .allocThunkBadArity mode [] (by simp) each
  | cons first rest =>
    have firstCovered := each first (by simp)
    cases rest with
    | nil => exact .allocThunk mode first firstCovered
    | cons second rest => exact .allocThunkBadArity mode (first :: second :: rest) (by simp) each

/-- Thunk update is covered for every operand count. -/
theorem updateThunkExpression_covered (mode : ThunkMode) (args : List AstHOL.Exp)
    (each : ∀ expr, expr ∈ args → LocalEnvBoundedArrayExpression expr) :
    LocalEnvBoundedArrayExpression (.app (.thunkOp (.updateThunk mode)) args) := by
  cases args with
  | nil => exact .updateThunkBadArity mode [] (by simp) each
  | cons first rest =>
    have firstCovered := each first (by simp)
    cases rest with
    | nil => exact .updateThunkBadArity mode [first] (by simp) each
    | cons second rest =>
      have secondCovered := each second (by simp)
      cases rest with
      | nil => exact .updateThunk mode first second firstCovered secondCovered
      | cons third rest => exact .updateThunkBadArity mode (first :: second :: third :: rest) (by simp) each

/-- Function applications are covered for every operand count. -/
theorem callExpression_covered (args : List AstHOL.Exp)
    (each : ∀ expr, expr ∈ args → LocalEnvBoundedArrayExpression expr) :
    LocalEnvBoundedArrayExpression (.app .opapp args) := by
  cases args with
  | nil => exact .callBadArity [] (by simp) each
  | cons first rest =>
    have firstCovered := each first (by simp)
    cases rest with
    | nil => exact .callBadArity [first] (by simp) each
    | cons second rest =>
      have secondCovered := each second (by simp)
      cases rest with
      | nil => exact .call first second firstCovered secondCovered
      | cons third rest => exact .callBadArity (first :: second :: third :: rest) (by simp) each

/-- Thunk forcing is covered for every operand count. -/
theorem forceThunkExpression_covered (args : List AstHOL.Exp)
    (each : ∀ expr, expr ∈ args → LocalEnvBoundedArrayExpression expr) :
    LocalEnvBoundedArrayExpression (.app (.thunkOp .forceThunk) args) := by
  cases args with
  | nil => exact .forceThunkBadArity [] (by simp) each
  | cons first rest =>
    have firstCovered := each first (by simp)
    cases rest with
    | nil => exact .forceThunk first firstCovered
    | cons second rest => exact .forceThunkBadArity (first :: second :: rest) (by simp) each

/-- Environment-ID applications are covered for every operand count. -/
theorem envIdExpression_covered (args : List AstHOL.Exp)
    (each : ∀ expr, expr ∈ args → LocalEnvBoundedArrayExpression expr) :
    LocalEnvBoundedArrayExpression (.app .envId args) := by
  cases args with
  | nil => exact .envIdBadArity [] (by simp) each
  | cons first rest =>
    have firstCovered := each first (by simp)
    cases rest with
    | nil => exact .envId first firstCovered
    | cons second rest => exact .envIdBadArity (first :: second :: rest) (by simp) each

/-- Empty-array allocation is covered for every operand count. -/
theorem arrayEmptyExpression_covered (args : List AstHOL.Exp)
    (each : ∀ expr, expr ∈ args → LocalEnvBoundedArrayExpression expr) :
    LocalEnvBoundedArrayExpression (.app .aallocEmpty args) := by
  cases args with
  | nil => exact .arrayEmptyBadArity [] (by simp) each
  | cons first rest =>
    have firstCovered := each first (by simp)
    cases rest with
    | nil => exact .arrayEmpty first firstCovered
    | cons second rest => exact .arrayEmptyBadArity (first :: second :: rest) (by simp) each

/-- Conversion applications are covered for every operand count. -/
theorem conversionExpression_covered (fromType toType : PrimType) (args : List AstHOL.Exp)
    (each : ∀ expr, expr ∈ args → LocalEnvBoundedArrayExpression expr) :
    LocalEnvBoundedArrayExpression (.app (.fromTo fromType toType) args) := by
  cases args with
  | nil => exact .conversionBadArity fromType toType [] (by simp) each
  | cons first rest =>
    have firstCovered := each first (by simp)
    cases rest with
    | nil => exact .conversion fromType toType first firstCovered
    | cons second rest => exact .conversionBadArity fromType toType (first :: second :: rest) (by simp) each

/-- Shift applications are covered for every operand count. -/
theorem shiftExpression_covered (size : WordSize) (shift : Shift) (amount : Nat) (args : List AstHOL.Exp)
    (each : ∀ expr, expr ∈ args → LocalEnvBoundedArrayExpression expr) :
    LocalEnvBoundedArrayExpression (.app (.shift size shift amount) args) := by
  cases args with
  | nil => exact .shiftBadArity size shift amount [] (by simp) each
  | cons first rest =>
    have firstCovered := each first (by simp)
    cases rest with
    | nil => cases size with
      | w8 => exact .word8Shift shift amount first firstCovered
      | w64 => exact .word64Shift shift amount first firstCovered
    | cons second rest => exact .shiftBadArity size shift amount (first :: second :: rest) (by simp) each

/-- Equality and primitive comparisons are covered for every operand count. -/
theorem comparisonExpression_covered (test : Option (Test × PrimType)) (args : List AstHOL.Exp)
    (each : ∀ expr, expr ∈ args → LocalEnvBoundedArrayExpression expr) :
    LocalEnvBoundedArrayExpression (.app (match test with | none => .equality | some (test, typ) => .test test typ) args) := by
  cases test with
  | none =>
    cases args with
    | nil => exact .equalityBadArity [] (by simp) each
    | cons first rest =>
      cases rest with
      | nil => exact .equalityBadArity [first] (by simp) each
      | cons second rest =>
        cases rest with
        | nil => exact .equality first second (each first (by simp)) (each second (by simp))
        | cons third rest => exact .equalityBadArity (first :: second :: third :: rest) (by simp) each
  | some pair =>
    obtain ⟨test, typ⟩ := pair
    cases args with
    | nil => exact .testBadArity test typ [] (by simp) each
    | cons first rest =>
      cases rest with
      | nil => exact .testBadArity test typ [first] (by simp) each
      | cons second rest =>
        cases rest with
        | nil => exact .test test typ first second (each first (by simp)) (each second (by simp))
        | cons third rest => exact .testBadArity test typ (first :: second :: third :: rest) (by simp) each

/-- Every source primitive application is covered when all of its operands
are covered. This is structural coverage, not the full correctness theorem. -/
theorem applicationExpression_covered (op : Op) (args : List AstHOL.Exp)
    (each : ∀ expr, expr ∈ args → LocalEnvBoundedArrayExpression expr) :
    LocalEnvBoundedArrayExpression (.app op args) := by
  cases op with
  | arith action typ => exact arithmeticExpression_covered action typ args each
  | fromTo fromType toType => exact conversionExpression_covered fromType toType args each
  | shift size shift amount => exact shiftExpression_covered size shift amount args each
  | equality => exact comparisonExpression_covered none args each
  | test test typ => exact comparisonExpression_covered (some (test, typ)) args each
  | opapp => exact callExpression_covered args each
  | eval => exact .eval args each
  | aallocEmpty => exact arrayEmptyExpression_covered args each
  | aallocFixed => exact .arrayFixed args each
  | envId => exact envIdExpression_covered args each
  | ffi name => exact ffiExpression_covered name args each
  | thunkOp op => cases op with
    | allocThunk mode => exact allocThunkExpression_covered mode args each
    | updateThunk mode => exact updateThunkExpression_covered mode args each
    | forceThunk => exact forceThunkExpression_covered args each
  | opref | opderef | aw8length | implode | explode | strlen | strcat | vfromList | vlength | alength =>
    apply unaryBasicExpression_covered _ args (by simp [UnaryBasicOp]) each
  | opassign | listAppend | aw8alloc | aw8sub | aw8subUnsafe | xorAw8StrUnsafe | strsub | vsub | vsubUnsafe | aalloc | asub | asubUnsafe | configGC =>
    apply binaryBasicExpression_covered _ args (by simp [BinaryBasicOp]) each
  | aupdate | aupdateUnsafe | aw8update | aw8updateUnsafe | copyStrStr | copyAw8Str =>
    apply ternaryBasicExpression_covered _ args (by simp [TernaryBasicOp]) each
  | copyStrAw8 | copyAw8Aw8 =>
    apply fiveArgBasicExpression_covered _ args (by simp [FiveArgBasicOp]) each

/-- Every source expression has a structural coverage derivation. The
simulation itself still depends on the preliminary factored relations. -/
theorem allExpressions_covered : (expr : AstHOL.Exp) → LocalEnvBoundedArrayExpression expr
  | .raise body => .raise_ body (allExpressions_covered body)
  | .handle body rows => .handle body rows (allExpressions_covered body)
      (fun pat row _member => allExpressions_covered row)
  | .lit lit => .base _ (.base _ (.base _ (.base _ (.literal lit))))
  | .con none args => .tuple args (fun expr _member => allExpressions_covered expr)
  | .con (some id) args => .constructor id args (fun expr _member => allExpressions_covered expr)
  | .var id => .base _ (.base _ (.base _ (.base _ (.variable_ id))))
  | .fn name body => .base _ (.base _ (.base _ (.base _ (.function_ name body))))
  | .app op args => applicationExpression_covered op args (fun expr _member => allExpressions_covered expr)
  | .log op left right => .log op left right (allExpressions_covered left) (allExpressions_covered right)
  | .if_ cond yes no => .if_ cond yes no (allExpressions_covered cond)
      (allExpressions_covered yes) (allExpressions_covered no)
  | .mat body rows => .mat body rows (allExpressions_covered body)
      (fun pat row _member => allExpressions_covered row)
  | .let_ none first body => .letAnonymous first body (allExpressions_covered first) (allExpressions_covered body)
  | .let_ (some name) first body => .letNamed name first body (allExpressions_covered first) (allExpressions_covered body)
  | .letrec funs body => .letrec funs body (allExpressions_covered body)
  | .tannot body typ => .tannot body typ (allExpressions_covered body)
  | .lannot body loc => .lannot body loc (allExpressions_covered body)
termination_by expr => sizeOf expr
decreasing_by
  all_goals simp_wf
  all_goals try omega
  all_goals have h := List.sizeOf_lt_of_mem _member
  all_goals try simp only [Prod.mk.sizeOf_spec] at h
  all_goals omega

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
  | unaryBasicBadArity op args unary badArity _ ih =>
    exact localEnvBounded_unaryBasic_badArity interp transform limit op args unary badArity ih
  | binaryBasicBadArity op args binary badArity _ ih =>
    exact localEnvBounded_binaryBasic_badArity interp transform limit op args binary badArity ih
  | ternaryBasicBadArity op args ternary badArity _ ih =>
    exact localEnvBounded_ternaryBasic_badArity interp transform limit op args ternary badArity ih
  | fiveArgBasicBadArity op args copy badArity _ ih =>
    exact localEnvBounded_fiveArgBasic_badArity interp transform limit op args copy badArity ih
  | eval args _ ih => exact localEnvBounded_eval interp transform limit decsIH args ih
  | call left right _ _ leftIH rightIH =>
    exact localEnvBounded_opapp interp transform limit calledIH left right leftIH rightIH
  | callBadArity args badArity _ ih => exact localEnvBounded_opapp_badArity interp transform limit args badArity ih
  | arrayEmpty body _ ih => exact localEnvBounded_aallocEmpty interp transform limit body ih
  | arrayEmptyBadArity args badArity _ ih =>
    exact localEnvBounded_aallocEmpty_badArity interp transform limit args badArity ih
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
  | ffiBadArity name args badArity _ ih =>
    exact localEnvBounded_ffi_badArity interp transform limit name args badArity ih
  | configGC left right _ _ leftIH rightIH =>
    exact localEnvBounded_configGC interp transform limit left right leftIH rightIH
  | forceThunk body _ ih => exact localEnvBounded_forceThunk interp transform limit calledIH body ih
  | forceThunkBadArity args badArity _ ih =>
    exact localEnvBounded_forceThunk_badArity interp transform limit args badArity ih
  | allocThunk mode body _ ih => exact localEnvBounded_allocThunk interp transform limit mode body ih
  | allocThunkBadArity mode args badArity _ ih =>
    exact localEnvBounded_allocThunk_badArity interp transform limit mode args badArity ih
  | updateThunk mode pointer value _ _ pointerIH valueIH =>
    exact localEnvBounded_updateThunk interp transform limit mode pointer value pointerIH valueIH
  | updateThunkBadArity mode args badArity _ ih =>
    exact localEnvBounded_updateThunk_badArity interp transform limit mode args badArity ih
  | byteXor array string _ _ arrayIH stringIH =>
    exact localEnvBounded_xorAw8StrUnsafe interp transform limit array string arrayIH stringIH
  | listAppend left right _ _ leftIH rightIH =>
    exact localEnvBounded_listAppend interp transform limit left right leftIH rightIH
  | envId body _ ih => exact localEnvBounded_envId interp transform limit body ih
  | envIdBadArity args badArity _ ih => exact localEnvBounded_envId_badArity interp transform limit args badArity ih
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
  | equalityBadArity args badArity _ ih =>
    exact localEnvBounded_comparison_badArity interp transform limit none args badArity ih
  | testBadArity test typ args badArity _ ih =>
    exact localEnvBounded_comparison_badArity interp transform limit (some (test, typ)) args badArity ih
  | booleanNot body _ ih => exact localEnvBounded_booleanNot interp transform limit body ih
  | floatFma first second third _ _ _ firstIH secondIH thirdIH =>
    exact localEnvBounded_floatFma interp transform limit first second third firstIH secondIH thirdIH
  | floatTernaryNonFma action args notFma arity _ ih =>
    exact localEnvBounded_floatTernary_nonFma interp transform limit action args notFma arity ih
  | floatBinary action left right _ _ leftIH rightIH =>
    exact localEnvBounded_floatBinary interp transform limit action left right leftIH rightIH
  | floatUnary action body _ ih => exact localEnvBounded_floatUnary interp transform limit body action ih
  | arithExtremeArity action typ args badArity _ ih =>
    exact localEnvBounded_arith_extremeArity interp transform limit action typ args badArity ih
  | intWordArithBadArity action size args badArity _ ih =>
    exact localEnvBounded_intWordArith_badArity interp transform limit action size args badArity ih
  | boolArithBadArity action args badArity _ ih =>
    exact localEnvBounded_boolArith_badArity interp transform limit action args badArity ih
  | arithRejectedType action typ args unsupported _ ih =>
    exact localEnvBounded_arith_rejectedType interp transform limit action typ args unsupported ih
  | integerArith action left right _ _ leftIH rightIH =>
    exact localEnvBounded_integerArith interp transform limit action left right leftIH rightIH
  | word8Arith action left right _ _ leftIH rightIH =>
    exact localEnvBounded_word8Arith interp transform limit action left right leftIH rightIH
  | word64Arith action left right _ _ leftIH rightIH =>
    exact localEnvBounded_word64Arith interp transform limit action left right leftIH rightIH
  | word8Shift shift amount body _ ih => exact localEnvBounded_word8Shift interp transform limit body shift amount ih
  | word64Shift shift amount body _ ih => exact localEnvBounded_word64Shift interp transform limit body shift amount ih
  | shiftBadArity size shift amount args badArity _ ih =>
    exact localEnvBounded_shift_badArity interp transform limit size shift amount args badArity ih
  | conversion fromType toType body _ ih =>
    exact localEnvBounded_conversion interp transform limit body fromType toType ih
  | conversionBadArity fromType toType args badArity _ ih =>
    exact localEnvBounded_conversion_badArity interp transform limit fromType toType args badArity ih
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
