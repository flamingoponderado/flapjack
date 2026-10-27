import Flapjack.AstHOL.Syntax
import Flapjack.FfiHOL

/-! CakeML source-semantics value and store carriers. Statement review is
pending; the source evaluator and compiler correctness theorem are not yet
ported by this module. -/
namespace Flapjack.SemanticPrimitivesHOL
open Flapjack.AstHOL Flapjack.NamespaceHOL Flapjack.Basis.Pure.MlString

/-- Unique identities for datatype and exception constructors. -/
@[hol "cakeml/semantics/semanticPrimitivesScript.sml" "stamp"]
inductive Stamp where
  | typeStamp : ConN → Nat → Stamp
  | exnStamp : Nat → Stamp
  deriving DecidableEq

/-- Lexical value and constructor environments. -/
@[hol "cakeml/semantics/semanticPrimitivesScript.sml" "sem_env"]
structure SemEnv (α : Type) where
  v : Namespace ModN VarN α
  c : Namespace ModN ConN (Nat × Stamp)

/-- CakeML source values, including lexical and recursive closures. -/
@[hol "cakeml/semantics/semanticPrimitivesScript.sml" "v"]
inductive Value where
  | litv : Lit → Value
  | conv : Option Stamp → List Value → Value
  | closure : SemEnv Value → VarN → AstHOL.Exp → Value
  | recclosure : SemEnv Value → List (VarN × VarN × AstHOL.Exp) → VarN → Value
  | loc : Bool → Nat → Value
  | vectorv : List Value → Value
  | env : SemEnv Value → (Nat × Nat) → Value

/-- Source-evaluation aborts, including final FFI events. -/
@[hol "cakeml/semantics/semanticPrimitivesScript.sml" "abort"]
inductive Abort where
  | typeError
  | timeoutError
  | ffiError : HolFinalEvent → Abort

@[hol "cakeml/semantics/semanticPrimitivesScript.sml" "error_result"]
inductive ErrorResult (α : Type) where
  | raise : α → ErrorResult α
  | abort : Abort → ErrorResult α

@[hol "cakeml/semantics/semanticPrimitivesScript.sml" "result"]
inductive Result (α β : Type) where
  | val : α → Result α β
  | err : ErrorResult β → Result α β

/-- Source store elements retain HOL's byte words and thunk mode. -/
@[hol "cakeml/semantics/semanticPrimitivesScript.sml" "store_v"]
inductive StoreValue (α : Type) where
  | refv : α → StoreValue α
  | w8array : List (BitVec 8) → StoreValue α
  | varray : List α → StoreValue α
  | thunk : ThunkMode → α → StoreValue α

@[hol "cakeml/semantics/semanticPrimitivesScript.sml" "store_v_same_type_def"]
def storeValueSameType {α : Type} : StoreValue α → StoreValue α → Bool
  | .refv _, .refv _ => true
  | .w8array _, .w8array _ => true
  | .varray _, .varray _ => true
  | .thunk .notEvaluated _, .thunk _ _ => true
  | _, _ => false

@[hol "cakeml/semantics/semanticPrimitivesScript.sml" "store"]
abbrev Store (α : Type) := List (StoreValue α)

@[hol "cakeml/semantics/semanticPrimitivesScript.sml" "empty_store_def"]
def emptyStore {α : Type} : Store α := []

@[hol "cakeml/semantics/semanticPrimitivesScript.sml" "store_lookup_def"]
def storeLookup {α : Type} (n : Nat) (store : Store α) : Option (StoreValue α) :=
  store[n]?

@[hol "cakeml/semantics/semanticPrimitivesScript.sml" "store_alloc_def"]
def storeAlloc {α : Type} (value : StoreValue α) (store : Store α) : Store α × Nat :=
  (store ++ [value], store.length)

@[hol "cakeml/semantics/semanticPrimitivesScript.sml" "store_assign_def"]
def storeAssign {α : Type} (n : Nat) (value : StoreValue α) (store : Store α) : Option (Store α) := do
  let old ← store[n]?
  if storeValueSameType old value then some (store.set n value) else none

@[hol "cakeml/semantics/semanticPrimitivesScript.sml" "compiler_args"]
abbrev CompilerArgs := (Nat × Nat) × Value × List AstHOL.Dec

@[hol "cakeml/semantics/semanticPrimitivesScript.sml" "compiler_fun"]
abbrev CompilerFun := CompilerArgs → Option (Value × List (BitVec 8) × List (BitVec 64))

@[hol "cakeml/semantics/semanticPrimitivesScript.sml" "eval_decs_state"]
structure EvalDecsState where
  compiler : CompilerFun
  compilerState : Value
  envIdCounter : Nat × Nat × Nat
  decodeDecs : Value → Option (List AstHOL.Dec)

@[hol "cakeml/semantics/semanticPrimitivesScript.sml" "eval_oracle_fun"]
abbrev EvalOracleFun := Nat → CompilerArgs

@[hol "cakeml/semantics/semanticPrimitivesScript.sml" "eval_oracle_state"]
structure EvalOracleState where
  oracle : EvalOracleFun
  customDoEval : List Value → EvalOracleFun → Option ((Nat × Nat) × EvalOracleFun × List AstHOL.Dec)
  envs : List (List (SemEnv Value))
  generation : Nat

@[hol "cakeml/semantics/semanticPrimitivesScript.sml" "eval_state"]
inductive EvalState where
  | evalDecs : EvalDecsState → EvalState
  | evalOracle : EvalOracleState → EvalState

/-- Source evaluator state, including its FFI and optional Eval machinery. -/
@[hol "cakeml/semantics/semanticPrimitivesScript.sml" "state"]
structure State (σ : Type) where
  clock : Nat
  refs : Store Value
  ffi : HolFfiState σ
  nextTypeStamp : Nat
  nextExnStamp : Nat
  evalState : Option EvalState

@[hol "cakeml/semantics/semanticPrimitivesScript.sml" "do_con_check_def"]
def doConCheck (env : Namespace ModN ConN (Nat × Stamp))
    (name : Option (Ident ModN ConN)) (arity : Nat) : Bool :=
  match name with
  | none => true
  | some name => match nsLookup env name with
    | none => false
    | some (expected, _) => arity == expected

@[hol "cakeml/semantics/semanticPrimitivesScript.sml" "one_con_check_def"]
def oneConCheck (env : Namespace ModN ConN (Nat × Stamp)) : AstHOL.Exp → Bool
  | .con name args => doConCheck env name args.length
  | _ => true

@[hol "cakeml/semantics/semanticPrimitivesScript.sml" "build_conv_def"]
def buildConv (env : Namespace ModN ConN (Nat × Stamp))
    (name : Option (Ident ModN ConN)) (values : List Value) : Option Value :=
  match name with
  | none => some (.conv none values)
  | some name => match nsLookup env name with
    | none => none
    | some (_, stamp) => some (.conv (some stamp) values)

@[hol "cakeml/semantics/semanticPrimitivesScript.sml" "lit_same_type_def"]
def litSameType : Lit → Lit → Bool
  | .intLit _, .intLit _ => true
  | .char _, .char _ => true
  | .strLit _, .strLit _ => true
  | .word8 _, .word8 _ => true
  | .word64 _, .word64 _ => true
  | .float64 _, .float64 _ => true
  | _, _ => false

@[hol "cakeml/semantics/semanticPrimitivesScript.sml" "match_result"]
inductive MatchResult (α : Type) where
  | noMatch
  | typeError
  | match : α → MatchResult α

@[hol "cakeml/semantics/semanticPrimitivesScript.sml" "same_type_def"]
def sameType : Stamp → Stamp → Bool
  | .typeStamp _ n, .typeStamp _ m => n == m
  | .exnStamp _, .exnStamp _ => true
  | _, _ => false

@[hol "cakeml/semantics/semanticPrimitivesScript.sml" "same_ctor_def"]
def sameCtor (a b : Stamp) : Bool := decide (a = b)

@[hol "cakeml/semantics/semanticPrimitivesScript.sml" "ctor_same_type_def"]
def ctorSameType : Option Stamp → Option Stamp → Bool
  | none, none => true
  | some a, some b => sameType a b
  | _, _ => false

@[hol "cakeml/semantics/semanticPrimitivesScript.sml" "bool_type_num_def"]
def boolTypeNum : Nat := 0

@[hol "cakeml/semantics/semanticPrimitivesScript.sml" "Boolv_def"]
def boolValue (b : Bool) : Value :=
  .conv (some (.typeStamp (ofString (if b then "True" else "False")) boolTypeNum)) []

@[hol "cakeml/semantics/semanticPrimitivesScript.sml" "find_recfun_def"]
def findRecFun {α β : Type} (name : VarN) : List (VarN × α × β) → Option (α × β)
  | [] => none
  | (f, x, body) :: rest => if f = name then some (x, body) else findRecFun name rest

@[hol "cakeml/semantics/semanticPrimitivesScript.sml" "build_rec_env_def"]
def buildRecEnv (funs : List (VarN × VarN × AstHOL.Exp)) (closureEnv : SemEnv Value)
    (env : Namespace ModN VarN Value) : Namespace ModN VarN Value :=
  funs.foldr (fun (name, _, _) rest => nsBind name (.recclosure closureEnv funs name) rest) env

@[hol "cakeml/semantics/semanticPrimitivesScript.sml" "bind_stamp_def"]
def bindStamp : Stamp := .exnStamp 0
@[hol "cakeml/semantics/semanticPrimitivesScript.sml" "chr_stamp_def"]
def chrStamp : Stamp := .exnStamp 1
@[hol "cakeml/semantics/semanticPrimitivesScript.sml" "div_stamp_def"]
def divStamp : Stamp := .exnStamp 2
@[hol "cakeml/semantics/semanticPrimitivesScript.sml" "subscript_stamp_def"]
def subscriptStamp : Stamp := .exnStamp 3

@[hol "cakeml/semantics/semanticPrimitivesScript.sml" "bind_exn_v_def"]
def bindExnV : Value := .conv (some bindStamp) []
@[hol "cakeml/semantics/semanticPrimitivesScript.sml" "chr_exn_v_def"]
def chrExnV : Value := .conv (some chrStamp) []
@[hol "cakeml/semantics/semanticPrimitivesScript.sml" "div_exn_v_def"]
def divExnV : Value := .conv (some divStamp) []
@[hol "cakeml/semantics/semanticPrimitivesScript.sml" "sub_exn_v_def"]
def subExnV : Value := .conv (some subscriptStamp) []

end Flapjack.SemanticPrimitivesHOL
