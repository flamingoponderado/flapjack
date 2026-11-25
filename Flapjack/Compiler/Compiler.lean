module

public import Flapjack.Compiler.Backend.Backend
public import Flapjack.Compiler.Inference.Infer
public import Flapjack.Basis.Pure.MlString.Ops
public import Flapjack.Basis.Pure.MlString.Prefix
public import Flapjack.HolRef

@[expose] public section

/-!
# `compilerScript.sml`

Declarations of the top-level CakeML compiler driver used by the Pancake route.
-/

namespace Flapjack.Compiler
open Flapjack.Basis.Pure.MlString Flapjack.Basis.Pure.MlString.MlString

/-- The original CakeML compiler configuration, including its inference
environment, backend, target assembler, and input/output mode flags. -/
@[hol "cakeml/compiler/compilerScript.sml" "config"
  (words_as_type_indexed_bitvec)]
structure CompilerConfig (width : Nat) [NeZero width] where
  inferencerConfig : Inference.Infer.Env
  backendConfig : Flapjack.Compiler.Backend.Backend.Config
  asmConfig : Flapjack.Compiler.Encoders.Asm.AsmConfigExact width
  inputIsSexp : Bool
  excludePrelude : Bool
  skipTypeInference : Bool
  onlyPrintTypes : Bool
  onlyPrintSexp : Bool

/-- HOL `pancake_backend_conf_def` (`compilerScript.sml:744-747`): the backend configuration
used to compile Pancake, which is the given one with the data configuration's `gc_kind`
set to `None`. -/
@[hol "cakeml/compiler/compilerScript.sml" "pancake_backend_conf_def"]
def pancakeBackendConf (c : Backend.Backend.Config) : Backend.Backend.Config :=
  { c with dataConf := { c.dataConf with gcKind := .none } }

/-! The self-contained `cakeml` command-line helpers: argument flag tests,
mlstring printing, and the parsing and line utilities used by the
configuration parsers. -/

/-- Original `has_version_flag_def`: the `--version` argument is present. -/
@[hol "cakeml/compiler/compilerScript.sml" "has_version_flag_def"]
def hasVersionFlag (ls : List MlString) : Bool := ls.elem (ofString "--version")

/-- Original `has_help_flag_def`. -/
@[hol "cakeml/compiler/compilerScript.sml" "has_help_flag_def"]
def hasHelpFlag (ls : List MlString) : Bool := ls.elem (ofString "--help")

/-- Original `has_pancake_flag_def`. -/
@[hol "cakeml/compiler/compilerScript.sml" "has_pancake_flag_def"]
def hasPancakeFlag (ls : List MlString) : Bool := ls.elem (ofString "--pancake")

/-- Original `print_bool_def`. -/
@[hol "cakeml/compiler/compilerScript.sml" "print_bool_def"]
def printBool (b : Bool) : MlString := if b then ofString "true" else ofString "false"

/-- Original `print_option_def`: print an optional string with its prefix and
    a trailing newline. -/
@[hol "cakeml/compiler/compilerScript.sml" "print_option_def"]
def printOption (h : MlString) : Option MlString → MlString
  | none => ofString ""
  | some y => strcat (strcat (strcat h (ofString " ")) y) (ofString "\n")

/-- Original `is_error_msg_def`: messages beginning with `###`. -/
@[hol "cakeml/compiler/compilerScript.sml" "is_error_msg_def"]
noncomputable def isErrorMessage (x : MlString) : Bool := isPrefix (ofString "###") x

/-- Original `parse_bool_def`. -/
@[hol "cakeml/compiler/compilerScript.sml" "parse_bool_def"]
def parseBool (str : MlString) : Option Bool :=
  if str = ofString "true" then some true
  else if str = ofString "false" then some false
  else none

/-- Original `safe_substring_def`: a substring clipped to the string length. -/
@[hol "cakeml/compiler/compilerScript.sml" "safe_substring_def"]
def safeSubstring (s : MlString) (n l : Nat) : MlString :=
  let k := strlen s
  if k ≤ n then ofString ""
  else if n + l ≤ k then substring s n l
  else substring s n (k - n)

/-- Original `get_err_str_def`: the error text of a parse result, empty on
    success. -/
@[hol "cakeml/compiler/compilerScript.sml" "get_err_str_def"]
def getErrStr {α : Type} : α ⊕ MlString → MlString
  | .inl _ => ofString ""
  | .inr n => MlString.concat [n, ofString "\n"]

/-- Original `find_str_def`: the first argument carrying `flag` as a prefix,
    with that prefix removed. -/
@[hol "cakeml/compiler/compilerScript.sml" "find_str_def"]
noncomputable def findStr (flag : MlString) : List MlString → Option MlString
  | [] => none
  | x :: xs =>
    if isPrefix flag x then some (extract x (strlen flag) none) else findStr flag xs

/-- Original `find_strs_def`: every argument carrying `flag` as a prefix, with
    that prefix removed. -/
@[hol "cakeml/compiler/compilerScript.sml" "find_strs_def"]
noncomputable def findStrs (flag : MlString) : List MlString → List MlString
  | [] => []
  | x :: xs =>
    if isPrefix flag x then extract x (strlen flag) none :: findStrs flag xs
    else findStrs flag xs

/-- Original `comma_tokens_def`: split a comma-separated string into its
    (possibly empty) fields. -/
@[hol "cakeml/compiler/compilerScript.sml" "comma_tokens_def"]
def commaTokens : List MlString → List HolChar → List HolChar → List MlString
  | acc, xs, [] => if xs = [] then acc else acc ++ [MlString.implode xs]
  | acc, xs, c :: cs =>
    if c = (44 : HolChar) then
      commaTokens (acc ++ (if xs = [] then [] else [MlString.implode xs])) [] cs
    else commaTokens acc (xs ++ [c]) cs

/-- Original `find_bool_def`: read the boolean after `flag`, defaulting when the
    flag is absent. -/
@[hol "cakeml/compiler/compilerScript.sml" "find_bool_def"]
noncomputable def findBool (flag : MlString) (ls : List MlString) (default : Bool) :
    Bool ⊕ MlString :=
  match findStr flag ls with
  | none => .inl default
  | some rest =>
    match parseBool rest with
    | none =>
      .inr (MlString.concat [ofString "Unable to parse as bool: ", rest,
        ofString " for flag: ", flag])
    | some b => .inl b

/-- Original `find_next_newline_def`: the first newline position at or after
    `n`, or `n` once the string ends. -/
@[hol "cakeml/compiler/compilerScript.sml" "find_next_newline_def"]
noncomputable def findNextNewline (n : Nat) (s : MlString) : Nat :=
  if strlen s ≤ n then n
  else if strsub s n = (10 : HolChar) then n
  else findNextNewline (n + 1) s
termination_by strlen s - n

/-- Original `get_nth_line_def`: the `k`-th line of the string, starting at
    position `n`. -/
@[hol "cakeml/compiler/compilerScript.sml" "get_nth_line_def"]
noncomputable def getNthLine (k : Nat) (s : MlString) (n : Nat) : MlString :=
  if k = 0 then safeSubstring s n (findNextNewline n s - n)
  else getNthLine (k - 1) s (findNextNewline n s + 1)
termination_by k

end Flapjack.Compiler
