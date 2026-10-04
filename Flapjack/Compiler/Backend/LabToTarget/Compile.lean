import Flapjack.Compiler.Backend.LabFilter
import Flapjack.Compiler.Backend.LabToTarget.RemoveLabels
import Flapjack.Compiler.Backend.LabToTarget.ShmemInfo
import Flapjack.Compiler.Encoders.Asm
import Flapjack.FfiHOL
import Flapjack.Misc.ListSubset
import Flapjack.Misc.Sptree
import Flapjack.Basis.Pure.MlString
import Flapjack.HolRef

/-!
# Faithful Cake `compile_lab`/`compile` (`lab_to_targetScript.sml`)

Exact definitions from `cakeml/compiler/backend/lab_to_targetScript.sml:358-478`.
The `config` record holds the label map, section positions/lengths, byte
position, initial clock, FFI name list, extra shared-memory records and hash
size. `compile_lab` collects the program's current FFI names, checks the
supplied `ffi_names` against them with `list_subset`, runs `remove_labels`,
converts the result to bytes with `prog_to_bytes`, gathers shared-memory records
with `get_shmem_info`, and finally updates the config. `compile` filters skip
instructions with `filter_skip` and delegates to `compile_lab`.

Only the linked `Line`/`Section` carrier's position field is a type-indexed HOL
`'a word`; `compile_lab`/`compile` translate it to the positive-width
`BitVec width` (`words_as_type_indexed_bitvec`). The `config` datatype itself
carries no type-indexed word (its `shmem_info_num` byte sizes are the fixed HOL
`word8`), so it is an unqualified `reviewed_exact` port. HOL `LENGTH` is
`.length`, HOL `#` is `×`, and the record update `c with <| ... |>` is Lean
`{ c with ... }`.
-/

namespace Flapjack.Compiler.Backend.LabToTarget

open Flapjack.Compiler.Backend.LabLang
open Flapjack.Compiler.Backend.LabFilter
open Flapjack.Compiler.Encoders.Asm
open Flapjack.Basis.Pure.MlString
open Flapjack.Misc
open Flapjack

/-- Exact HOL `lab_to_target$config` (`lab_to_targetScript.sml:358-368`): the
record `<| labels : num num_map num_map; sec_pos_len : (num # num # num) list;
pos : num; init_clock : num; ffi_names : ffiname list option;
shmem_extra : shmem_info_num list; hash_size : num |>`. Field order matches
HOL; `num_map` is the reviewed `Spt`, `#` is `×`, and the FFI-name list is the
exact `HolFfiName`. No field carries HOL's type-indexed `'a word` (`nbytes` is
the fixed `word8` inside `ShmemInfoNum`), so this is reviewed_exact. -/
@[hol "cakeml/compiler/backend/lab_to_targetScript.sml" "config"]
structure Config where
  labels : Spt (Spt Nat)
  secPosLen : List (Nat × Nat × Nat)
  pos : Nat
  initClock : Nat
  ffiNames : Option (List HolFfiName)
  shmemExtra : List ShmemInfoNum
  hashSize : Nat
  deriving DecidableEq, Repr

/-- Exact HOL `lab_to_target$compile_lab_def`
(`lab_to_targetScript.sml:430/453`): `current_ffis = find_ffi_names sec_list`;
`(ffis, ffis_ok)` is `(ffis, list_subset current_ffis ffis)` when
`c.ffi_names = SOME ffis` and `(current_ffis, T)` otherwise; when `ffis_ok`,
`remove_labels c.init_clock asm_conf c.pos c.labels ffis sec_list` returning
`SOME (sec_list, l1)` yields `bytes = prog_to_bytes sec_list`,
`(new_ffis, shmem_infos) = get_shmem_info sec_list c.pos [] []` and
`SOME (bytes, c with <| labels := l1; pos := LENGTH bytes + c.pos;
sec_pos_len := get_symbols c.pos sec_list; ffi_names := SOME (ffis ++ new_ffis);
shmem_extra := shmem_infos |>)`; otherwise `NONE`. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
def compileLab {width : Nat} [NeZero width] (asmConf : AsmConfigExact width)
    (c : Config)
    (secList : List (Section (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width)))) :
    Option (List (BitVec 8) × Config) :=
  let currentFfis := findFfiNames secList
  let (ffis, ffisOk) :=
    match c.ffiNames with
    | some ffis => (ffis, listSubset currentFfis ffis)
    | none => (currentFfis, true)
  if ffisOk then
    match removeLabels c.initClock asmConf c.pos c.labels ffis secList with
    | some (secList, l1) =>
        let bytes := progToBytes secList
        let (newFfis, shmemInfos) := getShmemInfo secList c.pos [] []
        some (bytes, { c with
          labels := l1
          pos := bytes.length + c.pos
          secPosLen := getSymbols c.pos secList
          ffiNames := some (ffis ++ newFfis)
          shmemExtra := shmemInfos })
    | none => none
  else none

/-- Exact HOL `lab_to_target$compile_def` (`lab_to_targetScript.sml:478`):
`compile asm_conf c sec_list = compile_lab asm_conf c (filter_skip sec_list)`. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
def compile {width : Nat} [NeZero width] (asmConf : AsmConfigExact width)
    (c : Config)
    (secList : List (Section (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width)))) :
    Option (List (BitVec 8) × Config) :=
  compileLab asmConf c (filterSkip secList)

end Flapjack.Compiler.Backend.LabToTarget
