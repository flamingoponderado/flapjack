load "preamble";
load "word_allocProofTheory";
open bossLib HolKernel Parse preamble word_allocProofTheory word_allocTheory sptreeTheory;
val _ = Globals.linewidth := 1000;
val lookup_force_rename_aux = prove (``∀ls ssa.
  lookup x (force_rename (REVERSE ls) ssa) =
  case ALOOKUP ls x of
    NONE => lookup x ssa
  | SOME y => SOME y``,
ho_match_mp_tac SNOC_INDUCT>>
  rw[REVERSE_SNOC]
  >- simp[force_rename_def]>>
  rename1`h::REVERSE _`>>
  Cases_on`h`>>
  rw[force_rename_def]>>
  every_case_tac>>gvs[]>>
  rw[lookup_insert]>>gvs[ALOOKUP_SNOC]);
val lookup_force_rename = prove (``lookup x (force_rename ls ssa) =
  case ALOOKUP (REVERSE ls) x of
    NONE => lookup x ssa
  | SOME y => SOME y``,
metis_tac[lookup_force_rename_aux,REVERSE_REVERSE]);
val domain_force_rename = prove (``domain (force_rename ls ssa) =
    domain ssa ∪ set (MAP FST ls)``,
rw[EXTENSION,domain_lookup]>>
  rw[lookup_force_rename,EQ_IMP_THM]>>
  gvs[AllCaseEqs(),MEM_MAP]>>
  metis_tac[ALOOKUP_EXISTS_IFF,FST,PAIR,MEM_REVERSE,option_CASES]);
fun out label th = (print(label ^ "="); print_thm th; print "\n");
val _ = out "fr_definition" force_rename_def;
val _ = out "fr_lookup_force_rename_aux" lookup_force_rename_aux;
val _ = out "fr_lookup_force_rename" lookup_force_rename;
val _ = out "fr_domain_force_rename" domain_force_rename;
fun ty label q = (print(label ^ "="); print_type(type_of q); print "\n");
val _ = ty "fr_type" ``force_rename``;
