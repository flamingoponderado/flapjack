import Flapjack.Pancake.Proofs.LoopLive.CompileCorrect

/-! Direct parity for HOL `domain_list_delete`
(`cakeml/pancake/proofs/loop_liveProofScript.sml:561-562`) against the tagged
Lean port `sptDomain_sptListDelete` over the exact `Spt` carrier.  Each row
matches `scripts/hol-probes/loop_live_domain_list_delete_probe.out`, the HOL
`EVAL` of the same membership query on
`fromAList [(0,());(1,());(2,());(3,())]`. -/

namespace Flapjack.Test.LoopLiveDomainListDeleteParity

open Flapjack

private def tree : Spt Unit := sptFromAList [(0, ()), (1, ()), (2, ()), (3, ())]

/-- HOL `domain_list_delete` observations:
`1 IN domain (list_delete [3] t)` etc.  `sptMem k t` is
`sptDomain t k`, the reviewed rendering of `k IN domain t`, so each row is the
`sptLookup` membership of the deleted tree. -/
def domainListDeleteGuard : Bool :=
  -- dld_kept=T
  (sptLookup 1 (sptListDelete [3] tree)).isSome &&
  -- dld_deleted=F
  !(sptLookup 3 (sptListDelete [3] tree)).isSome &&
  -- dld_pair_kept=T
  (sptLookup 2 (sptListDelete [1, 3] tree)).isSome &&
  -- dld_pair_deleted=F
  !(sptLookup 1 (sptListDelete [1, 3] tree)).isSome &&
  -- dld_absent=F
  !(sptLookup 9 (sptListDelete [3] tree)).isSome

#guard domainListDeleteGuard

/-- The tagged port applies to the concrete probe tree. -/
example : sptMem 1 (sptListDelete [3] tree) ↔ sptMem 1 tree ∧ 1 ∉ [3] :=
  sptDomain_sptListDelete [3] tree 1

def runChecks : IO Bool := do
  if domainListDeleteGuard then
    IO.println "PASS loop_live domain_list_delete HOL parity"
  else
    IO.println "FAIL loop_live domain_list_delete HOL parity"
  pure domainListDeleteGuard

end Flapjack.Test.LoopLiveDomainListDeleteParity
