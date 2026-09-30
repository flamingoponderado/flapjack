Pinned HOL4 source snapshots for declaration references.

SOURCES.json records the upstream repository, commit and SHA-256 of each
unmodified source/license file. The reference checker permits only the reviewed
snapshots (`src/finite_maps/sptreeScript.sml`,
`examples/pl-semantics/lprefix_lub/lprefix_lubScript.sml`,
`src/n-bit/fcpScript.sml`, `src/coalgebras/llistScript.sml`, and
`src/coretypes/optionScript.sml`) and verifies the
bytes of each source plus the shared COPYRIGHT before accepting a tag. These
files are reference inputs; they are not a build of HOL or evidence of
cross-assistant equivalence. Update the snapshot, license and lock together
after source review. Retain the upstream copyright notice and redistribution
conditions in COPYRIGHT.

The fcp snapshot supplies the original `dimindex_def` finite/cardinality and
infinite/one clauses for reviewing bare word-index translations. Its presence
does not approve any Lean carrier or qualifier; those need separate review.

The llist snapshot supplies original lazy-list representation and prefix-order
declarations for individual source reviews. Pinning it does not establish Lean
carrier equivalence or approve tags on the surrounding lazy-list library.
