# Public snapshot: scope and provenance

## Purpose

This snapshot publishes a formal reconstruction of Balaban’s multiscale coercivity theorem, its supporting constructions, and an explicit source-fidelity investigation. It also preserves the later exploratory work with its actual verification status. It is not a claim to have constructed continuum Yang–Mills theory or proved a mass gap.

The public history starts with a clean snapshot. The former private history and working files were backed up before preparation. This avoids redistributing the third-party source corpus through old commits. A private commit date is not asserted to establish public priority.

## Accepted core

Base: private integration commit `f6199f6ff72b0910d263ddf798d73899e90107e9`.

- **2,782 registered Lean modules.**
- **572 main checked axiom records and one separate historical R7 record.**
- All 2,807 tracked files under `lean/`—including sources, manifests, Checks, and Lake configuration—are byte-identical to that accepted snapshot.
- The additional 20 fidelity modules live in [`lean/src/AHP/`](lean/src/AHP/); they are registered in the default build, not merely placed in the exploratory archive.
- The main result is `AdalyFormal.Total.p428Target8Total`; the earlier headline is `AdalyFormal.M2RightInv.p428Target8`.

The additional fidelity results include the exact unguarded touching-variant refutation for every \(\ell\geq2\), \(0<a\leq4\sqrt5\); class-inclusion and non-vacuity comparisons; raw/normalized form comparisons; and six testable statement-sheet variants. Their encoded statements and qualifications matter. The touching refutation uses singular carriers and totalised inverses; it is not an all-inverses-exist counterexample or a declaration that Balaban’s historical theorem is false.

During release preparation, remote commits through `b011e7e7f796ee56d33953a1847e49d83f1412e5` removed the four `paper/` files without changing Lean sources. This snapshot respects those deletions: it does not restore the draft, its PDF, or the paper ledgers. The statement sheet and historical handoff were not rewritten into a final journal submission, and some references still point to the unpublished paper. Read the most recent relevant report and the actual Lean declaration, rather than treating an old status sentence as current.

## Verification changes made for publication

No Lean theorem, definition, proof, or import was changed for this release.

The reproduction script now checks **complete** `#print axioms` messages using [`tools/check_axioms.py`](tools/check_axioms.py). The old extraction retained only each message’s first line, potentially missing a forbidden axiom on a continuation line. Regression tests exercise the actual shell gate with controlled compiler-output fixtures: wrapped `sorryAx`, other unexpected axioms, truncated records, complete allowed records, and axiom-free records. Additional parser tests cover malformed lists and names containing apostrophes.

The retained 573 complete records were checked against the accepted historical first-line expectations and the allowed axiom set. Exactly five main expected lines needed expansion to include their complete wrapped lists. The policy remains a subset of `{propext, Classical.choice, Quot.sound}`; it was not relaxed.

The release reproduction used copy-on-write copies of the previously accepted project and mathlib caches, then ran the full root reproduction command and all numbered axiom checks. It finished on **2026-10-27 at 05:49:36 UTC with `ALL CHECKS PASSED`**. The ten validator tests passed, and the round-15 documentation recheck passed at 05:53:39 UTC. **This is a cache-assisted replay, not an independent cold rebuild or an end-to-end network-install test.** See [`verification/README.md`](verification/README.md) for the complete raw axiom records, run summary, and evidence limits.

## Research archive

[`AHP/README.md`](AHP/README.md) indexes the later sources, reviews, numerical data, and blueprints. Failed attempts and unproved premises are preserved, not concealed. They are not all covered by the root reproduction command.

Round 15 produced no P3, CofinalP3, physical area seed, or `GoalNeg2` closure. Its first-inverse-only all-plaquette target is numerically strongly disfavoured / conjectured false, not formally refuted. The full-guard variant is already proved in the core. No new mathematical proof search was undertaken for publication.

Historical workflow definitions are in [`research/workflows/`](research/workflows/). Private agent conversations, runtime credentials and dependencies are not part of the release. Host-specific paths in retained scientific sources and logs are historical provenance and may need adaptation to rerun an experiment; they are not external build dependencies of the checked core.

## Exclusions and preservation

The public export excludes the private `sources/` corpus (120 entries at the integration base), 40 copied page images under `AHP/`, eight Python bytecode files, three transient lock files, and one partial output. The original research data and omitted transient output remain in the verified private backup. Reference hashes and citation metadata are retained under [`references/`](references/README.md), without the source reproductions.

Pre-existing Compact-related work in the original working tree belongs to a separate effort. It was preserved privately, left untouched, and not silently included in this accepted-core release.

The public repository’s license does not grant rights to excluded third-party publications.
