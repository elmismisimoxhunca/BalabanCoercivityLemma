# Research supplement: statement fidelity and alternative readings

This archive accompanies the [checked core](../README.md). It preserves useful proofs, failed attempts, numerical experiments, review reports, and the final research state rather than presenting only successful runs.

**Do not run a recursive Lean build over this directory and expect every file to pass.** Experimental files, unresolved premises, negative controls, and failed joins are intentional parts of the record. Only modules registered under `lean/` are included in the root `REPRODUCE.sh` contract.

## Where to start

| Material | Purpose |
|---|---|
| [`fidelity/`](fidelity/) | Initial design, numerical tests, frozen statements, and verified variants of the statement-fidelity questions. |
| [`round11/refute-r2/Attempt.lean`](round11/refute-r2/Attempt.lean) | Accepted exact unguarded touching-variant refutation for every block factor, in its stated parameter window. A packaged copy is in `lean/src/AHP/S1TouchingSqrt5.lean`. |
| [`round13/BLUEPRINT.md`](round13/BLUEPRINT.md) | Independently checked intermediate guarded-path results and their remaining joins. |
| [`round14/BLUEPRINT.md`](round14/BLUEPRINT.md) | Conditional area-seed reductions and their evidence levels. |
| [`round15/BLUEPRINT.md`](round15/BLUEPRINT.md) | Final cumulative Markdown blueprint, including the timeout closeout. |
| [`round15/blueprint/content.tex`](round15/blueprint/content.tex) | Corresponding leanblueprint-style LaTeX content; not a claim of a freshly built blueprint website. |
| [`round15/audit/README.md`](round15/audit/README.md) | Final evidence audit: accepted builder records, rejected late files, numerical scope, and open physical identifications. |
| [`round15/shared/GAPS.md`](round15/shared/GAPS.md) | The remaining mathematical gaps and the paused research disposition. |

The workflow definitions are preserved separately in [`research/workflows/`](../research/workflows/). They are historical process specifications, not automatically installed or running agents.

## Evidence levels

The blueprints distinguish independently verified results, builder-only whole-file compilation, conditional implications, numerics, open premises, and unverified declarations. These labels are not interchangeable.

In particular, the round-15 supplement introduces **119 nodes: 101 builder-evidence nodes, 8 open nodes, 5 numerical nodes, 4 conditional nodes, and 1 unverified node; no new independently replayed nodes**. The 101 builder-evidence nodes comprise 62 theorems and 39 definitions. This is a catalogue of retained evidence, not 101 new independently verified mathematical conclusions.

A zero exit marker alone is not sufficient evidence. The round-15 audit explicitly rejects a stale success marker attached to a newer failing `Stencil.lean`, as well as other files without acceptable whole-file evidence. Those attempts remain in the archive so the rejection can be inspected.

## Current mathematical disposition

- The main multiscale coercivity theorem is proved in the checked core.
- The **full-guard all-plaquette theorem** is also proved there.
- The **first-inverse-only all-plaquette formulation** is formally open and numerically strongly disfavoured / conjectured false. No formal refutation or probability estimate is claimed.
- The physical operator-to-matrix identification, same-generator nonzero area seed, P3, CofinalP3, and `GoalNeg2` have not been closed. Explicit matrix algebra does not supply these identifications by itself.
- Round 15 ended at a 24-hour workflow timeout. Its later documentation-only closeout succeeded; that did not turn the research timeout into a proof success.
- Held-out q=1, R=42 numerical runs succeeded. The q=2, R=42 attempt timed out and is excluded from the successful numerical evidence.

The open auxiliary counterexample is not a prerequisite for the existing main theorem.

## Reproduction and historical paths

This is a research archive, not a second turnkey Lake project. Some scripts retain the original absolute workspace paths and dependencies, and some provenance reports refer to private workflow records not distributed here. Consult individual scripts before running them; do not assume the root reproduction command certifies this archive.

Retained `.log`, `.exit`, and JSON files are evidence with the qualifications above. Pickle/NPZ files are numerical caches, not proof certificates; Python pickle loading can execute code, so inspect or regenerate those caches rather than loading an untrusted copy. None is needed by the core Lean build.

Third-party page images have been excluded from the public snapshot. Their omission is recorded in [`RELEASE.md`](../RELEASE.md) and the reference metadata. Original proof sources and retained compile evidence are preserved byte-for-byte; publication of an attempt does not promote its verification status.
