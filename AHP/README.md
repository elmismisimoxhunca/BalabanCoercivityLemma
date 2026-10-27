# Supplemental results and experiments

This directory contains statement-fidelity proofs, alternative formulations, numerical experiments, and mathematical blueprints. The results included in the main build are packaged separately under [`lean/src/AHP/`](../lean/src/AHP/).

**The root reproduction command does not check this directory wholesale.** It contains exploratory and incomplete files as well as proved results. The individual reports distinguish compiled results, independently replayed proofs, conditional implications, numerical evidence, and open premises.

## Guide

| Topic | Material |
|---|---|
| Initial statement-fidelity comparisons | [`fidelity/`](fidelity/) |
| Unguarded touching formulation | [`round11/refute-r2/Attempt.lean`](round11/refute-r2/Attempt.lean); compiled counterpart in [`S1TouchingSqrt5.lean`](../lean/src/AHP/S1TouchingSqrt5.lean) |
| Guarded-path intermediate results | [`round13/BLUEPRINT.md`](round13/BLUEPRINT.md) |
| Conditional area-seed reductions | [`round14/BLUEPRINT.md`](round14/BLUEPRINT.md) |
| Cumulative blueprint and remaining mathematical gaps | [`round15/BLUEPRINT.md`](round15/BLUEPRINT.md), [LaTeX](round15/blueprint/content.tex), and [`GAPS.md`](round15/shared/GAPS.md) |
| Source and axiom evidence for the latest intermediate results | [`round15/audit/`](round15/audit/) |

## The remaining all-plaquette question

The full-guard all-plaquette theorem is proved in the main development. The **first-inverse-only** formulation remains formally open and is **numerically strongly disfavoured / conjectured false**.

The unresolved ingredients are identification of the model matrices with the physical operators, a nonzero area on the same kernel generator, and the required cofinal control. Conditional implications and explicit matrix calculations do not supply those premises.

The numerical archive includes \(q=1,2,4\) with even \(R=18,\ldots,40\), and a held-out \(q=1,R=42\) check. The unsuccessful \(q=2,R=42\) computation is not counted as supporting evidence. These calculations are not formal or interval-certified counterexamples.

## Using the archive

Check each file’s verification status before relying on it. In particular, an isolated successful axiom print does not certify a whole file; the audit identifies files whose retained logs are incomplete or stale. Some experimental scripts need path and dependency adjustments to run on another machine.

Pickle/NPZ files are numerical caches, not proof certificates. Inspect or regenerate pickle data before loading it: unpickling can execute code. These files are not needed for the main Lean build.
