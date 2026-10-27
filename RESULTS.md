# Results and scope

## Coercivity and its supporting constructions

| Result | Lean entry point |
|---|---|
| Uniform coercivity and existence of the required inverses, with constants chosen before the cube factor, scales, and depth | [`AdalyFormal.Total.p428Target8Total`](lean/src/TT_F.lean) |
| The original formal headline | [`AdalyFormal.M2RightInv.p428Target8`](lean/src/RI6.lean) |
| Exact configuration-level hypotheses and conclusion | `CoercG8AtWD`, `InstAtWD`, and `InstIneq` in [`ZT5A.lean`](lean/src/ZT5A.lean) |
| Local gauge/chart construction | [`TT_Z.lean`](lean/src/TT_Z.lean) |
| Covariant right inverse with weighted norm and gradient bounds | [`AdalyFormal.M2RightInv.classRightInvCov`](lean/src/RI5.lean); specification in [`OL15.lean`](lean/src/OL15.lean) |
| Joint non-vacuity with curvature and a nonzero admissible field | [`AdalyFormal.NonVacC.headline_regime_nonvacuousC`](lean/src/NVC7.lean) |

The setting is dimension 3 and SU(2), with compatible periodic geometry, admissible towers and collars, local gauge regularity, and explicit coverage. The non-vacuity construction has depth two; it is not a richness theorem at every depth. The coercivity theorem itself ranges over arbitrary admissible depth. Its constants are existential, not claimed to be numerically sharp.

## Statement fidelity

These results distinguish mathematical consequences of a chosen encoding from questions about the intended reading of the original text.

### Coverage

The encoded statement without coverage is false even when inverse existence is granted, for every block factor \(\ell\geq2\), cube factor \(c\geq10\), and \(a>0\). Keeping both coverage clauses gives a consequence of the main theorem.

At \(\ell=2\), the explicit depth-two witness satisfies site coverage while violating common-plaquette coverage. Thus dropping only the latter also fails in that formal class. This does not assert that Balaban’s printed hypotheses are insufficient under every interpretation.

Entry points: [`NuA3.lean`](lean/src/NuA3.lean), [`CaT2d.lean`](lean/src/CaT2d.lean), and [`CaT1.lean`](lean/src/CaT1.lean).

### Touching conventions and class inclusion

The exact unguarded four-bond touching formulation is refuted for every \(\ell\geq2\) and \(0<a\leq4\sqrt5\): [`Round11.RefuteR2.window_sqrt5_closed_proved`](lean/src/AHP/S1TouchingSqrt5.lean).

This refutation uses singular carriers and totalised inverses. It is **not** an example in which all printed inverses exist.

Class-inclusion comparisons and proper-domain witnesses are in [`ClassInclusion.lean`](lean/src/AHP/ClassInclusion.lean), [`S2Nonvacuity.lean`](lean/src/AHP/S2Nonvacuity.lean), and [`S2OddNonvacuity.lean`](lean/src/AHP/S2OddNonvacuity.lean). The four-bond witnesses cover every \(\ell\geq2\); their flatness and the separate corner-domain obstruction must not be conflated with the curved non-vacuity result above.

### Normalization and other variants

[`S3FullComparison.lean`](lean/src/AHP/S3FullComparison.lean) proves the raw/normalized full-form comparisons with scalar 1 and unchanged \(a\), under the stated inverse guards and linked conventions. This settles those formal comparisons, not every interpretive question about the source’s gauges and parametrization.

Further compiled variants concern non-strict collars, alternative coordinate readings, scale conventions, a global gauge assumption, Hilbert–Schmidt normalization, and quantifier order. Their statements are in [`lean/src/AHP/`](lean/src/AHP/).

### All-plaquette formulations

- **Proved:** the full-guard formulation, [`SolR345Audit.full_guard_literal`](lean/src/SolR345Audit.lean).
- **Formally open:** the weaker formulation guarded only by existence of the first inverse. Numerical experiments strongly disfavor it, but no formal counterexample is claimed.

The outstanding step is a physical operator/area identification and nonzero-area argument, not the finite-matrix calculations alone. See the [supplemental results](AHP/README.md). This auxiliary question is separate from the proved coercivity theorem.

## Reading the evidence

The [statement sheet](notes/statement_sheet.pdf) compares the formalization with the source clause by clause. Some entries predate the results above. The [verification records](verification/README.md) establish the checked theorem dependencies; they do not, by themselves, decide historical interpretation.
