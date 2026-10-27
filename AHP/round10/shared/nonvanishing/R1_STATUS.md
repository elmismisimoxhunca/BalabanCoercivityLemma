# Nonvanishing track — round 1 final hand-off

**GoalNeg2 remains OPEN.** A new finite-source estimate is compiled (standard axioms), not merely a restatement of nonvanishing. Three files are published here with their own wrapper logs and exit 0 records:

- `R1_SourceDominance.lean` — uniform finite-source domination;
- `R1_RecurrenceNonvanishing.lean` — reversible scalar recurrences and nested dyadic/even-radius cofinality;
- `R1_TransferNonvanishing.lean` — invertible finite-dimensional transfer systems, nonzero denominators, arithmetic progressions.

These are byte-identical to the originals under `AHP/round10/nonvanishing/r1/`, independently recompiled in the hand-off directory. Audit: 27 distinct declarations, 6 successful compilations, no warnings, only the three standard axioms (`nonvanishing/r1/CHECKS.json`).

Namespace: `AdalyFormal.Round10.Nonvanishing`. Sole import: frozen `D1IVT` (Mathlib only). No round-9 prefix needed.

## Useful sign/dominance criterion

Use N=n+1 blocks. Zero-pad a_{-1}=a_N=0. Suppose the **exact neutral source equations** are

\[
6a_j+a_{j-1}+a_{j+1}=\tfrac32\mathbf1_{j=0},\qquad 0\le j<N.
\]

These are the source equations documented by `round6/probe/leading_source.py`; their identification with the frozen H/J operators remains the dictionary obligation.

Set h_j=1_{j=0}-2a_{j-1}+2a_{j+1}, and v_j=C2_j(W0 u). The new theorem proves, uniformly in N:

\[
\left|\sum_{j<N}h_jv_j-v_0\right|\le\frac{15}{19}|v_0|
\]

whenever |v_j|≤|v_0| for every j<N. Its absolute value is at least (4/19)|v_0|. Consequently if v_0≠0, the entire coupling is nonzero **and has the sign of v_0**. No explicit square roots, transfer eigenvalues, alternating-sign theorem, limiting argument, or asymptotic error estimate is used.

The requested interface is `BlockSourceData coupling`:

```lean
∃ (n : ℕ) (a v : ℕ → ℝ) (factor : ℝ),
  a (n + 1) = 0 ∧
  (∀ j < n + 1,
    6 * a j + left a j + a (j + 1) = if j = 0 then (3 / 2 : ℝ) else 0) ∧
  (∀ j < n + 1, |v j| ≤ |v 0|) ∧ v 0 ≠ 0 ∧
  factor ≠ 0 ∧ coupling = factor * sourcePairing n a v
```

`coupling_ne_zero_of_blockSourceData` consumes it. The usual factor is 2, plus any nonzero physical normalization.

**Not proved:** the exact operator/block identification, the jet inequality, or v_0≠0 for the actual crossing vector. Thus this is a sufficient criterion, NOT an unconditional coupling proof. Full-kernel identification is also still needed by assembly.

Evidence only: all 36 stored jets in each of the three R9 left-twist R=8 examples satisfy the proposed inequality. The largest |v_j/v_0| for j>0 is respectively 0.03940, 0.05498, 0.07908 at k=-π/8,-0.267,-π/32. This was checked from retained JSON, not by a new solve; see `nonvanishing/r1/existing_terms_check.json`.

Held-out follow-up: assembly's actual q=2,R=22,left-twist 220-digit file has 184 blocks, maximum noninitial jet ratio 0.0394005110280, and relative pairing error 0.1076574921718562 <15/19. I read the artifact and recomputed the latter from c1/2 and v0; details are in the r1 NOTES. This remains floating-point evidence, with no full-character screen or exact dictionary.

## Recurrence fallback

`recurrence_cofinal_nonzero`: a scalar homogeneous recurrence

\[
u_{n+d+1}=\sum_{i=0}^d c_i u_{n+i},\quad c_0\ne0
\]

and one nonzero value imply unboundedly many nonzero values. `RadiusRecurrenceData` applies it directly to c(q,2(n+9)); `radius_cofinal_nonzero` returns unbounded even R≥18, and `dyadic_cofinal_nonzero` preserves the nested scale quantifiers.

`transfer_cofinal_nonzero` avoids finding scalar recurrence coefficients: for a linear observable L on any finite-dimensional space and an injective transfer T, one nonzero L(T^k x) implies unboundedly many nonzero values. `transfer_quotient_cofinal_nonzero` allows a nonzero denominator varying with n, and `transfer_progression_cofinal_nonzero` handles T^step and arbitrary offset.

Important: a collar-mode recurrence is **not yet** a recurrence for the scalar coupling evaluated at the R-dependent crossing. Inverses, eigenvector normalization, and the crossing angle depend on R. That identification is not silently assumed. Likewise, the transfer result requires a linear observable of a fixed finite-dimensional transfer state, not an arbitrary nonlinear function of a collar mode.

Full mathematics, exact remaining statements, numerical-evidence limitations and audit details: `AHP/round10/nonvanishing/r1/NOTES.md`.
