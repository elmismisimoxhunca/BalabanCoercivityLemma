# Nonvanishing track, round 2 — free defect location removes cancellation

## Decision

**GoalNeg2 is NOT proved. No actual round-9 cofinal coupling premise is proved.**

A stronger finite-block result is compiled: every nonzero vector of tangential block jets couples to at least one single-site interior defect. Unlike round 1, this needs neither domination by the first jet nor a nonzero first jet specifically. The defect location is free, as permitted by `CofinalAnyProfileCoupling` / `CofinalAnyPathCoupling`.

This is an unconditional theorem about the explicitly defined finite Dirichlet-chain model. Applying it to the frozen operators remains conditional on their exact dictionary and on a nonzero crossing jet. Those hypotheses have NOT been proved here.

Published: `AHP/round10/shared/nonvanishing/R2_SourceFamily.lean` (503 lines), with its independently generated `.log` and `.exit=0`. Namespace `AdalyFormal.Round10.Nonvanishing.FreeProfile`. All 47 declarations individually audited, only standard axioms.

## 1. Why change the source instead of estimating its alternating tail?

Round 1 fixed the leftmost defect and proved nonvanishing from

\[
v_0\ne0,\qquad |v_j|\le |v_0|\quad(0\le j<N).
\]

The source itself is interior data, independent of the exterior path. The round-9 weak premise allows **some** profile at each instance, rather than fixing `dilMask`. We can move the defect to any even longitudinal site inside the core. The corresponding family of source functionals separates all nonzero finite jet vectors. This removes the entire cancellation/jet-domination obligation; it does not remove the need to show that the jet vector is nonzero.

No transfer recurrence for the R-dependent crossing scalar is asserted. No canonical q=1 radius identification is used. The finite argument works for every N, so it introduces no radius threshold or uniform-in-q asymptotic error.

## 2. Exact finite source family

There are N blocks. All block sequences are zero-padded at N, and

\[
\operatorname{prev}(a)_j=\begin{cases}0&j=0,\\a_{j-1}&j>0.\end{cases}
\]

For source location i<N, let \(c^{(i)}\) solve

\[
6c^{(i)}_j+c^{(i)}_{j-1}+c^{(i)}_{j+1}
 =\tfrac32\mathbf 1_{j=i}+\tfrac12\mathbf 1_{j+1=i},
\qquad c^{(i)}_{-1}=c^{(i)}_N=0.
\]

Define

\[
h_i(j)=\mathbf 1_{j=i}-\mathbf 1_{j+1=i}
       -2c^{(i)}_{j-1}+2c^{(i)}_{j+1},
\qquad P_i(b)=\sum_{j<N}h_i(j)b_j.
\]

At i=0 these are **exactly** round 1's equations and source weights. At an interior i, the extra neighboring RHS and Kronecker term are essential; merely translating the one-sided first-site formula would be incorrect.

`exists_tri_solution` proves existence for every finite N and every RHS. The tridiagonal linear map is injective: at a maximal absolute entry, a homogeneous solution satisfies \(6M\le2M\), hence M=0. In finite dimension, injectivity implies surjectivity. No inverse is postulated and no explicit root or square root is needed.

The main theorem is

\[
\sum_{i<N} b_iP_i(b)>0 \quad\text{if }(b_0,\ldots,b_{N-1})\ne0.
\]

In particular some \(P_i(b)\ne0\). This proves positivity of the quadratic source-response form; scalar couplings to individual sites may have either sign.

## 3. Proof by the constrained fine Dirichlet lift

Given coarse data b, solve

\[
6a_j+a_{j-1}+a_{j+1}=b_{j-1}-b_{j+1},\qquad a_{-1}=a_N=0.
\]

Set

\[
y_0=y_{2N+1}=0,\quad y_{2j+1}=b_j+a_j,\quad y_{2j+2}=b_j-a_j.
\]

Thus the two-site average is b. The tridiagonal equation says exactly that the two fine Laplacian entries in each block agree:

\[
2y_{2j+1}-y_{2j}-y_{2j+2}
=2y_{2j+2}-y_{2j+1}-y_{2j+3}
=b_j-b_{j-1}+3a_j+a_{j-1}=:r_j.
\]

This is the stationarity condition for varying opposite entries of a block while fixing its average. Exact tridiagonal reciprocity gives \(P_i(b)=r_i\) (`column_pairing`), for **any** source amplitudes satisfying the displayed equations, not just the chosen solution.

Discrete summation by parts gives

\[
2\sum_jb_jr_j=\sum_{x=0}^{2N}(y_{x+1}-y_x)^2.
\]

Every summand is nonnegative. If the sum vanishes then all adjacent values coincide; the left Dirichlet endpoint forces all of y to be zero, hence every b_j is zero. This proves strict positivity for nonzero b, and therefore some nonzero single-source response.

## 4. Compiled statements

`DirichletResponse.lean` (152 lines, 13 declarations): finite summation by parts, energy positivity, stationary-lift response identity, and nonzero local response from a nonzero average.

`TridiagonalResponse.lean` (304 lines, 29 declarations, includes the preceding file verbatim): existence of every finite tridiagonal solve; explicit lift and stationarity; positive response form.

`SourceFamily.lean` (503 lines, 47 declarations, includes the preceding file verbatim): exact source equations and weights; reciprocity; separation by one source; actual-dictionary interfaces. Main declarations:

```lean
theorem sourceResponse_pos (n : ℕ) (b : ℕ → ℝ) (hb : b n = 0)
    (hne : ∃ j < n, b j ≠ 0) :
    0 < ∑ i ∈ Finset.range n, b i * sourceResponse n i b

theorem exists_sourceResponse_ne_zero (n : ℕ) (b : ℕ → ℝ)
    (hb : b n = 0) (hne : ∃ j < n, b j ≠ 0) :
    ∃ i < n, sourceResponse n i b ≠ 0
```

The choice-independent interface is:

```lean
theorem exists_coupling_of_source_columns (n : ℕ) (b coupling : ℕ → ℝ)
    (c : ℕ → ℕ → ℝ) (factor : ℝ)
    (hb : b n = 0) (hne : ∃ j < n, b j ≠ 0) (hf : factor ≠ 0)
    (hc : ∀ i < n, c i n = 0)
    (heq : ∀ i < n, ∀ j < n,
      6*c i j + prev (c i) j + c i (j+1) = sourceRhs i j)
    (hdict : ∀ i < n, coupling i = factor *
      (∑ j ∈ Finset.range n, columnWeight (c i) i j * b j)) :
    ∃ i < n, coupling i ≠ 0
```

**For the actual vacuum crossing, `hne`, `hc`, `heq`, and `hdict` are not supplied by this file.** The abstract existence theorem constructs c for the scalar equations but does not identify it with any frozen H/J operator.

## 5. Physical indices and normalization — dictionary hand-off

Put

\[
p=q(2R+4),\qquad N=4q(R+1).
\]

Source i is a direction-1 bond at longitudinal coordinate p+2i, repeated at **even** transverse coordinates. Its profile takes values 0 and 1; it is not a perturbation of the blocking stride or a replacement torus. The corresponding jet j is direction 1 at fine base (p+2j,0,0), coarse base (p/2+j,0,0). R6's `b1` list index is 3j+2, because list index 0 is an incoming longitudinal coarse bond.

The level-1 normalization 1/2 of `C2fullOf` is included in the jet. There are two distinct valid conventions for b:

- **Physical jet:** b_j is the actual normalized `C2fullOf` coordinate of the physically normalized lifted vector. There are (4q)^2 transverse coarse cells, so the predicted overall coupling factor is \(2(4q)^2\).
- **Numerical cell jet:** b_j is R6 `rawjet` on the cell-normalized charged vector. The physical isometric lift divides that vector by 4q, hence its quadratic jet by (4q)^2; this cancels the cell count. The predicted factor is **2**.

Both factors are nonzero for q>0. The finite theorem keeps `factor ≠ 0` explicit rather than silently confusing the conventions. Neither physical identification is yet formalized here.

The interior source is independent of which exterior twist produces the kernel. The left-only twist remains preferable because it avoids the symmetric twist's exponentially small partner splitting. The same finite source argument can be used with the canonical symmetric path if its full kernel is identified.

## 6. Numerical check of the new generalized formula

`check_source_family.py` imports the round-6 transcription read-only, disables bytecode writes, and tightens its inherited address-space limit to **2 GiB before allocating a family**. It forms the exact-flat numerical source `Delta_flat * profile`, then solves the **full neutral augmented KKT system**, not an inverse of a boundary compression. It compares every top component with the new source formula. The equality of that flat source with the actual curvature derivative remains a Lean dictionary obligation; no finite-curvature extrapolation is used.

80-digit tests, four source locations per geometry:

| q | R | N | source locations |
|---:|---:|---:|---|
| 1 | 2 | 12 | 0,1,6,11 |
| 2 | 2 | 24 | 0,1,12,23 |
| 2 | 18 | 152 | 0,1,76,151 |
| 4 | 18 | 304 | 0,1,152,303 |

Across all 16 tests:

- maximum full-vector discrepancy: **7.49e-74**;
- maximum component in the other top directions: **7.49e-74**;
- peak RSS: **621548 KiB**, about 607 MiB;
- job exit 0, `bb heavy run`, single-threaded BLAS.

The tridiagonal comparison uses a linear-time Thomas solve, not a dense inverse. Artifacts: `source_family_check.json`, `.log`, `.exit`.

These are **floating-point evidence only**. No interval certificate, exact frozen-operator dictionary, new crossing solve, nonzero crossing jet, full-character exclusion, or cofinal proof is claimed. Small R=2 checks are not admissible cofinal witnesses; R=18 checks test only the source dictionary, not the spectral conditions.

## 7. Exact remaining endpoint and next step

The unchanged round-9 goal is still, for example,

```lean
AdalyFormal.Round9.Guarded.QualitativeR2Joint.CofinalAnyProfileCoupling
```

whose definition in its original namespaces is:

```lean
∀ j₀ : ℕ, ∃ j : ℕ, j₀ ≤ j ∧ ∀ R₀ : ℕ, ∃ R : ℕ,
  R₀ ≤ R ∧ 2 ∣ R ∧ 18 ≤ R ∧
  ∃ f : Bond (scaleUp 2 1 (dilLu (2^j) R)) → ℝ,
    QualitativeR2.CanonicalCoupling (2^j) R (uthPath (2^j) R)
      (corrDeriv (2^j) R f)
```

It is **not proved**. On the proposed single-character route, the remaining work is:

1. Prove the generalized source-column dictionary against the frozen source derivative, H, and normalized C2. The r2 dictionary track's U(1)/neutral-coordinate results alone do not establish the tridiagonal equations or the selected transverse components.
2. Prove **some** direction-1 block jet is nonzero on a crossing vector. This is strictly weaker than round 1's nonzero v0 plus domination, but it is still a real missing theorem. Unique continuation of the vector alone does not force a nonzero commutator jet.
3. Prove full-kernel containment in one charged complex line (or another definiteness argument), excluding other singular characters. The source site selected by this round depends on the chosen jet vector. In general, “for every nonzero kernel vector some profile couples” does **not** imply “one profile is definite on the whole kernel”; traceless quadratic pencils are a counterexample to that quantifier exchange. Assembly's `canonicalCoupling_of_line` is the appropriate conditional bridge when its whole-kernel `KernelLine` hypothesis is supplied. Its alternative whole-kernel source criterion requires a single coercive sign, which is not established by this round's vectorwise source selection.
4. Supply these facts for nested cofinal dyadic scales and even radii, then use the existing free-profile bridge. A left-only exterior path instead uses the free-path bridge and its path/crossing obligations.

The local exact statements still needed for the finite hand-off are the `hne` and actual `hdict` displayed in section 4, plus the source equations if using externally supplied amplitudes. Nothing here proves the canonical fixed source has nonzero coupling; the proved conclusion selects a possibly different source site.

### Late dictionary hand-off

After the nonvanishing r2 result was returned, dictionary published `AHP/round10/shared/dictionary/R2_SourceDictionary.lean` (1055 lines). I inspected its actual source statements, recorded exit 0, and relevant standard-axiom records. It proves the explicit source derivative for **every profile**:

```lean
Source.bulkSource_tendsto q R f
```

with derivative

```lean
pE (geomOf 2 1 (dilTower q R))
  (PhaseSource.sourceLinear (plaqIn ((dilTower q R).Om 0))
    (Source.interiorProfile q R f))
```

`PhaseSource.sourceLinear` is the exact scalar backward-divergence-of-circulation stencil times the frozen neutral Pauli vector. This discharges the source calculus/stencil step, **not** its equality with the curl-adjoint composition, the energy identity, the tridiagonal KKT dictionary, or crossing nonvanishing.

A promising next step is the exact discrete curl-adjoint/energy identity. For a candidate obtained from `H0 C2(Wu)`, first prove that it is neutral, extract its scalar E3 coefficient, and use its exterior-zero carrier lift as the profile. The exterior masking must be handled explicitly: `interiorProfile` zeroes bonds in `Zb`, whereas the carrier is supported on touching bonds. Profile admissibility/rescaling and every actual boundary row in any Q/curl telescoping argument must also be checked.

**Nonzero C2 alone does not imply nonzero coarse circulation.** Any circulation obstruction needs an additional proved identity or hypothesis about the selected component/character; it cannot be inferred merely from the nonzero vector. Even after the energy identity, proving a nonzero localized curl on the crossing mode and full-kernel definiteness remains necessary. A profile selected from u supplies vectorwise detection only. Assembly reports a compiled U(1)-invariant counterexample in its `R2_ProfileQuantifiers` to swapping this with one fixed profile definite on the whole kernel; retain `KernelLine` or prove another common-sign argument. No new proof or reclassification of GoalNeg2 is claimed from these late hand-offs.

## 8. Verification and hygiene

Every compiler invocation used only `AHP/round3/lean1.sh <file.lean>` directly in bash with a long timeout. No timeout or memory kill occurred. Final original and shared files all have exit 0, no errors/warnings, and one `#print axioms` record per declaration. Every record lists only `propext`, `Classical.choice`, `Quot.sound`.

`audit.py` produces `CHECKS.json` with pass=true. It checks imports, prohibited-device absence, diagnostics, source/log/exit timestamps, assembly byte identities, shared byte equality, and all declaration/dependency records. It explicitly records the actual goal, actual source dictionary, actual crossing jet and fixed-source nonvanishing as **unproved**.

Reproduction:

```sh
python3 AHP/round10/nonvanishing/r2/assemble.py
AHP/round3/lean1.sh AHP/round10/nonvanishing/r2/DirichletResponse.lean
AHP/round3/lean1.sh AHP/round10/nonvanishing/r2/TridiagonalResponse.lean
AHP/round3/lean1.sh AHP/round10/nonvanishing/r2/SourceFamily.lean
AHP/round3/lean1.sh AHP/round10/shared/nonvanishing/R2_SourceFamily.lean
python3 AHP/round10/nonvanishing/r2/audit.py
```

The `.lean.txt` files are assembly fragments, not standalone modules. Failed development compiles were ordinary local elaboration/tactic failures; those were fixed before the final audited compiles. One important fix made all finite-vector neighbor arithmetic explicit in Nat, avoiding accidental Fin wraparound at the Dirichlet boundary.

Only this round's track directory and nonvanishing-owned files in `AHP/round10/shared/nonvanishing/` were written. Earlier rounds, other tracks and protected files were read only. No integration-checkout edit, lake build, REPRODUCE, git commit/push, removal outside the track, or new worktree.
