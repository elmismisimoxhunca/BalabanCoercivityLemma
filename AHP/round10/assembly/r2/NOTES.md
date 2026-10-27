# Assembly and cross-check, round 2

## Decision

**GoalNeg2 is NOT proved. No round-9 cofinal coupling premise is proved.**

This round repairs the round-1 concrete-glue compilation gap, integrates nonvanishing's new free-source theorem into the exact round-9 free-profile premise, and performs independent held-out high-precision tests. It also proves an abstract U(1)-invariant counterexample to a tempting quantifier shortcut. None supplies the missing actual spectral/source facts.

## 1. Compiled concrete glue

`Compact.lean` is **1506 lines**, sole import frozen `DrEquiv`, wrapper exit **0**. Its independently compiled byte-identical publication is `AHP/round10/shared/assembly/R2_SourceGlue.lean`, also exit 0. Both logs have 80 allowed-axiom records, no warnings/errors. All **14 new concrete declarations** have individual records, each a subset of `{propext, Classical.choice, Quot.sound}`.

The harness copies 33 operative declarations verbatim from round 9 and the R1 dictionary, and includes the complete shared R1 SourceDominance, R1 Cofinal, and R2 SourceFamily bodies with only redundant imports removed. `COPIES.json` records the copied declaration locations and hashes; `CHECKS.json` checks those slices, the included bodies, source equality and all axiom records. It does not assert that any missing premise is proved.

Namespace: `AdalyFormal.Round10.Assembly.R2`.

| Compact line | declaration | status/content |
|---:|---|---|
| 1294 | `deriv_symmetric` | A symmetric operator family has a symmetric totalized derivative. No differentiability assertion is fabricated. |
| 1314 | `corrDeriv_symmetric` | Unconditional symmetry of the actual named round-9 corrDeriv. |
| 1323 | `KernelLine` | Explicit **missing** full-kernel charged-line geometry for any exterior path. |
| 1334 | `canonicalCoupling_of_line` | Full-kernel line + nonzero actual scalar ⇒ actual `CanonicalCoupling`, any exterior path. |
| 1360 | `canonicalCoupling_of_dominatedSource` | Compiled repair of the R1 source-domination glue; source/jet/kernel hypotheses remain. |
| 1408 | `canonicalCoupling_of_kernelSource` | A source identity and coercive first-jet sign on the **whole** kernel imply coupling without spectral simplicity. Hypotheses unproved. |
| 1440 | `exists_profile_coupling_of_sourceFamily` | New free-source theorem + actual dictionary + nonzero jet + full-kernel line ⇒ some actual profile couples. |
| 1454 | `exists_profile_coupling_of_sourceColumns` | Same, accepting supplied exact source-column equations rather than chosen amplitudes. |
| 1470–1482 | `SourceFamilyData`, `CofinalSourceFamily`, `cofinalAnyProfileCoupling_of_sourceFamily` | Exact missing hand-off and its compiled implication to round 9's unchanged `CofinalAnyProfileCoupling`. |

### Why the compact proof needs no missing regularity lemma

The R1 dictionary already proves `corrDeriv_U1` for the actual named derivative, with no extra hypotheses. The new symmetry proof handles a differentiable operator family by differentiating its matrix coefficients and using uniqueness; at a nondifferentiable point the totalized derivative is zero and symmetric. Round 9 separately proves actual differentiability for admissible q,R, so this does not substitute a zero operator for the genuine coefficient.

Copying `scalar_on_complex_line` verbatim from round 9 then gives scalar quadratic action on span{u,Ju} whenever J²u=−u. A nonzero form value there produces either positive or negative coercivity on the entire kernel, provided the **whole-kernel containment** is supplied. No claim of that containment is inferred from U(1) symmetry.

## 2. The preferred improvement: choose the defect site

Nonvanishing's new `R2_SourceFamily.lean` proves a positive-definite finite source-response form. For N blocks and every nonzero jet vector b there is an i<N with nonzero source response. The source i need not be the leftmost site. Thus the actual free-profile route no longer needs b0≠0 or |bj|≤|b0|. It still needs some actual jet component to be nonzero.

Our compiled theorem combines that fact with the actual scalar-to-full-kernel bridge. In original namespaces, the exact remaining sufficient premise is:

```lean
def CofinalSourceFamily : Prop :=
  ∀ j₀ : ℕ, ∃ j : ℕ, j₀ ≤ j ∧ ∀ R₀ : ℕ, ∃ R : ℕ,
    R₀ ≤ R ∧ 2 ∣ R ∧ 18 ≤ R ∧
      SourceFamilyData (2^j) R (uthPath (2^j) R)
```

Expanded per instance:

```lean
def SourceFamilyData (q R : ℕ)
    (V : ℝ → LinkCfg (scaleUp 2 1 (dilLu q R))) : Prop :=
  ∃ (u : TwistSpace q R), KernelLine q R V u ∧
    ∃ (N : ℕ) (b : ℕ → ℝ)
      (profiles : ℕ → Bond (scaleUp 2 1 (dilLu q R)) → ℝ)
      (factor : ℝ),
      b N = 0 ∧ (∃ j < N, b j ≠ 0) ∧ factor ≠ 0 ∧
      (∀ i < N, ⟪u, corrDeriv q R (profiles i) u⟫ =
        factor * Nonvanishing.FreeProfile.sourceResponse N i b)
```

**Not proved.** The exact full-kernel expansion and choice-independent source-column statements are recorded in `shared/GAPS.md`. The missing actual facts are:

1. The frozen H*/C2/W source-column dictionary, including jet aggregation/normalization. Dictionary R2 has now proved the raw J' stencil; the propagated H* source columns are not identified.
2. Some actual direction-1 quadratic jet is nonzero on the selected exact crossing vector.
3. The full real carrier kernel is contained in its charged complex line, or a separate common-sign whole-kernel proof.
4. These facts hold at nested cofinal dyadic scales and even radii.

The physical jet and numerical cell jet have different normalization: for physical C2 coordinates the expected multiplicity factor is 2(4q)²; for the isometrically normalized numerical cell jet it is 2. The compiled interface deliberately keeps an explicit nonzero factor. No normalization is silently identified. Alternatively, as dictionary R2 suggests, use b[j] as the **sum** of physical neutral jet coefficients over the entire corresponding transverse slice. Once the source columns are proved constant on that slice, factor 2 follows by grouping the physical sum, with no Bloch normalization needed. The existing finite source-family theorem and compiled assembly interface accept this aggregated b without change; its nonzero component and exact source identity remain unproved.

The new per-instance theorems accept **any** exterior path. For a left-only path the free-path bridge still needs its path/canonical-crossing obligations; the written cofinal `CofinalSourceFamily` specialization uses the canonical symmetric twist. Our left-twist numerics do not discharge that specialization.

## 3. Whole-kernel alternative and a rigorous caution

`canonicalCoupling_of_kernelSource` compiles a different sufficient criterion. If for every kernel vector u the actual coupling equals factor times the finite source sum, the jets satisfy |v(u,j)|≤|v(u,0)|, and one σ∈{1,−1} has

\[
\delta\|u\|^2\le\sigma v(u,0),\qquad\delta>0,
\]

then the original source-error estimate gives coercivity factor·(4/19)·δ. This does not require a single singular character or a two-dimensional real kernel. **No actual first-jet coercivity is proved.**

One cannot instead swap the quantifiers in the free-profile theorem. `ProfileQuantifiers.lean` (67 lines), with independently compiled shared copy `R2_ProfileQuantifiers.lean`, proves an exact counterexample to that shortcut:

\[
Q_{a,b,c}(z,w)=a(|z|^2-|w|^2)+2b\Re(\bar zw)+2c\Im(\bar zw).
\]

- Every member is invariant under common U(1) phase rotations (`form_U1`).
- For every nonzero (z,w), coefficients chosen to match its quadratic components give Q=(|z|²+|w|²)²>0 (`every_vector_has_profile`).
- No fixed coefficients give a definite form on the whole space, since Q(1,0)=a and Q(0,1)=−a (`no_profile_definite`).

Both files exit 0 with six individual standard-axiom records and no diagnostics. This is **not** a counterexample to the actual round-9 premise. It explains precisely why full-kernel geometry remains necessary after vectorwise source controllability.

## 4. Independent numerical cross-checks

All runs use the frozen round-6 transcription read-only, with bytecode disabled, single-threaded BLAS, a 2 GiB address-space cap and `bb heavy run`. These are precision-stability checks, not interval certificates or replacement proof steps.

### Held-out actual crossing: q=4, R=20, left-only twist, character (15,15)

Two independent processes at **200 and 250 digits**. `numerics/crosscheck.py` is adapted from assembly's R1 independent check, not the source authors' tests. It computes the analytic trigonometric pencil derivative and full augmented null residual.

| quantity | result |
|---|---:|
| c1 | −1.35733610333104781077636950801306e−140 |
| c1/rho^(4qR) | −0.0359299026177330812705320851758 |
| relative agreement, 200/250 | **183.12 digits** |
| augmented residual divided by absolute c1, 250 digits | **1.66e−103** |
| next Schur eigenvalue within this character | 1.02753076273 |
| analytic pencil slope | −2.62870214830 |
| N | 336 |
| v0 | −7.71376714864573457104656622e−141 |
| maximum noninitial absolute jet ratio | 0.0655819865163 |
| relative source-pairing error | 0.120185975818 <15/19 |
| absolute tail divided by absolute first term | 0.0369323648883 |

Both exits 0; peak RSS ≤856 MiB. This supports the earlier fixed-source criterion on a new q,R case. It does not prove all-character exclusion or the full-kernel statement.

### Generalized R2 source columns: q=4, R=20, indices 2,112,334

`numerics/source_crosscheck.py` is separately written. It compares the **full neutral KKT solve** with the finite tridiagonal **hyperbolic Green kernel**, not the author's Thomas algorithm. Neither this geometry nor these three indices were in the source author's tests. No finite-curvature extrapolation is used; the input source is `Delta_flat * profile`.

| precision | maximum source-column discrepancy | maximum full KKT residual |
|---:|---:|---:|
| 150 | 7.26e−147 | 6.74e−147 |
| 190 | 3.72e−189 | 2.69e−190 |

Off-direction components obey the same discrepancy scale. The active source components are approximately 0.83. Both exits 0; peak RSS below 600 MiB. This supports the new source formula independently, but the exact frozen-source identification and nonzero actual crossing jet still need Lean proofs.

Raw JSON/log/exit files and `numerics/SUMMARY.json` retain all results and qualifications.

## 5. Full assembly, review and audit

`Attempt.lean` is **13,948 lines**. It begins with all 628,675 bytes of `AHP/round9/qualitative-r2/Attempt.lean` unchanged, then appends the R2 dictionary bodies in `DictionaryAppendix.lean` (660 lines), the R1 symmetry lemmas, shared source/cofinal results, the new appendix and `GoalBridge.lean`. The dictionary appendix copies `half_rotation_matrix` plus the complete PhaseSource, KKT and SourceAppendix bodies, with redundant imports removed. It is an assembly fragment, not a standalone compiled claim. The two final applications are **conditional** on `CofinalDominatedSource` or `CofinalSourceFamily`.

**No large-file compile was run.** The coordinator prohibited another attempt after R1's memory kills. Consequently no `.exit` or axiom record is claimed for the assembled `GoalBridge` applications. The actual implication into the original round-9 premise **is** independently compiled in the compact harness. No theorem named or represented as an unconditional closed goal is present.

Read the required R9/R8/R6 notes, every R1 shared Lean source/log/exit/status and track notes, and the R2 nonvanishing source/status/notes (including the choice-independent addition). The nonvanishing finite-source proof is integrated verbatim, not rederived or weakened. The dictionary's **final R2** source/KKT/stencil publication, log, exit, status and full track notes were also reviewed. `DICTIONARY_REVIEW.json` checks its 88 standard-axiom records, fresh exit 0, byte inclusion of all three inspected new bodies and its source hash. The publication preserves the original `QualitativeR2Joint.bulkU_dilMask` namespace. Its exact actual source stencil and neutral physical sum are now recorded as proved in GAPS; the physical one-dimensional H/source lift and nonzero jet/full-kernel claims remain open.

`python3 AHP/round10/assembly/r2/audit.py` gives **PASS** and writes `CHECKS.json`. It verifies four final compilation records, allowed dependencies, per-new-declaration records, no diagnostics/prohibited proof devices, 33 verbatim copied declarations, shared body equality, timestamps and the full round-9 byte prefix. It explicitly records all actual closure flags as false and the full Attempt as uncompiled.

Compile history: one ordinary compact development failure (two reversed `real_inner_comm` applications in derivative symmetry), repaired before all final compiles. Its failed log is retained under `history/Compact.v1.log` and is not counted. No timeout, memory kill, or prohibited large retry occurred this round. No numerical failure occurred.

Only `AHP/round10/assembly/r2/` and assembly-owned files under `AHP/round10/shared/` were written. No protected source, earlier round, integration checkout, lakefile, build, REPRODUCE, commit, push, or worktree operation. The pre-existing tracked modification of `lean/lakefile.toml` was untouched.
