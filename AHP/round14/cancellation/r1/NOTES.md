# Cancellation R1 — charged area structure; P3 remains open

## Verdict

**P3 is not proved.** This round supplies a compact, compiled exact structure for
the weighted mixed-colour area sum: it is a sesquilinear charged area, with exact
phase/amplitude scaling and a reversible complex-current recurrence. These are
algebraic interfaces, not a physical nonvanishing certificate. No common-sign
claim is made, and no numerical value is promoted to a theorem.

## Compiled deliverables

- Local: `AHP/round14/cancellation/r1/ChargedArea.lean` (200 lines), with
  `.lean.exit = 0` and a warning-free `.lean.log`.
- Reusable publication: `AHP/round14/shared/cancellation/ChargedArea.lean`,
  byte-identical to the local file and independently compiled through
  `AHP/round3/lean1.sh`, also `.lean.exit = 0` with a warning-free log.
- Every printed axiom record is a subset of
  `{propext, Classical.choice, Quot.sound}`. There is no `sorry`, `admit`,
  `axiom`, `native_decide`, `unsafe`, `implemented_by`, `extern`, or `opaque`.
  The only import is frozen `DrEquiv`. No `lake build` or `REPRODUCE.sh` was run.

All declarations are in `AdalyFormal.Round14.Cancellation`.

## 1. Exact charged structure of the original area sum

For a finite index type `ι`, define

```lean
chargedArea K z = ∑ e, ∑ d, (z e * conj (z d)).im * K e d
sesquilinearArea K z =
  (Complex.I * ∑ e, ∑ d, conj (z e) * (K e d : ℂ) * z d).re
```

The compiled theorem `chargedArea_eq_sesquilinear` proves these are equal for an
**arbitrary** real coefficient matrix `K`; no symmetry or definiteness is
assumed. More importantly for the physical dictionary,
`chargedArea_real_imag` proves

```lean
chargedArea K (fun e => (g e : ℂ) + (f e : ℂ) * Complex.I) =
  ∑ e : ι, ∑ d : ι, (f e * g d - g e * f d) * K e d
```

Thus, with the round-13 definitions, set
\[
  Z_u(e)=\operatorname{realPart}(u,e)+i\,\operatorname{imagPart}(u,e).
\]
Specializing the compiled theorem gives the exact identity
\[
  \operatorname{areaSum}(u)
  =\operatorname{chargedArea}(K,Z_u)
  =\operatorname{Re}\!\left(i\sum_{e,d}\overline{Z_u(e)}\,K_{e,d}Z_u(d)\right),
  \qquad K=\operatorname{aggregateCoefficient}.
\]
This is the genuine mixed-colour area, not a replacement by a common-sign sum.
It also makes the fixed-number-per-instance remark precise: the value at one
chosen generator is a single real number for each `q,R,j`, and phase scaling
controls every other vector on that charged line.

### Exact phase and complex-line identities

`chargedArea_smul` proves

```lean
chargedArea K (fun e => c * z e) = Complex.normSq c * chargedArea K z
```

and `chargedArea_affine` specializes it to real `a,b`:

```lean
chargedArea K (fun e => ((a : ℂ) + (b : ℂ) * Complex.I) * z e) =
  (a ^ 2 + b ^ 2) * chargedArea K z
```

`chargedArea_smul_ne_zero` preserves nonvanishing under every nonzero complex
phase/amplitude. This is the algebraic content needed when a vector on the
kernel line is written as `a • u + b • J u`, after the physical identification
of the quarter-turn with multiplication by `i` is supplied.

`chargedArea_common_phase_zero` proves the complementary obstruction:

```lean
chargedArea K (fun e => c * (w e : ℂ)) = 0
```

for every real array `w` and complex phase `c`. Hence a common-phase field has
zero area. A nonzero coordinate or chargedness alone cannot supply the missing
seed; a genuinely non-real spatial ratio is required.

The Hermitian identity is **not** a positivity theorem. For real skew `K`, the
Hermitian matrix `iK` has a spectrum symmetric about zero, so a general
fixed-sign assertion would be false even before considering cell cancellation.

## 2. Exact reversible complex current

`chargeCurrent z n = (conj (z n) * z (n+1)).im` satisfies the compiled recurrence

```lean
z (n+2) = (a n : ℂ) * z (n+1) + (b n : ℂ) * z n →
  chargeCurrent z (n+1) = -(b n) * chargeCurrent z n
```

under `chargeCurrent_step`. Then:

- `chargeCurrent_ne_zero` propagates a nonzero seed through any finite segment
  with `b n ≠ 0`;
- `chargeCurrent_eq_seed` proves exact conservation when `b n = -1`;
- `chargeCurrent_cofinal` gives `∀ N, ∃ n ≥ N, chargeCurrent z n ≠ 0` for an
  infinite reversible recurrence with a nonzero seed.

These results are deliberately parameterized by the recurrence and seed. The
actual `aggregateCoefficient` has **not** yet been identified with this current,
and no physical seed is asserted.

## 3. Numerical structure evidence only

`structure_probe.py` is a held-out numerical experiment at the right star,
`q=1,R=20`, 50 decimal digits. It uses the full flat constrained resolvent before
the nine-bond boundary Schur reduction, evaluates the actual two-atom neutral
jets, and checks the area dictionary against direct physical cell sums.
Artifacts are `structure_right_q1_R20_p50.{json,log,exit}`; the exit is zero.

- `areaSum_from_Hermitian = 7.0037756567830323922e-44`, agreeing with
  `two_physicalJetAggregate_direct` and the independently accumulated Fourier
  value to about `7.8e-44` relative error. This is floating-point evidence,
  not an interval certificate or a Lean stencil identification.
- The nine-bond Hermitian spectrum has approximate pairs
  `±3.91694e-44`, `±1.72225e-45`, `±2.00024e-53`, `±1.60254e-54`,
  plus a near-zero value. Thus the proposed definite-Hermitian shortcut is
  unsupported even at this restricted boundary level.
- Individual character contributions also have mixed signs, including
  `+2.21124e-43`, `-6.05554e-44`, `+4.25899e-43`, and `-2.61658e-44`.
  Neither cellwise signs nor characterwise signs provide a common-sign proof.

The script and JSON are diagnostic evidence only. The Schur vector is not a
unit-full-carrier Lean generator, and no exact cofinal or nonvanishing claim is
based on this run.

## 4. Exact statements still missing

The original P3 remains exactly:

```lean
∀ {q R : ℕ} (hq : 0 < q) (hR : 2 ∣ R) (hR18 : 18 ≤ R)
  (u : TwistSpace q R), KernelLine q R (rightStar hq R) u →
    CurlDetected q R u
```

The sufficient original area remainder also remains unproved:

```lean
∀ {q R : ℕ} (hq : 0 < q) (hR : 2 ∣ R) (hR18 : 18 ≤ R)
  (u : TwistSpace q R), KernelLine q R (rightStar hq R) u →
    ∃ j : ℕ, ∃ hj : j < blockCount q R, areaSum hq hj u ≠ 0
```

By `chargedArea_real_imag`, an exactly equivalent charged-form remainder is:

```lean
∀ {q R : ℕ} (hq : 0 < q) (hR : 2 ∣ R) (hR18 : 18 ≤ R)
  (u : TwistSpace q R), KernelLine q R (rightStar hq R) u →
    ∃ j : ℕ, ∃ hj : j < blockCount q R,
      chargedArea (aggregateCoefficient hq hj)
        (fun e => (realPart (G q R) u e : ℂ) +
          (imagPart (G q R) u e : ℂ) * Complex.I) ≠ 0
```

No inhabitant of any of these propositions is supplied here. A subsequent round
must either evaluate the fixed charged-area number at a crossing generator and
prove it nonzero, or identify the genuine physical current recurrence together
with a proved nonzero seed. The general identities above do not close either
physical input.

## Scope

Writes are confined to `AHP/round14/cancellation/r1/` and
`AHP/round14/shared/cancellation/`. Earlier rounds, frozen modules, the lakefile,
and the integration checkout were not edited. No git commit or push was made.
