# Round 10 assembly, round 1

## Decision

**GoalNeg2 is NOT proved. No round-9 coupling premise is proved.**

This round compiled four small cofinality lemmas, assembled a conditional source-domination bridge against the unchanged round-9 prefix, and independently checked the nonvanishing track's new sufficient inequality at an actual held-out radius. Neither the numerical evidence nor the conditional bridge supplies the missing spectral/operator statements.

**The full concatenation is assembled but uncompiled for memory reasons.** Two wrapper invocations were killed by bb's 8 GiB per-command memory limit while processing the old prefix. The second used `LEAN_NUM_THREADS=1`, also unsuccessfully. Neither returned a `.exit` file. Both processes were confirmed terminated. Following the coordinator's explicit instruction, no further large compilation was attempted, no asynchronous-elaboration option was inserted, and the prefix was not changed. The coordinator may compile later with more RAM or as a module on the integration branch. This worker did not modify that branch or checkout.

There is deliberately no `goalNeg2_closed` theorem: there is no proved premise to put in its proof.

## 1. Independently compiled short contribution

`Cofinal.lean`, sole import frozen `D1IVT`, namespace `AdalyFormal.Round10.Assembly`:

1. `eventually_ne_zero_of_normalized_limit`: if `z n / s n → K ≠ 0`, then `z n ≠ 0` eventually. No sign or uniform positive lower bound on `s` is assumed. Even nonzero denominators need not be separately hypothesized: the nonzero limit forces the relevant quotients to be nonzero eventually.
2. `cofinal_of_eventual_subsequence`: an eventual property on radii `r n ≥ n` is cofinal in the physical radius.
3. `even_radius_progression`: `2*(n+9)` is even, at least 18, and at least n.
4. `nested_cofinal_of_eventual`: each chosen scale may have its own radius threshold; an exponent sequence `j n ≥ n` and per-scale eventual radius assertions suffice for the required nested cofinality.

All four compiled with wrapper exit **0**, no warnings/errors. Axiom dependencies are subsets of `{propext, Classical.choice, Quot.sound}`; `even_radius_progression` uses only `propext, Quot.sound`.

The byte-identical hand-off `AHP/round10/shared/assembly/R1_Cofinal.lean` was independently compiled at its published path, exit 0 with the same four dependency records.

These are general transport facts, **not** nonvanishing results about the frozen operators.

## 2. Assembly and proposed short glue

`Attempt.lean` has 12,567 lines and starts with the **complete 628,675-byte round-9 qualitative-r2 file verbatim**. It is assembled by `build.py` as:

1. `AHP/round9/qualitative-r2/Attempt.lean`, unchanged;
2. snapshot `snap/SourceDominance.lean`, the nonvanishing track's published compiled source, with its redundant `import D1IVT` removed;
3. `Cofinal.lean`, with its redundant import removed;
4. `Glue.lean` (111 lines).

The snapshot source equals `shared/nonvanishing/R1_SourceDominance.lean`. Its log and exit are copied provenance, not a claim of compilation at the snapshot path. The nonvanishing track is credited for all finite-source estimates.

`Glue.lean` is a **proposed, uncompiled** concrete appendix. Its intended argument is:

- `CanonicalKernelLine q R u` separates the geometric/full-kernel clauses of round 9's `CanonicalU1Line` from scalar nonvanishing.
- `DominatedSource q R f u` is exactly the nonvanishing track's
  `BlockSourceData ⟪u, corrDeriv q R f u⟫`.
- `coupling_ne_zero_of_blockSourceData`, followed by the existing `hasDerivAt_corrDeriv` and `canonicalCoupling_of_U1`, gives a canonical coupling.
- Nested cofinal witnesses give `CofinalAnyProfileCoupling`, then the existing round-9 bridge gives `GoalNeg2` **conditionally**.

A second proposed theorem, `cofinalAnyProfileCoupling_of_normalized_limits`, composes the compiled cofinality facts with eventual full-kernel charged-line identification and a nonzero normalized scalar limit, allowing arbitrary profiles and exponent/radius subsequences. Its analytic and spectral premises are not supplied.

No claim is made that these new concrete declarations have passed elaboration: the large compiler runs never reached them. No new axiom output for them exists.

## 3. Exact remaining Lean statement

The verified round-9 endpoint still needed is:

```lean
AdalyFormal.Round9.Guarded.QualitativeR2Joint.CofinalAnyProfileCoupling
```

In its original namespace this is:

```lean
∀ j₀ : ℕ, ∃ j : ℕ, j₀ ≤ j ∧ ∀ R₀ : ℕ, ∃ R : ℕ,
  R₀ ≤ R ∧ 2 ∣ R ∧ 18 ≤ R ∧
  ∃ f : Bond (scaleUp 2 1 (dilLu (2^j) R)) → ℝ,
    QualitativeR2.CanonicalCoupling (2^j) R (uthPath (2^j) R)
      (corrDeriv (2^j) R f)
```

A specific sufficient hand-off proposed in `Glue.lean` is:

```lean
def CofinalDominatedSource : Prop :=
  ∀ j₀ : ℕ, ∃ j : ℕ, j₀ ≤ j ∧ ∀ R₀ : ℕ, ∃ R : ℕ,
    R₀ ≤ R ∧ 2 ∣ R ∧ 18 ≤ R ∧
    ∃ (f : Bond (scaleUp 2 1 (dilLu (2^j) R)) → ℝ)
      (u : AnalyticR1.TwistSpace (2^j) R),
      CanonicalKernelLine (2^j) R u ∧ DominatedSource (2^j) R f u
```

**It is not proved.** The exact expanded statements and missing dictionary/kernel/jet obligations are in `AHP/round10/shared/GAPS.md`.

The other available round-9 premises remain options. A different exterior path can avoid the symmetric twist's near-degenerate partner, but still needs its full-kernel coupling and the path hypotheses. No free profile or path was constructed here that makes those obligations easy enough to prove.

## 4. Independent held-out high-precision check

Actual dilated geometry, **q=2, R=22**, charged character (7,7), **left-only exterior twist**. This radius was absent from the round-8/9 tables used by the authors. Three independent processes recomputed the source, vacuum kernel, dressing, and finite-sum coupling at **140, 190, 220 decimal digits**.

`numerics/crosscheck.py` imports only the frozen round-6 numerical transcription read-only, with bytecode disabled. It implements the left exterior link rule locally, differentiates the trigonometric pencil analytically (not by finite differences), and measures the full augmented null residual. The latest run also checks the nonvanishing track's *new* jet-domination/source-equation conditions. The earlier script is retained as `crosscheck.v1.py` for the 140/190 runs.

| quantity | held-out result |
|---|---:|
| crossing angle | 0.56397151798556094217971533436 |
| next Schur eigenvalue within this character | 0.998075759859083 |
| exact pencil slope on the normalized vector | −3.126529356906154 |
| first-order scalar c1 | −2.77209622826237508173501482418e−85 |
| normalized K_L = c1 / rho^(4qR) | −0.0383278683889973412626542729662 |
| nonzero defect jet v0 | −1.55326917856313353181289436991e−85 |
| number of source blocks | 184 |
| max |v_j/v0| over j>0 | 0.0394005110280210 |
| |sum h_j v_j − v0| / |v0| | 0.107657492171856 < 15/19 |
| source-equation residual, 220 digits | 3.85e−219 |
| augmented null residual / |c1|, 220 digits | 1.76e−129 |
| absolute sum of all correction tail terms / |first summand| | 0.0219640512627923 |

The 140/190 runs agree on c1 to **128.90 relative digits**; the 190/220 runs to **174.93 relative digits**. K_L is consistent with twice the previous symmetric-twist normalized constant. Peak RSS was 457–496 MiB; all three solves used a 2 GiB address-space cap and `bb heavy run`. Each numerical process has exit 0.

**Qualification:** this is an independent evaluation of a held-out instance using a shared transcription, not an independently derived operator dictionary. It is not interval arithmetic, a certified eigenvector enclosure, a full-character screen, or a proof of cofinal nonvanishing. The source bound is numerically supported for the *left* twist; it is not thereby proved for the canonical symmetric twist.

## 5. Shared-piece review

Read the mandatory round-9 notes/results and the round-8/round-6 numerical discussions. Read all published nonvanishing hand-offs, their logs/exits, and `nonvanishing/r1/NOTES.md`.

- **Finite-source estimate:** accepted as a compiled abstract inequality. It leaves exact operator identification, jet domination and nonzero v0 open.
- **Reversible recurrence / transfer estimates:** accepted as compiled abstract cofinality facts. A mode recurrence is not automatically a recurrence for the scalar coupling at the R-dependent crossing. No such scalar representation or exact seed has been supplied.
- **Dictionary late hand-off reviewed:** read the full 1345-line `shared/dictionary/R1_Dictionary.lean`, its log/exit, `R1_STATUS.md`, and `dictionary/r1/NOTES.md`. Published-file exit 0, 84 standard-axiom records, no diagnostics, byte-identical to `Actual.lean`. It adds actual corrDeriv form invariance and zero neutral/charged cross pairing to the symmetry results already inspected. These still do not supply full dressed translation reduction, the exact source/jet dictionary, a one-line full kernel, or nonvanishing. GAPS.md was updated; the accepted round-1 conclusion remains unchanged.

A geometry caution is relevant: matching the q-dilated collar length by a canonical q=1 radius does not also match the core length unless q=1 (`no_canonical_radius_dilation`). The phase experiments are strong asymptotic evidence, not a literal finite-volume canonical-radius equality.

## 6. Verification, failures, hygiene

- `Cofinal.lean` and its published copy: wrapper exit 0, standard axioms, no errors/warnings.
- `Attempt.lean`: two **memory-killed** attempts, no exit file; no completion or axiom audit claimed. First source/log retained under `history/Attempt.oom.lean*`; current partial `Attempt.lean.log` is the second attempt. `LEAN_NUM_THREADS=1` was ineffective. No large retry after coordinator instruction.
- Numerical startup using `/usr/bin/time` failed because that executable is absent; preserved as `numerics/unavailable-time.log/.exit` (127). No numerical job had started in that failed call. Direct heavy-scheduled Python runs subsequently succeeded.
- `audit.py` records compiled-short-file checks, unchanged prefix/assembly bytes, absence of a full compile, and `goalNeg2_proved: false`. Its artifact checks do not establish mathematical closure.
- Only `AHP/round10/assembly/r1/` and assembly-owned files under `AHP/round10/shared/` were authored. Existing protected/unrelated repository changes were not modified. No commit, push, build, REPRODUCE, removal, integration-checkout edit, or source-prefix modification.
