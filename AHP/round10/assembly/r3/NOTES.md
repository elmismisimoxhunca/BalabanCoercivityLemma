# Assembly R3 — adaptive curl-energy and physical-jet glue

**Outcome: partial progress. GoalNeg2 and every original round-9 cofinal coupling premise remain OPEN.** No git commits/pushes or edits outside the assembly-owned round-10 scope were made by this worker.

## What is actually compiled

Six compact local/shared files, freshly compiled via `AHP/round3/lean1.sh`, all exit 0 with no diagnostics and only the permitted axioms:

| Local | Shared | Lines | Printed records |
|---|---|---:|---:|
| `Neutral.lean` | `shared/assembly/R3_NeutralResponse.lean` | 1169 | 97 |
| `Compact.lean` | `shared/assembly/R3_EnergyGlue.lean` | 2249 | 165 |
| `JetCompact.lean` | `shared/assembly/R3_JetGlue.lean` | 3178 | 254 |

Paths in this table are relative to `AHP/round10/assembly/r3/` for local files and `AHP/round10/` for shared files. There are **26 new R3 assembly declarations**. Every one has a printed axiom record. All imported operators are frozen; copied operative definitions remain verbatim in their original namespaces. `profileData` is just a type-fixed abbreviation of the actual `dataS`, not a new model.

### Actual neutral response: nine declarations

`NeutralAppendix.lean` proves the quarter-action-squared identity, evenness of the actual dressed quadratic jet, charged-input jet/response neutrality, componentwise Pauli-E3 representation, exact physical profile lift, and that exterior masking changes nothing. It uses the frozen quadratic bilinear witness and actual base-data gauge equivariance. It does not infer charge or nonzero jet from being in a crossing kernel.

### Arbitrary-profile derivative and cofinal curl-line glue: twelve declarations

`EnergyGlue.lean` proves `bulkD_zero_source` directly from the exact zero source and symmetric quadratic form, then specializes round-9 `limit_Delta2_div_form` using R2 `bulkSource_tendsto`. The result is:

```lean
corrDeriv_profile_form (q R : ℕ) (f : Bond (scaleUp 2 1 (dilLu q R)) → ℝ)
    (hr : ProfileRegular q R f) (u : TwistSpace q R) :
  ⟪u, corrDeriv q R f u⟫ = Dictionary.FreeSource.profileCoupling q R f u
```

`ProfileRegular` keeps three already-round-9-proved facts explicit: H continuity, C2 convergence and `HasDerivAt bulkD corrDeriv 0`. Their actual application is deferred as described below; **the compact theorem is not advertised as unconditional**.

`canonicalCoupling_of_curlDetected` takes `R2.KernelLine` and actual `CurlDetected`, selects the dictionary's physical adaptive profile, and obtains the original `CanonicalCoupling`. It uses the actual symmetric/U(1)-invariant derivative and a whole-kernel complex-line argument. `CofinalCurlLine` and `CofinalAnyPathCurlLine` are definitions of still-missing geometric premises. The corresponding compiled theorems imply the exact original `CofinalAnyProfileCoupling` / `CofinalAnyPathCoupling`, with `RegularityFacts` explicit.

### Physical-jet cofinal glue: five declarations

`JetGlue.lean` consumes the dictionary's `physicalJetAggregate` and `curlDetected_of_physicalJet`, rather than duplicating that proof. Its `CofinalJetLine` and `CofinalAnyPathJetLine` retain all cofinal/whole-kernel/path clauses and require one nonzero **physical** transverse jet aggregate. The two bridge theorems imply the curl-line premises under `FlatConstraintUnits`, a known round-9 property retained explicitly in the compact file.

The joint compact file contains the actual nonvanishing geometry/tiling/flux code and dictionary application. Assembly independently compiled those consumed bodies. Unused later nonvanishing neutral-functional conveniences and dictionary `TopJetDetected` conveniences are omitted; this is a dependency subset, not a modified operator. The named `TopJetDetected` predicate is definitionally the same indexed nonzero aggregate, as the standalone dictionary's `topJetDetected_iff` proves.

## Reviewed mathematics and what it removes

- Dictionary `SourceEnergy.source_sbp` is exact localized discrete summation by parts on the full torus. `inner_sourceLinear` extracts the E3 coefficient without requiring the entire field to be neutral.
- `FreeSource.profileCoupling_curl` identifies the explicit source pairing with twice the localized mixed curl sum. `adaptive_energy` makes it twice a sum of squares. Exterior masking is invisible on selected plaquettes.
- Nonvanishing `sum_Qfull_level_one` obtains the physical factor 1/8 times two fine-layer flux sums by actual even-site tiling and frozen Q1jet. Zero scalar curl makes transverse flux constant; level-zero constraints give a zero collar flux. A nonzero actual top-jet aggregate therefore forces selected nonzero curl.
- Dictionary `curlDetected_of_physicalJet` uses the full KKT QH identity. It needs neither compressed inverses nor a model source-column formula.

Therefore the preferred free-profile route no longer needs the R1 source-domination hypothesis, generalized tridiagonal source-column identification, tail estimates, or Bloch normalization proof. It STILL needs a nonzero actual crossing aggregate/curl, full-kernel definiteness and nested cofinality.

## Historical join — assembled, NOT compiled

`Attempt.lean` has **15524 lines**. It starts with the complete unchanged byte prefix of `AHP/round9/qualitative-r2/Attempt.lean` and retains the whole R2 assembly file as its prefix too. New bodies are appended with duplicate geometry declarations removed. No historical full-file compilation was attempted, following the coordinator's explicit 16 GiB/8 GiB cap instruction.

`GoalBridge.lean` contains the exact three-input specialization:

```lean
theorem regularityFacts : RegularityFacts := by
  intro q R hq hR hR18 f
  exact ⟨bulk_H_cont hq (by omega) (dil_admissible hq hR) f,
    bulk_C2_tendsto hq (dil_admissible hq hR) f,
    hasDerivAt_corrDeriv hq hR (by omega) f⟩
```

It then applies `corrDeriv_profile_form` and the original round-9 goal bridges. `HistoricalJetBridge.lean` similarly obtains the flat unit from `dil_N0_unit` and `dataFam_dil_zero`, then gives the conditional jet-line goal implications. **These exact final applications are not independently compiled here and have no claimed axiom audit.** Their text is also recorded in `shared/GAPS.md`. The coordinator explicitly approved this remaining verification boundary.

Even if that join compiles, it does not prove any missing cofinal premise. There is no unconditional GoalNeg2 declaration.

## Independent numerical cross-check

`numerics/energy_crosscheck.py` ran separately at 160 and 210 digits on held-out actual q=2,R=26, left-only twist, character (7,7). It reuses the frozen R6 transcription read-only and the previous assembly left-path construction; the new comparison independently evaluates local oriented circulation squares and solves the source-adjoint full KKT system.

- Crossing angle: 0.563971517985560942179715334362.
- Canonical coupling: −2.11990420173679913700776712786e−100, 143.15 relative digits of agreement.
- Scaled response energy: 13.9863753246574966997745240213, 142.77 relative digits of agreement.
- 210-digit direct-curl / source-reciprocity errors: 3.05e−210 / 1.38e−207.
- 210-digit full lift / source KKT residuals: 4.76e−207 / 1.05e−207.
- 210-digit null residual / |canonical coupling|: 3.25e−111.
- Restored cell-normalized adaptive coupling: 3.94679428561379363170952845221e−199.
- Peak RSS <896 MiB under a 2 GiB address-space cap; both runs exit 0.

The jets were scaled before the neutral solves, and the factor was explicitly restored. Numerical cell normalization is NOT identified with the physical Lean aggregate normalization. These are not interval enclosures, full-character screens, kernel definiteness or cofinal proofs. At 160 digits the unscaled null residual is about 1.18e−153, not the much smaller residual of the scaled neutral solve; these must not be conflated.

## Audit and reproduction

- `AUDIT.json`: successful source/log hashes, exits, all raw axiom records, 26-declaration list, verbatim-copy checks, historical-prefix evidence and remaining gaps.
- `COPIES.json`: exact operative-copy provenance and hashes.
- `build.py`: generates the compact and historical artifacts, writes only assembly-owned locations, and never compiles the historical file.
- `history/`: clearly labeled failed intermediate logs. These are not successful proof evidence.
- `numerics/SUMMARY.json`: reproducible cross-precision calculations and caveats.

Focused reproduction (compact files ONLY):

```sh
bash AHP/round10/assembly/r3/REPRODUCE.sh
```

The script uses the machine-wide two-slot wrapper sequentially and checks all six outputs. Use a long command timeout; if interrupted, inspect the corresponding `.exit` / running process before rerunning. Do not relaunch an active compilation.

To rerun the expensive numerics separately:

```sh
bb heavy run -- python3 AHP/round10/assembly/r3/numerics/energy_crosscheck.py --dps 160
bb heavy run -- python3 AHP/round10/assembly/r3/numerics/energy_crosscheck.py --dps 210
python3 AHP/round10/assembly/r3/numerics/summarize.py
```

## Exact unresolved work

See `shared/GAPS.md` for Lean statements of all cofinal premises and `KernelLine`.

1. Prove actual crossing `TopJetDetected` (or directly `CurlDetected`), not just nonzero vector or formal jet field.
2. Control the complete crossing kernel: one charged complex line or another rigorous common-sign argument. Symmetry and selected-sector numerical gaps do not suffice.
3. Obtain nested cofinal dyadic scales and even radii; no finite sample or one radius per scale suffices.
4. Compile the explicitly deferred historical regularity/unit/final goal join on an appropriate machine or split module setup.

No exact q=1 dilation, source recurrence at moving crossings, or full spatial covariance is assumed. R2's free-profile quantifier counterexample still applies: per-vector detection is not one-profile whole-kernel definiteness.
