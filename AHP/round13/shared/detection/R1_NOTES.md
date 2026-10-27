# Detection R1 — full flat guard closed; crossing jet still OPEN

## Verdict

**P3 is not proved, not disproved. GoalNeg2 and the requested cofinal premise remain open.**
This round closes the full flat `N`-unit prerequisite in a compact compilation,
and therefore removes that guard from the physical `TopJetDetected → CurlDetected`
handoff. It does not prove `TopJetDetected` for a right-star crossing generator.
The other new results precisely separate linear unique continuation from quadratic
jet nonvanishing. None is presented as an unconditional crossing result.

All writes are under `AHP/round13/detection/r1/` and
`AHP/round13/shared/detection/`. No earlier source, frozen module, lakefile,
commit, or push was changed. No large assembly, `lake build`, or reproduction
suite was run.

## Compiled artifacts

| Local | Published under `AHP/round13/shared/detection/` | Lines | Printed axiom records | Exit, local/shared |
|---|---|---:|---:|---|
| `FlatUnit.lean` | `R1_FlatUnit.lean` | 1175 | 4 | 0 / 0 |
| `JetBridge.lean` | `R1_JetBridge.lean` | 3577 | 226 | 0 / 0 |
| `Transfer.lean` | `R1_Transfer.lean` | 116 | 7 | 0 / 0 |
| `ColorTrace.lean` | `R1_ColorTrace.lean` | 373 | 24 | 0 / 0 |

Each source has its own `.lean.log` and `.lean.exit`. Local/shared sources are
byte-identical and each publication was compiled separately. These are builder
and publication executions, **not independent reviewer verification**. All
printed axiom sets are subsets of `{propext, Classical.choice, Quot.sound}`.
`AUDIT.json` records eight successful compiles, fifteen source-copy checks,
source/log hashes, and the individual new axiom records. `audit.py` passes.
Only frozen `DrEquiv` is imported; no AHP file is imported as an unbuilt module.

### 1. Unconditional full flat constraint unit

`AdalyFormal.Round13.Detection.flat_N_unit`,
`shared/detection/R1_FlatUnit.lean:1143`:

```lean
theorem flat_N_unit {q R : ℕ} (hq : 0 < q) (hR : 2 ∣ R) (hR18 : 18 ≤ R) :
    IsUnit (AdalyFormal.Round10.Dictionary.KKT.N
      (AdalyFormal.Round9.Guarded.AnalyticR2.flatData q R))
```

This is the **full** constraint matrix `(D.Q.comp D.G).comp D.Qs`, not a
nine-bond Schur compression. The compact reconstruction copies the historical
flat-carrier kernel proof and positivity proof from round 9, and the operative
`dataS`, `dilTower`, `flatData`, and `N` definitions verbatim from round-12 shared
files. It combines strict flat positivity, injectivity of the actual `Qs`, and
`isUnit_Q_inv_Qs`. No crossing, jet, eigenvalue estimate, or numerical premise
is used. This is a newly clean compact integration of historical facts, not a
new proof of their underlying geometry.

`cofinal_flat_N_units`, same file:1160, gives the nested dyadic/even statement
with `j := j₀` and `R := 2*(R₀+9)`. This closes only the flat guard, not P3.

Literal log line (`R1_FlatUnit.lean.log:1`):

```text
'AdalyFormal.Round13.Detection.flat_N_unit' depends on axioms: [propext, Classical.choice, Quot.sound]
```

### 2. Actual top-jet handoff without an external N-unit hypothesis

`AdalyFormal.Round13.Detection.curlDetected_of_topJet`,
`shared/detection/R1_JetBridge.lean:3540`:

```lean
theorem curlDetected_of_topJet {q R : ℕ} (hq : 0 < q) (hR : 2 ∣ R)
    (hR18 : 18 ≤ R) (u : TwistSpace q R) (hjet : TopJetDetected hq R u) :
    CurlDetected q R u
```

The file joins the existing genuine physical-jet dictionary with the proved
flat unit. The normalization, physical transverse cells, and `Wop` are those
of the original dictionary. **`hjet` remains a hypothesis.**

Literal log line (`R1_JetBridge.lean.log:363`):

```text
'AdalyFormal.Round13.Detection.curlDetected_of_topJet' depends on axioms: [propext, Classical.choice, Quot.sound]
```

`curlDetected_of_signed_top_row`, same file:3548, is a conditional sufficient
criterion: every actual neutral top-row cell has a common weak sign, and one
has strict sign. It retains `C2fullOf`, `Wop`, `iE`, and `topIdx` explicitly.
This does **not** establish the signs for a crossing. In fact the retained
numerics below argue against using this particularly strong criterion.

### 3. What two-layer continuation does and does not give

Namespace `AdalyFormal.Round13.Detection.Transfer`:

- `zero_prefix_of_zero_pair`, `R1_Transfer.lean:21`: for a finite module-valued
  recurrence `u (n+2) = a n • u (n+1) + b n • u n`, with nonzero `b n`, two
  adjacent zero observation layers force the entire preceding finite segment
  to vanish. No recurrence outside the finite segment is assumed.
- `pair_ne_zero_of_seed`: any nonzero source-side layer forbids the two
  observation layers from both vanishing. This does **not** identify the
  frozen carrier with such a recurrence, nor any nonzero quadratic observable.
- `area_step` and `area_ne_zero` (`:70`): for TWO scalar solutions with the
  same recurrence, the oriented area
  `x n * y (n+1) - y n * x (n+1)` evolves by multiplication by `-b n`.
  A nonzero **area seed**, not merely a nonzero vector, propagates.
- `decaying_trace_counterexample` (`:92`): `x n = (1/2)^n`, `y n = 0`
  satisfy `x(n+2) = (5/2)*x(n+1) - x(n)`, have nonzero linear trace at EVERY
  layer, and have zero area at EVERY layer. This is an exact algebraic example,
  **not** a claimed right-star kernel vector or counterexample to P3.

A potential area-based continuation route still needs BOTH a physical recurrence
identification and an identity identifying the actual top jet with an area
having a proved nonzero seed. Neither is supplied. The round-10 scalar
`RadiusRecurrenceData` is also still missing for the actual quadratic response
at the radius-dependent canonical root; it cannot be inferred from the mode's
linear recurrence. `R2_SourceFamily` separates a jet that is already nonzero;
it does not establish that input for the crossing.

### 4. Physical color obstruction to the proposed trace-only dictionary

`AdalyFormal.Round13.Detection.ColorTrace.flatJet_zero_of_pointwise_color`,
`R1_ColorTrace.lean:336`, proves for the actual frozen operators:

```lean
∀ {L : PeriodicLatticeExtent} (G : TowerGeom L) (a : ℝ)
  (u : ↥(bondSupp G)) (f : Bond L → ℝ),
  (∀ b, (u : BondFnL2 L) b = f b • pauliE1) →
  AdalyFormal.Round10.Dictionary.Color.flatJet G a u = 0
```

Thus arbitrary spatial variation in one charged color has zero full flat
dressed jet, not only the old isolated `oneColor` bond. The companion
`nonzero_trace_with_zero_jet` (`:357`) states that a nonzero value of `f` makes
`u` nonzero while its full jet remains zero. It uses the existing exact color
selection rule; no approximation, reduction to undressed fields, or flat
inverse hypothesis occurs. Neither theorem puts these fields in the crossing
kernel. The point is that a trace-only dictionary cannot hold for arbitrary
charged fields. Any valid use at the crossing must add crossing-specific
mixed-color information.

## Retained numerical evidence: cellwise sign route is too strong

No new eigenproblem or high-precision field solve was run. `audit.py` reads the
existing RIGHT-star `q=2,R=20` reports at 120 and 155 digits, hashes them, and
compares `max_abs_first_top_jet` with `abs(first_physical_top_jet_sums)`.
At BOTH precisions the ratios in directions 0,1,2 are approximately

```text
27.0668990694421, 1.62827660715810, 1.62840824834720
```

If all cell contributions had one sign, the absolute sum would be at least
the maximum absolute contribution. Here even the two positive tangential sums
are smaller than their largest cell magnitudes. Thus the retained floating-point
field has mixed cell signs; a proof by assigning one common sign to every
physical transverse cell is not supported. A sign proof would have to control
the **aggregate cancellations**, perhaps after a justified Fourier/symmetry
reorganization. This is a read-only analysis of old non-interval evidence,
**not** a Lean sign certificate, a new physical solve, or a cofinal conclusion.

## Exact remaining P3 — unchanged

Use the original shared-package opens:

```lean
open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.Round4.Guarded.RefuteR1
open AdalyFormal.Round5.Guarded.IVTR2
open AdalyFormal.Round9.Guarded.Qualitative
open AdalyFormal.Round9.Guarded.QualitativeR2
open AdalyFormal.Round9.Guarded.AnalyticR1 (TwistSpace)
open AdalyFormal.Round10.Assembly.R2 (KernelLine)
open AdalyFormal.Round10.Dictionary.FreeSource (CurlDetected)
open AdalyFormal.Round12.Noncancel.RightFamily (rightStar)
```

The requested unproved proposition, verbatim from round-12 GAPS:

```lean
∀ {q R : ℕ} (hq : 0 < q) (hR : 2 ∣ R) (hR18 : 18 ≤ R)
  (u : TwistSpace q R), KernelLine q R (rightStar hq R) u →
    CurlDetected q R u
```

By the newly compact unit/jet handoff it is sufficient to prove:

```lean
∀ {q R : ℕ} (hq : 0 < q) (hR : 2 ∣ R) (hR18 : 18 ≤ R)
  (u : TwistSpace q R), KernelLine q R (rightStar hq R) u →
    AdalyFormal.Round10.Nonvanishing.DilatedFlux.TopJetDetected hq R u
```

Equivalently for the proposed top-jet route, a genuine nonzero
`physicalJetAggregate hq hj u` at some `j < blockCount q R` is still needed.
`KernelLine` refers to the ORIGINAL canonical `vacEdge`; it must not be replaced
by a selected-character or arbitrary nonzero boundary vector.

The weaker cofinal sufficient family remains unproved as well:

```lean
∀ j₀ : ℕ, ∃ j : ℕ, j₀ ≤ j ∧ ∀ R₀ : ℕ, ∃ R : ℕ,
  R₀ ≤ R ∧ 2 ∣ R ∧ 18 ≤ R ∧
  ∃ u : TwistSpace (2^j) R,
    KernelLine (2^j) R (rightStar (by positivity) R) u ∧
    CurlDetected (2^j) R u
```

P1/P2 and their crossing-vector construction belong to the sibling tracks.
This track assumes none of them as an established fact. It supplies no
unconditional `KernelLine`, `CurlDetected`, response-noncancellation family,
or `GoalNeg2` inhabitant.

## Rebuild / verification

```sh
python3 AHP/round13/detection/r1/build_flat_unit.py
python3 AHP/round13/detection/r1/build_jet_bridge.py
python3 AHP/round13/detection/r1/build_color_trace.py
bb heavy run -- AHP/round3/lean1.sh AHP/round13/detection/r1/FlatUnit.lean
bb heavy run -- AHP/round3/lean1.sh AHP/round13/detection/r1/JetBridge.lean
bb heavy run -- AHP/round3/lean1.sh AHP/round13/detection/r1/Transfer.lean
bb heavy run -- AHP/round3/lean1.sh AHP/round13/detection/r1/ColorTrace.lean
python3 AHP/round13/detection/r1/audit.py
```

The publication audit also expects the four separately compiled shared files.
Do not recompile a timed-out job while it remains active; inspect its `.exit`.
Round 2 should target the actual mixed-color aggregate, not another abstract
linear-continuation lemma or an assumption of common sign across cells.
