# Round 6 boundary placement — exact zero-correction obstruction

**closedGoal: `none`. GoalNeg2 remains open.**

The proposed relocation does not enlarge the correction overlap. For the constructed boundary-only curved family, the **genuine assembled correction is identically zero**. This is now a parametric Lean theorem, not a numerical sign estimate. A more general theorem rules out all bounded-mask placements confined to sufficiently separated outer boundary strips of this tower.

## 1. Formal result and verification

Final file: `AHP/round6/placement-r1/Attempt.lean`.

- The complete round-3 pin is its exact byte prefix.
- The complete round-5 `guarded/ivt-r2/Attempt.lean`, including the requested bridge, is also its exact byte prefix. The inherited `refute-r1` definitions and proofs are therefore retained verbatim.
- Sole import: frozen `DrEquiv`. No AHP imports or protected-source edits.
- Final wrapper exit **0**, no errors or warnings.
- Byte-identical `Attempt.verify.lean` replay: exit **0**, no errors or warnings. This is a builder replay, not an independent judge run.
- All **158 local declarations** have exact fully qualified dependency records. All **178 dependency records** in each log use only `propext`, `Classical.choice`, `Quot.sound`.
- `audit.py` checks both prefixes, imports, forbidden tokens, complete declaration coverage, dependencies, source/log/exit ordering, replay identity, and numerical records. See `CHECKS.json`.

Main general boundary-mask declaration, **line 2749**:

```text
'AdalyFormal.Round6.Guarded.PlacementR1.boundary_strip_correction_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
```

The direct family result is `placement_correction_zero` at **line 2502**; the exact non-separation theorem is `placement_guard_iff_pencil` at **line 2511**. Both have the same permitted dependency set.

Source SHA256:

```text
840438cdf7b48ac936939cecae20e6ec5b9f999a0ebb1258241ad3b28755b674
```

Both final log SHA256 values:

```text
cbb7801974ceb731d07bd4e6a4cd4ec6d8b728c0b0a99e46c721070d83fc9dd7
```

## 2. The new family really is curved and in the pinned class

Keep the exact original `dilLu`, `dilTower`, `dilLam`, and `dilBt`. Thus the fine sides are

\[
(q(12R+16),8q,8q),\quad
\Omega_0=[4q,(12R+12)q),\quad
\Omega_1=[(2R+4)q,(10R+12)q).
\]

The new `placementPattern` (`:2451`) puts the direction-1 `Ug epsilon` links at

\[
x_0=4q+2,\qquad x_1,x_2\text{ even}.
\]

All other non-exterior links are identity; exterior links are an arbitrary field V. The distance of the defect from the left face is **two fine sites**, independent of q and R. This is a new family, not the original defect at `(2R+4)q`. The two-site offset keeps the curved plaquettes away from the omitted exterior plaquettes; the broader strip theorem also covers defects directly at the face.

New exact facts:

| Declaration | Line | Content |
|---|---:|---|
| `placement_regular` | 2460 | Genuine per-cube regularity from the copied arbitrary-mask theorem, when `abs epsilon <= alpha/80`. |
| `placement_holonomy` | 2546 | The selected (0,1)-plaquette has word `(Ug epsilon)^(-1)`. |
| `placement_plaq_level0` | 2581 | Every endpoint of that plaquette lies in `Omega0 \\ Omega1`, for every q>0 and R>=6. |
| `placement_plaq_in` | 2609 | It belongs to the actual localized plaquette selector. |
| `placementU_curved` | 2615 | Nonidentity interior holonomy for `0 < epsilon < 1`. |
| `placementU_nonflat` | 2623 | An actual nonidentity interior bond. |
| `placementU_not_pure_gauge` | 2636 | No global gauge flattens the configuration. |
| `uniform_placement_class_family` | 2654 | TorusOK, Admissible, LambdaOK2, both coverage clauses via ClassCoupled, cap, full regularity, both competitor restrictions and positive energy; one amplitude allocation works for **every exterior V**. |
| `cofinal_curved_placement_no_separation` | 2691 | Cofinal m and R, radius before cap, the entire nonspectral certificate, and exact equivalence of carrier guard and corrected pencil for these witnesses. |

The cap proof uses the same original allocation

\[
\alpha=\tfrac12\min(a_0/(24q),1),\qquad \varepsilon=\alpha/160.
\]

The cofinal theorem chooses `m=m0+1`, `q=2^m0`, and `R=2*(R0+18)` **before receiving a0**. It does not choose R in response to a cap. No geometry, class or competitor condition is dropped. The cofinal existence theorem selects V=1; the stronger uniform class theorem and the zero-correction theorem hold for arbitrary V, including the exterior twist.

The proofs specific to the moved defect are new adaptations of the original four-link, gauge and cap proofs. The unmodified originals are still present above them. No spectral dilation assertion is made.

## 3. Why the correction vanishes

This uses the actual definitions, not a substitute curvature operator.

The frozen level-zero constraints are coordinate restrictions: `QlinB_zero` in `lean/src/ZXR2Sector.lean:69`. Their second jet vanishes: `C2CompL_zero` in `lean/src/ZLocJet.lean:118`, and `C2full_level0_inner` in `lean/src/GdTheta.lean:56`.

If the localized source is supported on level-zero bonds, the exact source factorization is

\[
J=Q^*j_0,\qquad \langle C^{(2)}(Wv),j_0\rangle=0.
\]

For the true constrained solution

\[
H=GQ^*(QGQ^*)^{-1},
\]

there are two exhaustive cases:

1. `QGQ*` is a unit. Then `QH=I`, so the source pairing is zero by the level-zero jet identity.
2. It is not a unit. Its totalized inverse is zero, hence H=0, and again the pairing is zero.

Therefore the actual symmetric correction satisfies

\[
\langle v,Dv\rangle=2\langle H C^{(2)}(Wv),J\rangle=0
\quad\text{for every }v,
\qquad D=0.
\]

The frozen abstract proof is `GdAbs.lean:38`, `Delta2_eq_zero`; this attempt proves its actual source-support premise for the new family.

### General local theorem

`correction_zero_of_flat_near_top` (`:2423`) proves the following for any admissible tower and actual selected assembly:

> If U is identity on every bond whose base is within periodic distance three of some site in Omega1, then the assembled correction is zero.

A carrier bond outside level zero has an endpoint in Omega1 (`GdGeo.lean:36`). The source at its base reads only distance-two neighborhoods (`GdGeo.lean:105`). The extra one is the endpoint shift. Thus every relevant source read is flat; the source vanishes on non-level-zero carrier bonds. This theorem has **no class-smallness, localized-unit or numerical premise**.

`placement_flat_near_top` (`:2473`) proves this flat-neighborhood hypothesis for the actual new placement at every q>0, even R>=6, every real epsilon, every V. It accounts for periodic wrap using the exact longitudinal periodic-distance bound.

### All boundary strips, not only one defect pattern

`boundary_strip_correction_zero` (`:2749`) takes arbitrary real mask f and arbitrary exterior V in the copied `maskedU` family. Assume

\[
d+3\le 2Rq,
\]

and f vanishes throughout the middle region

\[
4q+d\le x_0,\qquad x_0+d<12Rq+12q.
\]

Thus curvature may occupy **either outer strip of width d**, with any transverse pattern or signs, but not the intervening middle. The genuine correction is exactly zero. This is parametric in q, R, d, every amplitude and every exterior configuration. The copied `uniform_masked_class_family` supplies full-class small masks there.

`boundary_strip_guard_iff_pencil` (`:2780`) consequently proves the exact equivalence between the carrier unit and CPen for every such mask. `placement_pairing_zero` (`:2793`) gives the explicit zero pairing for every vector of the chosen family, whether or not it is a kernel vector.

The obstacle is therefore not a tiny positive coefficient. **There is no positive coefficient at all for boundary-only masks covered by this theorem.** Moving the curvature away from Omega1 removes its nonlinear correction contribution, although its holonomy stays nontrivial.

## 4. High-precision numerical check

`placement_probe.py` subclasses the supplied probe's read-only transcription, changing only the defect position to `4*q+2`. It retains the exact raw Taylor jets, localized plaquette/source assembly and the full neutral KKT solve. See `SOURCES.md` for operator-to-Lean line references.

| q | R | epsilon | independent precisions | source x-support | positive-level H*J | raw-jet/source pairing |
|---:|---:|---:|---|---|---:|---:|
| 1 | 18 | 1e-3 | 80 / 160 digits | 5,6,7 | 0 | 0 |
| 2 | 18 | 1e-100 | 160 / 240 digits | 9,10,11 | 0 | 0 |

The source is nonzero (12 cell entries), but all entries lie on level-zero bonds. Independently constructing the KKT solution with zero carrier/auxiliary variables and the source as its level-zero multiplier gives exactly zero residual in the mpmath assembly. The direct KKT solve also returns zero positive-level multiplier and zero residual in these samples.

The test pairing uses a general charged bond input. It is **not asserted to be Wv or an exact crossing vector**. No sector screening, carrier crossing, full-carrier unit, initial positivity or corrected PSD is inferred from this diagnostic. The numerical evidence is not an interval certificate or a formal Fourier dictionary. The Lean zero theorem, rather than the samples, covers all dressed inputs and all q,R,epsilon.

Maximum recorded RSS: **276144 KiB** (about 270 MiB). The imported transcription enforces a 7 GiB address-space ceiling; every job is below 8 GB. All numerical runs used the heavy scheduler, even though these source-only tests finished in a few seconds. Read-only imports had bytecode writing disabled.

## 5. Concrete remaining obstacle and scope

**No pinned goal is closed.** The proposed outer-placement mechanism is ruled out for the constructed family, and more generally for the separated boundary strips above. Neither the round-5 `InitialKernelControl` nor a different cofinal separating premise is proved.

In fact A-D=A for this family. Consequently neither a positive correction on an exact carrier kernel nor a PD-carrier/negative-corrected-form alternative can work here. Nontrivial boundary holonomy does not imply a nonlinear correction.

A future successful refutation must leave this no-go class, for example by retaining curvature near the positive-level nonlinear constraints while changing the carrier crossing geometry or another part of the family. This attempt supplies no such construction, no positive parametric sign theorem, and no answer to the unrestricted positive guarded statement. The original probe's negative tiny-amplitude result is not relabelled as a proof either.

## 6. Commands and hygiene

Only the requested wrapper was used for Lean, directly through the bash tool:

```sh
AHP/round3/lean1.sh AHP/round6/placement-r1/Attempt.lean
AHP/round3/lean1.sh AHP/round6/placement-r1/Attempt.verify.lean
PYTHONDONTWRITEBYTECODE=1 python3 AHP/round6/placement-r1/audit.py
```

Numerical runs (each with `PYTHONDONTWRITEBYTECODE=1 OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1`):

```sh
"$BB_CLI" heavy run -- python3 AHP/round6/placement-r1/placement_probe.py --q 1 --R 18 --eps 1e-3 --dps 80
"$BB_CLI" heavy run -- python3 AHP/round6/placement-r1/placement_probe.py --q 1 --R 18 --eps 1e-3 --dps 160
"$BB_CLI" heavy run -- python3 AHP/round6/placement-r1/placement_probe.py --q 2 --R 18 --eps 1e-100 --dps 160
"$BB_CLI" heavy run -- python3 AHP/round6/placement-r1/placement_probe.py --q 2 --R 18 --eps 1e-100 --dps 240
```

Two intermediate completed Lean exit-1 runs exposed elaboration errors (an unnecessary namespace opening, a zero-mask branch, a reducible parameter projection, and a set-membership simplification). They were repaired locally before the final successful compilations. Their incomplete declarations are not counted as results. No compilation timed out or was relaunched while pending.

The requested round-5 report and all five route NOTES, the verbatim pin, and round-6 probe report/dictionary were read. Every authored file is under `AHP/round6/placement-r1/`. No protected source, earlier round, lakefile, olean, paper, notes directory, expected, extras, git commit or push was touched. No deletion, terminal session, direct Lean/Lake command, build, dependency update or reproduction script was used.
