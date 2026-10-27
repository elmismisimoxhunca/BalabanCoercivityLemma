# Noncancellation, round 1: finite exterior star

## Status

**The cofinal noncancellation premise is neither proved nor disproved. GoalNeg2 is not closed.**

The deliverable is a compact, compiled package of local frozen-operator identities, a whole-kernel trace criterion, and an actual finite-star path with a negative endpoint. The crucial application of trace-zero positivity at the crossing and crossing-specific jet detection remain open. No numerical result below is a certificate.

## Compiled artifacts

- `Attempt.lean`: 692 lines; sole import `DrEquiv` from frozen `lean/src`.
- Byte-identical publication: `AHP/round12/shared/noncancel/R1_Star.lean`, independently compiled through the required wrapper.
- Both have `.lean.log`, `.lean.exit` equal to `0`, and `.lean.resources.json`.
- `StarKernel.lean`, `Plaquette.lean`, and `Trace.lean` also compile independently, each with fresh log/exit/resource files.
- `AUDIT.json` checks all five files, all printed dependency lists, forbidden proof tokens, the import, and byte identity. The publication has **53 axiom records**, each a subset of `propext`, `Classical.choice`, `Quot.sound`.
- These are builder compilations, including the separate publication compile, not acceptance by an independent reviewing agent.
- Published SHA-256: `5754fb31d94f89ff3a5860f7bab10a3f05d2a080a138f06371a6662b5db2bb12`.

Names below have prefix `AdalyFormal.Round12.Noncancel.`; line numbers refer to the publication.

| Declaration | Line | What is actually proved |
|---|---:|---|
| `Star.pair_completion` | 33 | Exact two-leaf completion of the square |
| `Star.star_mass_lower` | 52 | Sum of disjoint leaf-mass inequalities |
| `Star.kernel_line_of_trace` | 88 | Positive zero fiber of one complex linear trace plus quarter-turn equivariance forces the **whole** kernel into a charged line |
| `Star.positive_on_trace_zero` | 129 | Conditional local-form criterion for that positivity |
| `Plaquette.frozen_three_form` | 236 | Actual frozen curl plus one-half `bilPlaq`, with the exterior second atom zero |
| `Plaquette.frozen_three_form_right` | 258 | Corresponding identity with the exterior fourth atom zero |
| `Plaquette.frozen_two_form` | 280 | First normal atom and exterior second atom zero |
| `Trace.physical_kernel_line` | 351 | Actual touching-bond carrier trace and actual constant-gauge quarter rotation; positivity and commutation remain assumptions |
| `Path.starPath` | 434 | Four-link equal-angle transverse star at one physical site |
| `Path.starPath_an` | 452 | Analytic family in the **verbatim original** `AnFam` definition |
| `Path.starPath_off_exterior` | 472 | Identity away from purely exterior bonds under slab transversality |
| `Path.star_negative_endpoint` | 527 | Actual frozen all-plaquette `Ginv` has a negative direction at pi, for the star immediately outside a right boundary point satisfying `BdPt` |
| `Gauge.star_all_comm` | 660 | Actual frozen star operator commutes with every constant diagonal gauge |
| `Gauge.star_kernel_line` | 673 | For this actual operator, trace-zero positivity and a nonzero kernel vector imply full charged-line containment; commutation is discharged |

The decisive dependency lines are:

```text
'AdalyFormal.Round12.Noncancel.Path.star_negative_endpoint' depends on axioms: [propext, Classical.choice, Quot.sound]
'AdalyFormal.Round12.Noncancel.Gauge.star_kernel_line' depends on axioms: [propext, Classical.choice, Quot.sound]
```

The analytic definitions `AnM`, `AnFam` are copied verbatim from the round-10 assembly. The all-plaquette covariance proof is copied from `R1_Dictionary.lean`, but only frozen operators are imported. No earlier-round file is imported or compiled by this work.

## Candidate and exact mechanism

For an exterior site \(x\), twist by \(u_t\) the transverse links based at \(x\) and \(x-e_d\), \(d=1,2\), and leave all other links at identity. The numerical site is the left exterior site \((4q-1,0,0)\). Its four carrier-relevant straddling plaquettes share one incoming normal bond, with eight distinct other carrier bonds.

For ordered charged atoms, the proven local form is

\[
Q_{c,s}(x,y,z)=c|x+y+z|^2+
2s\operatorname{Im}(\bar x y+\bar x z+\bar y z).
\]

When the central normal coordinate vanishes, only two atoms remain. If \(c^2+s^2=1\),

\[
|y|^2+|z|^2+Q_{c,s}(0,y,z)
=c(|y|^2+|z|^2)+|y+(c-is)z|^2.
\]

Thus for \(0<c\leq1\), one should be able to retain a positive fraction of the actual level-zero leaf masses. Neutral fields must also be handled: vanishing of the complex trace does **not** mean the entire central Lie-algebra value vanishes. Neutral positivity and charged/neutral orthogonality, plus the remaining flat form, are part of the still-unproved physical application. One must also justify that `W u` agrees with `u` on the nine-bond boundary patch for arbitrary carrier fields, not merely prove `W=id` on the proposed trial field. The natural positive base is the actual flat localized carrier form: its interior plaquettes are unaffected, and the exterior-star leaf masses should come from its level-zero mass rows.

The trace theorem avoids an all-character simplicity proof. Positivity on its zero fiber makes the trace injective on the entire real kernel. The actual quarter rotation multiplies this trace by \(i\); injectivity then gives \(J^2u=-u\) on the kernel and expresses every kernel vector as a real combination of \(u,Ju\). No global assumption \(J^2=-I\) is made (it is false on neutral fields).

### Important side distinction

The numerical candidate uses the **left** boundary. `star_negative_endpoint` uses a **right** `BdPt`, so that the frozen single-bond support, mass, and gauge-fixing theorems apply directly. It proves a real result for that right star, but **no reflection equivalence between these two paths has been formalized**. Do not combine the left numerical crossing/jet with the right endpoint theorem as if they were one proved family. The left plaquette holonomy is \(u_{-t}\), so its local dictionary has \(s=-\sin t\); the right formula has \(s=\sin t\). Both completion-of-square identities tolerate either sign.

## Actual endpoint theorem: hypotheses remain visible

`Path.star_negative_endpoint` assumes an admissible tower, `2 <= ell`, `17*ell <= R*M`, a right `BdPt`, `0 <= a < 4`, and a nonzero Lie-algebra value. Its operator is exactly

```lean
(dataS selAll selAll (gparams ell k Lu hell0 S
  (starPath (periodicLatticeShift x 0) Real.pi) a Lam)).Ginv
```

It proves an actual negative direction, using frozen `delta_value`, `Wop_sing`, `Tfull_sing_zero`, and `Mass_sing_le`. This does **not** prove the first crossing lies below pi/2, specialize the dyadic geometry, or establish `CurlDetected`.

The stronger pi/2 trial remains a model calculation: central normal amplitude 1, four adjacent normal amplitudes of magnitude 1/4 with imaginary signs, and one boundary tangential amplitude of magnitude 1/4. The proved polynomial is

\[
E(a,b)=1+16a^2-8a-2b+4b^2,
\qquad E(1/4,0)=0,\quad E(1/4,1/4)=-1/4.
\]

Its **physical** field identification, `W=id`, `T=0`, mass bookkeeping, and full plaquette sum are not proved. The q=2 numerical full-carrier calculation does verify the proposed energies and a zero gauge right-hand side, but that is evidence only.

## Numerical evidence

The full flat augmented resolvent is reconstructed from **all** transverse characters into the physical nine-bond boundary resolvent. This is not a selected-character crossing calculation. The scripts reuse the round-6 numerical operator transcription; no Lean equivalence or interval enclosure is supplied.

| Case | Charged root | Next Schur eigenvalue | Neutral first root |
|---|---:|---:|---:|
| q=1, R=18, uniform star | 1.20798785641901928304390613798561910599321772929534432491798… | 0.932012806275816171530438663313 | 1.7601668108… |
| q=2, R=18, uniform star, 64 characters | 1.208030537534755 | 0.9318300997626887 | 1.7601821139136906 |

For q=2,R=18, the two physical trial energies at pi/2 were `-1.78e-15` and `-0.24999999999999734`, versus the model values 0 and -1/4. The gauge right-hand-side maximum was exactly zero in the numerical representation. Linear residual: `7.77e-16`; peak RSS: 519636 KiB.

For q=1,R=18, separate 60- and 80-digit physical reconstructions agree on the first top-jet aggregates. At 80 digits, directions 0,1,2 give respectively:

```text
1.00872731019313957002672536705643637e-41
4.87537241179701197924455983068841923e-40
4.87537242990790989060629186728086880e-40
```

The 80-digit linear residual is `1.1478e-76`, the boundary null residual `4.1935e-80`, and peak RSS 293516 KiB. These tiny nonzero values are stable under the precision increase but are **not** proved to be the normalized Lean `physicalJetAggregate` or to persist cofinally.

Files: `star_q1_R18.json`, `star_q2_R18.json`, `starjet_q1_R18_p60.json`, `starjet_q1_R18_p80.json`, with corresponding `.log`/`.exit`. The single-link precursor `single_q1_R2.json` did not cross in its exploratory scan; it does not disprove an existential path premise. The alternative site-gauge sign pattern crosses sooner but has not been analyzed for invisibility and is not the preferred candidate.

## Exact remaining Lean statements

The ultimate open declaration is:

```lean
AdalyFormal.Round10.Assembly.R4.CofinalAnyPathNoResponseCancellation
```

A sufficient open declaration, with the original quantifiers, is:

```lean
AdalyFormal.Round10.Assembly.R3.CofinalAnyPathCurlLine
```

Expanded verbatim in its original namespace context, this is:

```lean
∀ j₀ : ℕ, ∃ j : ℕ, j₀ ≤ j ∧ ∀ R₀ : ℕ, ∃ R : ℕ,
  R₀ ≤ R ∧ 2 ∣ R ∧ 18 ≤ R ∧
  ∃ V : ℝ → LinkCfg (scaleUp 2 1 (dilLu (2^j) R)),
    AdalyFormal.D1Literal.ContFam V ∧ AnFam V ∧ V 0 = (fun _ => 1) ∧
    (∃ w, ⟪w, vacA (2^j) R V 1 Real.pi w⟫ < 0) ∧
    ∃ u : TwistSpace (2^j) R, KernelLine (2^j) R V u ∧ CurlDetected (2^j) R u
```

For **one consistently chosen** physical star family `V` and central normal bond `b`, the outstanding local statements in the original round-9/10 context are:

```lean
-- A physical pi/2 trial, not just Star.starTrialEnergy:
∃ w : TwistSpace q R, ⟪w, vacA q R V 1 (Real.pi/2) w⟫ < 0

-- Range of the actual psdEdge used by vacEdge:
0 < vacEdge q R V ∧ vacEdge q R V < Real.pi/2

-- Positivity on the complete real carrier, not just a charged Fourier block:
∀ u : TwistSpace q R,
  AdalyFormal.Round12.Noncancel.Trace.bondTrace
    (geomOf 2 1 (dilTower q R)) b u = 0 → u ≠ 0 →
  0 < ⟪u, vacA q R V 1 (vacEdge q R V) u⟫

-- Nonzero actual crossing witness:
∃ u : TwistSpace q R, u ≠ 0 ∧ vacA q R V 1 (vacEdge q R V) u = 0

-- The crossing-specific detection input (hq : 0 < q):
∃ u : TwistSpace q R, KernelLine q R V u ∧
  AdalyFormal.Round10.Nonvanishing.DilatedFlux.TopJetDetected hq R u
```

These are obligations with `q,R,V,b` fixed to the proposed family; they are not assertions for arbitrary paths. `TopJetDetected` implies `CurlDetected` through `Dictionary.JetDetection.curlDetected_of_topJet` once the genuine flat KKT `N` unit hypothesis is discharged. The same family must satisfy the unbounded dyadic-scale and even-radius quantifiers. Neither two tested scales nor one stable tiny jet replaces this step.

The kernel track's `Actual.kernelLine_of_boundary_positive` separately connects the same complete-carrier positivity criterion directly to the original `R2.KernelLine`. Our package supplies the local form identities and genuine star symmetry/path facts; it does not supply that physical positivity hypothesis.

## Reproduction and resource audit

From the repository root:

```bash
python3 AHP/round12/noncancel/r1/assemble.py --publish
for f in StarKernel Plaquette Trace Attempt; do
  python3 AHP/round12/noncancel/r1/verify_one.py AHP/round12/noncancel/r1/$f.lean
done
python3 AHP/round12/noncancel/r1/verify_one.py AHP/round12/shared/noncancel/R1_Star.lean
python3 AHP/round12/noncancel/r1/audit.py
```

`verify_one.py` invokes **only** `bb heavy run -- AHP/round3/lean1.sh <file>` for compilation, inside an ephemeral systemd scope with `MemoryMax=8G`, swap disabled. The wrapper itself limits global Lean concurrency to two. Recorded per-command peak child RSS remains below 8 GiB. Earlier address-space/data-limit attempts failed while mapping frozen mathlib files; they were not proof successes. Fresh successful logs overwrite those development failures.

Numerical reproduction (the imported numerical harness enforces a 2-GiB address-space cap):

```bash
bb heavy run -- python3 AHP/round12/noncancel/r1/star_probe.py --q 2 --R 18
bb heavy run -- python3 AHP/round12/noncancel/r1/star_jet_probe.py --q 1 --R 18 --dps 60
bb heavy run -- python3 AHP/round12/noncancel/r1/star_jet_probe.py --q 1 --R 18 --dps 80
```

No large round-9/10 file, build, or REPRODUCE script was compiled/run by this track. No edits were made to earlier rounds, frozen Lean sources, the lakefile, or the integration checkout. Pre-existing checkout changes remain untouched. Coordinator evidence in `shared/COORDINATOR.md` additionally reports that the large round-10 join has missing-helper errors, not merely a memory obstruction; this work does not repair or certify that join.
