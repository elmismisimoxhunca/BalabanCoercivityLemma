# Decision — s1-touching

**Route: `lean-comparison`. S-1 remains open.**

Advance the seven structural targets below, not `P428Target8Shell` and not a refutation of `P428Target8S selCorner selCorner`. This is neither a certified positive result nor a certified counterexample to the coercivity headline. No Lean, Lake, reproduction build, or numerical calculation was run in this decision pass.

## Why this route

The shell variant is honestly specified and has a viable flat non-vacuity construction, but it is **not the fully consistent literal touching reading** requested in OPEN_ITEMS S-1. `ReadBond` includes bonds with neither endpoint in the cube. It strengthens the CMP 102 bond condition; coverage remains frozen. A result about this repaired class must not close S-1 or be presented as the printed statement.

There are nevertheless exact formal comparisons worth checking. Shell regularity implies frozen regularity, the shell reads strictly more bonds than the endpoint convention on a concrete proper domain, and the corner selector cannot be obtained as `plaqIn` of any site set on that example. These are testable statements, so `reading-only` would discard genuine formal work. `lean-proof`/`lean-counterexample` would misleadingly promote the unsettled headline. The interpretation of the printed boundary prescription remains a separate reading question.

The smaller configuration class and larger plaquette selector do not give an implication between coercivity headlines. A negative raw Delta direction does not decide the gauge-fixed `genForm`. Nor does inequality of plaquette sets rule out every possible identity or inequality between forms on their relevant subspaces: it rules out the particular selector-identification route only.

## Repairs accepted and applied

`SPEC.md` now attributes the eigenmode decomposition to the existing `numerics/attack_check.json`, distinguishing the main-sequence configuration from the fresh-seed-0 configuration. These are inspected recorded reviewer measurements, not newly rerun measurements. Its unsupported assertion that weight-1 penalisation removes the pure-gauge part has been removed.

The six citation drifts identified in ATTACK were corrected in SPEC and, where present, in the `shell_touch.py` header: D1Eval:56; ClayStatement:1281; DeltaPrime:125/133; CovariantOperators:128 for the witness; D1Final:36 and :141. Script executable code and recorded numerical outputs are unchanged.

Further scope repairs in SPEC:

- Frozen coverage and the flat configuration supply non-vacuity; the outer-bond clause supplies control of additional links, not non-vacuity.
- No refutation of the frozen-class corner-selector headline is inferred from the old raw-Delta example.
- Random Cartan samples at caps pi/8 and 0.3 are transcription checks with positivity already forced by their pointwise caps. The gradient-constrained pi/4 conclusion is a Cartan-model analytic bound, with a single-bond numerical check, not a lattice-wide constrained spectral experiment.
- A full refutation must handle the headline's quantifier order **and** its actual form. These are not alternative requirements.
- Selector nonrepresentability does not exclude other analytic comparisons.

The attack's section 6 sentence saying the old configuration “leaves every TouchBond-only class” is reversed: the configuration changes only bonds with neither endpoint in Omega_0, so touching-only regularity can remain satisfied. The shell sees those links. No gauge-invariant exclusion of every shell representation at a given cap is inferred merely from the diagonal representative's phase bound.

## Stage-B definitions and import contract

Write only under `AHP/fidelity/s1-touching/lean/`, after the parent confirms the cold-build/reproduction gate has passed. Copy the exact definitions `TouchBond`, `plaqCorner`, `ReadBond`, `CurlReadsRead`, `PerCubeRegularShell`, and `ClassCoupledShell` from SPEC into namespace `Fidelity.S1`. Do not redefine coverage, cube sites, `Admissible`, or `LambdaOK2`. Do not introduce or prove the proposed coercivity headline for this comparison task.

Use imports `ZStatementP428`, `ZR2A`, `ZR6A`, `ZR2Ops2`, and `AdalyFormal.Target.ClayStatement`. The slab non-vacuity target additionally imports `D1Final` (which supplies `SlabNv` and imports `NV7`). `D1Lit`, `D1Path` and the raw-form calculations are not separate deliverables here. Add explicit opens rather than relying on opens in imported files:

```lean
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLane2
open AdalyFormal.StatementLaneG
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.D1Literal
open AdalyFormal.NonVac
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
open AdalyFormal.Balaban.RMapLipschitz (frobNorm)
open AdalyFormal.Balaban.CovariantHjMinimizer (periodicLatticeShiftBack)
```

Define these two concrete geometric objects inside `Fidelity.S1`:

```lean
def L6 : PeriodicLatticeExtent := fun _ => 5

def slab6 : Set (PeriodicLatticeSite L6) :=
  {x | (x 0).val < 2}
```

Here the side is six, not five. `slab6` is a proper nonempty two-site-wide slab; it is a selector-comparison example, **not** a small-torus instance of the full asymptotic headline. The independent slab-family target below addresses admissible-domain non-vacuity.

## Exact declaration statements for Stage B

The following are proposed signatures, not compiled declarations. All names are in `Fidelity.S1`; use the definitions and opens above. Preserve every quantifier and qualification.

### 1. Frozen bonds are read-bonds

```lean
lemma cubeBond_readBond
    {L : PeriodicLatticeExtent} {sites : Set (PeriodicLatticeSite L)}
    {e : Bond L} : CubeBond sites e → ReadBond sites e
```

No side-length assumption is needed: choose a direction different from that of the bond and put that edge in an ordered plaquette with its base corner in the set. This works even when a coordinate wraps degenerately.

### 2. Regularity inclusion

```lean
lemma perCubeRegularShell_toFrozen
    {L : PeriodicLatticeExtent} {ell M f k : ℕ} {S : Tower L}
    {α₀ η : ℝ} {U : LinkCfg L} :
    PerCubeRegularShell ell M f k S α₀ η U →
      PerCubeRegular2 ell M f k S α₀ η U
```

Reuse the same per-cube gauge and matrix field. Transfer both forward-difference hypotheses and each of the curl guards; do not check only the pointwise clause.

### 3. Coupled-class inclusion with frozen coverage

```lean
lemma classCoupledShell_toFrozen
    {L : PeriodicLatticeExtent} {ell M c k : ℕ} {S : Tower L}
    {α₀ η : ℝ} {U : LinkCfg L} :
    ClassCoupledShell ell M c k S α₀ η U →
      ClassCoupled ell M c k S α₀ η U
```

This is an inclusion for the explicitly stronger shell class with unchanged coverage. It does not settle S-2 for a different touching coverage definition and does not transfer the changed operators.

### 4. Flat configuration in every covered shell class

```lean
lemma classCoupledShell_one
    {L : PeriodicLatticeExtent} {ell M c k : ℕ} (S : Tower L)
    {α₀ η : ℝ} (hell : 0 < ell) (hM : 0 < M) (hc : 0 < c)
    (hα : 0 < α₀) (hη : 0 < η)
    (hcov : CoversOm0p ell M c k S) :
    ClassCoupledShell ell M c k S α₀ η (fun _ => 1)
```

Use gauge identically one and matrix field identically zero; the strict upper bounds require all the displayed positivity hypotheses. This target is conditional on coverage; the next target supplies coverage and proper-domain geometry rather than leaving it assumed.

### 5. Proper admissible covered shell family at arbitrarily small caps

```lean
lemma shell_slab_nonvacuous
    (M R : ℕ) (hM : 0 < M) (hdvd : 2 ∣ M) (hR : 18 ≤ R)
    (a₀ : ℝ) (ha₀ : 0 < a₀) :
    TorusOK 2 M (nvLu M R) ∧
    Admissible 2 M R 2 (SlabNv 2 M R) ∧
    LambdaOK2 2 M R 2 (SlabNv 2 M R) (LamN M R) ∧
    ((SlabNv 2 M R).Om 0).Nonempty ∧
    (SlabNv 2 M R).Om 0 ≠ Set.univ ∧
    ∃ α₀ : ℝ, 0 < α₀ ∧ (12 : ℝ) * (M : ℝ) * α₀ ≤ a₀ ∧
      ClassCoupledShell 2 M 12 2 (SlabNv 2 M R)
        α₀ (((2 : ℝ) ^ 2)⁻¹) (fun _ => 1)
```

Source scaffolding: `D1Final.lean:75` defines `SlabNv`; :78 supplies its boundary witness; :140–141 assemble admissibility and coverage; :163–164 use `torusOK_nv` and `lambdaOK2_nv`. Derive nonempty/proper from the boundary witness. Choose positive alpha below the cap and apply target 4. Every `M = 2^m` with `m ≥ 1` fits. This certifies a flat, depth-two family of hypothesis instances, not non-flat richness or the headline inequality. Do not replace it by a conditional non-vacuity claim with coverage or a proper-domain witness left unproved.

### 6. The shell is not the printed endpoint bond set

```lean
lemma readBond_not_touchBond_slab6 :
    ∃ e : Bond L6, ReadBond slab6 e ∧ ¬ TouchBond slab6 e
```

Use the direction-1 edge at `(2,0,0)`. It bounds the `(0,1)` plaquette based at `(1,0,0)`, which has a corner in the slab, while both edge endpoints have coordinate zero equal to 2 and lie outside the slab. This witnesses the precise extra regularity requirement.

### 7. Corner selection cannot be obtained by changing the site set

```lean
lemma no_plaqIn_eq_plaqCorner_slab6 :
    ¬ ∃ T : Set (PeriodicLatticeSite L6),
      plaqIn T = plaqCorner slab6
```

Any such T contains every corner of every selected plaquette. In particular, all four corners of the transverse `(1,2)` plaquette based at `(2,0,0)` are forced into T by adjacent `(0,1)` plaquettes based on the face at coordinate zero equal to 1. The transverse plaquette is therefore in `plaqIn T` but has no corner in `slab6`. Prove this finite geometric implication; do not enumerate all site subsets or infer it from floating-point output. No block-closure premise is necessary.

## Acceptance and remaining scope

For each of the seven declarations: compile its file with `lake env lean` only in Stage B and retain the exit status and `#print axioms` output. Every dependency must be among `propext`, `Classical.choice`, `Quot.sound`; an empty list is fine. No `sorry`, additional axiom, `native_decide`, or relaxed statement is acceptable. If a target fails, report it as unresolved rather than silently narrowing it.

No target above proves positivity for the corner operators, compares `genForm` numerically or formally, proves that the old configuration refutes the corner-selector headline, or answers the fully consistent endpoint/corner/coverage reading. The original S-1 question and the repaired shell coercivity question both remain open. Keep statement-sheet rows 5 and 7 open; no edits outside this target directory were made.
