# DECISION — guarded (item 5)

**Decision: `lean-comparison`. The guarded headline remains OPEN.**

Approve only an audit of the flat-interior exterior path: flat positivity, an in-class non-unit crossing on the existing slab family, and equality of the actual literal inverse operators on that path. Do not submit `GuardPencilT`, its negation, or `SepPathFamily2` as an expected Stage-B result. This is not `reading-only`: the remaining implication is a precise formal question. It is not `lean-counterexample`: no configuration with unit literal `Ginv` and singular corrected pencil was found. Nor does the proposed intermediate proof close the guarded headline.

## Decision against the attack and the sources

The attack's operator-transcription verdict stands, with the five corrections incorporated locally:

- **F1:** the retained probe grid uses the one-bond defect, not uniform direction-0 flux. At nonzero epsilon its local imaginary holonomy is not zero. Uniform-flux cancellation is a separate support check, reported by ATTACK, not output of the committed main.
- **F2:** `numerics/probe_results.json` is present after the attack's regeneration. The overlap numbers are now explicitly labelled hand-computed/reconstructed diagnostics, not scripted outputs. No new numerical replay was performed by this decision pass.
- **F3:** corrected the `pairBil`, `secondBilPlaq`, `bilPlaq` references to `DeltaPrimeOperator.lean:363,386,395`; flat positivity and form monotonicity are defined in `GdGap2.lean:42,125`.
- **F4:** the nonzero-epsilon flagged compressions already have negative carrier minimum. Indefiniteness is not non-invertibility, and a compression is not the full operator. These flags provide no separation certificate.
- **F5:** `AHP/attempts/sg-guarded/PencilPin.lean` is an uncompiled scalar draft, not certified lattice evidence.

The decision pass also found substantive omissions from both design and attack:

1. Flat positivity is **not a missing declaration**: `lean/src/D1Main.lean:66` already has `Fth_zero_psd`, and `lean/src/GdGap2.lean:42` covers any selectors. `D1Main.lean:141` already supplies the non-unit crossing under boundary-point hypotheses. The proposed slab result is a specialization/assembly of existing source, not new progress on the guard.
2. `lean/src/GdFam.lean:30`, `G1invS_eq_Ginv_theta`, already identifies literal `G1inv` with `Ginv` on this whole twist family under geometry hypotheses, **without assuming either is a unit**. Use that identity at singular points; do not apply `DrPath3.G1Lit_eq` there, since it requires `IsUnit Ginv`.
3. `lean/src/D1IVT.lean:86` exports only a non-unit point in the half-open interval. Its proof constructs a PSD point, but its statement exports neither PSD at that point nor a first-singularity characterization. No such extra conclusion is included below.
4. The kernel-visibility discussion is heuristic. A vanishing quadratic matrix element does not imply that the correction annihilates the vector; mixed blocks can shift roots. Neither a nonzero overlap nor a zero overlap alone establishes separated or coincident singularities. SPEC now flags this explicitly.

## Fidelity and non-vacuity limits

The numerical operators are only the plaquette curl-plus-correction operator on proper nonempty small boxes, not `Ginv`, `G1inv`, or `Delta2`. The small boxes do not inhabit the admissible in-regime hypothesis class. Their numerical kernels cannot be substituted into a guard argument.

The approved formal comparisons instead use the existing `Pth`, `dataS`, `G1invS` and `SlabNv`, with no invented replacement operators. The slab has `ell = 2`, `k = 2`, `a = 1`, `M = 2^m`, `m >= 1`, `R >= 18`. The source assembly at `lean/src/D1Final.lean:139–168` constructs admissibility, coverage, the boundary point, positive regularity parameter and the nonzero test-field package. `GdR5b.lean:80–140` additionally supplies guarded in-class points near zero at eventual thresholds. These are source-level witnesses to audit in Stage B, not a compilation claim by this pass. The crossing point itself deliberately **fails** the guard, so it cannot refute the guarded headline.

The full-guard statement in `SolR345Audit.full_guard_literal` is a different statement. None of these comparisons settle all inverses, the general non-flat-interior class, or the printed interpretation. Keep the distinction recorded in OPEN_ITEMS K–N and statement-sheet Part C row 7.

## Exact Stage-B signatures

Destination: `AHP/fidelity/guarded/lean/UthCross.lean`, only after the cold `REPRODUCE.sh` run has passed. These are **proposed signatures, not compiled declarations**. Use namespace `AdalyFormal.FidelityGuarded` with the following context; all target binders are explicit below.

```lean
open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLane2
open AdalyFormal.StatementLaneG
open AdalyFormal.StatementLaneR8
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.D1Literal
open AdalyFormal.D1Guarded
open AdalyFormal.NonVac
```

Suggested imports: `D1Main`, `D1Final`, `GdGap2`, `GdFam`, `GdR5b`, `GdR6a`, `GdR6b`. Avoid `DrSkeleton`. No imports from uncompiled AHP drafts.

### 1. Flat starting operator (audit wrapper)

```lean
Ginv_lit_psd_at_zero
    {ell k : ℕ} {Lu : PeriodicLatticeExtent}
    (hell0 : 0 < ell) (S : Tower (scaleUp ell k Lu))
    (a : ℝ) (Lam : Set (PeriodicLatticeSite Lu)) (ha : 0 ≤ a) :
    PSD (dataS selAll selAll (Pth ell k Lu hell0 S a Lam 0)).Ginv
```

Use `Ginv_psd_flat` directly or `Fth_zero_psd`. Do not present the wrapper as a newly discovered missing step.

### 2. In-class crossing, with the failed guard visible

```lean
Uth_hits_nonunit
    {m R : ℕ} (hm : 1 ≤ m) (hR : 18 ≤ R)
    {α₀ : ℝ} (hα : 0 < α₀) :
    ∃ θ : ℝ, 0 ≤ θ ∧ θ < Real.pi ∧
      ClassCoupled 2 (2 ^ m) 12 2 (SlabNv 2 (2 ^ m) R)
        α₀ (((2 : ℝ) ^ 2)⁻¹)
        (Uth ((SlabNv 2 (2 ^ m) R).Om 0) θ) ∧
      ¬ IsUnit
        (dataS selAll selAll
          (Pth 2 2 (nvLu (2 ^ m) R) (by norm_num)
            (SlabNv 2 (2 ^ m) R) 1 (LamN (2 ^ m) R) θ)).Ginv
```

Reuse the geometry and `exists_nonunit_Ginv` assembly from `D1Final`, then `perCubeRegular2_of_one_on_om0` for arbitrary positive `α₀`. Alternatively combine flat positivity, continuity and `domination_fails_pi`. Do not strengthen `0 ≤ θ` to `0 < θ` without separately establishing initial invertibility at the stated (not merely eventual) parameters.

### 3. Actual-operator no-separation comparison

```lean
Uth_singular_is_not_a_split
    {ell M R k : ℕ} {Lu : PeriodicLatticeExtent}
    (hell0 : 0 < ell) (S : Tower (scaleUp ell k Lu))
    (hS : Admissible ell M R k S) (h3 : 3 ≤ R * M)
    (a : ℝ) (Lam : Set (PeriodicLatticeSite Lu)) (θ : ℝ) :
    let P := Pth ell k Lu hell0 S a Lam θ
    (dataS selIn selIn P).Delta2 (dataS_laws selIn selIn P) = 0 ∧
    G1invS selAll selAll P = (dataS selAll selAll P).Ginv ∧
    (IsUnit (G1invS selAll selAll P) ↔
      IsUnit ((dataS selAll selAll P).Ginv -
        (dataS selIn selIn P).Delta2 (dataS_laws selIn selIn P)))
```

The local source vanishes because the interior plaquette holonomies are trivial. Derive the zero correction from its defining quadratic form and symmetry/uniqueness; `GdR6b.lean:40` is an alternative route. Obtain the literal operator equality from `G1invS_eq_Ginv_theta`, not from a conditional pencil identity. The final equivalence then follows by rewriting. Together these conclusions identify both operators with `Ginv`, including at the singular point of target 2.

## Acceptance and stopping rule

Compile the exact signatures in the destination file with `lake env lean` and print axioms for all three fully qualified names. Allow only `propext`, `Classical.choice`, `Quot.sound`, or subsets. No numerical claim is a proof; no declaration is accepted by this Stage-A record. Preserve the class membership in target 2 and do not insert invertibility as an extra premise to target 3.

After those checks, report only: **flat-path comparison audited; item 5 remains open**. Closing item 5 still requires an actual general guarded proof or an in-class, nonzero-test-field separation satisfying the necessary cofinal threshold quantifiers. A successful compilation of these wrappers must not be counted as that closure.

## Work performed in this decision pass

Read HANDOFF, OPEN_ITEMS B/K–N/R/S, the statement sheet, SPEC, ATTACK, and the cited source definitions relevant to the approved signatures. Corrected local SPEC and numerical-script citation text; inspected the retained numerical artifacts. Wrote this decision. No Lean, Lake, REPRODUCE, new numerical sweep, protected-file edit, commit, push, or deletion was performed.
