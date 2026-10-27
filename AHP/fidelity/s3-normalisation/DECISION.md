# DECISION — s3-normalisation

**Decision: `lean-comparison`. Reject the proposed matrix witness as a faithful S-3 counterexample.**

Send the structural comparisons below to Stage B, not `NoScalar.lean` as an S-3 closure. S-3 remains unresolved: the printed interpretation is a reading question, and comparison with the actual operators remains a formal task once that interpretation is fixed. This is not `reading-only`, because the proposed witness has a directly testable structural defect.

## Decisive defect missed by the attack

The witness takes k = 1 and assigns nonzero second jets to levels 0 and 1. The actual level-0 second jet is identically zero:

- `lean/src/ZLocJet.lean:104-105`: `D2CompL ... 0 = 0` by its recursive definition.
- `lean/src/ZLocJet.lean:115-120`: `C2CompL` and `C2CompL_zero`.
- `lean/src/ZXR2Sector.lean:83-89`: `C2rawB` and `C2rawB_eq` transfer that zero to the bond-field representation.
- `lean/src/CvS2a.lean:107-116`: `data_C2_lvl0` already carries it through the actual wired data, including `Wop`.

The SPEC's lower-level raw directions `(1,0,0,0)` and `(0,1,1,0)` with strength 1/10 therefore cannot be level-0 jets of these operators, for any background. This is not a small-torus or smallness caveat. In addition, `QlinB ... 0 A = A` (`ZXR2Sector.lean:70-71`); the arbitrary two-row level-0 stand-in is not accompanied by a representation identifying it with the actual restricted identity.

Consequently the sentence “a universal scalar identity for these weights would have to hold for every full-rank jet” is not justified for S-3. The actual jets are not arbitrary full-rank data. The header of `ZXG3A.lean` explicitly describes genuine ingredients, not a quantification over all ingredient families. Positive definite stand-in matrices establish algebraic non-vacuity, not realizability by a `LinkCfg`, tower, or printed test field.

At k = 1 the SPEC's own level-0-zero control removes the plainH discrepancy. More strongly, with the actual raw jets its plainH coefficient and its uniformBody coefficient agree at both permitted levels: level 0 because the raw jet vanishes, level 1 because eta = ell^-1. This is an exact structural comparison selected below. It does **not** certify plainH as the correct page reading.

## Assessment of Grok and Kimi

The rational matrix calculations survive, but Kimi's fidelity verdict does not. They are useful evidence against an identity for unrestricted abstract jets only. Do not promote them to a refutation of the normalisation of the genuine frozen first term or the printed form.

Other qualifications:

1. The stand-in has no printed support, axial-gauge or Q_1 B = 0 subspace. An identity needed only on that subspace need not hold for every arbitrary model B. The attack's assertion that the unrestricted identity is necessarily required is too strong.
2. The three coefficient recipes are specified mathematical alternatives, not an exhaustive derivation of the print. In particular, the argument of C_j in (3.14) is L^j eta A. Tracking its quadratic coefficient requires tracking that change of variable. The p.421 paragraph also offers two linked H/C conventions. Merely multiplying the second-order coefficient of the left-hand side of (3.14) by L^j eta does not independently identify the C_j^(2)(A) used on p.421. Read `sources/corpus/pages/CMP99b_p393.md` and `CMP99b_p421.md` together before accepting a recipe.
3. The SPEC's Stage B instruction “positive-definiteness ... or an exhibited inverse” conflates two properties: an inverse establishes nonsingularity, not positivity. Any future matrix diagnostic claiming positivity needs positive leading minors with symmetry, or another valid positivity certificate.
4. The actual `Jf` is minus `JSU2Loc 1`, with a chart explanation (`ZXR2Wire2.lean:45-53`). The arbitrary J in this witness is not a background-derived source. Citation of the scale alone is not an operator realization.
5. Changing site recursion coefficients from (3.24) in a flat bond-mass stand-in does not settle the constant-a bond term (3.16), nor the units of all terms of (3.156).

## Numerical recheck

Reran the unchanged `numerics/attack_check.py` with a virtual-memory cap of 3,906,250 KiB (4,000,000,000 bytes), one BLAS/OMP thread and bytecode writing disabled. It completed within the 30-second command limit. This is a four-coordinate rational model, not a torus run.

Output: `numerics/decision_check.txt`: **38 checks PASS**, followed by `ALL CHECKS PASSED` (the attack's “37/37” count is stale). The exact ratio pairs and the plainH top-only equality reproduce. This is evidence, not proof, and cannot cure the structural defect.

## Exact Stage B targets

File: `AHP/fidelity/s3-normalisation/lean/JetBoundaryComparison.lean`.
Import `ZXR2Sector`; namespace `AdalyFormal.AHP.FidelS3Normalisation`.
Open `AdalyFormal.Target.ClayStatement`, `AdalyFormal.IngredientFamilyR2`, and `AdalyFormal.Balaban.CovariantOperators (BondFnL2)`.

The following are requested declaration signatures, not compiled results:

```lean
raw_level_zero
    {L : PeriodicLatticeExtent} (G : TowerGeom L) (U : Cfg L)
    (A : BondFnL2 L) :
    C2rawB G U 0 A = 0

linear_level_zero
    {L : PeriodicLatticeExtent} (G : TowerGeom L) (U : Cfg L)
    (A : BondFnL2 L) :
    QlinB G U 0 A = A

plainH_eq_uniformBody_at_depth_one
    {L : PeriodicLatticeExtent} (G : TowerGeom L) (U : Cfg L)
    (A : BondFnL2 L) (j : ℕ) (hj : j ≤ 1) :
    (((G.ell : ℝ)⁻¹) ^ 2) • C2rawB G U j A =
      (G.ell : ℝ)⁻¹ •
        ((((G.ell : ℝ) ^ j)⁻¹) • C2rawB G U j A)
```

The last signature compares exactly the two recipes at depth one; it asserts nothing about a full Schur complement. It needs no class or inverse hypothesis and therefore introduces no empty class as a shortcut. Proof route: split j = 0 or 1; use raw_level_zero in the first case and scalar multiplication associativity in the second. The first two signatures are direct checks against existing definitions, not new analytic content.

Do not add the three matrix `no_scalar_*` statements to the accepted targets. Their independent algebraic interest does not justify a fidelity-counterexample label. Do not replace the actual jets by axiomatized arbitrary matrices to make an approved target pass.

After the reproduction prerequisite passes, compile this file from the existing Lake project context and print axioms for all three declarations. Accept only subsets of `propext`, `Classical.choice`, `Quot.sound`. No Lean, Lake or reproduction command was run in this decision stage.

## What remains before S-3 can be closed

Fix a full printed-unit dictionary for Q, adjoints and pairings, H, C^(2), J, and the top-level embedding; then compare with the genuine data, including the mass subtraction, nonlinear J term and bondEnergy. A nonzero lower-level second jet would require depth at least two and actual composite-jet/background realization, not merely renaming this matrix example's levels. Alternatively, prove the comparison on the actual admissible test subspace. Until then neither the success of uniformBody nor failure of the three unrestricted stand-ins settles the printed normalisation.

Only this decision and its numerical log were written; frozen sources and manuscript files were left untouched.
