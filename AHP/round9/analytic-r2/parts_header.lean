
/-!
Round 9 (analytic route, pass 2): the soft premise of pass 1 is a theorem.

Pass 1 (`AnalyticR1`) reduced `GoalNeg2` to `InteriorSoft ∧ VacuumLeftSpectral`.  This
appendix proves `InteriorSoft`: along the curved dilated family `ε ↦ dilU q R ε 1` (curvature
on the round-4 defect line, trivial exterior), for every scale `q > 0` and every even radius
`R ≥ 18`, the all-plaquette carrier and the dressing `W` are continuous at `ε = 0`, and the
localized correction satisfies `Δ⁽²⁾(ε)/ε → D₁`.  The proof is soft analysis of the frozen
assembly:
* the gauge projection is written with the frozen closed form `M1Site.Rproj_eq_strat`
  (`R = 1 - X Γ⁻¹ X*`), continuous where the Dirichlet operator and `Γ` are units;
* the raw blocking step is jointly smooth in (curvature, field) (the frozen `SG` calculus
  over the parameter space `ℝ × X`), so its first and second field jets are continuous;
* the localized source is smooth in the curvature and vanishes at the flat point;
* at the flat point the Dirichlet operator, `Γ` (frozen `MS6.exists_Gami_strat`) and `Q*`
  (frozen `W6F.qs_injective_strat`) are units/injective, and the flat localized carrier of
  the dilated tower is positive definite: a vanishing form forces a curl-free field, which
  is the gradient of an explicit longitudinal potential; the level-1 constraint rows
  telescope along the longitudinal chain of blocks, and the frozen final step applies.

Consequences: `goalNeg2_of_vacuumLeftSpectral : VacuumLeftSpectral → GoalNeg2` and
`cofinalTwistSeparation_of_twistVacuumCrossing : CofinalTwistVacuumCrossing →
CofinalTwistSeparation`.  Both premises are spectral statements about the vacuum (zero
curvature) operators only.

The remaining premise is then made explicit:
* the first-order coefficient of the correction has the quadratic form
  `⟪A, D₁ A⟫ = 2⟪H₀ C²₀(W₀ A), J'⟫` of the flat data (`dil_D1_form`, `vacCoupling`);
* the plaquette operator is smooth along smooth links (`contDiff_deltaKLocCLM`), so the vacuum
  carrier is differentiable in the exterior angle for the left and the round-8 twists
  (`hasDerivAt_extA_vac`): the angle derivative is computed, not assumed;
* at the trivial exterior field the vacuum all-plaquette carrier is positive definite
  (`extA_vac_one_pos`), so a crossing angle is never `0`.
Headline: `goalNeg2_of_vacuumLeftCouplingD : VacuumLeftCouplingD → GoalNeg2`, and for the
round-8 twist `cofinalTwistSeparation_of_twistVacuumCouplingD`.  The premise only asks, at
cofinal dyadic scales and radii, for a singular angle of the vacuum carrier at which the
computed angle derivative is negative definite on the kernel and the explicit coupling is
definite on the kernel.  Neither premise is proved here; no pinned goal is proved here.
-/
set_option autoImplicit false
