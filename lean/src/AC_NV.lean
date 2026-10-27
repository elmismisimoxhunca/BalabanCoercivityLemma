import MC1b
import ZR2B4

/-!
# AC_NV -- the hypotheses of `CoercG8At` at cube factor `c` are satisfiable for EVERY `c >= 10`, every `R`, every `M` (lane allc_20261016)

Answer to "do class cubes of factor `c` exist inside admissible towers when `c` is much larger than `R`": yes -- the full tower (`Omega_j = torus`, `j <= k`) is admissible for every `R`,
`Lambda = univ` is `LambdaOK2`, the class cubes of index `k` tile the torus (`fullTower_coversp`, any `c >= 2`), and every non-flat `Ufield eta chi` with `|chi| <= alpha0 eta^2 / 10`
is in `PerCubeRegular2` (`ufield_perCubeRegular2`, any `f >= 10`).  So the statement cannot become vacuous (nor can coverage fail) as `c` grows.
-/
set_option autoImplicit false
namespace AdalyFormal.AllC

open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane AdalyFormal.StatementLane2 AdalyFormal.StatementLaneG AdalyFormal.IngredientFamilyR2
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)

theorem classHyps_nonvacuous (ell M R k c : ℕ) (hell : 0 < ell) (hM : 0 < M) (hc : 10 ≤ c) (Lu : PeriodicLatticeExtent)
    (hT : ∀ μ : Fin 3, M ∣ Lu μ + 1) {α₀ : ℝ} (hα : 0 < α₀) (hk : 1 ≤ k)
    (χ : Bond (scaleUp ell k Lu) → ℝ) (hχ : ∀ e, |χ e| ≤ α₀ * (((ell : ℝ) ^ k)⁻¹) ^ 2 / 10) :
    Admissible ell M R k (fullTower ell k Lu) ∧
    LambdaOK2 (Lu := Lu) (Lf := scaleUp ell k Lu) ell M R k (fullTower ell k Lu) Set.univ ∧
    ClassCoupled ell M c k (fullTower ell k Lu) α₀ (((ell : ℝ) ^ k)⁻¹) (Ufield (((ell : ℝ) ^ k)⁻¹) χ) :=
  ⟨AdalyFormal.M0Corollary.fullTower_admissible ell M R k hell hk Lu hT,
   AdalyFormal.M0Corollary.univ_lambdaOK2 ell M R k hell Lu,
   ⟨AdalyFormal.M0Corollary.fullTower_coversp ell M c k hell hM (by omega) Lu hT,
    ufield_perCubeRegular2 hell hM hc _ hα χ hχ⟩⟩

end AdalyFormal.AllC

#print axioms AdalyFormal.AllC.classHyps_nonvacuous
