import MS10

/-!
# MS11 -- S2 and S3 under the stratified regime (no tower hypothesis)

With `ρ_T = (ℓ + 3πℓ²)ρ` and the MS9 regime (`hlink`, `hplaq`, collar `18 ≤ RM`, no wrap, `4·10⁶ℓ²ρ ≤ 1`), on `G = geomOf ℓ k S`:
* `hU_of_regime` : S1's in-block link hypothesis at `ρ_T`;
* **`isUnit_LP_M1`** (`216ρ_T² < 1`), **`gamma_lower_M1`**, **`exists_Gami_M1`** (S3), **`siteCT_inv_M1`** (S2).
-/
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 8000

namespace AdalyFormal.M1Site

open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.SiteCoercivity
open AdalyFormal.DLayer (siteWt)
open AdalyFormal.StatementLane (Tower Admissible)
open AdalyFormal.Balaban.AdmissibleSubspace (blockOf Bond)
open AdalyFormal.Balaban.CoarseCurl (coarseShift)
open AdalyFormal.Balaban.RMapLipschitz (frobNorm)
open AdalyFormal.CurvBlock (dv pw)

variable {Lf : PeriodicLatticeExtent}

theorem fac_ge_one (ell : ℕ) (hell : 2 ≤ ell) : 1 ≤ (ell : ℝ) + 3 * Real.pi * (ell : ℝ) ^ 2 := by
  have hellR : (2 : ℝ) ≤ ell := by exact_mod_cast hell
  have := Real.pi_pos; nlinarith

theorem hU_of_regime (ell M R k : ℕ) (hell : 2 ≤ ell) {S : Tower Lf} (hS : Admissible ell M R k S)
    (U : Cfg Lf) (ρ : ℝ) (hρ : 0 ≤ ρ)
    (hlink : ∀ j0, j0 ≤ k → ∀ b : Bond Lf, b.1 ∈ S.Om j0 → periodicLatticeShift b.1 b.2 ∈ S.Om j0 →
      dv (U b) ≤ ρ / (ell : ℝ) ^ j0) :
    ∀ j, j ≤ k → ∀ y ∈ (geomOf ell k S).Lam j, ∀ b ∈ inBlockBonds y (ell ^ j),
      frobNorm ((U b : Matrix (Fin 2) (Fin 2) ℂ) - 1) ≤ ((ell : ℝ) + 3 * Real.pi * (ell : ℝ) ^ 2) * ρ / (ell : ℝ) ^ j := by
  intro j hj y hy b hb
  have hell0 : 0 < ell := by omega
  rw [mem_inBlockBonds] at hb
  have h1 := hlink j hj b (block_sub_Om hell0 hS hj hy hb.1) (block_sub_Om hell0 hS hj hy hb.2)
  have hρρT : ρ ≤ ((ell : ℝ) + 3 * Real.pi * (ell : ℝ) ^ 2) * ρ := by
    have := fac_ge_one ell hell; nlinarith
  exact h1.trans (div_le_div_of_nonneg_right hρρT (by positivity))

section regime
variable (ell M R k : ℕ) (hell : 2 ≤ ell) {S : Tower Lf} (hS : Admissible ell M R k S)
  (hRM : 18 ≤ R * M) (hbig : ∀ σ, 4 * ell ^ k < Lf σ + 1)
  (U : Cfg Lf) (a : ℝ) (ha : 0 < a) (ρ : ℝ) (hρ : 0 ≤ ρ) (hsmall : 4000000 * (ell : ℝ) ^ 2 * ρ ≤ 1)
  (hlink : ∀ j0, j0 ≤ k → ∀ b : Bond Lf, b.1 ∈ S.Om j0 → periodicLatticeShift b.1 b.2 ∈ S.Om j0 →
      dv (U b) ≤ ρ / (ell : ℝ) ^ j0)
  (hplaq : ∀ j0, j0 ≤ k → ∀ (y : PeriodicLatticeSite Lf) (ν μ : Fin 3),
      y ∈ S.Om j0 → coarseShift y 1 ν ∈ S.Om j0 → coarseShift y 1 μ ∈ S.Om j0 →
      coarseShift (coarseShift y 1 ν) 1 μ ∈ S.Om j0 → dv (pw 1 U y ν μ) ≤ ρ / (ell : ℝ) ^ (2 * j0))
include hell hS hRM hbig hρ hsmall hlink hplaq

theorem isUnit_LP_M1 (h216 : 216 * (((ell : ℝ) + 3 * Real.pi * (ell : ℝ) ^ 2) * ρ) ^ 2 < 1) (ha : 0 < a) :
    IsUnit (LP (geomOf ell k S) U a) := by
  have hell0 : 0 < ell := by omega
  have hρT : 0 ≤ ((ell : ℝ) + 3 * Real.pi * (ell : ℝ) ^ 2) * ρ := mul_nonneg (by linarith [fac_ge_one ell hell]) hρ
  exact isUnit_LP_strat ell k hell (hdvd_of_admissible hS) (properTower_geomOf hell0 hS) U a ha _ hρT h216
    (hU_of_regime ell M R k hell hS U ρ hρ hlink)
    (hT_of_regime ell M R k hell hS hRM hbig U ρ hρ hsmall hlink hplaq)

theorem gamma_lower_M1 (h216 : 216 * (((ell : ℝ) + 3 * Real.pi * (ell : ℝ) ^ 2) * ρ) ^ 2 < 1) (ha : 0 < a)
    (v : YP (geomOf ell k S)) :
    (1 - 6 * (((ell : ℝ) + 3 * Real.pi * (ell : ℝ) ^ 2) * ρ)) ^ 2 *
        ∑ p, ‖v p‖ ^ 2 / betaS (geomOf ell k S) ell a (((ell : ℝ) + 3 * Real.pi * (ell : ℝ) ^ 2) * ρ) p
      ≤ (12 + a) * ‖Xop (geomOf ell k S) U a v‖ ^ 2 := by
  have hell0 : 0 < ell := by omega
  have hρT : 0 ≤ ((ell : ℝ) + 3 * Real.pi * (ell : ℝ) ^ 2) * ρ := mul_nonneg (by linarith [fac_ge_one ell hell]) hρ
  have h6 : 6 * (((ell : ℝ) + 3 * Real.pi * (ell : ℝ) ^ 2) * ρ) ≤ 1 := by nlinarith
  exact gamma_lower_strat hell (properTower_geomOf hell0 hS) (hdvd_of_admissible hS) U a ha _ hρT
    (hU_of_regime ell M R k hell hS U ρ hρ hlink)
    (hT_of_regime ell M R k hell hS hRM hbig U ρ hρ hsmall hlink hplaq) h6
    (isUnit_LP_M1 ell M R k hell hS hRM hbig U a ρ hρ hsmall hlink hplaq h216 ha) v

theorem exists_Gami_M1 (h216 : 216 * (((ell : ℝ) + 3 * Real.pi * (ell : ℝ) ^ 2) * ρ) ^ 2 < 1) (ha : 0 < a) :
    ∃ Gi : YP (geomOf ell k S) →L[ℝ] YP (geomOf ell k S),
      (∀ u, (ContinuousLinearMap.adjoint (Xop (geomOf ell k S) U a) ∘L Xop (geomOf ell k S) U a) (Gi u) = u) ∧
      (∀ u, Gi ((ContinuousLinearMap.adjoint (Xop (geomOf ell k S) U a) ∘L Xop (geomOf ell k S) U a) u) = u) := by
  have hell0 : 0 < ell := by omega
  have hρT : 0 ≤ ((ell : ℝ) + 3 * Real.pi * (ell : ℝ) ^ 2) * ρ := mul_nonneg (by linarith [fac_ge_one ell hell]) hρ
  exact exists_Gami_strat ell k hell (hdvd_of_admissible hS) (properTower_geomOf hell0 hS) U a ha _ hρT h216
    (hU_of_regime ell M R k hell hS U ρ hρ hlink)
    (hT_of_regime ell M R k hell hS hRM hbig U ρ hρ hsmall hlink hplaq)

theorem siteCT_inv_M1 (ha : 0 < a) (hu : IsUnit (DelpA (geomOf ell k S) U a + (1 - siteMask (geomOf ell k S).Om0)))
    (φ : PeriodicLatticeSite Lf → ℝ) (θ : ℝ) (hθ : 0 ≤ θ)
    (hφ : ∀ b : Bond Lf, periodicLatticeShift b.1 b.2 ∈ (geomOf ell k S).Om0 →
      |φ b.1 - φ (periodicLatticeShift b.1 b.2)| ≤ θ / (ell : ℝ) ^ stratG (geomOf ell k S) (periodicLatticeShift b.1 b.2))
    (δ0 : ℝ) (hδ0 : 0 ≤ δ0)
    (hbox : ∀ j, j ≤ k → ∀ y ∈ (geomOf ell k S).Lam j, ∀ x ∈ blockOf y (ell ^ j), |φ x - φ y| ≤ δ0)
    (c : ℝ) (hc0 : 0 ≤ c)
    (hc : c ≤ (1 / 2) * ((1 - 216 * (((ell : ℝ) + 3 * Real.pi * (ell : ℝ) ^ 2) * ρ) ^ 2) / max 6 (16 / (3 * a)))
      - (9 * (Real.exp θ - 1) ^ 2 + 3 * a * (Real.exp δ0 - 1) ^ 2))
    (g : SiteL2 Lf) :
    c * wNormSq (geomOf ell k S) (siteWt φ (Gp (geomOf ell k S) U a (siteWt (-φ) g)))
        ≤ ⟪siteWt φ (Gp (geomOf ell k S) U a (siteWt (-φ) g)), siteMask (geomOf ell k S).Om0 g⟫
      ∧ c ^ 2 * wNormSq (geomOf ell k S) (siteWt φ (Gp (geomOf ell k S) U a (siteWt (-φ) g)))
        ≤ dualNormSq (geomOf ell k S) g := by
  have hell0 : 0 < ell := by omega
  have hρT : 0 ≤ ((ell : ℝ) + 3 * Real.pi * (ell : ℝ) ^ 2) * ρ := mul_nonneg (by linarith [fac_ge_one ell hell]) hρ
  exact siteCT_inv_strat ell k hell (hdvd_of_admissible hS) (properTower_geomOf hell0 hS) U a ha _ hρT
    (hU_of_regime ell M R k hell hS U ρ hρ hlink)
    (hT_of_regime ell M R k hell hS hRM hbig U ρ hρ hsmall hlink hplaq) hu φ θ hθ hφ δ0 hδ0 hbox c hc0 hc g

end regime

#print axioms fac_ge_one
#print axioms hU_of_regime
#print axioms isUnit_LP_M1
#print axioms gamma_lower_M1
#print axioms exists_Gami_M1
#print axioms siteCT_inv_M1

end AdalyFormal.M1Site
