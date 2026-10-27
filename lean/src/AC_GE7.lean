import GE7
import AC_GE5
import AC_Base

/-! AC copy of GE7: affected declarations only (lane allc_20261016); 12 literal kept (control build). -/
set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace AdalyFormal.M2GlueGeo

open AdalyFormal.AllC
variable {fc : ℕ} [CubeFactor fc]

open AdalyFormal.Target.ClayStatement AdalyFormal.M2Glue3 AdalyFormal.M2Glue2
open AdalyFormal.StatementLane AdalyFormal.StatementLane2
open AdalyFormal.Balaban.SuTwoLogExp (SU2 M2 coe_mul coe_inv)
open AdalyFormal.Balaban.RMapLipschitz (frobNorm)

variable {L : PeriodicLatticeExtent}

theorem vertex_chart_of_towerAC {ell M R k : ℕ} {S : Tower L} (hS : Admissible ell M R k S)
    (hcov : CoversOm0p ell M fc k S) (hell : 2 ≤ ell) (hM : 0 < M) {m : ℕ} (hmk : m ≤ k)
    {x0 : PeriodicLatticeSite L} (hx0 : x0 ∈ S.Om (m + 1)) {v : PeriodicLatticeSite L}
    (hv : ∀ μ, (v μ).val % bigSide M ell m = 0)
    (hnear : ∀ p ∈ BoxS (bigSide M ell m), 2 * pdist (iota v p) x0 + 3 * (fc * bigSide M ell m) ≤ 2 * (R * bigSide M ell m))
    {α₀ η : ℝ} (hη : 0 < η) (hα : 0 ≤ α₀) {U : LinkCfg L} (hP : PerCubeRegular2H ell M fc 12 k S α₀ η U)
    (hsm : (12 : ℝ) * M * α₀ * ((ell : ℝ) ^ m)⁻¹ + 12 * M * α₀ * (((ell : ℝ) ^ m)⁻¹) ^ 2 ≤ 1)
    {R' : ℕ} (hR' : 1 ≤ R') (hRs : R' + 3 ≤ bigSide M ell m) (hinj : Set.InjOn (iota v) (Box (R' + 3)))
    (ht12 : (12 : ℝ) * M * α₀ * ((ell : ℝ) ^ m)⁻¹ ≤ 2)
    (hsmall : (4 * cB 1152 5 + 1) * (3 * (R' : ℝ) + 2) ^ 2 *
      ((1 + 4 * ((12 : ℝ) * M * α₀ * ((ell : ℝ) ^ m)⁻¹)) * ((12 : ℝ) * M * α₀ * (((ell : ℝ) ^ m)⁻¹) ^ 2)
        + 43 * ((12 : ℝ) * M * α₀ * ((ell : ℝ) ^ m)⁻¹) ^ 2) ≤ 1) :
    ∃ gv : PeriodicLatticeSite L → SU2,
      GChart U gv (lift v (Box R'))
        (KT1 4 1152 * (3 * R' + 2) * ((1 + 4 * ((12 : ℝ) * M * α₀ * ((ell : ℝ) ^ m)⁻¹)) *
          ((12 : ℝ) * M * α₀ * (((ell : ℝ) ^ m)⁻¹) ^ 2) + 43 * ((12 : ℝ) * M * α₀ * ((ell : ℝ) ^ m)⁻¹) ^ 2))
        (KT2 4 1152 * ((1 + 4 * ((12 : ℝ) * M * α₀ * ((ell : ℝ) ^ m)⁻¹)) *
          ((12 : ℝ) * M * α₀ * (((ell : ℝ) ^ m)⁻¹) ^ 2) + 43 * ((12 : ℝ) * M * α₀ * ((ell : ℝ) ^ m)⁻¹) ^ 2)) := by
  have hell0 : 0 < ell := by omega
  have hc : (0 : ℝ) ≤ 12 * M * α₀ := by positivity
  have hcubes := slab_cubeAC hS hcov hell hM hmk hx0 hv hnear
  have h : ∀ (σ : Fin 3) (b : Bool), ∃ g : PeriodicLatticeSite L → SU2,
      GChart U g (lift v (Hraw R' σ b)) ((12 : ℝ) * M * α₀ * ((ell : ℝ) ^ m)⁻¹)
        ((1 + 4 * ((12 : ℝ) * M * α₀ * ((ell : ℝ) ^ m)⁻¹)) * ((12 : ℝ) * M * α₀ * (((ell : ℝ) ^ m)⁻¹) ^ 2)) := by
    intro σ b
    obtain ⟨sites, j, hq, hjm, hall⟩ := hcubes σ b
    have hinv : (((ell : ℝ) ^ j)⁻¹) ≤ ((ell : ℝ) ^ m)⁻¹ := by
      have h1 : (1 : ℝ) ≤ ell := by exact_mod_cast hell0
      exact inv_anti₀ (by positivity) (pow_le_pow_right₀ h1 hjm)
    obtain ⟨hs1, ht1, ht2⟩ := cube_consts hc (by positivity) hinv hsm
    obtain ⟨g, hg⟩ := gchart_of_cubeH hη hP hq (by simpa [mul_assoc] using hs1) hell0 CubeFactor.pos
    refine ⟨g, hg.mono ?_ (by simpa [mul_assoc] using ht1) (by simpa [mul_assoc, pow_two] using ht2)⟩
    rintro _ ⟨p, hp, rfl⟩
    exact hall p (Hraw_sub_HSlab hRs σ b hp)
  choose g hg using h
  have ht1 : (0 : ℝ) ≤ (12 : ℝ) * M * α₀ * ((ell : ℝ) ^ m)⁻¹ := by positivity
  have ht2 : (0 : ℝ) ≤ (1 + 4 * ((12 : ℝ) * M * α₀ * ((ell : ℝ) ^ m)⁻¹)) * ((12 : ℝ) * M * α₀ * (((ell : ℝ) ^ m)⁻¹) ^ 2) := by
    positivity
  obtain ⟨gv, hgv, -⟩ := gchart_at_bad_vertex v hR' hinj g ht1 ht12 ht2 hg hsmall
  exact ⟨gv, hgv⟩

end AdalyFormal.M2GlueGeo

