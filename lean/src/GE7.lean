import GE6
import GV13

/-!
# GE7 -- from the cover geometry to `gchart_at_bad_vertex` (m2_gluegeo, 2026-10-15)

`vertex_chart_of_tower`: at a vertex `v` of the `s = M ell^m` grid (anchor `x0 in Omega_{m+1}`, `pdist (iota v p) x0 + 18 s <= R s`
on the box) a class-cube regular configuration `PerCubeRegular2 ell M 12 k S alpha0 eta U` gives six half-space `GChart`s at the
common constants `t1 = 12 M alpha0 ell^{-m}`, `t2 = (1 + 4 t1) 12 M alpha0 ell^{-2m}` (the cubes have index `>= m`, GE4/GE5), hence --
by `gchart_at_bad_vertex` (GV13) -- one `GChart` on `iota v '' Box R'` at the GV13 constants.  The non-wrap hypothesis
`InjOn (iota v) (Box (R'+3))` is an explicit hypothesis (item (e)).  No sorry / axiom.
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace AdalyFormal.M2GlueGeo

open AdalyFormal.Target.ClayStatement AdalyFormal.M2Glue3 AdalyFormal.M2Glue2
open AdalyFormal.StatementLane AdalyFormal.StatementLane2
open AdalyFormal.Balaban.SuTwoLogExp (SU2 M2 coe_mul coe_inv)
open AdalyFormal.Balaban.RMapLipschitz (frobNorm)

variable {L : PeriodicLatticeExtent}

theorem Hraw_sub_HSlab {R' s : ℕ} (hR : R' + 3 ≤ s) (σ : Fin 3) (b : Bool) : Hraw R' σ b ⊆ HSlab s σ b := by
  intro p hp
  refine ⟨fun i => ?_, hp.2⟩
  have h := hp.1 i
  have : (R' : ℤ) + 3 ≤ s := by exact_mod_cast hR
  constructor <;> (have := abs_le.mp h; omega)

theorem cube_consts {c a_j a_m : ℝ} (hc : 0 ≤ c) (hj0 : 0 ≤ a_j) (hjm : a_j ≤ a_m)
    (hsm : c * a_m + c * a_m ^ 2 ≤ 1) :
    c * a_j + c * a_j ^ 2 ≤ 1 ∧ c * a_j ≤ c * a_m ∧
      (1 + 4 * (c * a_j)) * (c * a_j ^ 2) ≤ (1 + 4 * (c * a_m)) * (c * a_m ^ 2) := by
  have h1 : c * a_j ≤ c * a_m := mul_le_mul_of_nonneg_left hjm hc
  have h2 : a_j ^ 2 ≤ a_m ^ 2 := pow_le_pow_left₀ hj0 hjm 2
  have h3 : c * a_j ^ 2 ≤ c * a_m ^ 2 := mul_le_mul_of_nonneg_left h2 hc
  refine ⟨by linarith, h1, ?_⟩
  have h4 : 0 ≤ c * a_j ^ 2 := by positivity
  have h5 : 0 ≤ 1 + 4 * (c * a_j) := by positivity
  exact mul_le_mul (by linarith) h3 h4 (by have : 0 ≤ c * a_m := le_trans (by positivity) h1; linarith)

theorem vertex_chart_of_tower {ell M R k : ℕ} {S : Tower L} (hS : Admissible ell M R k S)
    (hcov : CoversOm0p ell M 12 k S) (hell : 2 ≤ ell) (hM : 0 < M) {m : ℕ} (hmk : m ≤ k)
    {x0 : PeriodicLatticeSite L} (hx0 : x0 ∈ S.Om (m + 1)) {v : PeriodicLatticeSite L}
    (hv : ∀ μ, (v μ).val % bigSide M ell m = 0)
    (hnear : ∀ p ∈ BoxS (bigSide M ell m), pdist (iota v p) x0 + 18 * bigSide M ell m ≤ R * bigSide M ell m)
    {α₀ η : ℝ} (hη : 0 < η) (hα : 0 ≤ α₀) {U : LinkCfg L} (hP : PerCubeRegular2 ell M 12 k S α₀ η U)
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
  have hcubes := slab_cube hS hcov hell hM hmk hx0 hv hnear
  have h : ∀ (σ : Fin 3) (b : Bool), ∃ g : PeriodicLatticeSite L → SU2,
      GChart U g (lift v (Hraw R' σ b)) ((12 : ℝ) * M * α₀ * ((ell : ℝ) ^ m)⁻¹)
        ((1 + 4 * ((12 : ℝ) * M * α₀ * ((ell : ℝ) ^ m)⁻¹)) * ((12 : ℝ) * M * α₀ * (((ell : ℝ) ^ m)⁻¹) ^ 2)) := by
    intro σ b
    obtain ⟨sites, j, hq, hjm, hall⟩ := hcubes σ b
    have hinv : (((ell : ℝ) ^ j)⁻¹) ≤ ((ell : ℝ) ^ m)⁻¹ := by
      have h1 : (1 : ℝ) ≤ ell := by exact_mod_cast hell0
      exact inv_anti₀ (by positivity) (pow_le_pow_right₀ h1 hjm)
    obtain ⟨hs1, ht1, ht2⟩ := cube_consts hc (by positivity) hinv hsm
    obtain ⟨g, hg⟩ := gchart_of_cube hη hP hq (by simpa [mul_assoc] using hs1) hell0
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
