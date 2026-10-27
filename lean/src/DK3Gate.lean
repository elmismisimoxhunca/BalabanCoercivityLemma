import DK3Scales
import DK2DepthUnconditionalDepthUniformity
import SmoothHessian

/-! Proposition 1 is ONLY a regularity gate here; its ceiling is not gamma_2. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000
noncomputable section
attribute [local instance 10000] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra
namespace HConstruction.DK3
open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.SuTwoLogExp (SU2 M2 coe_mul coe_inv)
open AdalyFormal.Balaban.RMapLipschitz (frobNorm frobSq)
open DepthUniformity.Strided (orientedPlaqHolS)
open DepthUniformity.Fitted (SublatticePlaqBound)
open DepthUniformity.RawTower (etaSq)
open HConstruction.TransversePos (smooth_group_mul smooth_group_inv)

/-- Explicit admissible Prop1 constant, chosen independently of any coercivity gap. -/
def alpha0 : ℝ := 1/1000000

theorem alpha0_gates : 0 < alpha0 ∧
    4 * 44465 * alpha0 * (2:ℝ)^2 ≤ (2:ℝ)^2 - 1 ∧
    2 * alpha0 ≤ (400 * (2:ℝ)^2)⁻¹ := by norm_num [alpha0]

theorem smooth_U (b : AdalyFormal.Balaban.AdmissibleSubspace.Bond fineL) :
    ContDiff ℝ ⊤ (fun t => (U t b : M2)) := by
  by_cases hb : b = (origin,0)
  · simp only [U, hb]
    exact HConstruction.TransversePos.smooth_link_matrix
      (AdalyFormal.Balaban.AdmissibleSubspace.witnessY,0)
  · simp only [U, if_neg hb]
    exact contDiff_const

theorem smooth_fine_plaquette (y : FS) (μ ν : Fin 3) :
    ContDiff ℝ ⊤ (fun t => ((orientedPlaqHolS 1 (U t) y μ ν : SU2) : M2)) := by
  unfold orientedPlaqHolS
  exact smooth_group_mul (smooth_group_mul
    (smooth_group_mul (smooth_U _) (smooth_U _))
    (smooth_group_inv (smooth_U _))) (smooth_group_inv (smooth_U _))

private theorem continuous_frobNorm : Continuous (fun X : M2 => frobNorm X) := by
  unfold frobNorm frobSq
  apply Continuous.sqrt
  fun_prop

theorem fine_defect_continuous (y : FS) (μ ν : Fin 3) : Continuous
    (fun t => frobNorm (((orientedPlaqHolS 1 (U t) y μ ν : SU2) : M2) - 1)) :=
  continuous_frobNorm.comp ((smooth_fine_plaquette y μ ν).continuous.sub continuous_const)

theorem fine_defect_zero (y : FS) (μ ν : Fin 3) :
    frobNorm (((orientedPlaqHolS 1 (U 0) y μ ν : SU2) : M2) - 1) = 0 := by
  rw [U_zero, DepthUniformity.RawTower.orientedPlaqHolS_trivialU]
  simp

/-- Honest finite-volume shrink: all fine plaquettes are <= alpha0/64 on
one positive CLOSED interval. hfine is a conclusion, not an assumption. -/
theorem fine_radius_exists : ∃ r : ℝ, 0 < r ∧ ∀ t : ℝ, |t| < r →
    ∀ y μ ν, frobNorm (((orientedPlaqHolS 1 (U t) y μ ν : SU2) : M2) - 1)
      < alpha0 / 64 := by
  have he : ∀ᶠ t in nhds (0:ℝ), ∀ y μ ν,
      frobNorm (((orientedPlaqHolS 1 (U t) y μ ν : SU2) : M2) - 1) < alpha0 / 64 := by
    apply Filter.eventually_all.mpr
    intro y
    apply Filter.eventually_all.mpr
    intro μ
    apply Filter.eventually_all.mpr
    intro ν
    exact (fine_defect_continuous y μ ν).continuousAt.eventually
      (gt_mem_nhds (by
        dsimp only
        rw [fine_defect_zero]
        exact div_pos alpha0_gates.1 (by norm_num)))
  obtain ⟨r,hr,hs⟩ := Metric.eventually_nhds_iff.mp he
  exact ⟨r,hr,fun t ht => hs (by simpa only [dist_zero_right,Real.norm_eq_abs] using ht)⟩

def regularityRadius : ℝ := Classical.choose fine_radius_exists / 2

theorem regularityRadius_pos : 0 < regularityRadius :=
  half_pos (Classical.choose_spec fine_radius_exists).1

theorem fine_gate (t : ℝ) (ht : |t| ≤ regularityRadius) :
    ∀ y μ ν, frobNorm (((orientedPlaqHolS 1 (U t) y μ ν : SU2) : M2) - 1)
      ≤ alpha0 * etaSq 2 3 := by
  have hlt : |t| < Classical.choose fine_radius_exists := by
    have hp := (Classical.choose_spec fine_radius_exists).1
    change |t| ≤ Classical.choose fine_radius_exists / 2 at ht
    linarith
  intro y μ ν
  have h := ((Classical.choose_spec fine_radius_exists).2 t hlt y μ ν).le
  have he : alpha0 * etaSq 2 3 = alpha0 / 64 := by norm_num [etaSq, div_eq_mul_inv]
  rw [he]
  exact h

/-- Unconditional ell=2,k=3 regularity propagation on the actual U_t family.
No hProp1, hfine, hcontract or hc is left unpaid. No CubeClass is used. -/
theorem depth3_regularity (t : ℝ) (ht : |t| ≤ regularityRadius)
    (j : ℕ) (hj : j ≤ 3) :
    SublatticePlaqBound (2^j) (tower t j) (2 * alpha0) := by
  exact (DepthUniformityFinal.Assemble.unconditional_depth_uniformity 2 3
    (by norm_num) alpha0 alpha0_gates.1 alpha0_gates.2.1 alpha0_gates.2.2
    tiling.1 (U t) (fine_gate t ht) j hj).1

theorem current_background_regular (t : ℝ) (ht : |t| ≤ regularityRadius) :
    SublatticePlaqBound 8 (Vfine t) (2 * alpha0) :=
  depth3_regularity t ht 3 (by norm_num)
end HConstruction.DK3
