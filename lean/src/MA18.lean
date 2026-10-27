import MA17
import DX6
import W4N3
import HB2

/-!
# MA18 -- `M1Core` / `M1Target` outright (lane m1_assembly_20261014)

`eps_choice`: pure real choice of `eps2s, epsJ`.  `m1Core_ell_a`: for `ell >= 2`, `a > 0` the headline quantifier order
`exists m0, forall m >= m0, exists R0, forall R >= R0, M1Core ell (ell^m) R a`.  `m1Target`: `M1Target`.
-/
set_option autoImplicit false
set_option maxRecDepth 8000
set_option maxHeartbeats 16000000
set_option synthInstance.maxHeartbeats 400000
namespace AdalyFormal.M1Assembly

theorem eps_choice (a cBm c1 c2 Q : ℝ) (ha : 0 < a) (hcB : 0 < cBm) (hc1 : 0 < c1) (hc2 : 0 < c2) (hQ : 0 < Q) :
    ∃ εJ ε2s : ℝ, 0 < εJ ∧ 0 < ε2s ∧ ε2s ≤ c1 ∧ ε2s < c2 ∧ ε2s / c1 ≤ 1 / 2 ∧
      (ε2s / c1 * a + 2 * εJ) * cBm ^ 2 ≤ Q := by
  have hcB2 : 0 < cBm ^ 2 := by positivity
  set q1 : ℝ := Q / (2 * (a + 1) * cBm ^ 2) with hq1
  have hq1p : 0 < q1 := by positivity
  set εJ : ℝ := Q / (4 * cBm ^ 2) with hεJ
  have hεJp : 0 < εJ := by positivity
  set ε2s : ℝ := min (c1 * min (1 / 2) q1) (c2 / 2) with hε2s
  have hp : 0 < ε2s := lt_min (mul_pos hc1 (lt_min (by norm_num) hq1p)) (by linarith)
  have hA : ε2s ≤ c1 * min (1 / 2) q1 := min_le_left _ _
  have hB : ε2s ≤ c2 / 2 := min_le_right _ _
  have hm1 : min (1 / 2) q1 ≤ 1 / 2 := min_le_left _ _
  have hm2 : min (1 / 2) q1 ≤ q1 := min_le_right _ _
  have hr : ε2s / c1 ≤ min (1 / 2) q1 := by rw [div_le_iff₀ hc1]; linarith
  refine ⟨εJ, ε2s, hεJp, hp, ?_, by linarith, hr.trans hm1, ?_⟩
  · have : c1 * min (1 / 2) q1 ≤ c1 * 1 := mul_le_mul_of_nonneg_left (hm1.trans (by norm_num)) hc1.le
    linarith
  · have h1 : ε2s / c1 ≤ q1 := hr.trans hm2
    have h2 : ε2s / c1 * a * cBm ^ 2 ≤ q1 * a * cBm ^ 2 := by
      apply mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h1 ha.le) hcB2.le
    have h3 : q1 * a * cBm ^ 2 ≤ Q / 2 := by
      rw [hq1]
      have : Q / (2 * (a + 1) * cBm ^ 2) * a * cBm ^ 2 = Q / 2 * (a / (a + 1)) := by field_simp
      rw [this]
      have : a / (a + 1) ≤ 1 := by rw [div_le_one (by linarith)]; linarith
      nlinarith
    have h4 : 2 * εJ * cBm ^ 2 = Q / 2 := by rw [hεJ]; field_simp; ring
    nlinarith

open AdalyFormal.M1IMS AdalyFormal.M1GaugeW4 AdalyFormal.TowerLoc in
open AdalyFormal.M1NonFlat (epsNF PkA thetaN) in
theorem cwW4_lower {ell M R d : ℕ} {a cW α₀ ε1 c δ : ℝ} (hε1 : 0 < ε1) (hα0 : 0 ≤ α₀)
    (hdD : epsNF ell (PkA a) (thetaN ell) d ≤ cW / 2)
    (hcs : 0 < csOf a (rhoT ell 12 M α₀))
    (hηlt : etaC ell (R * M * ell) (csOf a (rhoT ell 12 M α₀)) (rho1 12 M α₀) ε1 < 1)
    (hU : ∀ s x K : ℝ, |s| < δ → |x| < δ → |K| < δ → c ≤ AdalyFormal.M1Num.Psi ell a ε1 1 (min a (cW / 2)) s x K)
    (hs : |((12 : ℕ) : ℝ) * M * α₀| < δ) (hx : |((R * M * ell : ℕ) : ℝ)⁻¹| < δ) (hK : |KG ell M 1 5| < δ) :
    c ≤ cwW4 ell M 1 5 (R * M * ell) a (rhoT ell 12 M α₀) (rho1 12 M α₀) ε1 1
          (cPnf ell (R * M * ell) d a cW α₀ ε1 12 M)
          (epsXnum ell (R * M * ell) a (rhoT ell 12 M α₀)) (CMcStar ell M 1 5 a (SstarM ell 12 M α₀)) := by
  have hρ1 := rho1_nonneg 12 M α₀ hα0
  have hη0 := etaC_nonneg ell (R * M * ell) _ _ ε1 hε1 hρ1 hcs
  exact (hU _ _ _ hs hx hK).trans (cwW4_ge_Psi one_pos hdD hη0 hηlt)

end AdalyFormal.M1Assembly

#print axioms AdalyFormal.M1Assembly.eps_choice
#print axioms AdalyFormal.M1Assembly.cwW4_lower
