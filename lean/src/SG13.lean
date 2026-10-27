import SG12
import W4N2

/-!
# SG13 -- numeric windows and torus facts for the field-level statements (lane m2_fields123_20261015)
-/
set_option autoImplicit false
set_option maxHeartbeats 16000000
set_option maxRecDepth 8000
set_option synthInstance.maxHeartbeats 400000
namespace AdalyFormal.M2F123

open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.TowerLoc (rho1)
open AdalyFormal.NonflatJet (r0 r0_pos)
open SmallnessBridge.Assemble (loopFactorBound)

/-- the smallness bundle consumed by `siteS1_of_charts`, `rowBound_of_charts`, `massComm_of_charts` (all in terms of `α' = ℓ³·2α₀`) -/
theorem window (ell : ℕ) (hell : 2 ≤ ell) :
    ∃ s : ℝ, 0 < s ∧ ∀ (M : ℕ) (α₀ : ℝ), 0 ≤ α₀ → (12 : ℝ) * M * α₀ ≤ s →
      (12 : ℝ) * M * ((ell : ℝ) ^ 3 * (2 * α₀)) ≤ 1 ∧
      4000000 * (ell : ℝ) ^ 2 * rho1 12 M ((ell : ℝ) ^ 3 * (2 * α₀)) ≤ 1 ∧
      (1 + 3 * Real.pi) * rho1 12 M ((ell : ℝ) ^ 3 * (2 * α₀)) ≤ 1 / (1000 * (ell : ℝ) ^ 4) ∧
      Real.pi / 2 * ((loopFactorBound ell : ℝ) * ((1 + 3 * Real.pi) * rho1 12 M ((ell : ℝ) ^ 3 * (2 * α₀)))) < r0 := by
  have hl : (2 : ℝ) ≤ ell := by exact_mod_cast hell
  have hC : (0 : ℝ) < (ell : ℝ) ^ 3 := by positivity
  have hlf : (0 : ℝ) ≤ (loopFactorBound ell : ℝ) := Nat.cast_nonneg _
  have hr0 := r0_pos
  set C : ℝ := (ell : ℝ) ^ 3 with hCdef
  have hK1 : (0 : ℝ) < 2 * C := by positivity
  have hK2 : (0 : ℝ) < 160000000 * (ell : ℝ) ^ 2 * C := by positivity
  have hK3 : (0 : ℝ) < 520000 * C * (ell : ℝ) ^ 4 := by positivity
  have hK4 : (0 : ℝ) < 2080 * ((loopFactorBound ell : ℝ) + 1) * C := by positivity
  refine ⟨min (min (1 / (2 * C)) (1 / (160000000 * (ell : ℝ) ^ 2 * C)))
      (min (1 / (520000 * C * (ell : ℝ) ^ 4)) (r0 / (2080 * ((loopFactorBound ell : ℝ) + 1) * C))), ?_, ?_⟩
  · refine lt_min (lt_min (by positivity) (by positivity)) (lt_min (by positivity) (by positivity))
  intro M α₀ hα hx
  set x : ℝ := 12 * M * α₀ with hxdef
  have hx0 : 0 ≤ x := by positivity
  have e1 : (12 : ℝ) * M * (C * (2 * α₀)) = 2 * C * x := by rw [hxdef]; ring
  have hrho : rho1 12 M (C * (2 * α₀)) ≤ 20 * (12 * M * (C * (2 * α₀))) := AdalyFormal.M1W4Num.rho1_le M _ (by positivity)
  have hrho0 : 0 ≤ rho1 12 M (C * (2 * α₀)) := AdalyFormal.TowerLoc.rho1_nonneg 12 M _ (by positivity)
  rw [e1] at hrho
  have hxa : x ≤ 1 / (2 * C) := le_trans hx (le_trans (min_le_left _ _) (min_le_left _ _))
  have hxb : x ≤ 1 / (160000000 * (ell : ℝ) ^ 2 * C) := le_trans hx (le_trans (min_le_left _ _) (min_le_right _ _))
  have hxc : x ≤ 1 / (520000 * C * (ell : ℝ) ^ 4) := le_trans hx (le_trans (min_le_right _ _) (min_le_left _ _))
  have hxd : x ≤ r0 / (2080 * ((loopFactorBound ell : ℝ) + 1) * C) := le_trans hx (le_trans (min_le_right _ _) (min_le_right _ _))
  have ha' := (le_div_iff₀ hK1).1 hxa
  have hb' := (le_div_iff₀ hK2).1 hxb
  have hc' := (le_div_iff₀ hK3).1 hxc
  have hd' := (le_div_iff₀ hK4).1 hxd
  have hpi := Real.pi_lt_four
  have hpi0 := Real.pi_pos
  refine ⟨by rw [e1]; nlinarith, ?_, ?_, ?_⟩
  · have : 4000000 * (ell : ℝ) ^ 2 * rho1 12 M (C * (2 * α₀)) ≤ 4000000 * (ell : ℝ) ^ 2 * (20 * (2 * C * x)) :=
      mul_le_mul_of_nonneg_left hrho (by positivity)
    nlinarith
  · rw [le_div_iff₀ (by positivity)]
    have h13 : (1 + 3 * Real.pi) * rho1 12 M (C * (2 * α₀)) ≤ 13 * (20 * (2 * C * x)) :=
      mul_le_mul (by linarith) hrho hrho0 (by norm_num)
    nlinarith
  · have h13 : (1 + 3 * Real.pi) * rho1 12 M (C * (2 * α₀)) ≤ 13 * (20 * (2 * C * x)) :=
      mul_le_mul (by linarith) hrho hrho0 (by norm_num)
    have h2 : (loopFactorBound ell : ℝ) * ((1 + 3 * Real.pi) * rho1 12 M (C * (2 * α₀)))
        ≤ (loopFactorBound ell : ℝ) * (13 * (20 * (2 * C * x))) := mul_le_mul_of_nonneg_left h13 hlf
    have h3 : Real.pi / 2 * ((loopFactorBound ell : ℝ) * ((1 + 3 * Real.pi) * rho1 12 M (C * (2 * α₀))))
        ≤ 2 * ((loopFactorBound ell : ℝ) * (13 * (20 * (2 * C * x)))) :=
      mul_le_mul (by linarith) h2 (by positivity) (by norm_num)
    have hx0' : 0 ≤ (loopFactorBound ell : ℝ) * C * x := by positivity
    nlinarith

/-- torus facts from `TorusOK` -/
theorem torus_facts {ell m k : ℕ} {Lu : PeriodicLatticeExtent} (hell : 2 ≤ ell) (hm : 6 ≤ m)
    (hT : TorusOK ell (ell ^ m) Lu) :
    (∀ μ, 5 ≤ Lu μ + 1) ∧ (∀ σ : Fin 3, 1 ≤ scaleUp ell k Lu σ) := by
  have hM : 5 ≤ ell ^ m := by
    have h1 : ell ^ 6 ≤ ell ^ m := Nat.pow_le_pow_right (by omega) hm
    have h2 : 4 ≤ ell ^ 2 := by nlinarith
    have h3 : ell ^ 6 = ell ^ 2 * ell ^ 4 := by ring
    have h4 : 1 ≤ ell ^ 4 := Nat.one_le_pow _ _ (by omega)
    nlinarith
  have h5 : ∀ μ, 5 ≤ Lu μ + 1 := fun μ => le_trans hM (Nat.le_of_dvd (by omega) (hT.2.2 μ))
  refine ⟨h5, fun σ => ?_⟩
  have hell0 : 0 < ell := by omega
  have := AdalyFormal.M2UnitCharts.scaleUp_succ ell k Lu hell0 σ
  have hp : 1 ≤ ell ^ k := Nat.one_le_pow _ _ hell0
  have : 5 * 1 ≤ (Lu σ + 1) * ell ^ k := Nat.mul_le_mul (h5 σ) hp
  omega

theorem pow_ge {ell m : ℕ} (hell : 2 ≤ ell) (hm : 6 ≤ m) : 4 * ell + 30 ≤ ell ^ m := by
  have h1 : ell ^ 6 ≤ ell ^ m := Nat.pow_le_pow_right (by omega) hm
  have h2 : ell ^ 6 = ell * ell ^ 5 := by ring
  have h3 : 32 ≤ ell ^ 5 := by
    calc 32 = 2 ^ 5 := by norm_num
      _ ≤ ell ^ 5 := Nat.pow_le_pow_left hell 5
  nlinarith

end AdalyFormal.M2F123

#print axioms AdalyFormal.M2F123.window
#print axioms AdalyFormal.M2F123.torus_facts
#print axioms AdalyFormal.M2F123.pow_ge
