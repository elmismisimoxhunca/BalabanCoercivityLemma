import RKN2
import RKB
/-!
# RKF -- `ginv_coercive_M0_kuniform`: the M0 coercivity theorem with a k-UNIFORM regularity threshold, every `ell ≥ 2`.

The crude, k-exponential field `hregthr : ∀ j<k, (8ell−6)(blkConstOf ell^j · e) < r0` of ASC5 `M0Regime` is REPLACED by
`KUSmall ell ρ` (ρ = `rhoM0 ell k e q0` = `ell^k e + 3π ell^{2k} q0`), three conditions on `(ell, ρ)` only:
  `8 ell κ̂ ≤ 1/(8π)`,   `Kc² (ρ/(3π) + ρ²) ≤ 1`,   `(8 ell − 6) κ̂ < r0`,     `κ̂ = 2ρ + Kc (ρ/(3π) + ρ²)`,
`Kc ell = 7 sig ell / (ell² − lamK ell)` (RKN2), `lamK ell = ell + 3(ell−1)²/ell` (RKL3).  No `k`, no volume.
Source of the all-bond regularity: RKN2 `regTower_allbond` (truncated seam bonds included).
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace AdalyFormal.RegBgKU

open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.StatementLane (scaleUp)
open AdalyFormal.SliceCoerc
open AdalyFormal.CurvBlock (dv pw_one_of_plaq)
open AdalyFormal.NonflatJet (r0)
open AdalyFormal.AsmM0 (rhoM0 M0RegimeR KhatM0 ginv_coercive_M0_reg)

/-- the k-free regularity radius. -/
noncomputable def kapHat (ell : ℕ) (ρ : ℝ) : ℝ := 2 * ρ + Kc ell * (ρ / (3 * Real.pi) + ρ ^ 2)

/-- k-FREE smallness for the all-bond regularity of the tower. -/
structure KUSmall (ell : ℕ) (ρ : ℝ) : Prop where
  c2 : 8 * (ell : ℝ) * kapHat ell ρ ≤ 1 / (8 * Real.pi)
  c4 : Kc ell ^ 2 * (ρ / (3 * Real.pi) + ρ ^ 2) ≤ 1
  c5 : (8 * (ell : ℝ) - 6) * kapHat ell ρ < r0

theorem class_bounds (ell k : ℕ) (hell : 1 ≤ ell) (e q0 : ℝ) (he0 : 0 ≤ e) (hq0 : 0 ≤ q0) :
    (ell : ℝ) ^ k * e ≤ rhoM0 ell k e q0 ∧
    ((ell : ℝ) ^ 2) ^ k * q0 ≤ rhoM0 ell k e q0 / (3 * Real.pi) ∧
    ((ell : ℝ) ^ 2) ^ k * (q0 + e ^ 2) ≤ rhoM0 ell k e q0 / (3 * Real.pi) + rhoM0 ell k e q0 ^ 2 := by
  have hpi := Real.pi_pos
  set n : ℝ := (ell : ℝ) ^ k with hn
  have hn0 : 0 ≤ n := by positivity
  have hmu : ((ell : ℝ) ^ 2) ^ k = n ^ 2 := by rw [hn, ← pow_mul, ← pow_mul, mul_comm]
  have hρ : rhoM0 ell k e q0 = n * e + 3 * Real.pi * (n ^ 2 * q0) := by unfold rhoM0; rw [← hn]; ring
  rw [hmu, hρ]
  have a1 : 0 ≤ n * e := by positivity
  have a2 : 0 ≤ n ^ 2 * q0 := by positivity
  refine ⟨by nlinarith, ?_, ?_⟩
  · rw [le_div_iff₀ (by positivity)]; nlinarith
  · have h1 : n ^ 2 * q0 ≤ (n * e + 3 * Real.pi * (n ^ 2 * q0)) / (3 * Real.pi) := by
      rw [le_div_iff₀ (by positivity)]; nlinarith
    have hX : 0 ≤ 3 * Real.pi * (n ^ 2 * q0) := by positivity
    have h2' : (n * e) ^ 2 ≤ (n * e + 3 * Real.pi * (n ^ 2 * q0)) ^ 2 := pow_le_pow_left₀ a1 (by linarith) 2
    have h2 : n ^ 2 * e ^ 2 ≤ (n * e + 3 * Real.pi * (n ^ 2 * q0)) ^ 2 := by rw [← mul_pow]; exact h2'
    have e1 : n ^ 2 * (q0 + e ^ 2) = n ^ 2 * q0 + n ^ 2 * e ^ 2 := by ring
    rw [e1]; linarith

theorem towerSmall_of_KU (ell k : ℕ) (hell : 2 ≤ ell) (e q0 : ℝ) (he0 : 0 ≤ e) (hq0 : 0 ≤ q0)
    (H : KUSmall ell (rhoM0 ell k e q0)) : TowerSmall ell k e q0 ∧ (8 * (ell : ℝ) - 6) * kap ell e q0 k < r0 := by
  have hpi := Real.pi_pos
  have hl : (2 : ℝ) ≤ ell := by exact_mod_cast hell
  obtain ⟨b1, b2, b3⟩ := class_bounds ell k (by omega) e q0 he0 hq0
  set ρ := rhoM0 ell k e q0
  have hKc := Kc_pos ell hell
  have hρ0 : 0 ≤ ρ := le_trans (by positivity) b1
  have hkap : kap ell e q0 k ≤ kapHat ell ρ := by
    unfold kap Bnd kapHat
    have := mul_le_mul_of_nonneg_left b3 hKc.le
    linarith
  have hkH0 : 0 ≤ kapHat ell ρ := by unfold kapHat; positivity
  have hρsmall : ρ ≤ 1 / 2 := by
    have h := H.c2; unfold kapHat at h
    have : 16 * (ell : ℝ) * ρ ≤ 1 / (8 * Real.pi) := by
      have : 0 ≤ 8 * (ell : ℝ) * (Kc ell * (ρ / (3 * Real.pi) + ρ ^ 2)) := by positivity
      nlinarith
    have : 1 / (8 * Real.pi) ≤ 1 := by rw [div_le_one (by positivity)]; nlinarith [Real.pi_gt_three]
    nlinarith
  refine ⟨⟨by linarith, ?_, ?_, ?_⟩, ?_⟩
  · exact le_trans (mul_le_mul_of_nonneg_left hkap (by positivity)) H.c2
  · have : ρ / (3 * Real.pi) ≤ 1 := by rw [div_le_one (by positivity)]; nlinarith [Real.pi_gt_three]
    linarith
  · exact le_trans (mul_le_mul_of_nonneg_left b3 (by positivity)) H.c4
  · have h86 : 0 ≤ 8 * (ell : ℝ) - 6 := by linarith
    exact lt_of_le_of_lt (mul_le_mul_of_nonneg_left hkap h86) H.c5

/-- **k-uniform `RegTower` for the M0 chain, every `ell ≥ 2`.** -/
theorem regTower_M0_kuniform (ell k : ℕ) (Lu : PeriodicLatticeExtent) (hell : 2 ≤ ell) (U : Cfg (scaleUp ell k Lu))
    (e q0 : ℝ) (he0 : 0 ≤ e) (hq0 : 0 ≤ q0) (hlinks : ∀ b, dv (U b) ≤ e)
    (hplaq : ∀ p : PeriodicLatticePlaquette (scaleUp ell k Lu), dv (periodicPlaquetteHolonomy U p) ≤ q0)
    (H : KUSmall ell (rhoM0 ell k e q0)) :
    RegTower ell (bgTower (GF ell k Lu) U) k := by
  obtain ⟨S, hthr⟩ := towerSmall_of_KU ell k hell e q0 he0 hq0 H
  exact regTower_allbond ell k hell U e q0 he0 hq0 hlinks (pw_one_of_plaq U q0 hq0 hplaq) S hthr

/-- **THE M0 THEOREM WITH A k-UNIFORM REGULARITY THRESHOLD (every `ell ≥ 2`).**
Hypotheses: `M0Regime` minus the crude `hregthr` (= `M0RegimeR`), plus `KUSmall ell ρ` (k-free in `ρ`). -/
theorem ginv_coercive_M0_kuniform (ell k : ℕ) (Lu : PeriodicLatticeExtent) (U : Cfg (scaleUp ell k Lu))
    (a t e q0 : ℝ) (R : M0RegimeR ell k Lu U a t e q0) (H : KUSmall ell (rhoM0 ell k e q0))
    (Lam : Set (PeriodicLatticeSite Lu)) (x : ↥(bondSupp (GF ell k Lu))) :
    ‖x‖ ^ 2 ≤ ((ell : ℝ) ^ k) ^ 2 * KhatM0 ell a t (rhoM0 ell k e q0) *
      ⟪x, (IngrBParams.data ⟨ell, k, Lu, (by have := R.hell; omega : 0 < ell), fullTower ell k Lu, U, a, Lam⟩).Ginv x⟫ :=
  ginv_coercive_M0_reg ell k Lu U a t e q0 R
    (regTower_M0_kuniform ell k Lu R.hell U e q0 R.he0 R.hq0 R.hlinks R.hplaq H) Lam x

#print axioms class_bounds
#print axioms towerSmall_of_KU
#print axioms regTower_M0_kuniform
#print axioms ginv_coercive_M0_kuniform

end AdalyFormal.RegBgKU
