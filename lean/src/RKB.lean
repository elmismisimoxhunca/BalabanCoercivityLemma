import RKA2

/-!
# RKB -- k-UNIFORM regularity of the background tower at ALL bonds for `ell ≥ 13`, and the k-uniform M0 theorem there.

`regTower_ge13`: for `13 ≤ ell`, fine links `dv ≤ e` (one gauge), fine plaquettes `dv ≤ q0`, and the k-FREE threshold
  `(8 ell − 6) · (1 + KC ell / (3π)) · ρ < ell · r0`,   `ρ = rhoM0 ell k e q0 = ell^k e + 3π ell^{2k} q0`,
the tower is regular at EVERY bond of EVERY level `j < k` (R2's `RegTower`, all edges incl. truncated seam bonds).
Source of the all-bond link bound: curvature_blocking CB5 `link_tower` (every bond, every extent, no divisibility):
  `dv (ubarTowerSU2 ell U j c) ≤ ell^j e + KC ell · (ell²)^j q0`, valid when `blkConstOf ell < ell²` (CB5 `blkConst_lt_sq`, ell ≥ 13).
`ginv_coercive_M0_kuniform_ge13`: RKA2 `ginv_coercive_M0_reg` with `hreg` discharged this way.
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace AdalyFormal.RegBgKU

open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Balaban.RegularUPerturbation (frobSupBond)
open AdalyFormal.StatementLane (scaleUp)
open AdalyFormal.SliceCoerc
open AdalyFormal.PortSlice
open AdalyFormal.CurvBlock (dv pw_one_of_plaq KC KC_nonneg link_tower blkConst_lt_sq)
open AdalyFormal.NonflatJet (r0 mem_LogReg_of_frob_lt)
open AdalyFormal.AsmM0 (rhoM0 M0RegimeR KhatM0 ginv_coercive_M0_reg frobSupBond_le_of)

/-- the k-free arithmetic: for `j < k`, `ell^j e + K (ell²)^j q0 ≤ (1 + K/(3π)) ρ / ell`. -/
theorem eps_le_rho (ell k j : ℕ) (hell : 1 ≤ ell) (hj : j < k) (e q0 K : ℝ) (he0 : 0 ≤ e) (hq0 : 0 ≤ q0) (hK : 0 ≤ K) :
    (ell : ℝ) ^ j * e + K * (((ell : ℝ) ^ 2) ^ j * q0) ≤ (1 + K / (3 * Real.pi)) * rhoM0 ell k e q0 / ell := by
  have hl : (1 : ℝ) ≤ ell := by exact_mod_cast hell
  have hl0 : (0 : ℝ) < ell := by linarith
  have hpi := Real.pi_pos
  set n : ℝ := (ell : ℝ) ^ k with hn
  set m : ℝ := (ell : ℝ) ^ j with hm
  have hm0 : 0 ≤ m := by positivity
  have hmn : m * ell ≤ n := by
    rw [hm, hn, ← pow_succ]; exact pow_le_pow_right₀ hl hj
  have hsq : ((ell : ℝ) ^ 2) ^ j = m ^ 2 := by rw [hm, ← pow_mul, ← pow_mul, mul_comm]
  rw [hsq]
  have hρ : rhoM0 ell k e q0 = n * e + 3 * Real.pi * (n ^ 2 * q0) := by unfold rhoM0; rw [← hn]; ring
  rw [hρ, le_div_iff₀ hl0]
  -- (m e + K m² q0) ell ≤ (1 + K/3π)(n e + 3π n² q0)
  have h1 : m * e * ell ≤ n * e := by nlinarith
  have h2 : m ^ 2 * ell ≤ n ^ 2 := by
    have : m ^ 2 * ell ≤ (m * ell) ^ 2 := by nlinarith
    nlinarith [mul_le_mul hmn hmn (by positivity) (by positivity)]
  have h3 : K * (m ^ 2 * q0) * ell ≤ K * (n ^ 2 * q0) := by
    have := mul_le_mul_of_nonneg_right h2 hq0
    nlinarith [mul_le_mul_of_nonneg_left this hK]
  have h4 : (1 + K / (3 * Real.pi)) * (n * e + 3 * Real.pi * (n ^ 2 * q0))
      = n * e + 3 * Real.pi * (n ^ 2 * q0) + K / (3 * Real.pi) * (n * e) + K * (n ^ 2 * q0) := by
    field_simp; ring
  rw [h4]
  have h5 : 0 ≤ K / (3 * Real.pi) * (n * e) := by positivity
  have h6 : 0 ≤ 3 * Real.pi * (n ^ 2 * q0) := by positivity
  nlinarith

/-- **k-uniform `RegTower` at all bonds, `ell ≥ 13`.** -/
theorem regTower_ge13 (ell k : ℕ) (Lu : PeriodicLatticeExtent) (hell : 13 ≤ ell) (U : Cfg (scaleUp ell k Lu))
    (e q0 : ℝ) (he0 : 0 ≤ e) (hq0 : 0 ≤ q0) (hlinks : ∀ b, dv (U b) ≤ e)
    (hplaq : ∀ p : PeriodicLatticePlaquette (scaleUp ell k Lu), dv (periodicPlaquetteHolonomy U p) ≤ q0)
    (hthr : (8 * (ell : ℝ) - 6) * ((1 + KC ell / (3 * Real.pi)) * rhoM0 ell k e q0) < (ell : ℝ) * r0) :
    RegTower ell (bgTower (GF ell k Lu) U) k := by
  have hell0 : 0 < ell := by omega
  have hl : (13 : ℝ) ≤ ell := by exact_mod_cast hell
  have hr := blkConst_lt_sq ell hell
  have hK := KC_nonneg ell hell0 hr
  have h0 := pw_one_of_plaq U q0 hq0 hplaq
  refine regTower_of_frobSup hell0 (bgTower (GF ell k Lu) U) k
    (fun j => (ell : ℝ) ^ j * e + KC ell * (((ell : ℝ) ^ 2) ^ j * q0)) ?_ r0 (fun g h => mem_LogReg_of_frob_lt h) ?_
  · intro j _
    refine frobSupBond_le_of _ (fun c => ?_)
    have := link_tower ell hell0 hr U q0 e hq0 h0 hlinks j c
    have e1 : KC ell * ((ell : ℝ) ^ 2) ^ j * q0 = KC ell * (((ell : ℝ) ^ 2) ^ j * q0) := by ring
    rw [e1] at this
    exact this
  · intro j hj
    have h := eps_le_rho ell k j (by omega) hj e q0 (KC ell) he0 hq0 hK
    have h8 : (0 : ℝ) ≤ 8 * (ell : ℝ) - 6 := by linarith
    have hl0 : (0 : ℝ) < ell := by linarith
    calc (8 * (ell : ℝ) - 6) * ((ell : ℝ) ^ j * e + KC ell * (((ell : ℝ) ^ 2) ^ j * q0))
        ≤ (8 * (ell : ℝ) - 6) * ((1 + KC ell / (3 * Real.pi)) * rhoM0 ell k e q0 / ell) :=
          mul_le_mul_of_nonneg_left h h8
      _ = (8 * (ell : ℝ) - 6) * ((1 + KC ell / (3 * Real.pi)) * rhoM0 ell k e q0) / ell := by ring
      _ < r0 := by rw [div_lt_iff₀ hl0]; linarith

/-- **The M0 theorem with a k-UNIFORM regularity threshold, `ell ≥ 13`.**  Every hypothesis is k-free in `ρ`. -/
theorem ginv_coercive_M0_kuniform_ge13 (ell k : ℕ) (Lu : PeriodicLatticeExtent) (U : Cfg (scaleUp ell k Lu))
    (a t e q0 : ℝ) (R : M0RegimeR ell k Lu U a t e q0) (hell13 : 13 ≤ ell)
    (hthr : (8 * (ell : ℝ) - 6) * ((1 + KC ell / (3 * Real.pi)) * rhoM0 ell k e q0) < (ell : ℝ) * r0)
    (Lam : Set (PeriodicLatticeSite Lu)) (x : ↥(bondSupp (GF ell k Lu))) :
    ‖x‖ ^ 2 ≤ ((ell : ℝ) ^ k) ^ 2 * KhatM0 ell a t (rhoM0 ell k e q0) *
      ⟪x, (IngrBParams.data ⟨ell, k, Lu, (by have := R.hell; omega : 0 < ell), fullTower ell k Lu, U, a, Lam⟩).Ginv x⟫ :=
  ginv_coercive_M0_reg ell k Lu U a t e q0 R
    (regTower_ge13 ell k Lu hell13 U e q0 R.he0 R.hq0 R.hlinks R.hplaq hthr) Lam x

#print axioms eps_le_rho
#print axioms regTower_ge13
#print axioms ginv_coercive_M0_kuniform_ge13

end AdalyFormal.RegBgKU
