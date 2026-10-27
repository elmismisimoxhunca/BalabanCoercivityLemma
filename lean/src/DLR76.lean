import DLR75
import DLR74

/-!
# DL76 -- **premise `hKDb` of DL5 at M0**: `Σ_{e'} ‖D̃⁽²⁾(B)(e')‖ ≤ KDfree ℓ · ‖B‖²`, `KDfree ℓ = 2ℓ²·K2s ℓ`

`D2in B = ℓ⁻¹ · h(C̃⁽²⁾(B))` (ZXR2Wire2, the frozen r7 object).  Unit background `Ū^k` (`unitBgU`) with links within
`κ̂ = kapHat ℓ ρ` of `1` (RKN2 `dv_bg_le` + MF7 `kap_le_kapHat`, as in DL4); `UnitSmall` gives `RegBg 1 ℓ Ū^k` and the
bijectivity of `H₀` (MF6d); ONE NEW k-free hypothesis
  `hKDc : 192·(8ℓκ̂ + 8·e2Majorant(rhoOf ℓ κ̂)) ≤ 1/(2ℓ³)`
makes the `ℓ¹` drift of `H₀` at most half of `H₀(1) = ℓ⁻³`, so `‖h‖_{ℓ¹→ℓ¹} ≤ 2ℓ³` (DL75 `hLift_l1`);
`‖C̃⁽²⁾ B‖_{ℓ¹} ≤ K2s ℓ ‖B‖²` (DL75 `C2tilde_l1`).  K-SCALING: none (unit lattice; k enters only through `ρ`).
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace AdalyFormal.DLayer

open scoped Matrix
open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.RMapLipschitz (frobSq frobNorm frobSq_nonneg frobNorm_nonneg frobNorm_sq)
open AdalyFormal.Balaban.SuTwoLogExp (SU2 M2)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.IngredientFamilyR2 (RegBg Cfg Q1jet H0 C2tilde hLift embY IngrBParams)
open AdalyFormal.StatementLane (scaleUp)
open AdalyFormal.NonflatJet (rhoOf)
open AdalyFormal.AsmM0 (rhoM0 M0RegimeR)
open AdalyFormal.RegBgKU (KUSmall kapHat Kc_pos towerSmall_of_KU dv_bg_le)
open AdalyFormal.M0Finish (PU UnitSmall kap_le_kapHat)
open EstimatesLayer.E1E3 (e2Majorant e2Majorant_nonneg)

noncomputable def KDfree (ell : ℕ) : ℝ := 2 * (ell : ℝ) ^ 2 * K2s ell

theorem hKDb_M0 (ell k : ℕ) (Lu : PeriodicLatticeExtent) (hell : 0 < ell) (U : Cfg (scaleUp ell k Lu))
    (a t e q0 : ℝ) (R : M0RegimeR ell k Lu U a t e q0) (H : KUSmall ell (rhoM0 ell k e q0))
    (HU : UnitSmall ell (rhoM0 ell k e q0)) (hd : ∀ μ, ell ∣ Lu μ + 1) (Lam : Set (PeriodicLatticeSite Lu))
    (hKDc : 192 * (8 * (ell : ℝ) * kapHat ell (rhoM0 ell k e q0)
        + 8 * e2Majorant (rhoOf ell (kapHat ell (rhoM0 ell k e q0)))) ≤ 1 / (2 * (ell : ℝ) ^ 3))
    (B : BondFnL2 Lu) :
    ∑ e', ‖((PU ell k Lu hell U a Lam).D2in B) e'‖ ≤ KDfree ell * ‖B‖ ^ 2 := by
  have hell2 : 2 ≤ ell := R.hell
  have hellR : (0 : ℝ) < ell := by exact_mod_cast hell
  set ρ := rhoM0 ell k e q0 with hρ
  set kh := kapHat ell ρ with hkh
  set P := PU ell k Lu hell U a Lam with hP
  have hκ0 : 0 ≤ kh := by rw [hkh]; unfold kapHat; have := Kc_pos ell hell2; have := m0_rho_nonneg ell k Lu U a t e q0 R; positivity
  obtain ⟨S, -⟩ := towerSmall_of_KU ell k hell2 e q0 R.he0 R.hq0 H
  have hV : ∀ e', frobNorm ((P.unitBgU e' : M2) - 1) ≤ kh := by
    intro e'
    have h1 := dv_bg_le ell k hell2 U e q0 R.he0 R.hq0 R.hlinks
      (AdalyFormal.CurvBlock.pw_one_of_plaq U q0 R.hq0 R.hplaq) S k le_rfl (embY ell k Lu hell e'.1, e'.2)
    exact h1.trans (kap_le_kapHat ell k hell2 e q0 R.he0 R.hq0)
  have hns := AdalyFormal.NonflatJet.numeric_small hell kh hκ0 HU.u1
  have hreg1 : RegBg 1 ell P.unitBgU :=
    AdalyFormal.NonflatJet.regBg_of_small Nat.one_pos P.unitBgU kh hκ0 hV HU.u2
  have hbV : Function.Bijective (H0 Lam (Q1jet ell P.unitBgU)) :=
    AdalyFormal.M0Finish.R7.hb_of_small P hd kh hκ0 HU.u1 HU.u2 hV
  set δ := 192 * (8 * (ell : ℝ) * kh + 8 * e2Majorant (rhoOf ell kh)) with hδ
  have hδ' : δ ≤ 1 / (2 * (ell : ℝ) ^ 3) := hKDc
  have hδlt : δ < 1 / (ell : ℝ) ^ 3 := by
    have : 1 / (2 * (ell : ℝ) ^ 3) < 1 / (ell : ℝ) ^ 3 := by
      rw [div_lt_div_iff₀ (by positivity) (by positivity)]; nlinarith [pow_pos hellR 3]
    linarith
  have hdrift := fun w => H0_drift_l1 hell hd Lam P.unitBgU kh hκ0 hV hns.1 hreg1 w
  have hL := hLift_l1 hell hd Lam P.unitBgU δ hbV hδlt hdrift (C2tilde ell P.unitBgU (WithLp.ofLp B))
  -- loops
  have hloop : 8 * (ell : ℝ) * kh ≤ 1 / 16 := by
    have h1 := HU.u1
    have hl2 : (2 : ℝ) ≤ ell := by exact_mod_cast hell2
    have hl3 : (8 : ℝ) * ell ≤ 8 * (ell : ℝ) ^ 4 := by nlinarith [pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 2) hl2 3]
    have h5 : 8 * (ell : ℝ) * kh ≤ 8 * (ell : ℝ) ^ 4 * (1 / (1000 * (ell : ℝ) ^ 4)) := by
      have := mul_le_mul hl3 h1 hκ0 (by positivity); linarith
    have h6 : 8 * (ell : ℝ) ^ 4 * (1 / (1000 * (ell : ℝ) ^ 4)) = 8 / 1000 := by field_simp
    linarith
  have hC := C2tilde_l1 hell hd P.unitBgU hreg1 kh hκ0 hV hloop (WithLp.ofLp B)
  -- assemble
  have hpos : 0 < 1 / (ell : ℝ) ^ 3 - δ := by linarith
  have hinv : 1 / (1 / (ell : ℝ) ^ 3 - δ) ≤ 2 * (ell : ℝ) ^ 3 := by
    rw [div_le_iff₀ hpos]
    have : 1 / (ell : ℝ) ^ 3 - δ ≥ 1 / (2 * (ell : ℝ) ^ 3) := by
      have e1 : 1 / (ell : ℝ) ^ 3 = 2 * (1 / (2 * (ell : ℝ) ^ 3)) := by field_simp
      linarith
    have e2 : 2 * (ell : ℝ) ^ 3 * (1 / (2 * (ell : ℝ) ^ 3)) = 1 := by field_simp
    nlinarith [pow_pos hellR 3]
  have hB2 : ∑ b : Bond Lu, ‖(WithLp.ofLp B) b‖ ^ 2 = ‖B‖ ^ 2 := by
    rw [PiLp.norm_sq_eq_of_L2]
  have hpt : ∀ e', ‖(P.D2in B) e'‖ = (ell : ℝ)⁻¹ * ‖hLift Lam (Q1jet ell P.unitBgU) (C2tilde ell P.unitBgU (WithLp.ofLp B)) e'‖ := by
    intro e'
    show ‖((ell : ℝ)⁻¹) • hLift Lam (Q1jet ell P.unitBgU) (C2tilde ell P.unitBgU (WithLp.ofLp B)) e'‖ = _
    rw [norm_smul, Real.norm_of_nonneg (by positivity)]
  rw [Finset.sum_congr rfl fun e' _ => hpt e', ← Finset.mul_sum]
  set S1 := ∑ c, ‖C2tilde ell P.unitBgU (WithLp.ofLp B) c‖ with hS1
  have hS10 : 0 ≤ S1 := Finset.sum_nonneg fun c _ => norm_nonneg _
  have hL' : ∑ b : Bond Lu, ‖hLift Lam (Q1jet ell P.unitBgU) (C2tilde ell P.unitBgU (WithLp.ofLp B)) b‖
      ≤ 2 * (ell : ℝ) ^ 3 * S1 := by
    refine hL.trans ?_
    rw [div_eq_mul_one_div, mul_comm]
    exact mul_le_mul_of_nonneg_right hinv hS10
  rw [hB2] at hC
  have hK0 : 0 ≤ K2s ell := by unfold K2s; positivity
  calc (ell : ℝ)⁻¹ * ∑ b : Bond Lu, ‖hLift Lam (Q1jet ell P.unitBgU) (C2tilde ell P.unitBgU (WithLp.ofLp B)) b‖
      ≤ (ell : ℝ)⁻¹ * (2 * (ell : ℝ) ^ 3 * S1) := mul_le_mul_of_nonneg_left hL' (by positivity)
    _ ≤ (ell : ℝ)⁻¹ * (2 * (ell : ℝ) ^ 3 * (K2s ell * ‖B‖ ^ 2)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hC (by positivity)) (by positivity)
    _ = KDfree ell * ‖B‖ ^ 2 := by unfold KDfree; field_simp

#print axioms hKDb_M0

end AdalyFormal.DLayer
