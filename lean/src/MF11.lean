import MF7

/-!
# MF11 -- `WellDef` (the frozen `GenP.WellDef`: `hb ∧ IsUnit G₁⁻¹ ∧ IsUnit N`) at NON-FLAT `U` on the full tower (M0).

From the regime (`M0RegimeR`, `KUSmall`, `UnitSmall`) and the D-layer premise `hD2` with `ε2s K̂ < 1` only (`hJ` is not needed):
`hb` (`hb_of_small`, ported, unit background `Ū^k` small at every bond), `Q*` injective (`qs_injective_PU`), units (`units_PU`).
-/
set_option autoImplicit false
set_option maxHeartbeats 16000000
set_option maxRecDepth 8000

namespace AdalyFormal.M0Finish

open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane (scaleUp)
open AdalyFormal.StatementLaneG (GenP.WellDef GenP.Nmat)
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Balaban.SuTwoLogExp (M2)
open AdalyFormal.Balaban.RMapLipschitz (frobNorm)
open AdalyFormal.AsmM0
open AdalyFormal.CurvBlock (pw_one_of_plaq)
open AdalyFormal.RegBgKU (KUSmall kapHat Kc_pos towerSmall_of_KU class_bounds dv_bg_le ginv_coercive_M0_kuniform)

theorem wellDef_M0 (ell k : ℕ) (Lu : PeriodicLatticeExtent) (hell : 0 < ell) (U : Cfg (scaleUp ell k Lu))
    (a t e q0 : ℝ) (R : M0RegimeR ell k Lu U a t e q0) (H : KUSmall ell (rhoM0 ell k e q0))
    (HU : UnitSmall ell (rhoM0 ell k e q0)) (hd : ∀ μ, ell ∣ Lu μ + 1)
    (Lam : Set (PeriodicLatticeSite Lu)) (ε2s : ℝ)
    (hε' : ε2s * KhatM0 ell a t (rhoM0 ell k e q0) < 1)
    (hD2 : ‖(PU ell k Lu hell U a Lam).data.Delta2 (PU ell k Lu hell U a Lam).data_laws‖
      ≤ ε2s / ((ell : ℝ) ^ k) ^ 2) :
    GenP.WellDef (PU ell k Lu hell U a Lam) := by
  have hell2 : 2 ≤ ell := R.hell
  set ρ := rhoM0 ell k e q0 with hρdef
  set n : ℝ := (ell : ℝ) ^ k with hn
  have hnpos : 0 < n := pow_pos (by exact_mod_cast hell) k
  have ha := R.ha
  have hρnn : 0 ≤ ρ := le_trans (mul_nonneg (pow_nonneg (Nat.cast_nonneg _) k) R.he0)
    (class_bounds ell k (by omega) e q0 R.he0 R.hq0).1
  set Kh := KhatM0 ell a t ρ with hKh
  have hKhpos : 0 < Kh := KhatM0_pos ell a t ρ ha R.h216
  have hC1 := hC1_M0 ell k Lu U a t e q0 R H
  have hφ := phi_sq_small ell a t ρ ha R.ht hρnn R.hsmallU
  have hsm : 16 * n ^ 2 * (Real.sqrt a * phiC ell (3600 * (ell : ℝ) * ρ) / n) ^ 2 < a := by
    rw [div_pow, mul_pow, Real.sq_sqrt ha.le]
    have e1 : 16 * n ^ 2 * (a * phiC ell (3600 * (ell : ℝ) * ρ) ^ 2 / n ^ 2)
        = a * (16 * phiC ell (3600 * (ell : ℝ) * ρ) ^ 2) := by field_simp
    rw [e1]
    have : 16 * phiC ell (3600 * (ell : ℝ) * ρ) ^ 2 < 1 := by linarith
    nlinarith
  have hQs := qs_injective_PU ell k Lu hell U a ha Lam _ hC1 hsm
  have hcoer : ∀ y : ↥(bondSupp (PU ell k Lu hell U a Lam).G),
      ‖y‖ ^ 2 ≤ n ^ 2 * Kh * ⟪y, (PU ell k Lu hell U a Lam).data.Ginv y⟫ :=
    fun y => ginv_coercive_M0_kuniform ell k Lu U a t e q0 R H Lam y
  have hC0 : 0 < n ^ 2 * Kh := by positivity
  have hε2C : ε2s / n ^ 2 * (n ^ 2 * Kh) < 1 := by
    rw [show ε2s / n ^ 2 * (n ^ 2 * Kh) = ε2s * Kh by field_simp]; exact hε'
  obtain ⟨hG, hN⟩ := units_PU ell k Lu hell U a Lam (n ^ 2 * Kh) (ε2s / n ^ 2) hC0 hε2C hcoer hD2 hQs
  set P := PU ell k Lu hell U a Lam with hP
  have hκ0 : 0 ≤ kapHat ell ρ := by unfold kapHat; have := Kc_pos ell hell2; positivity
  obtain ⟨S, -⟩ := towerSmall_of_KU ell k hell2 e q0 R.he0 R.hq0 H
  have hV : ∀ e', frobNorm ((P.unitBgU e' : M2) - 1) ≤ kapHat ell ρ := by
    intro e'
    have h1 := dv_bg_le ell k hell2 U e q0 R.he0 R.hq0 R.hlinks (pw_one_of_plaq U q0 R.hq0 R.hplaq) S k le_rfl
      (embY ell k Lu hell e'.1, e'.2)
    exact h1.trans (kap_le_kapHat ell k hell2 e q0 R.he0 R.hq0)
  have hb : Function.Bijective (H0 P.Lam P.Q1) :=
    AdalyFormal.M0Finish.R7.hb_of_small P hd (kapHat ell ρ) hκ0 HU.u1 HU.u2 hV
  exact ⟨hb, hG, hN⟩

#print axioms wellDef_M0

end AdalyFormal.M0Finish
