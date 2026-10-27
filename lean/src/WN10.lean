import WN9
import W2F

/-!
# WN10 -- W3 for lane E's DECOUPLED form `G0` at a NON-FLAT background (the form W4 consumes via W2)

`G0form S ell k U a A = ‖χ_P C_U A‖² + ‖R_U D_U* A‖² + ‖√w Q_U A‖²` (lane E MI19).  On the patch, at `U` with the WN7
link/plaquette regime, `‖A‖² ≤ n² KG0 G0(A)` for EVERY bond field `A` (`g0_patch_nonflat`), `n = ell^(j+1)`,
`KG0 = 32 Kflat (1 + Mc²) + 4 Mc`, under the WN7 conditions plus `hs6` (`8·272 (r/3π)/(4√2) ≤ 1/Kflat`).
Route: `A = W A + D ν`; slice coercivity of `Φ_U` at `W A` (WN1/WN7 inputs), `Δ'` absorbed by `hs6`, the curvature
commutator `‖χ C_U D_U ν‖² ≤ 12 q0² ‖ν‖²` (`curl_grad_le`, from DL25 `curv_pt`), `‖ν‖ ≤ PU² ‖R D* A‖` (Poincaré twice),
mass unchanged along `D N(Q'(U))`.
* `G0form_gauge`, `wnormSq_gauge` : `G0` and lane B's weighted norm are invariant under `A ↦ Ad_γ A`, `U ↦ U^γ`.
* `W3G0Stmt ell a` (the `W3Stmt` shape with `G0form` and every `A`); **`w3G0_nonflat_of_LemI`** : `LemIFlat → W3G0Stmt`.
* **`w3G0At_of_stmt`** : `W3G0Stmt` gives the W2 lane's `W3G0At ell L U a cW` for every torus `L` and every `U` that is in
  the M1 regime on EVERY two-stratum patch tower of `L` (the per-patch hypothesis is stated explicitly).
No sorry / axiom.
Copy in m1_patch_nonflat_20261014 of compute/w3_nonflat_20261013/src/WN10.lean (never compiled there); one change:
`hsmallc` closes with `div_le_one` (the original `div_le_div_iff₀` rewrite did not match).
-/
set_option autoImplicit false
set_option maxHeartbeats 16000000

namespace AdalyFormal.W3NF

open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2 RMap)
open AdalyFormal.Balaban.CovariantHjMinimizer (trivialU)
open AdalyFormal.Balaban.RMapLipschitz (frobNorm)
open AdalyFormal.Balaban.RegularUPerturbation (frobSupBond)
open AdalyFormal.StatementLane (BlockClosed scaleUp)
open AdalyFormal.StatementLaneG (gparams)
open AdalyFormal.SiteCoercivity (ProperTower)
open AdalyFormal.M1Patch (patchTower GP patch_proper om0_univ dvd_scaleUp LemIFlat Kflat Pc)
open AdalyFormal.BondComposite (TowerClass deltaM)
open AdalyFormal.CurvBlock (dv pw)
open AdalyFormal.RegBgKU (KUSmall kapHat kap Kc Kc_pos)
open AdalyFormal.AsmM0 (rhoM0 Mc phiC)
open AdalyFormal.M1IMS (G0form)
open AdalyFormal.Balaban.AlphaAnalyticity (GaugeFn)

/-- the `n`-free constant of the `G0` bound -/
noncomputable def KG0 (a Ci : ℝ) : ℝ := 32 * Kflat a Ci * (1 + Mc a ^ 2) + 4 * Mc a

theorem KG0_pos {a Ci : ℝ} (ha : 0 < a) (hCi : 0 ≤ Ci) : 0 < KG0 a Ci := by
  unfold KG0; have := Kflat_pos ha hCi; have := Mc_pos a; positivity

/-- **curvature commutator**: `‖χ_P C_U (D_U ν)‖² ≤ 12 q0² ‖ν‖²` if every plaquette defect is `≤ q0`. -/
theorem curl_grad_le {L : PeriodicLatticeExtent} (U : Cfg L) (q0 : ℝ) (hq0 : 0 ≤ q0)
    (hplaq : ∀ y ν μ, dv (pw 1 U y ν μ) ≤ q0) (P : Set (PeriodicLatticePlaquette L)) (f : SiteL2 L) :
    ‖AdalyFormal.StatementLaneR6.plaqMask P (AdalyFormal.Balaban.DeltaKFull.curlCovariantLM_L2 U (gradL2 U f))‖ ^ 2
      ≤ 12 * q0 ^ 2 * ‖f‖ ^ 2 := by
  classical
  have hpl := AdalyFormal.CurvBlock.plaq_of_pw_one U q0 hplaq
  have hpt : ∀ p : PeriodicLatticePlaquette L,
      ‖(AdalyFormal.StatementLaneR6.plaqMask P (AdalyFormal.Balaban.DeltaKFull.curlCovariantLM_L2 U (gradL2 U f))) p‖ ^ 2
        ≤ 4 * q0 ^ 2 * ‖f (periodicLatticeShift (periodicLatticeShift p.1 p.2.1.1) p.2.1.2)‖ ^ 2 := by
    intro p
    rw [AdalyFormal.StatementLaneR6.plaqMask_apply]
    split_ifs with hp
    · have hc := AdalyFormal.DLayer.curv_pt U f p
      have e : (AdalyFormal.Balaban.DeltaKFull.curlCovariantLM_L2 U (gradL2 U f)) p
          = (AdalyFormal.DLayer.curlC U (gradL2 U f)) p := rfl
      rw [e]
      have h1 : ‖(AdalyFormal.DLayer.curlC U (gradL2 U f)) p‖
          ≤ 2 * q0 * ‖f (periodicLatticeShift (periodicLatticeShift p.1 p.2.1.1) p.2.1.2)‖ :=
        hc.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hpl p) (by norm_num)) (norm_nonneg _))
      calc _ ≤ (2 * q0 * ‖f (periodicLatticeShift (periodicLatticeShift p.1 p.2.1.1) p.2.1.2)‖) ^ 2 :=
            pow_le_pow_left₀ (norm_nonneg _) h1 2
        _ = _ := by ring
    · rw [norm_zero, zero_pow two_ne_zero]; positivity
  rw [PiLp.norm_sq_eq_of_L2]
  calc ∑ p, ‖(AdalyFormal.StatementLaneR6.plaqMask P (AdalyFormal.Balaban.DeltaKFull.curlCovariantLM_L2 U (gradL2 U f))) p‖ ^ 2
      ≤ ∑ p : PeriodicLatticePlaquette L, 4 * q0 ^ 2 *
          ‖f (periodicLatticeShift (periodicLatticeShift p.1 p.2.1.1) p.2.1.2)‖ ^ 2 :=
        Finset.sum_le_sum (fun p _ => hpt p)
    _ = 4 * q0 ^ 2 * ∑ d : PeriodicPlaquetteDirections, ∑ x : PeriodicLatticeSite L,
          ‖f (periodicLatticeShift (periodicLatticeShift x d.1.1) d.1.2)‖ ^ 2 := by
        rw [← Finset.mul_sum, Fintype.sum_prod_type_right]
    _ = 4 * q0 ^ 2 * ∑ _d : PeriodicPlaquetteDirections, ‖f‖ ^ 2 := by
        congr 1
        exact Finset.sum_congr rfl (fun d _ => AdalyFormal.DLayer.sum_site_le f d.1.1 d.1.2)
    _ = _ := by rw [Finset.sum_const, Finset.card_univ, AdalyFormal.DLayer.card_dirs]; simp; ring

/-- **`G0` coercivity on the patch at a non-flat background.** -/
theorem g0_patch_nonflat {ell : ℕ} (hell : 2 ≤ ell) {a Ci : ℝ} (ha : 0 < a) (hCi : 0 ≤ Ci)
    (hI : LemIFlat ell a Ci) (j : ℕ) (Lu : PeriodicLatticeExtent)
    (Rg : Set (PeriodicLatticeSite (scaleUp ell (j + 1) Lu))) (hRg : BlockClosed (ell ^ (j + 1)) Rg)
    (U : Cfg (scaleUp ell (j + 1) Lu)) (e q0 : ℝ) (he0 : 0 ≤ e) (hq0 : 0 ≤ q0)
    (hlinks : ∀ b, dv (U b) ≤ e) (h0 : ∀ y ν μ, dv (pw 1 U y ν μ) ≤ q0)
    (H : KUSmall ell (rhoM0 ell (j + 1) e q0))
    (hs1 : 432 * kapHat ell (rhoM0 ell (j + 1) e q0) ^ 2 ≤ 1)
    (hs2 : kapHat ell (rhoM0 ell (j + 1) e q0) ≤ 1 / (1000 * (ell : ℝ) ^ 3))
    (hs3 : kapHat ell (rhoM0 ell (j + 1) e q0) ≤ 1)
    (hs4 : 324 * lamC ell * kapHat ell (rhoM0 ell (j + 1) e q0) ≤ 1)
    (hs5 : 2 * ThetaP ell a (kapHat ell (rhoM0 ell (j + 1) e q0)) ≤ 1 / Kflat a Ci)
    (hs6 : 8 * (272 * (kapHat ell (rhoM0 ell (j + 1) e q0) / (3 * Real.pi)) / (4 * Real.sqrt 2)) ≤ 1 / Kflat a Ci)
    (A : BondFnL2 (scaleUp ell (j + 1) Lu)) :
    ‖A‖ ^ 2 ≤ ((ell : ℝ) ^ (j + 1)) ^ 2 * KG0 a Ci * G0form (patchTower j Rg) ell (j + 1) U a A := by
  have hell0 : 0 < ell := by omega
  have hellR : (2 : ℝ) ≤ ell := by exact_mod_cast hell
  have hl1 : (1 : ℝ) ≤ ell := by linarith
  have hlpos : (0 : ℝ) < ell := by linarith
  have hpi := Real.pi_pos
  have hKc := Kc_pos ell hell
  set n : ℝ := (ell : ℝ) ^ (j + 1) with hn
  have hnpos : 0 < n := by positivity
  set s : ℝ := Real.sqrt n with hs
  have hspos : 0 < s := Real.sqrt_pos.mpr hnpos
  set ρ := rhoM0 ell (j + 1) e q0 with hρ
  set r := kapHat ell ρ with hr
  have hρ_eq : ρ = n * e + 3 * Real.pi * (n ^ 2 * q0) := by
    rw [hρ]; unfold rhoM0; rw [← hn]; ring
  have hρ0 : 0 ≤ ρ := by rw [hρ_eq]; positivity
  have hρr : ρ ≤ r := by
    rw [hr]; unfold kapHat
    have : 0 ≤ Kc ell * (ρ / (3 * Real.pi) + ρ ^ 2) := by positivity
    linarith
  have hr0 : 0 ≤ r := hρ0.trans hρr
  have hen : e ≤ r / n := by
    rw [le_div_iff₀ hnpos]
    have : 0 ≤ 3 * Real.pi * (n ^ 2 * q0) := by positivity
    nlinarith
  have hq0n : n ^ 2 * q0 ≤ r / (3 * Real.pi) := by
    rw [le_div_iff₀ (by positivity)]
    have : 0 ≤ n * e := by positivity
    nlinarith
  have hlinksr : ∀ b, dv (U b) ≤ r / n := fun b => (hlinks b).trans hen
  have hsup : frobSupBond U ≤ r / n := AdalyFormal.AsmM0.frobSupBond_le_of U hlinksr
  have hrn0 : 0 ≤ r / n := by positivity
  -- the background tower
  obtain ⟨S, -⟩ := AdalyFormal.RegBgKU.towerSmall_of_KU ell (j + 1) hell e q0 he0 hq0 H
  have hcl := towerClass_patch ell j hell Lu U e q0 he0 hq0 hlinks h0 S
  have hε0 : ∀ i, 0 ≤ kap ell e q0 i := fun i => kap_nonneg' ell hell e q0 he0 hq0 i
  have hkapk : kap ell e q0 (j + 1) ≤ r := AdalyFormal.M0Finish.kap_le_kapHat ell (j + 1) hell e q0 he0 hq0
  have hεη : ∀ i, i < j + 1 → kap ell e q0 i ≤ (ell : ℝ) ^ i * (r / n) := by
    intro i hi
    refine (kap_le_class ell hell e q0 he0 hq0 (j + 1) i hi.le).trans ?_
    exact mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hkapk hnpos.le) (by positivity)
  have hεs : ∀ i, i < j + 1 → kap ell e q0 i ≤ 1 / (1000 * (ell : ℝ) ^ 4) := by
    intro i hi
    have h1 : (ell : ℝ) ^ i * ell ≤ n := by rw [hn, ← pow_succ]; exact pow_le_pow_right₀ hl1 hi
    have h2 : (ell : ℝ) ^ i * (r / n) ≤ r / ell := by
      rw [mul_div_assoc', div_le_div_iff₀ hnpos hlpos]
      nlinarith [mul_le_mul_of_nonneg_left h1 hr0]
    have h3 : r / ell ≤ 1 / (1000 * (ell : ℝ) ^ 4) := by
      calc r / ell ≤ (1 / (1000 * (ell : ℝ) ^ 3)) / ell := div_le_div_of_nonneg_right hs2 hlpos.le
        _ = 1 / (1000 * (ell : ℝ) ^ 4) := by
          rw [div_div, show 1000 * (ell : ℝ) ^ 3 * ell = 1000 * (ell : ℝ) ^ 4 by ring]
    exact (hεη i hi).trans (h2.trans h3)
  have hreg : RegTower ell (bgTower (AdalyFormal.SliceCoerc.GF ell (j + 1) Lu) U) (j + 1) :=
    AdalyFormal.RegBgKU.regTower_M0_kuniform ell (j + 1) Lu hell U e q0 he0 hq0 hlinks
      (AdalyFormal.CurvBlock.plaq_of_pw_one U q0 h0) H
  -- geometry and site layer
  have hdvd := dvd_scaleUp ell j Lu hell0
  have hP : ProperTower (GP ell j Lu Rg) ell (j + 1) := patch_proper hell0 hRg
  have hOm : (GP ell j Lu Rg).Om0 = Set.univ := om0_univ j Rg ell
  have h216 : 216 * r ^ 2 < 1 := by nlinarith
  have hU := hU_patch ell j hell0 (GP ell j Lu Rg) U r hr0 hlinksr
  have hT := hT_patch ell j hell0 Lu Rg U (fun i => kap ell e q0 i) r hr0 hcl hεη
  have hu : IsUnit (DelpA (GP ell j Lu Rg) U a + (1 - siteMask (GP ell j Lu Rg).Om0)) :=
    AdalyFormal.M1Site.isUnit_LP_strat ell (j + 1) hell hdvd hP U a ha r hr0 h216 hU hT
  have hPoincU : ∀ ν ∈ NQp (GP ell j Lu Rg) U, ‖ν‖ ≤ Pc ell (j + 1) a r * ‖gradL2 U ν‖ := fun ν hν =>
    AdalyFormal.M1Patch.poincare_patch hell hdvd hP hOm U a ha r hr0 h216 hU hT ν hν
  have hPoinc1 : ∀ ν ∈ NQp (GP ell j Lu Rg) (trivialU (scaleUp ell (j + 1) Lu)),
      ‖ν‖ ≤ n * Real.sqrt (Mc a) * ‖gradL2 (trivialU (scaleUp ell (j + 1) Lu)) ν‖ := by
    intro ν hν
    have h := AdalyFormal.M1Patch.poincare_patch hell hdvd hP hOm (flatCfg : Cfg (scaleUp ell (j + 1) Lu)) a ha 0
      le_rfl (by norm_num) (AdalyFormal.M1Patch.flat_hU ell (j + 1) (GP ell j Lu Rg)) (AdalyFormal.M1Patch.flat_hT ell (j + 1) (GP ell j Lu Rg)) ν hν
    rw [Pc0_eq] at h
    exact h
  have hB0 : ∀ ν ∈ NQp (GP ell j Lu Rg) U, (bondSectorOf (GP ell j Lu Rg) U).Qfull (gradL2 U ν) = 0 :=
    fun ν hν => AdalyFormal.M1Patch.patch_B0 hell0 hRg hdvd U hreg ν hν
  -- Φ drift
  have hsm : ∀ i, i < j + 1 → AdalyFormal.NonflatJet.rhoOf ell (kap ell e q0 i) < Real.pi / 2 :=
    fun i hi => AdalyFormal.BondComposite.hsm_of_le ell hell0 _ (hε0 i) (hεs i hi)
  set δm : ℝ := Real.sqrt 2 * (ell : ℝ) * deltaM ell (j + 1) a (fun i => kap ell e q0 i) with hδm
  have hm := fun x => hm_patch ell j Lu hell0 Rg U a ha.le (fun i => kap ell e q0 i) hreg hcl
    (fun i _ => hε0 i) hsm x
  have hnr : (ell : ℝ) ^ (j + 1) * (r / n) = r := by rw [← hn]; field_simp
  have hdM : n * deltaM ell (j + 1) a (fun i => kap ell e q0 i) ≤ Real.sqrt a * phiC ell (3600 * (ell : ℝ) * r) := by
    have h := AdalyFormal.BondComposite.n_deltaM_le ell (j + 1) hell a ha.le (fun i => kap ell e q0 i) (r / n) hrn0
      (fun i _ => hε0 i) hεη hεs
    rw [hnr] at h
    unfold phiC
    exact h
  have hdM0 : 0 ≤ deltaM ell (j + 1) a (fun i => kap ell e q0 i) :=
    AdalyFormal.AsmM0.deltaM_nonneg ell (j + 1) hell0 a ha.le _ (fun i _ => hε0 i)
  have hplaq := AdalyFormal.CurvBlock.plaq_of_pw_one U q0 h0
  have hpl : AdalyFormal.NonflatHunit.PlaqDef (q0 / (4 * Real.sqrt 2)) U := by
    intro p
    have h := hplaq p
    have e1 : 4 * Real.sqrt 2 * (q0 / (4 * Real.sqrt 2)) = q0 := by
      have : Real.sqrt 2 ≠ 0 := by positivity
      field_simp
    rw [e1]; exact h
  have hα0 : 0 ≤ q0 / (4 * Real.sqrt 2) := by positivity
  have hdp := theta_patch ell j Lu Rg U hα0 hpl
  have hc' : ∀ x : BondFnL2 (scaleUp ell (j + 1) Lu),
      ‖AdalyFormal.StatementLaneR6.plaqMask (plaqIn (GP ell j Lu Rg).Om0)
          (AdalyFormal.Balaban.DeltaKFull.curlCovariantLM_L2 (trivialU _) x)
        - AdalyFormal.StatementLaneR6.plaqMask (plaqIn (GP ell j Lu Rg).Om0)
          (AdalyFormal.Balaban.DeltaKFull.curlCovariantLM_L2 U x)‖ ≤ (4 * Real.sqrt 2 * (r / n)) * ‖x‖ := by
    intro x
    refine le_trans (AdalyFormal.SliceCoerc.hc_of_frobSup U _ x) ?_
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hsup (by positivity)) (norm_nonneg _)
  set e' : ℝ := (1 + 1) * (272 * (q0 / (4 * Real.sqrt 2)))
    + (1 + 1 / 1) * ((4 * Real.sqrt 2 * (r / n)) ^ 2 + δm ^ 2) with he'
  have hdrift : ∀ x : BondFnL2 (scaleUp ell (j + 1) Lu),
      PhiG (GP ell j Lu Rg) a (trivialU _) x ≤ (1 + 1) * PhiG (GP ell j Lu Rg) a U x + e' * ‖x‖ ^ 2 := fun x =>
    phi_drift_gen (GP ell j Lu Rg) U a ha.le 1 one_pos (4 * Real.sqrt 2 * (r / n)) (272 * (q0 / (4 * Real.sqrt 2))) δm hc' hdp hm x
  -- gradient drift
  have hd : ∀ f, ‖gradL2 (trivialU (scaleUp ell (j + 1) Lu)) f - gradL2 U f‖ ≤ (Real.sqrt 12 * (r / n)) * ‖f‖ :=
    fun f => AdalyFormal.SliceCoerc.hd_of_frobSup U hrn0 hsup f
  -- constraint rows
  set q : ℝ := lamC ell / (n * s) with hq
  have hq0' : 0 ≤ q := by rw [hq]; unfold lamC; positivity
  have hqeq : Real.sqrt ((1 / (ell : ℝ) ^ 3) ^ j) = q := q_eq' ell j hell0
  have hQq : ∀ f, ‖Qrow (GP ell j Lu Rg) U f‖ ≤ q * ‖f‖ := fun f => by
    have h := Qrow_patch_norm ell j hell0 Lu Rg hRg U f
    rwa [hqeq] at h
  have hD : ∀ m, m ≤ j + 1 → |AdalyFormal.BondComposite.dsum ell (fun i => kap ell e q0 i) m| ≤ 6 * r := by
    intro m hm
    have h := dsum_le_class ell hell (fun i => kap ell e q0 i) hε0 (r / n) hrn0 (j + 1) hεη m hm
    rwa [hnr] at h
  have hdriftQ : ∀ f, ‖Qrow (GP ell j Lu Rg) U f - Qrow (GP ell j Lu Rg) (trivialU _) f‖ ≤ (6 * r * q) * ‖f‖ := fun f => by
    have h := Qrow_patch_drift ell j hell0 Lu Rg hRg U (fun i => kap ell e q0 i) hcl (6 * r) (by positivity) hD f
    rwa [hqeq] at h
  have haq : 6 * r * q * aEP ell j = 162 * lamC ell * r := by
    rw [aEP_eq, hq, ← hn, ← hs]; field_simp; try ring
  have hεa : 6 * r * q * aEP ell j < 1 := by rw [haq]; nlinarith
  have hcoef : (bEP ell j + Real.sqrt 12 * (r / n) * aEP ell j) / (1 - 6 * r * q * aEP ell j) ≤ s * Bbar ell := by
    rw [haq]
    have hden : (1 : ℝ) / 2 ≤ 1 - 162 * lamC ell * r := by linarith
    have hnum : bEP ell j + Real.sqrt 12 * (r / n) * aEP ell j
        = s * (Real.sqrt 78732 * ell + 27 * Real.sqrt 12 * r) := by
      rw [aEP_eq, bEP_eq, ← hn, ← hs]; field_simp; try ring
    rw [hnum, div_le_iff₀ (by linarith)]
    unfold Bbar
    have h12 : 0 ≤ Real.sqrt 12 := Real.sqrt_nonneg _
    have h78 : 0 ≤ Real.sqrt 78732 := Real.sqrt_nonneg _
    have hA : 0 ≤ Real.sqrt 78732 * ell + 27 * Real.sqrt 12 * r := by positivity
    have hB : Real.sqrt 78732 * ell + 27 * Real.sqrt 12 * r ≤ Real.sqrt 78732 * ell + 27 * Real.sqrt 12 := by
      nlinarith
    nlinarith [mul_le_mul_of_nonneg_left hden (mul_nonneg hspos.le hA), mul_le_mul_of_nonneg_left hB hspos.le]
  have hext : ∀ w : CRow (GP ell j Lu Rg), ∃ f, Qrow (GP ell j Lu Rg) U f = w ∧ ‖gradL2 U f‖ ≤ (s * Bbar ell) * ‖w‖ := by
    intro w
    obtain ⟨f, hf, hfD⟩ := hext_row ell j hell0 Lu Rg hRg U (Real.sqrt 12 * (r / n)) (6 * r * q) (by positivity)
      (by positivity) hεa hd hdriftQ w
    exact ⟨f, hf, hfD.trans (mul_le_mul_of_nonneg_right hcoef (norm_nonneg _))⟩
  have hQN1 : ∀ ν ∈ NQp (GP ell j Lu Rg) (trivialU (scaleUp ell (j + 1) Lu)), ‖Qrow (GP ell j Lu Rg) U ν‖ ≤ (6 * r * q) * ‖ν‖ :=
    fun ν hν => hQN1_row (GP ell j Lu Rg) U (6 * r * q) hdriftQ ν hν
  have hNU : ∀ f, Qrow (GP ell j Lu Rg) U f = 0 → f ∈ NQp (GP ell j Lu Rg) U := fun f hf => mem_NQp_of_Qrow (GP ell j Lu Rg) hOm U f hf
  -- flat input
  have hflat := hflat_patch hell ha hCi hI j Lu Rg hRg
  -- smallness
  have hMc := Mc_pos a
  have hmM : Real.sqrt (Mc a) ^ 2 = Mc a := Real.sq_sqrt hMc.le
  set γ := gamS (n * Real.sqrt (Mc a)) (Real.sqrt 12 * (r / n)) (s * Bbar ell) (6 * r * q) q with hγ
  have hnγ : n * γ = r * GamP ell a := by
    rw [hγ, hq, gam_identity n s (lamC ell) (Bbar ell) (Real.sqrt (Mc a)) (Mc a) r hnpos hspos hmM]
    unfold GamP; ring
  have hKf := Kflat_pos ha hCi
  have hc1 : 0 < 1 / Kflat a Ci := by positivity
  have hθn : n ^ 2 * (272 * (q0 / (4 * Real.sqrt 2))) ≤ 272 * (r / (3 * Real.pi)) / (4 * Real.sqrt 2) := by
    have e1 : n ^ 2 * (272 * (q0 / (4 * Real.sqrt 2))) = 272 * (n ^ 2 * q0) / (4 * Real.sqrt 2) := by ring
    rw [e1]
    apply div_le_div_of_nonneg_right _ (by positivity)
    linarith
  have hδmn : n ^ 2 * δm ^ 2 ≤ 2 * (ell : ℝ) ^ 2 * (a * phiC ell (3600 * (ell : ℝ) * r) ^ 2) := by
    have e1 : n ^ 2 * δm ^ 2 = 2 * (ell : ℝ) ^ 2 * (n * deltaM ell (j + 1) a (fun i => kap ell e q0 i)) ^ 2 := by
      rw [hδm, mul_pow, mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]; ring
    rw [e1]
    have h2 : (n * deltaM ell (j + 1) a (fun i => kap ell e q0 i)) ^ 2
        ≤ (Real.sqrt a * phiC ell (3600 * (ell : ℝ) * r)) ^ 2 := pow_le_pow_left₀ (by positivity) hdM 2
    have h3 : (Real.sqrt a * phiC ell (3600 * (ell : ℝ) * r)) ^ 2 = a * phiC ell (3600 * (ell : ℝ) * r) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt ha.le]
    rw [h3] at h2
    have : (0 : ℝ) ≤ 2 * (ell : ℝ) ^ 2 := by positivity
    exact mul_le_mul_of_nonneg_left h2 this
  have hδcn : n ^ 2 * (4 * Real.sqrt 2 * (r / n)) ^ 2 = 32 * r ^ 2 := by
    rw [mul_pow, mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]; field_simp; ring
  have hΘ : n ^ 2 * γ ^ 2 + n ^ 2 * e' ≤ ThetaP ell a r := by
    have e1 : n ^ 2 * γ ^ 2 = (r * GamP ell a) ^ 2 := by rw [← hnγ]; ring
    have e2 : n ^ 2 * e' = 2 * (n ^ 2 * (272 * (q0 / (4 * Real.sqrt 2))))
        + 2 * (n ^ 2 * (4 * Real.sqrt 2 * (r / n)) ^ 2 + n ^ 2 * δm ^ 2) := by
      rw [he']; norm_num; ring
    rw [e1, e2, hδcn]
    unfold ThetaP
    linarith
  have hsmall : n ^ 2 * γ ^ 2 + n ^ 2 * e' < 1 / Kflat a Ci := by
    have hT0 : 0 ≤ ThetaP ell a r := by
      unfold ThetaP
      have := phiC_nonneg ell (show 0 ≤ 3600 * (ell : ℝ) * r by positivity)
      positivity
    linarith

  -- the slice bound at U
  have hn2 : 0 < n ^ 2 := by positivity
  have hslice : ∀ y : BondFnL2 (scaleUp ell (j + 1) Lu), Rproj (GP ell j Lu Rg) U (gradAdj U y) = 0 →
      (1 / Kflat a Ci - n ^ 2 * γ ^ 2 - n ^ 2 * e') / (1 + 1) * ‖y‖ ^ 2 ≤ n ^ 2 * PhiG (GP ell j Lu Rg) a U y :=
    fun y hy => slice_coercive_gen (GP ell j Lu Rg) hOm U a (Qrow (GP ell j Lu Rg) U) (n ^ 2) (1 / Kflat a Ci) 1 e'
      (n * Real.sqrt (Mc a)) (Real.sqrt 12 * (r / n)) (s * Bbar ell) (6 * r * q) q hn2.le zero_le_one (by positivity)
      (by positivity) (by unfold Bbar; positivity) (by positivity) hq0' hflat hdrift hPoinc1 hd hNU hext hQq hQN1 y hy
  -- decomposition A = A' + D ν
  set A' := Wop (GP ell j Lu Rg) U a A with hA'
  set ν := Gp (GP ell j Lu Rg) U a (Rproj (GP ell j Lu Rg) U (gradAdj U A)) with hνdef
  have hνN : ν ∈ NQp (GP ell j Lu Rg) U := (AdalyFormal.SliceCoerc.Gp_Rproj_mem (GP ell j Lu Rg) U a hu _).1
  have hdiff : A - A' = gradL2 U ν := by
    simp only [hA', Wop, ContinuousLinearMap.sub_apply, ContinuousLinearMap.one_apply,
      ContinuousLinearMap.comp_apply, hνdef]
    abel
  have hsl := hslice A' (AdalyFormal.SliceCoerc.slice_of_Wop (GP ell j Lu Rg) hOm U a hu A)
  have hPU0 : 0 ≤ Pc ell (j + 1) a r := Real.sqrt_nonneg _
  have hgp := AdalyFormal.SliceCoerc.gauge_part_le (GP ell j Lu Rg) hOm U a hu (Pc ell (j + 1) a r) hPU0 hPoincU A
  have hνP : ‖ν‖ ≤ Pc ell (j + 1) a r * ‖gradL2 U ν‖ := hPoincU ν hνN
  -- mass of A' = mass of A
  have hQ : (bondSectorOf (GP ell j Lu Rg) U).Qfull A' = (bondSectorOf (GP ell j Lu Rg) U).Qfull A := by
    have h1 : A' = A - gradL2 U ν := by rw [← hdiff]; abel
    rw [h1, map_sub, hB0 ν hνN, sub_zero]
  have hmass : ⟪A', MassFull (GP ell j Lu Rg) a (bondSectorOf (GP ell j Lu Rg) U) A'⟫
      = ‖AdalyFormal.M1IMS.Ymass (GP ell j Lu Rg) U a A‖ ^ 2 := by
    rw [inner_MassFull, ← AdalyFormal.M1IMS.inner_MassFull_eq (GP ell j Lu Rg) U a ha.le A, inner_MassFull, hQ]
  -- curl of A'
  set X := ‖AdalyFormal.StatementLaneR6.plaqMask (plaqIn (GP ell j Lu Rg).Om0)
    (AdalyFormal.Balaban.DeltaKFull.curlCovariantLM_L2 U A)‖ with hX
  set Tn := ‖Tfull (GP ell j Lu Rg) U A‖ with hTn
  set Mm := ‖AdalyFormal.M1IMS.Ymass (GP ell j Lu Rg) U a A‖ ^ 2 with hMm
  have hcg := curl_grad_le U q0 hq0 h0 (plaqIn (GP ell j Lu Rg).Om0) ν
  have hcurl : ‖AdalyFormal.StatementLaneR6.plaqMask (plaqIn (GP ell j Lu Rg).Om0)
      (AdalyFormal.Balaban.DeltaKFull.curlCovariantLM_L2 U A')‖ ^ 2
        ≤ 2 * X ^ 2 + 2 * (12 * q0 ^ 2 * ‖ν‖ ^ 2) := by
    have e1 : A' = A - gradL2 U ν := by rw [← hdiff]; abel
    rw [e1, map_sub, map_sub]
    have h1 := norm_sub_le (AdalyFormal.StatementLaneR6.plaqMask (plaqIn (GP ell j Lu Rg).Om0)
      (AdalyFormal.Balaban.DeltaKFull.curlCovariantLM_L2 U A))
      (AdalyFormal.StatementLaneR6.plaqMask (plaqIn (GP ell j Lu Rg).Om0)
      (AdalyFormal.Balaban.DeltaKFull.curlCovariantLM_L2 U (gradL2 U ν)))
    set Y := ‖AdalyFormal.StatementLaneR6.plaqMask (plaqIn (GP ell j Lu Rg).Om0)
      (AdalyFormal.Balaban.DeltaKFull.curlCovariantLM_L2 U (gradL2 U ν))‖
    have hY0 : 0 ≤ Y := norm_nonneg _
    have hX0 : 0 ≤ X := norm_nonneg _
    have h2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
    nlinarith [sq_nonneg (X - Y)]
  -- the Δ' term of A'
  have hdpA := hdp A'
  have hPhi : PhiG (GP ell j Lu Rg) a U A' = ‖AdalyFormal.StatementLaneR6.plaqMask (plaqIn (GP ell j Lu Rg).Om0)
        (AdalyFormal.Balaban.DeltaKFull.curlCovariantLM_L2 U A')‖ ^ 2
      + AdalyFormal.StatementLaneR6.deltaPrimeBilL2NormLoc U (plaqIn (GP ell j Lu Rg).Om0) A' A' + Mm := by
    unfold PhiG Delta
    rw [AdalyFormal.StatementLaneR6.inner_deltaKLocCLM, hmass, real_inner_self_eq_norm_sq]
  -- numeric facts
  have hq0n' : n ^ 2 * q0 ≤ 1 / (3 * Real.pi) := hq0n.trans (div_le_div_of_nonneg_right hs3 (by positivity))
  have hPU2 : Pc ell (j + 1) a r ^ 2 ≤ 2 * (n ^ 2 * Mc a) := by
    rw [Pc_sq ell (j + 1) a r h216, ← hn]
    have hden : (1 : ℝ) / 2 ≤ 1 - 216 * r ^ 2 := by nlinarith
    rw [div_le_iff₀ (by linarith)]
    nlinarith [mul_le_mul_of_nonneg_left hden (by positivity : (0 : ℝ) ≤ n ^ 2 * Mc a)]
  have hθ' : n ^ 2 * (272 * (q0 / (4 * Real.sqrt 2))) ≤ (1 / Kflat a Ci) / 8 := by
    have := hθn
    have h2 : 272 * (r / (3 * Real.pi)) / (4 * Real.sqrt 2) ≤ (1 / Kflat a Ci) / 8 := by linarith
    linarith
  have hcs4 : (1 / Kflat a Ci) / 4 ≤ (1 / Kflat a Ci - n ^ 2 * γ ^ 2 - n ^ 2 * e') / (1 + 1) := by
    have : n ^ 2 * γ ^ 2 + n ^ 2 * e' ≤ (1 / Kflat a Ci) / 2 := by linarith
    linarith
  -- ‖ν‖ ≤ PU² ‖T A‖
  have hgradν : ‖gradL2 U ν‖ ≤ Pc ell (j + 1) a r * Tn := by rw [← hdiff]; exact hgp
  have hν2 : ‖ν‖ ^ 2 ≤ Pc ell (j + 1) a r ^ 4 * Tn ^ 2 := by
    have h1 : ‖ν‖ ≤ Pc ell (j + 1) a r * (Pc ell (j + 1) a r * Tn) :=
      hνP.trans (mul_le_mul_of_nonneg_left hgradν hPU0)
    have h2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
    calc ‖ν‖ ^ 2 ≤ (Pc ell (j + 1) a r * (Pc ell (j + 1) a r * Tn)) ^ 2 := h2
      _ = Pc ell (j + 1) a r ^ 4 * Tn ^ 2 := by ring
  have hq0sq : n ^ 2 * (12 * q0 ^ 2 * Pc ell (j + 1) a r ^ 4) ≤ n ^ 2 * Mc a ^ 2 := by
    -- q0 ≤ 1/(3π n²), PU⁴ ≤ 4 n⁴ Mc²
    have hP4 : Pc ell (j + 1) a r ^ 4 ≤ 4 * (n ^ 2) ^ 2 * Mc a ^ 2 := by
      have h0 : 0 ≤ Pc ell (j + 1) a r ^ 2 := sq_nonneg _
      have := pow_le_pow_left₀ h0 hPU2 2
      calc Pc ell (j + 1) a r ^ 4 = (Pc ell (j + 1) a r ^ 2) ^ 2 := by ring
        _ ≤ (2 * (n ^ 2 * Mc a)) ^ 2 := this
        _ = 4 * (n ^ 2) ^ 2 * Mc a ^ 2 := by ring
    have hq2 : (n ^ 2 * q0) ^ 2 ≤ (1 / (3 * Real.pi)) ^ 2 := pow_le_pow_left₀ (by positivity) hq0n' 2
    have hpi3 : (3 : ℝ) < Real.pi := Real.pi_gt_three
    have hsmallc : 48 * (1 / (3 * Real.pi)) ^ 2 ≤ 1 := by
      rw [div_pow, one_pow]
      rw [mul_one_div, div_le_one (by positivity)]
      nlinarith
    apply mul_le_mul_of_nonneg_left _ hn2.le
    have hM2 : 0 ≤ Mc a ^ 2 := sq_nonneg _
    calc 12 * q0 ^ 2 * Pc ell (j + 1) a r ^ 4 ≤ 12 * q0 ^ 2 * (4 * (n ^ 2) ^ 2 * Mc a ^ 2) :=
          mul_le_mul_of_nonneg_left hP4 (by positivity)
      _ = 48 * (n ^ 2 * q0) ^ 2 * Mc a ^ 2 := by ring
      _ ≤ 48 * (1 / (3 * Real.pi)) ^ 2 * Mc a ^ 2 := by
          have := mul_le_mul_of_nonneg_right hq2 hM2
          linarith
      _ ≤ 1 * Mc a ^ 2 := mul_le_mul_of_nonneg_right hsmallc hM2
      _ = Mc a ^ 2 := by ring
  -- combine
  have hY'0 : 0 ≤ ‖A'‖ ^ 2 := sq_nonneg _
  have hdA := abs_le.mp hdpA
  have hc1pos : 0 < 1 / Kflat a Ci := hc1
  have hstep1 : (1 / Kflat a Ci) / 8 * ‖A'‖ ^ 2 ≤ n ^ 2 * (2 * X ^ 2 + Mm + 2 * Mc a ^ 2 * Tn ^ 2) := by
    have e2 : n ^ 2 * (2 * X ^ 2 + 2 * (12 * q0 ^ 2 * ‖ν‖ ^ 2)) ≤ n ^ 2 * (2 * X ^ 2) + n ^ 2 * (2 * Mc a ^ 2 * Tn ^ 2) := by
      have : n ^ 2 * (12 * q0 ^ 2 * ‖ν‖ ^ 2) ≤ n ^ 2 * (12 * q0 ^ 2 * Pc ell (j + 1) a r ^ 4) * Tn ^ 2 := by
        have := mul_le_mul_of_nonneg_left hν2 (show (0 : ℝ) ≤ n ^ 2 * (12 * q0 ^ 2) by positivity)
        linarith
      have h3 := mul_le_mul_of_nonneg_right hq0sq (sq_nonneg Tn)
      linarith
    have hθA : n ^ 2 * AdalyFormal.StatementLaneR6.deltaPrimeBilL2NormLoc U (plaqIn (GP ell j Lu Rg).Om0) A' A'
        ≤ (1 / Kflat a Ci) / 8 * ‖A'‖ ^ 2 := by
      have h1 := mul_le_mul_of_nonneg_left hdA.2 hn2.le
      have h2 := mul_le_mul_of_nonneg_right hθ' hY'0
      linarith
    have hsl' := hsl
    rw [hPhi] at hsl'
    have hcA := mul_le_mul_of_nonneg_left hcurl hn2.le
    have h4 := mul_le_mul_of_nonneg_right hcs4 hY'0
    linarith
  have htri : ‖A‖ ^ 2 ≤ 2 * ‖A'‖ ^ 2 + 2 * ‖A - A'‖ ^ 2 := by
    have h1 : ‖A‖ ≤ ‖A'‖ + ‖A - A'‖ := by
      calc ‖A‖ = ‖A' + (A - A')‖ := by congr 1; abel
        _ ≤ ‖A'‖ + ‖A - A'‖ := norm_add_le _ _
    nlinarith [norm_nonneg A, norm_nonneg A', norm_nonneg (A - A'), sq_nonneg (‖A'‖ - ‖A - A'‖)]
  have hZ : ‖A - A'‖ ^ 2 ≤ 2 * (n ^ 2 * Mc a) * Tn ^ 2 := by
    have h1 := pow_le_pow_left₀ (norm_nonneg _) hgp 2
    rw [mul_pow] at h1
    exact h1.trans (mul_le_mul_of_nonneg_right hPU2 (sq_nonneg _))
  have hG0 : G0form (patchTower j Rg) ell (j + 1) U a A = X ^ 2 + Tn ^ 2 + Mm := rfl
  rw [hG0]
  have hKf' : Kflat a Ci * (1 / Kflat a Ci) = 1 := by field_simp
  have hY'b : ‖A'‖ ^ 2 ≤ 8 * Kflat a Ci * (n ^ 2 * (2 * X ^ 2 + Mm + 2 * Mc a ^ 2 * Tn ^ 2)) := by
    have := mul_le_mul_of_nonneg_left hstep1 (show (0 : ℝ) ≤ 8 * Kflat a Ci by positivity)
    calc ‖A'‖ ^ 2 = 8 * Kflat a Ci * ((1 / Kflat a Ci) / 8 * ‖A'‖ ^ 2) := by field_simp
      _ ≤ _ := this
  have hX2 : 0 ≤ X ^ 2 := sq_nonneg _
  have hT2 : 0 ≤ Tn ^ 2 := sq_nonneg _
  have hM0 : 0 ≤ Mm := sq_nonneg _
  have hMc0 := hMc.le
  have hKf0 := hKf.le
  have hdiff2 : KG0 a Ci * (X ^ 2 + Tn ^ 2 + Mm)
      - (32 * Kflat a Ci * X ^ 2 + 16 * Kflat a Ci * Mm + 32 * Kflat a Ci * Mc a ^ 2 * Tn ^ 2 + 4 * Mc a * Tn ^ 2)
      = 32 * Kflat a Ci * Mc a ^ 2 * X ^ 2 + 4 * Mc a * X ^ 2 + 32 * Kflat a Ci * Tn ^ 2
        + 16 * Kflat a Ci * Mm + 32 * Kflat a Ci * Mc a ^ 2 * Mm
        + 4 * Mc a * Mm := by
    unfold KG0; ring
  have hdiff2' : 0 ≤ KG0 a Ci * (X ^ 2 + Tn ^ 2 + Mm)
      - (32 * Kflat a Ci * X ^ 2 + 16 * Kflat a Ci * Mm + 32 * Kflat a Ci * Mc a ^ 2 * Tn ^ 2 + 4 * Mc a * Tn ^ 2) := by
    rw [hdiff2]; positivity
  calc ‖A‖ ^ 2 ≤ 2 * (8 * Kflat a Ci * (n ^ 2 * (2 * X ^ 2 + Mm + 2 * Mc a ^ 2 * Tn ^ 2)))
        + 2 * (2 * (n ^ 2 * Mc a) * Tn ^ 2) := by linarith
    _ = n ^ 2 * (32 * Kflat a Ci * X ^ 2 + 16 * Kflat a Ci * Mm + 32 * Kflat a Ci * Mc a ^ 2 * Tn ^ 2
          + 4 * Mc a * Tn ^ 2) := by ring
    _ ≤ n ^ 2 * (KG0 a Ci * (X ^ 2 + Tn ^ 2 + Mm)) := mul_le_mul_of_nonneg_left (by linarith) hn2.le
    _ = n ^ 2 * KG0 a Ci * (X ^ 2 + Tn ^ 2 + Mm) := by ring

#print axioms KG0_pos
#print axioms curl_grad_le
#print axioms g0_patch_nonflat

end AdalyFormal.W3NF
