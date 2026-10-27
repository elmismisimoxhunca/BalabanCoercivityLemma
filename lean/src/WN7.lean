import WN6

/-!
# WN7 -- Ginv coercivity on the two-stratum patch at a NON-FLAT background, from `LemIFlat` and a link/plaquette regime

Patch `G = GP ell j Lu Rg` (torus `scaleUp ell (j+1) Lu`, `n = ell^(j+1)`), background `U` with
`dv (U b) ≤ e` (every link) and `dv (pw 1 U y ν μ) ≤ q0` (every plaquette), `ρ = rhoM0 ell (j+1) e q0 = n(e + 3π n q0)`,
`r = kapHat ell ρ` (the k-free all-bond tower radius of RKF/RKN2).

* `aEP_eq`, `bEP_eq`, `q_eq'`, `Pc0_eq` : closed forms of the FlatExt constants, `‖Q'‖` and the flat Poincaré constant.
* `gam_identity` : `n · γ = r · Γ` for the slice constant `γ = gamS P δ b ε q` at the chosen parameters.
* **`ginv_patch_nonflat`** : `‖x‖² ≤ n² · K0 a Ci · ⟨x, G⁻¹ x⟩` (r8 `IngrBParams.data.Ginv` of `gparams … U …`) assuming
  `LemIFlat ell a Ci`, `KUSmall ell ρ`, and the five numeric conditions `hs1`–`hs5` on `r` (none involves `j`, `Lu`, `Rg`).
  `K0 a Ci = max (8 Kflat) (4 Mc)`.
No sorry / axiom.
-/
set_option autoImplicit false
set_option maxHeartbeats 16000000

namespace AdalyFormal.W3NF

open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
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

/-- `λ = √(ell³)` -/
noncomputable def lamC (ell : ℕ) : ℝ := Real.sqrt ((ell : ℝ) ^ 3)

/-- the extension-energy constant `2(√78732 ell + 27√12)` -/
noncomputable def Bbar (ell : ℕ) : ℝ := 2 * (Real.sqrt 78732 * ell + 27 * Real.sqrt 12)

/-- the slice constant `Γ` (`n γ = r Γ`) -/
noncomputable def GamP (ell : ℕ) (a : ℝ) : ℝ :=
  Bbar ell * lamC ell * (Real.sqrt 12 * Real.sqrt (Mc a)
    + Bbar ell * lamC ell * Mc a * (Real.sqrt 12 + 6 * (Bbar ell * lamC ell))) + Real.sqrt 12

/-- the `n`-free smallness quantity (`t = 1`) -/
noncomputable def ThetaP (ell : ℕ) (a r : ℝ) : ℝ :=
  (r * GamP ell a) ^ 2 + 2 * (272 * (r / (3 * Real.pi)) / (4 * Real.sqrt 2))
    + 2 * (32 * r ^ 2 + 2 * (ell : ℝ) ^ 2 * (a * phiC ell (3600 * (ell : ℝ) * r) ^ 2))

/-- the `n`-free coercivity constant -/
noncomputable def K0 (a Ci : ℝ) : ℝ := max (8 * Kflat a Ci) (4 * Mc a)

theorem Mc_pos (a : ℝ) : 0 < Mc a := by
  unfold Mc; exact lt_of_lt_of_le (by norm_num) (le_max_left _ _)

theorem Kflat_pos {a Ci : ℝ} (ha : 0 < a) (hCi : 0 ≤ Ci) : 0 < Kflat a Ci := by
  unfold Kflat
  have hM : (0 : ℝ) < max 6 (16 / (3 * a)) := lt_of_lt_of_le (by norm_num) (le_max_left _ _)
  have : (0 : ℝ) < min a 1 / 1000 := by positivity
  positivity

theorem K0_pos {a Ci : ℝ} (ha : 0 < a) (hCi : 0 ≤ Ci) : 0 < K0 a Ci :=
  lt_of_lt_of_le (by have := Kflat_pos ha hCi; linarith) (le_max_left _ _)

theorem aEP_eq (ell j : ℕ) : aEP ell j = 27 * (ell : ℝ) ^ (j + 1) * Real.sqrt ((ell : ℝ) ^ (j + 1)) := by
  unfold aEP
  rw [← Real.sqrt_mul (by positivity)]
  have e : 729 * ((ell : ℝ) ^ j) ^ 3 * (ell : ℝ) ^ 3 = (27 * (ell : ℝ) ^ (j + 1)) ^ 2 * (ell : ℝ) ^ (j + 1) := by
    ring
  rw [e, Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]

theorem bEP_eq (ell j : ℕ) : bEP ell j = Real.sqrt 78732 * ell * Real.sqrt ((ell : ℝ) ^ (j + 1)) := by
  unfold bEP
  rw [← Real.sqrt_mul (by positivity)]
  have e : 78732 * (ell : ℝ) ^ j * (ell : ℝ) ^ 3 = (78732 * (ell : ℝ) ^ 2) * (ell : ℝ) ^ (j + 1) := by ring
  rw [e, Real.sqrt_mul (by positivity), Real.sqrt_mul (by norm_num), Real.sqrt_sq (by positivity)]

theorem q_eq' (ell j : ℕ) (hell : 0 < ell) :
    Real.sqrt ((1 / (ell : ℝ) ^ 3) ^ j) = lamC ell / ((ell : ℝ) ^ (j + 1) * Real.sqrt ((ell : ℝ) ^ (j + 1))) := by
  have hl : (0 : ℝ) < ell := by exact_mod_cast hell
  have hn : (0 : ℝ) < (ell : ℝ) ^ (j + 1) := by positivity
  have hs : 0 < Real.sqrt ((ell : ℝ) ^ (j + 1)) := Real.sqrt_pos.mpr hn
  have hpos : 0 ≤ lamC ell / ((ell : ℝ) ^ (j + 1) * Real.sqrt ((ell : ℝ) ^ (j + 1))) := by
    unfold lamC; positivity
  conv_rhs => rw [← Real.sqrt_sq hpos]
  congr 1
  have h1 : (lamC ell / ((ell : ℝ) ^ (j + 1) * Real.sqrt ((ell : ℝ) ^ (j + 1)))) ^ 2
      = (ell : ℝ) ^ 3 / (((ell : ℝ) ^ (j + 1)) ^ 2 * (ell : ℝ) ^ (j + 1)) := by
    unfold lamC
    rw [div_pow, mul_pow, Real.sq_sqrt (by positivity), Real.sq_sqrt hn.le]
  rw [h1, one_div_pow, div_eq_div_iff (by positivity) (by positivity)]
  ring

theorem Pc0_eq (ell k : ℕ) (a : ℝ) : Pc ell k a 0 = (ell : ℝ) ^ k * Real.sqrt (Mc a) := by
  unfold Pc Mc
  have hM : 0 ≤ max 6 (16 / (3 * a)) := le_trans (by norm_num) (le_max_left _ _)
  rw [show (1 : ℝ) - 216 * 0 ^ 2 = 1 by norm_num, div_one, Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]

theorem Pc_sq (ell k : ℕ) (a ρ : ℝ) (h : 216 * ρ ^ 2 < 1) :
    Pc ell k a ρ ^ 2 = ((ell : ℝ) ^ k) ^ 2 * Mc a / (1 - 216 * ρ ^ 2) := by
  unfold Pc
  have hM := Mc_pos a
  unfold Mc at hM ⊢
  rw [Real.sq_sqrt (div_nonneg (by positivity) (by linarith))]

/-- **the slice constant at the chosen parameters**: `n · γ = r · Γ`. -/
theorem gam_identity (n s lam B m M r : ℝ) (hn : 0 < n) (hs : 0 < s) (hm : m ^ 2 = M) :
    n * gamS (n * m) (Real.sqrt 12 * (r / n)) (s * B) (6 * r * (lam / (n * s))) (lam / (n * s))
      = r * (B * lam * (Real.sqrt 12 * m + B * lam * M * (Real.sqrt 12 + 6 * (B * lam))) + Real.sqrt 12) := by
  unfold gamS
  rw [← hm]
  field_simp
  try ring

theorem phiC_nonneg (ell : ℕ) {s : ℝ} (hs : 0 ≤ s) : 0 ≤ phiC ell s := by
  unfold phiC
  have := AdalyFormal.BondComposite.rr_nonneg ell
  positivity

/-- **Ginv coercivity on the patch at a non-flat background.** -/
theorem ginv_patch_nonflat {ell : ℕ} (hell : 2 ≤ ell) {a Ci : ℝ} (ha : 0 < a) (hCi : 0 ≤ Ci)
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
    (Lam : Set (PeriodicLatticeSite Lu)) (x : ↥(bondSupp (GP ell j Lu Rg))) :
    ‖x‖ ^ 2 ≤ ((ell : ℝ) ^ (j + 1)) ^ 2 * K0 a Ci *
      ⟪x, (gparams ell (j + 1) Lu (by omega) (patchTower j Rg) U a Lam).data.Ginv x⟫ := by
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
  -- assemble
  have hn2 : 0 < n ^ 2 := by positivity
  have hmain : ‖x‖ ^ 2 ≤ max (2 / csS (n ^ 2) (1 / Kflat a Ci) 1 e' γ) (2 * Pc ell (j + 1) a r ^ 2) *
      ⟪x, (gparams ell (j + 1) Lu (by omega) (patchTower j Rg) U a Lam).data.Ginv x⟫ :=
    ginv_coercive_gen (GP ell j Lu Rg) hOm U a _ hu hB0 (Pc ell (j + 1) a r) (Real.sqrt_nonneg _) hPoincU (Qrow (GP ell j Lu Rg) U)
      (n ^ 2) (1 / Kflat a Ci) 1 e' (n * Real.sqrt (Mc a)) (Real.sqrt 12 * (r / n)) (s * Bbar ell) (6 * r * q) q
      hn2 zero_le_one (by positivity) (by positivity) (by unfold Bbar; positivity) (by positivity) hq0'
      (by rw [← hγ]; linarith) hflat hdrift hPoinc1 hd hNU hext hQq hQN1 x
  set Gx := ⟪x, (gparams ell (j + 1) Lu (by omega) (patchTower j Rg) U a Lam).data.Ginv x⟫ with hGx
  have hcs : 2 / csS (n ^ 2) (1 / Kflat a Ci) 1 e' γ ≤ n ^ 2 * (8 * Kflat a Ci) := by
    unfold csS
    have hDpos : 0 < 1 / Kflat a Ci - n ^ 2 * γ ^ 2 - n ^ 2 * e' := by linarith
    have hD2 : (1 / Kflat a Ci) / 2 ≤ 1 / Kflat a Ci - n ^ 2 * γ ^ 2 - n ^ 2 * e' := by
      have hT0 : n ^ 2 * γ ^ 2 + n ^ 2 * e' ≤ (1 / Kflat a Ci) / 2 := by linarith
      linarith
    have e1 : 2 / ((1 / Kflat a Ci - n ^ 2 * γ ^ 2 - n ^ 2 * e') / (1 + 1) / n ^ 2)
        = 4 * n ^ 2 / (1 / Kflat a Ci - n ^ 2 * γ ^ 2 - n ^ 2 * e') := by
      field_simp; ring
    rw [e1, div_le_iff₀ hDpos]
    have h8 : n ^ 2 * (8 * Kflat a Ci) * ((1 / Kflat a Ci) / 2) = 4 * n ^ 2 := by field_simp; ring
    nlinarith [mul_le_mul_of_nonneg_left hD2 (by positivity : (0 : ℝ) ≤ n ^ 2 * (8 * Kflat a Ci))]
  have hPU : 2 * Pc ell (j + 1) a r ^ 2 ≤ n ^ 2 * (4 * Mc a) := by
    rw [Pc_sq ell (j + 1) a r h216, ← hn]
    have hden : (1 : ℝ) / 2 ≤ 1 - 216 * r ^ 2 := by nlinarith
    rw [mul_div_assoc', div_le_iff₀ (by linarith)]
    nlinarith [mul_le_mul_of_nonneg_left hden (by positivity : (0 : ℝ) ≤ n ^ 2 * (4 * Mc a))]
  have hKle : max (2 / csS (n ^ 2) (1 / Kflat a Ci) 1 e' γ) (2 * Pc ell (j + 1) a r ^ 2) ≤ n ^ 2 * K0 a Ci := by
    unfold K0
    rw [mul_max_of_nonneg _ _ hn2.le]
    exact max_le_max hcs hPU
  have hcspos : 0 < 2 / csS (n ^ 2) (1 / Kflat a Ci) 1 e' γ := by
    unfold csS
    have hDpos : 0 < 1 / Kflat a Ci - n ^ 2 * γ ^ 2 - n ^ 2 * e' := by linarith
    positivity
  have hKpos : 0 < max (2 / csS (n ^ 2) (1 / Kflat a Ci) 1 e' γ) (2 * Pc ell (j + 1) a r ^ 2) :=
    lt_of_lt_of_le hcspos (le_max_left _ _)
  have hGnn : 0 ≤ Gx := by
    by_contra hneg
    push Not at hneg
    have := mul_neg_of_pos_of_neg hKpos hneg
    have h0' : 0 ≤ ‖x‖ ^ 2 := sq_nonneg _
    linarith [hmain]
  calc ‖x‖ ^ 2 ≤ max (2 / csS (n ^ 2) (1 / Kflat a Ci) 1 e' γ) (2 * Pc ell (j + 1) a r ^ 2) * Gx := hmain
    _ ≤ n ^ 2 * K0 a Ci * Gx := mul_le_mul_of_nonneg_right hKle hGnn

#print axioms Mc_pos
#print axioms Kflat_pos
#print axioms K0_pos
#print axioms aEP_eq
#print axioms bEP_eq
#print axioms q_eq'
#print axioms Pc0_eq
#print axioms Pc_sq
#print axioms gam_identity
#print axioms phiC_nonneg
#print axioms ginv_patch_nonflat

end AdalyFormal.W3NF
