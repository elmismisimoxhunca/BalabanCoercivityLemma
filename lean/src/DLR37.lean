import DLR36

/-!
# DL37 -- the M0 regime package: every concrete input of the scaled chain, derived from `M0RegimeR` (+ `KUSmall`)

Text-adapted from the preamble of `ginv_coercive_M0_pinned_reg` (compute/regbg_kuniform_20261010/RKA.lean, copied, not edited):
with `n = ℓ^k`, `ρ = rhoM0 ℓ k e q0 = n(e + 3π n q0)`, `η = ρ/n`, `ε_j = ℓ^j e + 3π (ℓ²)^j q0`:
* `m0_hU` (`frobSupBond U ≤ ρ/n`), `m0_cl` (tower class), `m0_hAl`, **`m0_site`** (`(1−216ρ²)‖f‖² ≤ Mc(a) n² ⟪f,Δ'_a f⟫`),
  `m0_hu`, `m0_hd`, `m0_hQdrift`, `m0_hεa`, `m0_reg`, `m0_hε0`, `m0_hsm`, `m0_hpl` (`PlaqDef (q0/(4√2)) U`), `m0_nq0`
  (`n² q0 ≤ ρ/(3π)`), `m0_S` (`Σ_{i<k} θ(ε_i) ≤ 3600 ℓ ρ`).
-/
set_option autoImplicit false
set_option maxHeartbeats 16000000

namespace AdalyFormal.DLayer

open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Balaban.CovariantHjMinimizer (trivialU)
open AdalyFormal.Balaban.RegularUPerturbation (frobSupBond)
open AdalyFormal.SliceCoerc (coarseC Qtop GF)
open AdalyFormal.StatementLane (scaleUp)
open AdalyFormal.AsmM0 (M0RegimeR rhoM0 Mc AlignedLinkBound)
open AdalyFormal.BondComposite (TowerClass thetaOf)
open AdalyFormal.CurvBlock (dv)

section
variable (ell k : ℕ) (Lu : PeriodicLatticeExtent) (U : Cfg (scaleUp ell k Lu)) (a t e q0 : ℝ)
  (R : M0RegimeR ell k Lu U a t e q0)
include R

/-- the class link bounds of the tower -/
noncomputable def epsCl (j : ℕ) : ℝ := (ell : ℝ) ^ j * e + 3 * Real.pi * (((ell : ℝ) ^ 2) ^ j * q0)

theorem m0_rho_nonneg : 0 ≤ rhoM0 ell k e q0 := by
  have := R.he0; have := R.hq0; have := Real.pi_pos
  unfold rhoM0; positivity

theorem m0_hU : frobSupBond U ≤ rhoM0 ell k e q0 / (ell : ℝ) ^ k := by
  have hell0 : 0 < ell := by have := R.hell; omega
  have hnpos : (0 : ℝ) < (ell : ℝ) ^ k := by positivity
  refine (AdalyFormal.AsmM0.frobSupBond_le_of U R.hlinks).trans ?_
  unfold rhoM0
  have e1 : (ell : ℝ) ^ k * (e + 3 * Real.pi * ((ell : ℝ) ^ k * q0)) / (ell : ℝ) ^ k
      = e + 3 * Real.pi * ((ell : ℝ) ^ k * q0) := by field_simp
  rw [e1]
  have := R.hq0; have := Real.pi_pos
  nlinarith [mul_nonneg hnpos.le R.hq0]

theorem m0_hεs : ∀ j, j < k → epsCl ell e q0 j ≤ 1 / (1000 * (ell : ℝ) ^ 4) := by
  intro j hj
  have hell := R.hell
  have hellR : (2 : ℝ) ≤ ell := by exact_mod_cast hell
  have hellpos : (0 : ℝ) < ell := by linarith
  set n : ℝ := (ell : ℝ) ^ k with hn
  have hnpos : 0 < n := by positivity
  set ρ := rhoM0 ell k e q0 with hρdef
  set η : ℝ := e + 3 * Real.pi * (n * q0) with hηdef
  have hρ : ρ = n * η := rfl
  have hρnn : 0 ≤ ρ := m0_rho_nonneg ell k Lu U a t e q0 R
  have hηρ : η = ρ / n := by rw [hρ]; field_simp
  have hεη : epsCl ell e q0 j ≤ (ell : ℝ) ^ j * η :=
    AdalyFormal.BondComposite.eps_class_le ell k (by omega) e q0 R.hq0 j hj.le
  have h1 : (ell : ℝ) ^ j * ell ≤ n := by
    rw [hn, ← pow_succ]; exact pow_le_pow_right₀ (by linarith) hj
  have h2 : (ell : ℝ) ^ j * η ≤ ρ / ell := by
    rw [hηρ, mul_div_assoc', div_le_div_iff₀ hnpos hellpos]
    nlinarith [mul_le_mul_of_nonneg_left h1 hρnn]
  have h3 : ρ / ell ≤ 1 / (1000 * (ell : ℝ) ^ 4) := by
    calc ρ / ell ≤ (1 / (1000 * (ell : ℝ) ^ 3)) / ell := div_le_div_of_nonneg_right R.h1000 hellpos.le
      _ = 1 / (1000 * (ell : ℝ) ^ 4) := by field_simp
  exact hεη.trans (h2.trans h3)

theorem m0_hε0 : ∀ j, j < k → 0 ≤ epsCl ell e q0 j := by
  intro j _
  have := R.he0; have := R.hq0; have := Real.pi_pos
  unfold epsCl; positivity

theorem m0_cl : TowerClass ell k Lu U (epsCl ell e q0) :=
  AdalyFormal.BondComposite.towerClass_of_blocking ell k Lu R.hell U q0 e R.hq0
    (AdalyFormal.CurvBlock.pw_one_of_plaq U q0 R.hq0 R.hplaq) R.hlinks R.hN R.hcb

theorem m0_hAl : ∀ i, i < k → AlignedLinkBound (ell ^ i) (bgTower (GF ell k Lu) U i)
    (rhoM0 ell k e q0 * (ell : ℝ) ^ i / (ell : ℝ) ^ k) := by
  intro i hi z hz μ
  have hcl := m0_cl ell k Lu U a t e q0 R
  refine (hcl i hi z hz μ).trans ?_
  have hell := R.hell
  set n : ℝ := (ell : ℝ) ^ k with hn
  have hnpos : 0 < n := by positivity
  have hεη : epsCl ell e q0 i ≤ (ell : ℝ) ^ i * (e + 3 * Real.pi * (n * q0)) :=
    AdalyFormal.BondComposite.eps_class_le ell k (by omega) e q0 R.hq0 i hi.le
  refine hεη.trans (le_of_eq ?_)
  unfold rhoM0
  rw [← hn]; field_simp

theorem m0_site (f : SiteL2 (scaleUp ell k Lu)) :
    (1 - 216 * rhoM0 ell k e q0 ^ 2) * ‖f‖ ^ 2
      ≤ Mc a * ((ell : ℝ) ^ k) ^ 2 * ⟪f, DelpA (GF ell k Lu) U a f⟫ := by
  have hρnn := m0_rho_nonneg ell k Lu U a t e q0 R
  have hE := AdalyFormal.SiteCoercivity.geom_tower_sum ell k R.hell (rhoM0 ell k e q0) hρnn
  have h := AdalyFormal.AsmM0.site_coercive_GF_al ell k Lu R.hell U a R.ha (rhoM0 ell k e q0) (6 * rhoM0 ell k e q0)
    (m0_hU ell k Lu U a t e q0 R) (fun i => rhoM0 ell k e q0 * (ell : ℝ) ^ i / (ell : ℝ) ^ k)
    (m0_hAl ell k Lu U a t e q0 R) hE f
  have e1 : (1 : ℝ) - 72 * rhoM0 ell k e q0 ^ 2 - 4 * (6 * rhoM0 ell k e q0) ^ 2 = 1 - 216 * rhoM0 ell k e q0 ^ 2 := by ring
  rw [e1] at h
  unfold Mc
  exact h

theorem m0_hu : IsUnit (DelpA (GF ell k Lu) U a + (1 - siteMask (GF ell k Lu).Om0)) := by
  have hρnn := m0_rho_nonneg ell k Lu U a t e q0 R
  have hE := AdalyFormal.SiteCoercivity.geom_tower_sum ell k R.hell (rhoM0 ell k e q0) hρnn
  have h216 := R.h216
  have hpos : 72 * rhoM0 ell k e q0 ^ 2 + 4 * (6 * rhoM0 ell k e q0) ^ 2 < 1 := by nlinarith
  exact AdalyFormal.AsmM0.hu_al ell k Lu R.hell U a R.ha (rhoM0 ell k e q0) (6 * rhoM0 ell k e q0) hpos
    (m0_hU ell k Lu U a t e q0 R) (fun i => rhoM0 ell k e q0 * (ell : ℝ) ^ i / (ell : ℝ) ^ k)
    (m0_hAl ell k Lu U a t e q0 R) hE

theorem m0_hd (f : SiteL2 (scaleUp ell k Lu)) :
    ‖gradL2 (trivialU (scaleUp ell k Lu)) f - gradL2 U f‖
      ≤ (Real.sqrt 12 * (rhoM0 ell k e q0 / (ell : ℝ) ^ k)) * ‖f‖ := by
  have hell := R.hell
  have hρnn := m0_rho_nonneg ell k Lu U a t e q0 R
  have hnpos : (0 : ℝ) < (ell : ℝ) ^ k := by positivity
  exact AdalyFormal.SliceCoerc.hd_of_frobSup U (by positivity) (m0_hU ell k Lu U a t e q0 R) f

theorem m0_hQdrift (f : SiteL2 (scaleUp ell k Lu)) :
    ‖Qtop (GF ell k Lu) U f - Qtop (GF ell k Lu) (trivialU _) f‖
      ≤ (6 * rhoM0 ell k e q0 * Real.sqrt (1 / ((ell : ℝ) ^ k) ^ 3)) * ‖f‖ := by
  have hell0 : 0 < ell := by have := R.hell; omega
  have hcl := m0_cl ell k Lu U a t e q0 R
  have h := AdalyFormal.BondComposite.class_eps0_bound ell k R.hell e q0 R.he0 R.hq0
  refine (AdalyFormal.BondComposite.hQdrift_of_tower ell k Lu hell0 U (epsCl ell e q0) hcl f).trans ?_
  refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg f)
  refine h.trans (le_of_eq ?_)
  unfold rhoM0; ring

theorem m0_hεa : (6 * rhoM0 ell k e q0 * Real.sqrt (1 / ((ell : ℝ) ^ k) ^ 3)) * AdalyFormal.FlatExt.aFE ell k < 1 := by
  have hell0 : 0 < ell := by have := R.hell; omega
  have hellR : (2 : ℝ) ≤ ell := by exact_mod_cast R.hell
  have e1 : (6 * rhoM0 ell k e q0 * Real.sqrt (1 / ((ell : ℝ) ^ k) ^ 3)) * AdalyFormal.FlatExt.aFE ell k
      = 6 * rhoM0 ell k e q0 * 27 := by
    have := AdalyFormal.AsmM0.aFE_mul_q ell k hell0
    calc 6 * rhoM0 ell k e q0 * Real.sqrt (1 / ((ell : ℝ) ^ k) ^ 3) * AdalyFormal.FlatExt.aFE ell k
        = 6 * rhoM0 ell k e q0 * (AdalyFormal.FlatExt.aFE ell k * Real.sqrt (1 / ((ell : ℝ) ^ k) ^ 3)) := by ring
      _ = 6 * rhoM0 ell k e q0 * 27 := by rw [this]
  rw [e1]
  have : 1000 * (ell : ℝ) ^ 3 ≥ 8000 := by nlinarith [pow_le_pow_left₀ (by norm_num) hellR 3]
  have h8 : rhoM0 ell k e q0 ≤ 1 / 8000 := R.h1000.trans (by rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith)
  linarith

theorem m0_hsm : ∀ j, j < k → AdalyFormal.NonflatJet.rhoOf ell (epsCl ell e q0 j) < Real.pi / 2 := by
  intro j hj
  have hell0 : 0 < ell := by have := R.hell; omega
  exact AdalyFormal.BondComposite.hsm_of_le ell hell0 (epsCl ell e q0 j) (m0_hε0 ell k Lu U a t e q0 R j hj)
    (m0_hεs ell k Lu U a t e q0 R j hj)

theorem m0_hpl : AdalyFormal.NonflatHunit.PlaqDef (q0 / (4 * Real.sqrt 2)) U := by
  intro p
  have h := R.hplaq p
  have e1 : 4 * Real.sqrt 2 * (q0 / (4 * Real.sqrt 2)) = q0 := by
    have : Real.sqrt 2 ≠ 0 := by positivity
    field_simp
  rw [e1]; exact h

theorem m0_nq0 : ((ell : ℝ) ^ k) ^ 2 * q0 ≤ rhoM0 ell k e q0 / (3 * Real.pi) := by
  have h := (AdalyFormal.RegBgKU.class_bounds ell k (by have := R.hell; omega) e q0 R.he0 R.hq0).2.1
  have e1 : ((ell : ℝ) ^ 2) ^ k = ((ell : ℝ) ^ k) ^ 2 := by rw [← pow_mul, ← pow_mul, mul_comm]
  rw [e1] at h
  exact h

theorem m0_S : ∑ i ∈ Finset.range k, thetaOf ell (epsCl ell e q0 i) ≤ 3600 * (ell : ℝ) * rhoM0 ell k e q0 := by
  have hη : 0 ≤ e + 3 * Real.pi * ((ell : ℝ) ^ k * q0) := by
    have := R.he0; have := R.hq0; have := Real.pi_pos; positivity
  have h := AdalyFormal.BondComposite.S_le ell k R.hell (epsCl ell e q0) _ hη (m0_hε0 ell k Lu U a t e q0 R)
    (fun j hj => AdalyFormal.BondComposite.eps_class_le ell k (by have := R.hell; omega) e q0 R.hq0 j hj.le)
    (m0_hεs ell k Lu U a t e q0 R)
  refine h.trans (le_of_eq ?_)
  unfold rhoM0; ring

end

#print axioms m0_rho_nonneg
#print axioms m0_hU
#print axioms m0_hεs
#print axioms m0_hε0
#print axioms m0_cl
#print axioms m0_hAl
#print axioms m0_site
#print axioms m0_hu
#print axioms m0_hd
#print axioms m0_hQdrift
#print axioms m0_hεa
#print axioms m0_hsm
#print axioms m0_hpl
#print axioms m0_nq0
#print axioms m0_S

end AdalyFormal.DLayer
