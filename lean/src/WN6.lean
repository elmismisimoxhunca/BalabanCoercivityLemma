import WN5
import RKF
import MF7
import GN11
import GN13
import PB3
import SL1

/-!
# WN6 -- the non-flat ingredients on the two-stratum patch `GP ell j Lu Rg` (torus `scaleUp ell (j+1) Lu`)

* `dsum_le_class` : `|dsum ell ε m| ≤ 6 ell^k η` for `ε ≥ 0`, `ε_i ≤ ell^i η` (`i < k`), `m ≤ k`.
* `patch_rows_ge` : every constraint row of the patch has level `≥ j`.
* `Qrow_patch_norm`, `Qrow_patch_drift` : `‖Q'(U)‖ ≤ q`, `‖Q'(U) − Q'(1)‖ ≤ D q`, `q = √((ℓ⁻³)^j)`.
* `hext_row` : a right inverse of `Q'(U)` (all rows) with `‖D_U f‖ ≤ (b + δ a)/(1 − ε₀ a) ‖w‖` (flat right inverse of WN4
  + gradient drift `δ` + constraint drift `ε₀`, SL1 `ext_of_rightInverse`).
* `hQN1_row` : `‖Q'(U) ν‖ ≤ ε₀ ‖ν‖` on `N(Q'(1))`.
* `towerClass_patch` : the background tower class with `ε_i = kap ell e q0 i` from RKN2 `dv_bg_le` (ALL bonds, no
  torus-size hypothesis), under `TowerSmall ell (j+1) e q0`.
* `kap_le_class` : `kap_i ≤ ell^i (kap_k / ell^k)` (`i ≤ k`).
* `hU_patch`, `hT_patch` : lane C's site hypotheses from a uniform link bound `r/ell^(j+1)` and the tower class.
* `hflat_patch` : the flat input `(1/Kflat) ‖y‖² ≤ n² (Φ_1(y) + ‖R_1 D_1* y‖²)` from `LemIFlat` (lane D's R1q route).
* `theta_patch` : given `PlaqDef α U` (`α ≥ 0`), `|Δ'_U(x,x)| ≤ 272 α ‖x‖²` on the patch (M0 `theta_ported`, `Ω₀ = univ`).
No sorry / axiom.
-/
set_option autoImplicit false
set_option maxHeartbeats 8000000

namespace AdalyFormal.W3NF

open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.Balaban.CovariantHjMinimizer (trivialU)
open AdalyFormal.Balaban.AdmissibleSubspace (blockOf CoarseLattice mem_CoarseLattice Bond)
open AdalyFormal.Balaban.RMapLipschitz (frobNorm)
open AdalyFormal.Balaban.CoarseCurl (coarseShift)
open AdalyFormal.StatementLane (BlockClosed scaleUp)
open AdalyFormal.M1Site (QIdx jq yq jq_le yq_mem)
open AdalyFormal.SiteCoercivity (ProperTower)
open AdalyFormal.M1Patch (patchTower GP patch_proper om0_univ dvd_scaleUp lam_lt LemIFlat Kflat Kq Pc PhiP)
open AdalyFormal.BondComposite (TowerClass dsum)
open AdalyFormal.CurvBlock (dv pw)
open AdalyFormal.RegBgKU (KUSmall kapHat kap TowerSmall dv_bg_le Kc_pos)

/-! ### arithmetic -/

theorem dsum_nonneg' (ell : ℕ) (hell : 1 ≤ ell) (ε : ℕ → ℝ) (hε0 : ∀ i, 0 ≤ ε i) (m : ℕ) :
    0 ≤ dsum ell ε m := by
  have hl : (1 : ℝ) ≤ ell := by exact_mod_cast hell
  unfold dsum
  refine Finset.sum_nonneg (fun i _ => ?_)
  have := hε0 i
  have : (0 : ℝ) ≤ (ell : ℝ) - 1 := by linarith
  positivity

theorem dsum_le_class (ell : ℕ) (hell : 2 ≤ ell) (ε : ℕ → ℝ) (hε0 : ∀ i, 0 ≤ ε i) (η : ℝ) (hη : 0 ≤ η)
    (k : ℕ) (hε : ∀ i, i < k → ε i ≤ (ell : ℝ) ^ i * η) (m : ℕ) (hm : m ≤ k) :
    |dsum ell ε m| ≤ 6 * ((ell : ℝ) ^ k * η) := by
  have hl : (2 : ℝ) ≤ ell := by exact_mod_cast hell
  rw [abs_of_nonneg (dsum_nonneg' ell (by omega) ε hε0 m)]
  have hmono : dsum ell ε m ≤ dsum ell ε k := by
    unfold dsum
    refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hm) (fun i _ _ => ?_)
    have := hε0 i
    have : (0 : ℝ) ≤ (ell : ℝ) - 1 := by linarith
    positivity
  refine hmono.trans ?_
  have hgeom := geom_sum_mul (ell : ℝ) k
  unfold dsum
  calc ∑ i ∈ Finset.range k, 6 * ((ell : ℝ) - 1) * ε i
      ≤ ∑ i ∈ Finset.range k, 6 * ((ell : ℝ) - 1) * ((ell : ℝ) ^ i * η) :=
        Finset.sum_le_sum fun i hi => mul_le_mul_of_nonneg_left (hε i (Finset.mem_range.mp hi)) (by linarith)
    _ = 6 * η * ((∑ i ∈ Finset.range k, (ell : ℝ) ^ i) * ((ell : ℝ) - 1)) := by
        rw [Finset.sum_mul, Finset.mul_sum]
        exact Finset.sum_congr rfl fun i _ => by ring
    _ = 6 * η * ((ell : ℝ) ^ k - 1) := by rw [hgeom]
    _ ≤ 6 * ((ell : ℝ) ^ k * η) := by nlinarith [hη]

theorem le_mul_of_sq_le {x y c : ℝ} (hc : 0 ≤ c) (hx : 0 ≤ x) (hy : 0 ≤ y) (h : x ^ 2 ≤ c ^ 2 * y ^ 2) :
    x ≤ c * y := by
  have h2 : x ^ 2 ≤ (c * y) ^ 2 := by rw [mul_pow]; exact h
  calc x = Real.sqrt (x ^ 2) := (Real.sqrt_sq hx).symm
    _ ≤ Real.sqrt ((c * y) ^ 2) := Real.sqrt_le_sqrt h2
    _ = c * y := Real.sqrt_sq (by positivity)

/-! ### the constraint rows of the patch -/

theorem patch_rows_ge {ell j : ℕ} {L : PeriodicLatticeExtent} (Rg : Set (PeriodicLatticeSite L))
    (q : QIdx (geomOf ell (j + 1) (patchTower j Rg))) : j ≤ jq q := by
  by_contra h
  push Not at h
  have hy := yq_mem q
  have hL : (geomOf ell (j + 1) (patchTower j Rg)).Lam (jq q) = ∅ := lam_lt ell j Rg h
  rw [hL] at hy
  exact hy

section rows
variable (ell j : ℕ) (hell : 0 < ell) (Lu : PeriodicLatticeExtent)
  (Rg : Set (PeriodicLatticeSite (scaleUp ell (j + 1) Lu))) (hRg : BlockClosed (ell ^ (j + 1)) Rg)
include hell hRg

theorem Qrow_patch_norm (U : Cfg (scaleUp ell (j + 1) Lu)) (f : SiteL2 (scaleUp ell (j + 1) Lu)) :
    ‖Qrow (GP ell j Lu Rg) U f‖ ≤ Real.sqrt ((1 / (ell : ℝ) ^ 3) ^ j) * ‖f‖ := by
  have h := Qrow_norm_sq (patch_proper hell hRg) (dvd_scaleUp ell j Lu hell) hell j (fun q => patch_rows_ge Rg q) U f
  have hc : (0 : ℝ) ≤ (1 / (ell : ℝ) ^ 3) ^ j := by positivity
  refine le_mul_of_sq_le (Real.sqrt_nonneg _) (norm_nonneg _) (norm_nonneg _) ?_
  rw [Real.sq_sqrt hc]; exact h

theorem Qrow_patch_drift (U : Cfg (scaleUp ell (j + 1) Lu)) (ε : ℕ → ℝ)
    (hcl : TowerClass ell (j + 1) Lu U ε) (D : ℝ) (hD0 : 0 ≤ D)
    (hD : ∀ m, m ≤ j + 1 → |dsum ell ε m| ≤ D) (f : SiteL2 (scaleUp ell (j + 1) Lu)) :
    ‖Qrow (GP ell j Lu Rg) U f - Qrow (GP ell j Lu Rg) (trivialU _) f‖
      ≤ D * Real.sqrt ((1 / (ell : ℝ) ^ 3) ^ j) * ‖f‖ := by
  have h := Qrow_drift_sq (patch_proper hell hRg) (dvd_scaleUp ell j Lu hell) hell j (fun q => patch_rows_ge Rg q) U ε
    (fun i hi y hy μ => hcl i hi y hy μ) D hD0 (fun q => hD (jq q) (jq_le q)) f
  have hc : (0 : ℝ) ≤ (1 / (ell : ℝ) ^ 3) ^ j := by positivity
  refine le_mul_of_sq_le (by positivity) (norm_nonneg _) (norm_nonneg _) ?_
  rw [mul_pow, Real.sq_sqrt hc]
  calc _ ≤ D ^ 2 * ((1 / (ell : ℝ) ^ 3) ^ j * ‖f‖ ^ 2) := h
    _ = _ := by ring

/-- **the right inverse of `Q'(U)` on the patch.** -/
theorem hext_row (U : Cfg (scaleUp ell (j + 1) Lu)) (δ ε0 : ℝ) (hδ : 0 ≤ δ) (hε0 : 0 ≤ ε0)
    (hεa : ε0 * aEP ell j < 1)
    (hd : ∀ f, ‖gradL2 (trivialU (scaleUp ell (j + 1) Lu)) f - gradL2 U f‖ ≤ δ * ‖f‖)
    (hdrift : ∀ f, ‖Qrow (GP ell j Lu Rg) U f - Qrow (GP ell j Lu Rg) (trivialU _) f‖ ≤ ε0 * ‖f‖)
    (w : CRow (GP ell j Lu Rg)) :
    ∃ f, Qrow (GP ell j Lu Rg) U f = w ∧
      ‖gradL2 U f‖ ≤ (bEP ell j + δ * aEP ell j) / (1 - ε0 * aEP ell j) * ‖w‖ := by
  obtain ⟨E1, hQE, hEa, hEb⟩ := flatExt_patch_gen ell j hell (scaleUp ell 1 Lu) (scaleUp ell (j + 1) Lu)
    (scaleUp_split ell j hell Lu) Rg hRg (dvd_scaleUp ell j Lu hell)
  have haE := aEP_nonneg ell j
  have hbE := bEP_nonneg ell j
  have hEbU : ∀ w, ‖gradL2 U (E1 w)‖ ≤ (bEP ell j + δ * aEP ell j) * ‖w‖ := by
    intro w
    have h1 : ‖gradL2 U (E1 w)‖ ≤ ‖gradL2 (trivialU (scaleUp ell (j + 1) Lu)) (E1 w)‖
        + ‖gradL2 (trivialU (scaleUp ell (j + 1) Lu)) (E1 w) - gradL2 U (E1 w)‖ := by
      have := norm_sub_le (gradL2 (trivialU (scaleUp ell (j + 1) Lu)) (E1 w))
        (gradL2 (trivialU (scaleUp ell (j + 1) Lu)) (E1 w) - gradL2 U (E1 w))
      simpa using this
    have h2 := hd (E1 w)
    have h3 := mul_le_mul_of_nonneg_left (hEa w) hδ
    nlinarith [hEb w]
  have hb' : 0 ≤ bEP ell j + δ * aEP ell j := by positivity
  obtain ⟨f, hf, hfD, -⟩ := AdalyFormal.SliceCoerc.ext_of_rightInverse
    (Qrow (GP ell j Lu Rg) (trivialU _)) (Qrow (GP ell j Lu Rg) U) E1 (gradL2 U) (aEP ell j)
    (bEP ell j + δ * aEP ell j) ε0 haE hb' hε0 hεa hQE hEa hEbU hdrift w
  exact ⟨f, hf, hfD⟩

end rows

theorem hQN1_row {L : PeriodicLatticeExtent} (G : TowerGeom L) (U : Cfg L) (ε0 : ℝ)
    (hdrift : ∀ f, ‖Qrow G U f - Qrow G (trivialU L) f‖ ≤ ε0 * ‖f‖) (ν : SiteL2 L)
    (hν : ν ∈ NQp G (trivialU L)) : ‖Qrow G U ν‖ ≤ ε0 * ‖ν‖ := by
  have := hdrift ν
  rwa [Qrow_of_NQp G (trivialU L) ν hν, sub_zero] at this

/-! ### background tower -/

/-- **the tower class on the patch from the ALL-bond tower bound** (no torus-size hypothesis). -/
theorem towerClass_patch (ell j : ℕ) (hell : 2 ≤ ell) (Lu : PeriodicLatticeExtent)
    (U : Cfg (scaleUp ell (j + 1) Lu)) (e q0 : ℝ) (he0 : 0 ≤ e) (hq0 : 0 ≤ q0)
    (hlinks : ∀ b, dv (U b) ≤ e) (h0 : ∀ y ν μ, dv (pw 1 U y ν μ) ≤ q0)
    (S : TowerSmall ell (j + 1) e q0) :
    TowerClass ell (j + 1) Lu U (fun i => kap ell e q0 i) := by
  intro i hi y _ μ
  exact dv_bg_le ell (j + 1) hell U e q0 he0 hq0 hlinks h0 S i hi.le (y, μ)

theorem kap_nonneg' (ell : ℕ) (hell : 2 ≤ ell) (e q0 : ℝ) (he0 : 0 ≤ e) (hq0 : 0 ≤ q0) (i : ℕ) :
    0 ≤ kap ell e q0 i := by
  have hKc := Kc_pos ell hell
  unfold kap AdalyFormal.RegBgKU.Bnd
  positivity

theorem kap_le_class (ell : ℕ) (hell : 2 ≤ ell) (e q0 : ℝ) (he0 : 0 ≤ e) (hq0 : 0 ≤ q0) (k i : ℕ) (hik : i ≤ k) :
    kap ell e q0 i ≤ (ell : ℝ) ^ i * (kap ell e q0 k / (ell : ℝ) ^ k) := by
  have hl : (1 : ℝ) ≤ ell := by exact_mod_cast (by omega : 1 ≤ ell)
  have hKc := Kc_pos ell hell
  have hk : (0 : ℝ) < (ell : ℝ) ^ k := by positivity
  have hpi : (ell : ℝ) ^ i ≤ (ell : ℝ) ^ k := pow_le_pow_right₀ hl hik
  have hQ : 0 ≤ q0 + e ^ 2 := by positivity
  unfold kap AdalyFormal.RegBgKU.Bnd
  have e1 : (ell : ℝ) ^ i * ((2 * ((ell : ℝ) ^ k * e)
        + AdalyFormal.RegBgKU.Kc ell * (((ell : ℝ) ^ 2) ^ k * (q0 + e ^ 2))) / (ell : ℝ) ^ k)
      = 2 * ((ell : ℝ) ^ i * e) + AdalyFormal.RegBgKU.Kc ell * ((ell : ℝ) ^ i * (ell : ℝ) ^ k * (q0 + e ^ 2)) := by
    field_simp; ring
  have e2 : ((ell : ℝ) ^ 2) ^ i = (ell : ℝ) ^ i * (ell : ℝ) ^ i := by ring
  rw [e1, e2]
  have h3 : (ell : ℝ) ^ i * (ell : ℝ) ^ i * (q0 + e ^ 2) ≤ (ell : ℝ) ^ i * (ell : ℝ) ^ k * (q0 + e ^ 2) := by
    apply mul_le_mul_of_nonneg_right _ hQ
    exact mul_le_mul_of_nonneg_left hpi (by positivity)
  nlinarith [mul_le_mul_of_nonneg_left h3 hKc.le]

/-! ### lane C site hypotheses -/

theorem hU_patch (ell j : ℕ) (hell : 0 < ell) {L : PeriodicLatticeExtent} (G : TowerGeom L) (U : Cfg L) (r : ℝ)
    (hr : 0 ≤ r) (hlinks : ∀ b, dv (U b) ≤ r / (ell : ℝ) ^ (j + 1)) :
    ∀ i, i ≤ j + 1 → ∀ y ∈ G.Lam i, ∀ b ∈ AdalyFormal.SiteCoercivity.inBlockBonds y (ell ^ i),
      frobNorm ((U b : Matrix (Fin 2) (Fin 2) ℂ) - 1) ≤ r / (ell : ℝ) ^ i := by
  intro i hi y _ b _
  have hl : (1 : ℝ) ≤ ell := by exact_mod_cast hell
  refine (hlinks b).trans ?_
  exact div_le_div_of_nonneg_left hr (by positivity) (pow_le_pow_right₀ hl hi)

theorem hT_patch (ell j : ℕ) (hell : 0 < ell) (Lu : PeriodicLatticeExtent)
    (Rg : Set (PeriodicLatticeSite (scaleUp ell (j + 1) Lu))) (U : Cfg (scaleUp ell (j + 1) Lu))
    (ε : ℕ → ℝ) (r : ℝ) (hr : 0 ≤ r) (hcl : TowerClass ell (j + 1) Lu U ε)
    (hε : ∀ i, i < j + 1 → ε i ≤ (ell : ℝ) ^ i * (r / (ell : ℝ) ^ (j + 1))) :
    ∀ i, i ≤ j + 1 → ∀ y ∈ (GP ell j Lu Rg).Lam i, ∀ i', i' < i → ∀ z ∈ blockOf y (ell ^ i),
      z ∈ CoarseLattice (scaleUp ell (j + 1) Lu) (ell ^ i') → ∀ μ : Fin 3,
      coarseShift z (ell ^ i') μ ∈ blockOf y (ell ^ i) →
      frobNorm ((bgTower (GP ell j Lu Rg) U i' (z, μ) : Matrix (Fin 2) (Fin 2) ℂ) - 1)
        ≤ r * (ell : ℝ) ^ i' / (ell : ℝ) ^ i := by
  intro i hi y _ i' hi' z _ hz μ _
  have hl : (1 : ℝ) ≤ ell := by exact_mod_cast hell
  have h1 := hcl i' (by omega) z hz μ
  refine h1.trans ((hε i' (by omega)).trans ?_)
  have e1 : (ell : ℝ) ^ i' * (r / (ell : ℝ) ^ (j + 1)) = r * (ell : ℝ) ^ i' / (ell : ℝ) ^ (j + 1) := by ring
  rw [e1]
  exact div_le_div_of_nonneg_left (by positivity) (by positivity) (pow_le_pow_right₀ hl hi)

/-! ### the flat input on the patch, from `LemIFlat` -/

/-- **flat input** `(1/Kflat) ‖y‖² ≤ n² (Φ_1(y) + ‖R_1 D_1* y‖²)`, every `y`, `n = ell^(j+1)`. -/
theorem hflat_patch {ell : ℕ} (hell : 2 ≤ ell) {a Ci : ℝ} (ha : 0 < a) (hCi : 0 ≤ Ci) (hI : LemIFlat ell a Ci)
    (j : ℕ) (Lu : PeriodicLatticeExtent) (Rg : Set (PeriodicLatticeSite (scaleUp ell (j + 1) Lu)))
    (hRg : BlockClosed (ell ^ (j + 1)) Rg) (y : BondFnL2 (scaleUp ell (j + 1) Lu)) :
    1 / Kflat a Ci * ‖y‖ ^ 2 ≤ ((ell : ℝ) ^ (j + 1)) ^ 2 *
      (PhiG (GP ell j Lu Rg) a (trivialU _) y
        + ‖Rproj (GP ell j Lu Rg) (trivialU _) (gradAdj (trivialU _) y)‖ ^ 2) := by
  have hell0 : 0 < ell := by omega
  have hdvd := dvd_scaleUp ell j Lu hell0
  have hP : ProperTower (GP ell j Lu Rg) ell (j + 1) := patch_proper hell0 hRg
  have hOm : (GP ell j Lu Rg).Om0 = Set.univ := om0_univ j Rg ell
  have hu : IsUnit (DelpA (GP ell j Lu Rg) (flatCfg : Cfg (scaleUp ell (j + 1) Lu)) a
      + (1 - siteMask (GP ell j Lu Rg).Om0)) :=
    AdalyFormal.M1Site.isUnit_LP_strat ell (j + 1) hell hdvd hP (flatCfg : Cfg (scaleUp ell (j + 1) Lu)) a ha 0 le_rfl
      (by norm_num) (AdalyFormal.M1Patch.flat_hU ell (j + 1) (GP ell j Lu Rg))
      (AdalyFormal.M1Patch.flat_hT ell (j + 1) (GP ell j Lu Rg))
  have hreg : RegTower ell (bgTower (GP ell j Lu Rg) (flatCfg : Cfg (scaleUp ell (j + 1) Lu))) (j + 1) :=
    fun i _ => by rw [AdalyFormal.M1Patch.bg_flat]; exact RegBg_flat _ _
  have hB0 := AdalyFormal.M1Patch.patch_B0 hell0 hRg hdvd (flatCfg : Cfg (scaleUp ell (j + 1) Lu)) hreg
  have hM : (0 : ℝ) < max 6 (16 / (3 * a)) := lt_of_lt_of_le (by norm_num) (le_max_left _ _)
  have hn : (0 : ℝ) < ((ell : ℝ) ^ (j + 1)) ^ 2 := by
    have : (0 : ℝ) < ell := by exact_mod_cast hell0
    positivity
  have hc1 : (0 : ℝ) < min a 1 / 1000 := by positivity
  have hmain := AdalyFormal.M1Patch.r1q_coercive (gradL2 (flatCfg : Cfg (scaleUp ell (j + 1) Lu)))
    (NQp (GP ell j Lu Rg) (flatCfg : Cfg (scaleUp ell (j + 1) Lu)))
    (Rproj (GP ell j Lu Rg) (flatCfg : Cfg (scaleUp ell (j + 1) Lu)))
    (PhiP (GP ell j Lu Rg) (flatCfg : Cfg (scaleUp ell (j + 1) Lu)) a)
    (fun A ν hν => AdalyFormal.M1Patch.PhiP_inv (GP ell j Lu Rg) (flatCfg : Cfg (scaleUp ell (j + 1) Lu)) a hOm hu
      hB0 A ν hν)
    (fun ν hν => AdalyFormal.M1Patch.Rproj_fix (GP ell j Lu Rg) (flatCfg : Cfg (scaleUp ell (j + 1) Lu)) hOm ν hν)
    (fun s => AdalyFormal.M1Patch.Rproj_le (GP ell j Lu Rg) (flatCfg : Cfg (scaleUp ell (j + 1) Lu)) s)
    (Pc ell (j + 1) a 0) ((min a 1 / 1000) / (((ell : ℝ) ^ (j + 1)) ^ 2 * (1 + Ci))) Ci
    (Real.sqrt_nonneg _) (by positivity) hCi
    (fun ν hν => AdalyFormal.M1Patch.poincare_patch hell hdvd hP hOm (flatCfg : Cfg (scaleUp ell (j + 1) Lu)) a ha
      0 le_rfl (by norm_num) (AdalyFormal.M1Patch.flat_hU ell (j + 1) (GP ell j Lu Rg))
      (AdalyFormal.M1Patch.flat_hT ell (j + 1) (GP ell j Lu Rg)) ν hν)
    (fun y hy => AdalyFormal.M1Patch.qc_flat hell0 Lu hRg ha hCi y (hI j Lu Rg hRg y hy))
    (fun y hy => hI j Lu Rg hRg y hy) y
  have hPc : Pc ell (j + 1) a 0 ^ 2 = ((ell : ℝ) ^ (j + 1)) ^ 2 * max 6 (16 / (3 * a)) := by
    unfold Pc
    rw [Real.sq_sqrt (by positivity)]; ring
  have hK : Kq ((min a 1 / 1000) / (((ell : ℝ) ^ (j + 1)) ^ 2 * (1 + Ci))) Ci (Pc ell (j + 1) a 0)
      = ((ell : ℝ) ^ (j + 1)) ^ 2 * Kflat a Ci := by
    unfold Kq Kflat
    rw [hPc]
    field_simp
  rw [hK] at hmain
  have hPhi : PhiP (GP ell j Lu Rg) (flatCfg : Cfg (scaleUp ell (j + 1) Lu)) a y
      = PhiG (GP ell j Lu Rg) a (trivialU _) y := by
    unfold PhiP PhiG
    rw [← AdalyFormal.M1Patch.delta_flat_eq_dpi (GP ell j Lu Rg) (GP ell j Lu Rg) hOm hOm a y]
    rfl
  rw [hPhi] at hmain
  have hKf : 0 < Kflat a Ci := by
    unfold Kflat
    positivity
  set Z := PhiG (GP ell j Lu Rg) a (trivialU _) y
    + ‖Rproj (GP ell j Lu Rg) (trivialU _) (gradAdj (trivialU _) y)‖ ^ 2 with hZ
  have hmain' : ‖y‖ ^ 2 ≤ ((ell : ℝ) ^ (j + 1)) ^ 2 * Kflat a Ci * Z := hmain
  rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ hKf]
  nlinarith [hmain']

/-! ### the plaquette (`Δ'`) term on the patch -/

theorem theta_patch (ell j : ℕ) (Lu : PeriodicLatticeExtent) (Rg : Set (PeriodicLatticeSite (scaleUp ell (j + 1) Lu)))
    (U : Cfg (scaleUp ell (j + 1) Lu)) {α : ℝ} (hα : 0 ≤ α) (hpl : AdalyFormal.NonflatHunit.PlaqDef α U)
    (x : BondFnL2 (scaleUp ell (j + 1) Lu)) :
    |AdalyFormal.StatementLaneR6.deltaPrimeBilL2NormLoc U (plaqIn (GP ell j Lu Rg).Om0) x x| ≤ (272 * α) * ‖x‖ ^ 2 := by
  have h := AdalyFormal.PortSlice.theta_ported ell (j + 1) Lu U hα hpl x
  have hF : (AdalyFormal.SliceCoerc.GF ell (j + 1) Lu).Om0 = Set.univ :=
    AdalyFormal.SliceCoerc.fullTower_Om0 ell (j + 1) Lu
  rw [hF] at h
  rw [om0_univ]
  exact h

#print axioms dsum_nonneg'
#print axioms dsum_le_class
#print axioms le_mul_of_sq_le
#print axioms patch_rows_ge
#print axioms Qrow_patch_norm
#print axioms Qrow_patch_drift
#print axioms hext_row
#print axioms hQN1_row
#print axioms towerClass_patch
#print axioms kap_nonneg'
#print axioms kap_le_class
#print axioms hU_patch
#print axioms hT_patch
#print axioms hflat_patch
#print axioms theta_patch

end AdalyFormal.W3NF
