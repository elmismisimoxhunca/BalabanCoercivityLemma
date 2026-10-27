import PW6
import PW2b
import PB1

/-!
# PW7 -- W3 at FLAT `U` on the two-stratum patch, modulo ONE named analytic input (`LemIFlat`)

* `LemIFlat ell a Ci` (the named input; Prop, not assumed anywhere else): on every two-stratum patch, for every bond field `y`
  orthogonal to the gauge directions `D N(Q')` (i.e. `D* y ⟂ N(Q')`), `‖D* y‖² ≤ Ci · Φ(y)`, `Φ = ⟨y,Δ_π y⟩ + ⟨y,Q*aQ y⟩`.
* `qc_flat` : quotient coercivity `c1/(n²(1+Ci)) ‖y‖² ≤ Φ(y)` for every `y` satisfying the `LemIFlat` bound
  `‖D* y‖² ≤ Ci Φ(y)` (taken as the hypothesis `hI`; no orthogonality hypothesis is needed), from the M0 FULL-TOWER flat floor
  (`hflat_ported`, PB1, Fourier; `c1 = min(a,1)/1000`) at height `j+1` on the same torus, the flat mass comparison
  `massF_univ_le` (PW6) and `LemIFlat`.
* **`w3_flat_plain`** : `‖x‖² ≤ n_{j+1}² · Kflat · ⟨x, G⁻¹ x⟩` for every `x`, the r8 `IngrBParams.data.Ginv` at `U = 1` on
  `patchTower j Rg` (any `Rg` union of `ell^{j+1}`-blocks, any unit torus `Lu`, any `Λ`),
  `Kflat = (1+Ci)/c1 + 2·max(6, 16/(3a))·(1+Ci)` (independent of `j`, `Lu`, `Rg`, `Λ`).
* the weighted form is `w3flat_of_LemI` (PW8).
No sorry / axiom.
-/
set_option autoImplicit false
set_option maxHeartbeats 16000000

namespace AdalyFormal.M1Patch

open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.StatementLane (Tower BlockClosed scaleUp)
open AdalyFormal.StatementLaneG (gparams)
open AdalyFormal.Balaban.SuTwoLogExp (SU2)
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.CovariantHjMinimizer (trivialU)
open AdalyFormal.Balaban.RMapLipschitz (frobNorm)

/-- the patch geometry on the fine torus of `Lu` unit blocks. -/
abbrev GP (ell j : ℕ) (Lu : PeriodicLatticeExtent) (Rg : Set (PeriodicLatticeSite (scaleUp ell (j + 1) Lu))) :
    TowerGeom (scaleUp ell (j + 1) Lu) := geomOf ell (j + 1) (patchTower j Rg)

/-- **the named analytic input** (divergence control on the orthogonal complement of the gauge directions, flat `U`). -/
def LemIFlat (ell : ℕ) (a Ci : ℝ) : Prop :=
  ∀ (j : ℕ) (Lu : PeriodicLatticeExtent) (Rg : Set (PeriodicLatticeSite (scaleUp ell (j + 1) Lu))),
    BlockClosed (ell ^ (j + 1)) Rg →
    ∀ y : BondFnL2 (scaleUp ell (j + 1) Lu),
      (∀ ν ∈ NQp (GP ell j Lu Rg) (flatCfg : Cfg _), ⟪gradAdj (flatCfg : Cfg _) y, ν⟫ = 0) →
      ‖gradAdj (flatCfg : Cfg _) y‖ ^ 2 ≤ Ci * PhiP (GP ell j Lu Rg) (flatCfg : Cfg _) a y

/-- the flat constant. -/
noncomputable def Kflat (a Ci : ℝ) : ℝ := (1 + Ci) / (min a 1 / 1000) + 2 * max 6 (16 / (3 * a)) * (1 + Ci)

theorem dvd_scaleUp (ell j : ℕ) (Lu : PeriodicLatticeExtent) (hell : 0 < ell) :
    ∀ μ : Fin 3, ell ^ (j + 1) ∣ scaleUp ell (j + 1) Lu μ + 1 := fun μ => by
  rw [scaleUp_succ ell (j + 1) Lu hell μ]; exact dvd_mul_left _ _

theorem delta_flat_eq_dpi {L : PeriodicLatticeExtent} (G G' : TowerGeom L) (hG : G.Om0 = Set.univ)
    (hG' : G'.Om0 = Set.univ) (a : ℝ) (y : BondFnL2 L) :
    ⟪y, Delta G (flatCfg : Cfg L) y⟫ = ⟪y, DpiFull G' (flatCfg : Cfg L) a y⟫ := by
  rw [AdalyFormal.StatementLane3.Delta_flat_form, AdalyFormal.StatementLaneG.inner_DpiFull_flat, hG, hG']
  rfl

/-- quotient coercivity on the patch at flat `U`, from the full-tower flat floor + mass comparison + `LemIFlat`. -/
theorem qc_flat {ell j : ℕ} (hell : 0 < ell) (Lu : PeriodicLatticeExtent) {Rg : Set (PeriodicLatticeSite (scaleUp ell (j + 1) Lu))}
    (hRg : BlockClosed (ell ^ (j + 1)) Rg) {a Ci : ℝ} (ha : 0 < a) (hCi : 0 ≤ Ci)
    (y : BondFnL2 (scaleUp ell (j + 1) Lu))
    (hI : ‖gradAdj (flatCfg : Cfg _) y‖ ^ 2 ≤ Ci * PhiP (GP ell j Lu Rg) (flatCfg : Cfg _) a y) :
    (min a 1 / 1000) / (((ell : ℝ) ^ (j + 1)) ^ 2 * (1 + Ci)) * ‖y‖ ^ 2
      ≤ PhiP (GP ell j Lu Rg) (flatCfg : Cfg _) a y := by
  have hfl := AdalyFormal.PortSlice.hflat_ported ell (j + 1) Lu hell a ha y
  have hdvd := dvd_scaleUp ell j Lu hell
  -- identify the full-tower objects with the patch objects at Rg = univ
  have hGF : AdalyFormal.SliceCoerc.GF ell (j + 1) Lu = GP ell j Lu Set.univ := by
    show geomOf ell (j + 1) (fullTower ell (j + 1) Lu) = geomOf ell (j + 1) (patchTower j Set.univ)
    rw [patchTower_univ]
  have hPhi : AdalyFormal.SliceCoerc.PhiF ell (j + 1) Lu a (trivialU (scaleUp ell (j + 1) Lu)) y
      ≤ PhiP (GP ell j Lu Rg) (flatCfg : Cfg _) a y := by
    unfold AdalyFormal.SliceCoerc.PhiF PhiP
    rw [hGF]
    have h1 : ⟪y, Delta (GP ell j Lu Set.univ) (trivialU (scaleUp ell (j + 1) Lu)) y⟫
        = ⟪y, DpiFull (GP ell j Lu Rg) (flatCfg : Cfg _) a y⟫ :=
      delta_flat_eq_dpi _ _ (om0_univ j _ ell) (om0_univ j _ ell) a y
    have h2 : ⟪y, MassFull (GP ell j Lu Set.univ) a (bondSectorOf (GP ell j Lu Set.univ)
        (trivialU (scaleUp ell (j + 1) Lu))) y⟫ ≤ ⟪y, MassFull (GP ell j Lu Rg) a (bondSectorOf (GP ell j Lu Rg)
        (flatCfg : Cfg _)) y⟫ :=
      massF_univ_le hell hRg hdvd y a ha.le
    linarith
  have hR := Rproj_le (AdalyFormal.SliceCoerc.GF ell (j + 1) Lu) (trivialU (scaleUp ell (j + 1) Lu))
    (gradAdj (trivialU (scaleUp ell (j + 1) Lu)) y)
  have hR2 : ‖Rproj (AdalyFormal.SliceCoerc.GF ell (j + 1) Lu) (trivialU (scaleUp ell (j + 1) Lu))
      (gradAdj (trivialU (scaleUp ell (j + 1) Lu)) y)‖ ^ 2 ≤ ‖gradAdj (flatCfg : Cfg _) y‖ ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) hR 2
  have hn : (0 : ℝ) < ((ell : ℝ) ^ (j + 1)) ^ 2 := by
    have : (0 : ℝ) < ell := by exact_mod_cast hell
    positivity
  have hpow : ((ell : ℝ) ^ (2 * (j + 1))) = ((ell : ℝ) ^ (j + 1)) ^ 2 := by rw [← pow_mul, mul_comm]
  rw [hpow] at hfl
  have key : min a 1 / 1000 * ‖y‖ ^ 2 ≤ ((ell : ℝ) ^ (j + 1)) ^ 2 * ((1 + Ci) * PhiP (GP ell j Lu Rg) (flatCfg : Cfg _) a y) := by
    calc min a 1 / 1000 * ‖y‖ ^ 2 ≤ ((ell : ℝ) ^ (j + 1)) ^ 2 * (AdalyFormal.SliceCoerc.PhiF ell (j + 1) Lu a
          (trivialU (scaleUp ell (j + 1) Lu)) y + ‖Rproj (AdalyFormal.SliceCoerc.GF ell (j + 1) Lu)
          (trivialU (scaleUp ell (j + 1) Lu)) (gradAdj (trivialU (scaleUp ell (j + 1) Lu)) y)‖ ^ 2) := hfl
      _ ≤ ((ell : ℝ) ^ (j + 1)) ^ 2 * (PhiP (GP ell j Lu Rg) (flatCfg : Cfg _) a y + Ci * PhiP (GP ell j Lu Rg) (flatCfg : Cfg _) a y) := by
          apply mul_le_mul_of_nonneg_left _ hn.le
          have := hR2.trans hI
          linarith
      _ = _ := by ring
  rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
  linarith

theorem flat_hU (ell k : ℕ) {L : PeriodicLatticeExtent} (G : TowerGeom L) :
    ∀ j, j ≤ k → ∀ y ∈ G.Lam j, ∀ b ∈ AdalyFormal.SiteCoercivity.inBlockBonds y (ell ^ j),
      frobNorm (((flatCfg : Cfg L) b : Matrix (Fin 2) (Fin 2) ℂ) - 1) ≤ (0 : ℝ) / (ell : ℝ) ^ j := by
  intro j _ y _ b _
  simp [flatCfg]

theorem flat_hT (ell k : ℕ) {L : PeriodicLatticeExtent} (G : TowerGeom L) :
    ∀ j, j ≤ k → ∀ y ∈ G.Lam j, ∀ i, i < j → ∀ z ∈ AdalyFormal.Balaban.AdmissibleSubspace.blockOf y (ell ^ j),
      z ∈ AdalyFormal.Balaban.AdmissibleSubspace.CoarseLattice L (ell ^ i) → ∀ μ : Fin 3,
      AdalyFormal.Balaban.CoarseCurl.coarseShift z (ell ^ i) μ ∈ AdalyFormal.Balaban.AdmissibleSubspace.blockOf y (ell ^ j) →
      frobNorm ((bgTower G (flatCfg : Cfg L) i (z, μ) : Matrix (Fin 2) (Fin 2) ℂ) - 1) ≤ (0 : ℝ) * (ell : ℝ) ^ i / (ell : ℝ) ^ j := by
  intro j _ y _ i _ z _ _ μ _
  rw [bg_flat]
  simp [flatCfg]

/-- **W3, flat `U`, plain norm** (modulo `LemIFlat`). -/
theorem w3_flat_plain {ell : ℕ} (hell : 2 ≤ ell) {a Ci : ℝ} (ha : 0 < a) (hCi : 0 ≤ Ci) (hI : LemIFlat ell a Ci)
    (j : ℕ) (Lu : PeriodicLatticeExtent) (Rg : Set (PeriodicLatticeSite (scaleUp ell (j + 1) Lu)))
    (hRg : BlockClosed (ell ^ (j + 1)) Rg) (Lam : Set (PeriodicLatticeSite Lu))
    (x : ↥(bondSupp (GP ell j Lu Rg))) :
    ‖x‖ ^ 2 ≤ ((ell : ℝ) ^ (j + 1)) ^ 2 * Kflat a Ci *
      ⟪x, (gparams ell (j + 1) Lu (by omega) (patchTower j Rg) (flatCfg : Cfg _) a Lam).data.Ginv x⟫ := by
  have hell0 : 0 < ell := by omega
  have hdvd := dvd_scaleUp ell j Lu hell0
  have hP : AdalyFormal.SiteCoercivity.ProperTower (GP ell j Lu Rg) ell (j + 1) := patch_proper hell0 hRg
  have hOm : (GP ell j Lu Rg).Om0 = Set.univ := om0_univ j Rg ell
  have hu : IsUnit (DelpA (GP ell j Lu Rg) (flatCfg : Cfg (scaleUp ell (j + 1) Lu)) a + (1 - siteMask (GP ell j Lu Rg).Om0)) :=
    AdalyFormal.M1Site.isUnit_LP_strat ell (j + 1) hell hdvd hP (flatCfg : Cfg (scaleUp ell (j + 1) Lu)) a ha 0 le_rfl (by norm_num)
      (flat_hU ell (j + 1) (GP ell j Lu Rg)) (flat_hT ell (j + 1) (GP ell j Lu Rg))
  have hreg : RegTower ell (bgTower (GP ell j Lu Rg) (flatCfg : Cfg (scaleUp ell (j + 1) Lu))) (j + 1) := fun i _ => by rw [bg_flat]; exact RegBg_flat _ _
  have hB0 := patch_B0 hell0 hRg hdvd (flatCfg : Cfg (scaleUp ell (j + 1) Lu)) hreg
  have hM : (0 : ℝ) < max 6 (16 / (3 * a)) := lt_of_lt_of_le (by norm_num) (le_max_left _ _)
  have hn : (0 : ℝ) < ((ell : ℝ) ^ (j + 1)) ^ 2 := by
    have : (0 : ℝ) < ell := by exact_mod_cast hell0
    positivity
  have hc1 : (0 : ℝ) < min a 1 / 1000 := by positivity
  have hmain := r1q_coercive (gradL2 (flatCfg : Cfg (scaleUp ell (j + 1) Lu))) (NQp (GP ell j Lu Rg) (flatCfg : Cfg (scaleUp ell (j + 1) Lu))) (Rproj (GP ell j Lu Rg) (flatCfg : Cfg (scaleUp ell (j + 1) Lu))) (PhiP (GP ell j Lu Rg) (flatCfg : Cfg (scaleUp ell (j + 1) Lu)) a)
    (fun A ν hν => PhiP_inv (GP ell j Lu Rg) (flatCfg : Cfg (scaleUp ell (j + 1) Lu)) a hOm hu hB0 A ν hν)
    (fun ν hν => Rproj_fix (GP ell j Lu Rg) (flatCfg : Cfg (scaleUp ell (j + 1) Lu)) hOm ν hν) (fun s => Rproj_le (GP ell j Lu Rg) (flatCfg : Cfg (scaleUp ell (j + 1) Lu)) s)
    (Pc ell (j + 1) a 0) ((min a 1 / 1000) / (((ell : ℝ) ^ (j + 1)) ^ 2 * (1 + Ci))) Ci
    (Real.sqrt_nonneg _) (by positivity) hCi
    (fun ν hν => poincare_patch hell hdvd hP hOm (flatCfg : Cfg (scaleUp ell (j + 1) Lu)) a ha 0 le_rfl (by norm_num)
      (flat_hU ell (j + 1) (GP ell j Lu Rg)) (flat_hT ell (j + 1) (GP ell j Lu Rg)) ν hν)
    (fun y hy => qc_flat hell0 Lu hRg ha hCi y (hI j Lu Rg hRg y hy))
    (fun y hy => hI j Lu Rg hRg y hy) (iE (GP ell j Lu Rg) x)
  have hform := ginv_form (gparams ell (j + 1) Lu (by omega) (patchTower j Rg) (flatCfg : Cfg (scaleUp ell (j + 1) Lu)) a Lam) x
  have hx : ‖x‖ = ‖iE (GP ell j Lu Rg) x‖ := rfl
  have hPc : Pc ell (j + 1) a 0 ^ 2 = ((ell : ℝ) ^ (j + 1)) ^ 2 * max 6 (16 / (3 * a)) := by
    unfold Pc
    rw [Real.sq_sqrt (by positivity)]; ring
  have hK : Kq ((min a 1 / 1000) / (((ell : ℝ) ^ (j + 1)) ^ 2 * (1 + Ci))) Ci (Pc ell (j + 1) a 0)
      = ((ell : ℝ) ^ (j + 1)) ^ 2 * Kflat a Ci := by
    unfold Kq Kflat
    rw [hPc]
    field_simp
  rw [hx]
  rw [hK] at hmain
  rw [hform]
  exact hmain

#print axioms qc_flat
#print axioms w3_flat_plain

end AdalyFormal.M1Patch
