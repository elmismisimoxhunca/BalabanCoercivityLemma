import TL6b
import W6H

/-!
# DR1 -- the bond right inverse with weighted energy (W6 node for D2) under the REGIONAL tower class, and in the M1
regime (M1 D-layer lane, 2026-10-14)

W6's `bond_rightinv_strat` uses the GLOBAL `TowerClass` through `drift_D`; the M1 regime only gives regional classes
(towerloc TL3/TL6b).  Here:
* `drift_D_loc` : `Σ_p ℓ^{lev p} ‖(Q_V − Q₁) x‖² ≤ 3ℓ² δ*² wnormSq x` (TL3 `level_drift_loc` per level + W6 `foot_levels_w`);
* `bond_rightinv_of_drift` : W6's right-inverse construction from ANY drift bound `nD((Q₁ − Q_V)x) ≤ D wnormSq x` with
  `D·CwE ≤ 1/4` (the proof of W6H `bond_rightinv_strat`, the drift as a hypothesis);
* **`drift_D_M1`**, **`bond_rightinv_M1`** : in the M1 gauge `U^g` (TL6b's data `epsM`, `WM`, `hcl_M1`, `SstarM`), the
  right inverse `Q x = u`, `wnormSq x ≤ 4 CwE nD u`, `gradW x ≤ 4 CgE nD u`, under `3ℓ² δ*(SstarM)² CwE ≤ 1/4` (`k`-free).
No sorry / native_decide / axiom.
-/
set_option autoImplicit false
set_option maxHeartbeats 16000000
set_option maxRecDepth 8000

namespace AdalyFormal.M1DStrat

open Finset
open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.Balaban.SuTwoLogExp (SU2 M2)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond CoarseLattice mem_CoarseLattice)
open AdalyFormal.Balaban.RMapLipschitz (frobNorm)
open AdalyFormal.Balaban.CovariantHjMinimizer (trivialU)
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
open AdalyFormal.NonflatJet
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.StatementLane (Tower Admissible scaleUp)
open AdalyFormal.StatementLaneR8
open AdalyFormal.StatementLaneG (gparams)
open AdalyFormal.SliceCoerc (GF)
open AdalyFormal.DLayer (Foot bondRestr)
open AdalyFormal.BondComposite
open SmallnessBridge.Assemble (loopFactorBound)
open AdalyFormal.W6
open AdalyFormal.TowerLoc

section drift
variable {ell M R k : ℕ} {Lu : PeriodicLatticeExtent} {S : Tower (scaleUp ell k Lu)}

/-- **regional drift in the `D` norm** -/
theorem drift_D_loc (hell2 : 2 ≤ ell) (hS : Admissible ell M R k S) (hM : 0 < M) (hR : 8 * ell ≤ R)
    (V : Cfg (scaleUp ell k Lu)) (ε : ℕ → ℕ → ℝ) (W : ℕ → ℕ → Set (PeriodicLatticeSite (scaleUp ell k Lu)))
    (hcl : ∀ j : Fin (k + 1), ∀ l, l < k → ∀ z ∈ W j l, z ∈ CoarseLattice (scaleUp ell k Lu) (ell ^ l) → ∀ μ : Fin 3,
      frobNorm (((bgTower (GF ell k Lu) V l (z, μ) : SU2) : M2) - 1) ≤ ε j l)
    (hε0 : ∀ j : Fin (k + 1), ∀ l, l < k → 0 ≤ ε j l)
    (hsm : ∀ j : Fin (k + 1), ∀ l, l < k → rhoOf ell (ε j l) < Real.pi / 2)
    (hr : ∀ j : Fin (k + 1), ∀ l, l < k → Real.pi / 2 * ((loopFactorBound ell : ℝ) * ε j l) < r0)
    (hW : ∀ j : Fin (k + 1),
      ∀ r : {b : Bond (scaleUp ell k Lu) // b ∈ bondsLam (geomOf ell k S) j}, ∀ l, l < (j : ℕ) →
        Ball r.1.1 (rhoT ell j - rhoT ell l) ⊆ W j l)
    (Sstar : ℝ) (hSstar : ∀ j : Fin (k + 1), ∑ l ∈ range (j : ℕ), thetaOf ell (ε j l) ≤ Sstar)
    (x : BondFnL2 (scaleUp ell k Lu)) :
    ∑ p, wD p * ‖(bondSectorOf (geomOf ell k S) V).Qfull x p
        - (bondSectorOf (geomOf ell k S) (trivialU _)).Qfull x p‖ ^ 2
      ≤ 3 * (ell : ℝ) ^ 2 * delStar ell Sstar ^ 2 * AdalyFormal.M1.wnormSq S ell k x := by
  have hell : 0 < ell := by omega
  have hr0 := rr_pos hell
  rw [Fintype.sum_sigma (fun p : BIdx (geomOf ell k S) => wD p * ‖(bondSectorOf (geomOf ell k S) V).Qfull x p
      - (bondSectorOf (geomOf ell k S) (trivialU _)).Qfull x p‖ ^ 2)]
  have hdel : ∀ j : Fin (k + 1), delLoc ell (ε j) j ≤ delStar ell Sstar := by
    intro j
    have hjk : (j : ℕ) ≤ k := Nat.lt_succ_iff.mp j.isLt
    have h0 : 0 ≤ ∑ l ∈ range (j : ℕ), thetaOf ell (ε j l) :=
      Finset.sum_nonneg (fun l hl => thetaOf_nonneg ell _ (hε0 j l (lt_of_lt_of_le (Finset.mem_range.mp hl) hjk)))
    have h1 : (∑ l ∈ range (j : ℕ), thetaOf ell (ε j l)) / rr ell ≤ Sstar / rr ell :=
      div_le_div_of_nonneg_right (hSstar j) hr0.le
    have h2 : 0 ≤ (∑ l ∈ range (j : ℕ), thetaOf ell (ε j l)) / rr ell := div_nonneg h0 hr0.le
    unfold delLoc delStar
    exact mul_le_mul h1 (Real.exp_le_exp.mpr h1) (Real.exp_pos _).le (le_trans h2 h1)
  have hlev : ∀ j : Fin (k + 1), ∑ r : {b : Bond (scaleUp ell k Lu) // b ∈ bondsLam (geomOf ell k S) j},
      wD (⟨j, r⟩ : BIdx (geomOf ell k S)) * ‖(bondSectorOf (geomOf ell k S) V).Qfull x ⟨j, r⟩
        - (bondSectorOf (geomOf ell k S) (trivialU _)).Qfull x ⟨j, r⟩‖ ^ 2
      ≤ delStar ell Sstar ^ 2 * ((((ell : ℝ) ^ (j : ℕ))⁻¹) ^ 2 * ‖bondRestr (FootL (S := S) j) x‖ ^ 2) := by
    intro j
    have h := level_drift_loc (S := S) hell V (ε j) (W j) (hcl j) (hε0 j) (hsm j) (hr j) j (hW j) x
    simp only [wD_eq hell]
    have e : ∑ r : {b : Bond (scaleUp ell k Lu) // b ∈ bondsLam (geomOf ell k S) j},
        (((ell : ℝ) ^ ((⟨j, r⟩ : BIdx (geomOf ell k S)).1 : ℕ))⁻¹) ^ 2 * wF (⟨j, r⟩ : BIdx (geomOf ell k S))
          * ‖(bondSectorOf (geomOf ell k S) V).Qfull x ⟨j, r⟩ - (bondSectorOf (geomOf ell k S) (trivialU _)).Qfull x ⟨j, r⟩‖ ^ 2
        = (((ell : ℝ) ^ (j : ℕ))⁻¹) ^ 2 * ∑ r : {b : Bond (scaleUp ell k Lu) // b ∈ bondsLam (geomOf ell k S) j},
          ((ell : ℝ) ^ (j : ℕ)) ^ 3 * ‖(bondSectorOf (geomOf ell k S) V).Qfull x ⟨j, r⟩
            - (bondSectorOf (geomOf ell k S) (trivialU _)).Qfull x ⟨j, r⟩‖ ^ 2 := by
      rw [Finset.mul_sum]; refine Finset.sum_congr rfl (fun r _ => ?_); unfold wF; ring
    rw [e]
    have hI : 0 ≤ (((ell : ℝ) ^ (j : ℕ))⁻¹) ^ 2 := sq_nonneg _
    have h0 : 0 ≤ delLoc ell (ε j) j := by
      have hjk : (j : ℕ) ≤ k := Nat.lt_succ_iff.mp j.isLt
      have : 0 ≤ ∑ l ∈ range (j : ℕ), thetaOf ell (ε j l) :=
        Finset.sum_nonneg (fun l hl => thetaOf_nonneg ell _ (hε0 j l (lt_of_lt_of_le (Finset.mem_range.mp hl) hjk)))
      unfold delLoc
      exact mul_nonneg (div_nonneg this hr0.le) (Real.exp_pos _).le
    have hd2 : delLoc ell (ε j) j ^ 2 ≤ delStar ell Sstar ^ 2 := pow_le_pow_left₀ h0 (hdel j) 2
    calc (((ell : ℝ) ^ (j : ℕ))⁻¹) ^ 2 * ∑ r : {b : Bond (scaleUp ell k Lu) // b ∈ bondsLam (geomOf ell k S) j},
          ((ell : ℝ) ^ (j : ℕ)) ^ 3 * ‖(bondSectorOf (geomOf ell k S) V).Qfull x ⟨j, r⟩
            - (bondSectorOf (geomOf ell k S) (trivialU _)).Qfull x ⟨j, r⟩‖ ^ 2
        ≤ (((ell : ℝ) ^ (j : ℕ))⁻¹) ^ 2 * (delLoc ell (ε j) j ^ 2 * ‖bondRestr (FootL (S := S) j) x‖ ^ 2) :=
          mul_le_mul_of_nonneg_left h hI
      _ ≤ (((ell : ℝ) ^ (j : ℕ))⁻¹) ^ 2 * (delStar ell Sstar ^ 2 * ‖bondRestr (FootL (S := S) j) x‖ ^ 2) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hd2 (sq_nonneg _)) hI
      _ = _ := by ring
  refine (Finset.sum_le_sum (fun j _ => hlev j)).trans ?_
  rw [← Finset.mul_sum]
  have h3 := foot_levels_w hell2 hS hM hR x
  have hd : 0 ≤ delStar ell Sstar ^ 2 := sq_nonneg _
  calc delStar ell Sstar ^ 2 * ∑ j : Fin (k + 1), (((ell : ℝ) ^ (j : ℕ))⁻¹) ^ 2 * ‖bondRestr (FootL (S := S) j) x‖ ^ 2
      ≤ delStar ell Sstar ^ 2 * (3 * (ell : ℝ) ^ 2 * AdalyFormal.M1.wnormSq S ell k x) := mul_le_mul_of_nonneg_left h3 hd
    _ = _ := by ring

/-- **W6's energy right inverse from an abstract `D`-norm drift bound** -/
theorem bond_rightinv_of_drift (hell : 0 < ell) (hell2 : 2 ≤ ell) (hS : Admissible ell M R k S) (hM : 0 < M)
    (hR : 8 * ell ≤ R) (U : LinkCfg (scaleUp ell k Lu)) (a : ℝ) (Lam : Set (PeriodicLatticeSite Lu))
    (Dd : ℝ) (hDd : 0 ≤ Dd)
    (hdr : ∀ x : BondFnL2 (scaleUp ell k Lu),
      ∑ p, wD p * ‖(bondSectorOf (geomOf ell k S) U).Qfull x p
        - (bondSectorOf (geomOf ell k S) (trivialU _)).Qfull x p‖ ^ 2 ≤ Dd * AdalyFormal.M1.wnormSq S ell k x)
    (hsmall : Dd * CwE ell ≤ 1 / 4) (u : FSp (geomOf ell k S)) :
    ∃ x : ↥(bondSupp (geomOf ell k S)), (gparams ell k Lu hell S U a Lam).data.Q x = u ∧
      AdalyFormal.M1.wnormSq S ell k (x : BondFnL2 (scaleUp ell k Lu)) ≤ 4 * CwE ell * nD u ∧
      ∀ ν0 : Fin 3, gradW (x : BondFnL2 (scaleUp ell k Lu)) ν0 ≤ 4 * CgE ell * nD u := by
  set A : ↥(bondSupp (geomOf ell k S)) →L[ℝ] FSp (geomOf ell k S) :=
    ((bondSectorOf (geomOf ell k S) U).Qfull).comp (iE (geomOf ell k S)) with hA
  set E2 : FSp (geomOf ell k S) →ₗ[ℝ] ↥(bondSupp (geomOf ell k S)) :=
    LinearMap.codRestrict (bondSupp (geomOf ell k S)) (ErightL hell) (fun y => Eright_mem hell hS y) with hE2
  set T : FSp (geomOf ell k S) →ₗ[ℝ] FSp (geomOf ell k S) :=
    (A : ↥(bondSupp (geomOf ell k S)) →ₗ[ℝ] FSp (geomOf ell k S)).comp E2 with hT
  have hTapp : ∀ y, T y = (bondSectorOf (geomOf ell k S) U).Qfull (ErightL hell y) := fun y => rfl
  set c := Dd * CwE ell with hc
  have hCwE : 0 ≤ CwE ell := by unfold CwE; have := CE_pos; positivity
  have hc0 : 0 ≤ c := mul_nonneg hDd hCwE
  have hdrift : ∀ y, nD (y - T y) ≤ c * nD y := by
    intro y
    have hd : y - T y = (bondSectorOf (geomOf ell k S) (trivialU _)).Qfull (ErightL hell y)
        - (bondSectorOf (geomOf ell k S) U).Qfull (ErightL hell y) := by
      rw [hTapp, Eright_rightInv hell hell2 hS hM hR y]
    rw [hd]
    have h1 := hdr (ErightL hell y)
    have h1' : nD ((bondSectorOf (geomOf ell k S) (trivialU _)).Qfull (ErightL hell y)
          - (bondSectorOf (geomOf ell k S) U).Qfull (ErightL hell y))
        ≤ Dd * AdalyFormal.M1.wnormSq S ell k (ErightL hell y) := by
      refine le_trans (le_of_eq ?_) h1
      unfold nD
      refine Finset.sum_congr rfl (fun p _ => ?_)
      rw [show ((bondSectorOf (geomOf ell k S) (trivialU _)).Qfull (ErightL hell y)
            - (bondSectorOf (geomOf ell k S) U).Qfull (ErightL hell y)) p
          = (bondSectorOf (geomOf ell k S) (trivialU _)).Qfull (ErightL hell y) p
            - (bondSectorOf (geomOf ell k S) U).Qfull (ErightL hell y) p from rfl, norm_sub_rev]
    have h2 := Eright_wnorm hell hell2 hS hM hR y
    calc _ ≤ Dd * AdalyFormal.M1.wnormSq S ell k (ErightL hell y) := h1'
      _ ≤ Dd * (CwE ell * nD y) := mul_le_mul_of_nonneg_left h2 hDd
      _ = c * nD y := by rw [hc]; ring
  have hapriori : ∀ y, nD y ≤ 4 * nD (T y) := by
    intro y
    have h1 := nD_add_le hell (T y) (y - T y)
    rw [add_sub_cancel] at h1
    have h2 := hdrift y
    have hy := nD_nonneg hell y
    nlinarith
  have hTinj : Function.Injective T := by
    rw [injective_iff_map_eq_zero]
    intro y hy0
    have h := hapriori y
    rw [hy0] at h
    have h0 : nD (0 : FSp (geomOf ell k S)) = 0 := by unfold nD; simp
    rw [h0, mul_zero] at h
    have hterm : ∀ p, wD p * ‖y p‖ ^ 2 = 0 := by
      intro p
      exact (Finset.sum_eq_zero_iff_of_nonneg (fun p _ => mul_nonneg (wD_pos hell p).le (sq_nonneg ‖y p‖))).mp
        (le_antisymm h (nD_nonneg hell y)) p (mem_univ p)
    refine PiLp.ext (fun p => ?_)
    have h1 := hterm p
    have hw := wD_pos hell p
    have h2 : ‖y p‖ ^ 2 = 0 := by
      rcases mul_eq_zero.mp h1 with h | h
      · exact absurd h hw.ne'
      · exact h
    have : ‖y p‖ = 0 := by simpa using h2
    simpa using this
  have hTsurj : Function.Surjective T := LinearMap.injective_iff_surjective.mp hTinj
  obtain ⟨v, hv⟩ := hTsurj u
  have hvn : nD v ≤ 4 * nD u := by have := hapriori v; rw [hv] at this; exact this
  refine ⟨E2 v, ?_, ?_, ?_⟩
  · exact hv
  · have h : AdalyFormal.M1.wnormSq S ell k ((E2 v : ↥(bondSupp (geomOf ell k S))) : BondFnL2 (scaleUp ell k Lu))
        ≤ CwE ell * nD v := Eright_wnorm hell hell2 hS hM hR v
    nlinarith
  · intro ν0
    have h : gradW ((E2 v : ↥(bondSupp (geomOf ell k S))) : BondFnL2 (scaleUp ell k Lu)) ν0 ≤ CgE ell * nD v :=
      Eright_grad hell hell2 hS hM hR v ν0
    have hC : 0 ≤ CgE ell := by unfold CgE; have := GE_pos; have := CE_pos; positivity
    nlinarith

end drift

section m1
variable {ell M R k f : ℕ} {Lu : PeriodicLatticeExtent} {S : Tower (scaleUp ell k Lu)} {α₀ η : ℝ}
  (hell2 : 2 ≤ ell) (hS : Admissible ell M R k S) (hroom : 17 * ell ≤ R * M)
  (hT3 : ∀ μ, 3 ≤ Lu μ + 1) (U : LinkCfg (scaleUp ell k Lu))
  (g : PeriodicLatticeSite (scaleUp ell k Lu) → Matrix.specialUnitaryGroup (Fin 2) ℂ)
  (A : Bond (scaleUp ell k Lu) → Matrix (Fin 2) (Fin 2) ℂ)
  (hU : ∀ e : Bond (scaleUp ell k Lu), ((periodicGaugeTransform g U e : Matrix.specialUnitaryGroup (Fin 2) ℂ) :
      Matrix (Fin 2) (Fin 2) ℂ) = NormedSpace.exp (((η : ℂ) * Complex.I) • A e))
  (hB : AdalyFormal.M1.M1Bounds S ell M f k α₀ η A) (hη : 0 < η) (hα0 : 0 ≤ α₀)
  (ha1 : (f : ℝ) * M * α₀ ≤ 1)
  (hsm4 : 4000000 * (ell : ℝ) ^ 2 * rho1 f M α₀ ≤ 1)
  (hsmA : (1 + 3 * Real.pi) * rho1 f M α₀ ≤ 1 / (1000 * (ell : ℝ) ^ 4))
  (hrr : Real.pi / 2 * ((loopFactorBound ell : ℝ) * ((1 + 3 * Real.pi) * rho1 f M α₀)) < r0)

include hell2 hS hroom hT3 hU hB hη hα0 ha1 hsm4 hsmA hrr in
/-- **the `D`-norm drift at `U^g` in the M1 regime** (`k`-free) -/
theorem drift_D_M1 (hM : 0 < M) (hR : 8 * ell ≤ R) (x : BondFnL2 (scaleUp ell k Lu)) :
    ∑ p, wD p * ‖(bondSectorOf (geomOf ell k S) (periodicGaugeTransform g U)).Qfull x p
        - (bondSectorOf (geomOf ell k S) (trivialU _)).Qfull x p‖ ^ 2
      ≤ 3 * (ell : ℝ) ^ 2 * delStar ell (SstarM ell f M α₀) ^ 2 * AdalyFormal.M1.wnormSq S ell k x := by
  have hell : 0 < ell := by omega
  have hsmall : ∀ j l : ℕ, epsM ell f M α₀ j l ≤ 1 / (1000 * (ell : ℝ) ^ 4) := fun j l =>
    (epsM_le ell f M hell α₀ hα0 j l).trans hsmA
  refine drift_D_loc hell2 hS hM hR (periodicGaugeTransform g U) (fun j l => epsM ell f M α₀ j l)
    (fun j l => WM ell k S j l)
    (fun j l hlk z hzW hzA μ => hcl_M1 hell2 hS hroom hT3 U g A hU hB hη hα0 ha1 hsm4 j l hlk z hzW hzA μ)
    (fun j l _ => epsM_nonneg ell f M α₀ hα0 j l) (fun j l _ => ?_) (fun j l _ => ?_) (fun j r l hl z hz => ?_)
    (SstarM ell f M α₀) (fun j => sum_theta_epsM ell f M hell2 α₀ hα0 hsmA j) x
  · have h0 := epsM_nonneg ell f M α₀ hα0 j l
    have h1 := rhoOf_le (ell := ell) _ h0
    have hellR : (1 : ℝ) ≤ ell := by exact_mod_cast hell
    have hk : epsM ell f M α₀ j l * (ell : ℝ) ^ 4 ≤ 1 / 1000 := by
      have hpos : (0 : ℝ) < (ell : ℝ) ^ 4 := by positivity
      have := mul_le_mul_of_nonneg_right (hsmall j l) hpos.le
      calc _ ≤ 1 / (1000 * (ell : ℝ) ^ 4) * (ell : ℝ) ^ 4 := this
        _ = 1 / 1000 := by field_simp
    have h4 : (ell : ℝ) ≤ (ell : ℝ) ^ 4 := by
      nlinarith [sq_nonneg ((ell : ℝ) - 1), sq_nonneg ((ell : ℝ) ^ 2 - 1)]
    have h5 : (ell : ℝ) * epsM ell f M α₀ j l ≤ 1 / 1000 := by
      nlinarith [mul_le_mul_of_nonneg_right h4 h0]
    have := Real.pi_gt_three
    nlinarith
  · have h0 := epsM_nonneg ell f M α₀ hα0 j l
    have hle := epsM_le ell f M hell α₀ hα0 j l
    refine lt_of_le_of_lt ?_ hrr
    have hpi := Real.pi_pos
    gcongr
  · exact ⟨hl, r, hz⟩

include hell2 hS hroom hT3 hU hB hη hα0 ha1 hsm4 hsmA hrr in
/-- **W6 for D2 in the M1 regime** -/
theorem bond_rightinv_M1 (hM : 0 < M) (hR : 8 * ell ≤ R) (a : ℝ) (Lam : Set (PeriodicLatticeSite Lu))
    (hsmall : 3 * (ell : ℝ) ^ 2 * delStar ell (SstarM ell f M α₀) ^ 2 * CwE ell ≤ 1 / 4)
    (u : FSp (geomOf ell k S)) :
    ∃ x : ↥(bondSupp (geomOf ell k S)),
      (gparams ell k Lu (by omega) S (periodicGaugeTransform g U) a Lam).data.Q x = u ∧
      AdalyFormal.M1.wnormSq S ell k (x : BondFnL2 (scaleUp ell k Lu)) ≤ 4 * CwE ell * nD u ∧
      ∀ ν0 : Fin 3, gradW (x : BondFnL2 (scaleUp ell k Lu)) ν0 ≤ 4 * CgE ell * nD u :=
  bond_rightinv_of_drift (by omega) hell2 hS hM hR (periodicGaugeTransform g U) a Lam
    (3 * (ell : ℝ) ^ 2 * delStar ell (SstarM ell f M α₀) ^ 2) (by positivity)
    (fun x => drift_D_M1 hell2 hS hroom hT3 U g A hU hB hη hα0 ha1 hsm4 hsmA hrr hM hR x) hsmall u

end m1

#print axioms drift_D_loc
#print axioms bond_rightinv_of_drift
#print axioms drift_D_M1
#print axioms bond_rightinv_M1

end AdalyFormal.M1DStrat
