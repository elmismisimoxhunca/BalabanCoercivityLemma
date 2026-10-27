import MF6f
import BC2
import NJ15Cov

/-!
# MF6g -- the two `C`-bounds consumed by MF4 (`hC`), from the unit background smallness.

* `q1_flat_l2`  : `Σ_c ‖Q₁(1) B c‖² ≤ ℓ⁻³ ‖B‖²` (sharp flat bound, from BC2 `T1_flat_l2`);
* `cop_bounds`  : with `dC = ℓ³ ω < 1`:
    `Σ‖C_V B̃ − C₁ B̃‖² ≤ dC² Σ‖C_V B̃‖²`   and   `Σ‖C_V B̃‖² ≤ ((1 + ℓ³·ℓ^{-3/2})/(1 − dC))² ‖B̃‖²`.
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section

namespace AdalyFormal.M0Finish.R7

open AdalyFormal.Target.ClayStatement
  (PeriodicLatticeExtent PeriodicLatticeSite PeriodicLinkConfiguration)
open AdalyFormal.Balaban.CovariantOperators (SuTwo)
open AdalyFormal.Balaban.SuTwoLogExp (SU2 M2)
open AdalyFormal.Balaban.LatticeOperators (CoarseBond)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.RMapLipschitz (frobNorm)
open AdalyFormal.Balaban.RegularUPerturbation (bondEnergy bondEnergy_nonneg)
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.IngredientFamily (q1SU2)
open AdalyFormal.NonflatJet (rhoOf)
open AdalyFormal.Balaban.CovariantHjMinimizer (trivialU)
open EstimatesLayer.E1E3

variable {L : PeriodicLatticeExtent}

theorem q1_flat_l2 {ell : ℕ} (hell : 0 < ell) (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1)) (B : Bond L → SuTwo) :
    ∑ c : CoarseBond L ell, ‖q1SU2 ell B c‖ ^ 2 ≤ (1 / (ell : ℝ) ^ 3) * bondEnergy B := by
  have h := AdalyFormal.BondComposite.T1_flat_l2 (L := L) hell (AdalyFormal.NonflatJet.bondToUnit B)
  rw [l1_gA_bondToUnit] at h
  have hpt : ∀ c : CoarseBond L ell, q1SU2 ell B c
      = AdalyFormal.Balaban.TowerLawCov.unitToCoarseCov 1 ell (trivialU L) (AdalyFormal.NonflatJet.bondToUnit B)
          (AdalyFormal.NonflatJet.cbEquiv ell c) := by
    intro c
    rw [show AdalyFormal.NonflatJet.cbEquiv ell c
        = (⟨⟨c.1.1, by rw [one_mul]; exact c.1.2⟩, c.2⟩ : CoarseBond L (1 * ell)) from rfl,
      AdalyFormal.NonflatJet.T1_eq_lineCoarseRestrictCov hdvd hell (trivialU L) B c,
      AdalyFormal.Balaban.LineIntegralCovariant.lineCoarseRestrictCov_trivialU]
    rfl
  have e := Equiv.sum_comp (AdalyFormal.NonflatJet.cbEquiv ell) (fun c' : CoarseBond L (1 * ell) =>
    ‖AdalyFormal.Balaban.TowerLawCov.unitToCoarseCov 1 ell (trivialU L) (AdalyFormal.NonflatJet.bondToUnit B) c'‖ ^ 2)
  calc ∑ c : CoarseBond L ell, ‖q1SU2 ell B c‖ ^ 2
      = ∑ c : CoarseBond L ell, ‖AdalyFormal.Balaban.TowerLawCov.unitToCoarseCov 1 ell (trivialU L)
          (AdalyFormal.NonflatJet.bondToUnit B) (AdalyFormal.NonflatJet.cbEquiv ell c)‖ ^ 2 :=
        Finset.sum_congr rfl (fun c _ => by rw [hpt c])
    _ = _ := e
    _ ≤ _ := h

/-- the two `C` bounds of MF4's `hC`. -/
theorem cop_bounds {ell : ℕ} (hell : 0 < ell) (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1))
    (Lam : Set (PeriodicLatticeSite L)) (V : PeriodicLinkConfiguration SU2 L) (ε0 : ℝ) (hε0 : 0 ≤ ε0)
    (hV : ∀ e, frobNorm ((V e : M2) - 1) ≤ ε0) (hsmall : rhoOf ell ε0 < Real.pi / 2)
    (hreg : RegBg 1 ell V) (hbV : Function.Bijective (H0 Lam (Q1jet ell V)))
    (dC : ℝ) (hdC : dC = (ell : ℝ) ^ 3 * Real.sqrt (384 * (ell * ε0) ^ 2 + 480 * (e2Majorant (rhoOf ell ε0)) ^ 2))
    (hdC1 : dC < 1) (Bt : Bond L → SuTwo) :
    ∑ b : Bond L, ‖Cop Lam (Q1jet ell V) Bt b - Cop Lam (q1SU2 ell) Bt b‖ ^ 2
        ≤ dC ^ 2 * ∑ b : Bond L, ‖Cop Lam (Q1jet ell V) Bt b‖ ^ 2 ∧
      ∑ b : Bond L, ‖Cop Lam (Q1jet ell V) Bt b‖ ^ 2
        ≤ ((1 + (ell : ℝ) ^ 3 * Real.sqrt (1 / (ell : ℝ) ^ 3)) / (1 - dC)) ^ 2 * bondEnergy Bt := by
  have hellR : (0 : ℝ) < ell := by exact_mod_cast hell
  have hω0 : 0 ≤ 384 * ((ell : ℝ) * ε0) ^ 2 + 480 * (e2Majorant (rhoOf ell ε0)) ^ 2 := by positivity
  have hdC0 : 0 ≤ dC := by rw [hdC]; positivity
  have hdC2 : dC ^ 2 = ((ell : ℝ) ^ 3) ^ 2 * (384 * ((ell : ℝ) * ε0) ^ 2 + 480 * (e2Majorant (rhoOf ell ε0)) ^ 2) := by
    rw [hdC, mul_pow, Real.sq_sqrt hω0]
  have hp := cop_pert hell hdvd Lam V ε0 hε0 hV hsmall hreg hbV Bt
  have h1 : ∑ b : Bond L, ‖Cop Lam (Q1jet ell V) Bt b - Cop Lam (q1SU2 ell) Bt b‖ ^ 2
      ≤ dC ^ 2 * ∑ b : Bond L, ‖Cop Lam (Q1jet ell V) Bt b‖ ^ 2 := by
    rw [hdC2]; exact hp
  refine ⟨h1, ?_⟩
  -- sqrt-norms
  set NU := Real.sqrt (∑ b : Bond L, ‖Cop Lam (Q1jet ell V) Bt b‖ ^ 2) with hNU
  set N1 := Real.sqrt (∑ b : Bond L, ‖Cop Lam (q1SU2 ell) Bt b‖ ^ 2) with hN1
  set ND := Real.sqrt (∑ b : Bond L, ‖Cop Lam (Q1jet ell V) Bt b - Cop Lam (q1SU2 ell) Bt b‖ ^ 2) with hND
  have hsU : 0 ≤ ∑ b : Bond L, ‖Cop Lam (Q1jet ell V) Bt b‖ ^ 2 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hND' : ND ≤ dC * NU := by
    rw [hND, hNU, ← Real.sqrt_sq hdC0, ← Real.sqrt_mul (sq_nonneg _)]
    exact Real.sqrt_le_sqrt h1
  have htri : NU ≤ N1 + ND := by
    have hn : ∀ f : Bond L → SuTwo, Real.sqrt (∑ b : Bond L, ‖f b‖ ^ 2)
        = ‖(WithLp.toLp 2 f : PiLp 2 (fun _ : Bond L => SuTwo))‖ := by
      intro f; rw [PiLp.norm_eq_of_L2]
    rw [hNU, hN1, hND, hn, hn, hn]
    have e : (WithLp.toLp 2 (Cop Lam (Q1jet ell V) Bt) : PiLp 2 (fun _ : Bond L => SuTwo))
        = WithLp.toLp 2 (Cop Lam (q1SU2 ell) Bt)
          + WithLp.toLp 2 (fun b => Cop Lam (Q1jet ell V) Bt b - Cop Lam (q1SU2 ell) Bt b) := by
      refine PiLp.ext (fun b => ?_)
      simp
    rw [e]; exact norm_add_le _ _
  have hfl := cop_flat_le hell hdvd Lam Bt
  have hq := q1_flat_l2 hell hdvd Bt
  have hq' : Real.sqrt (∑ c : CoarseBond L ell, ‖q1SU2 ell Bt c‖ ^ 2)
      ≤ Real.sqrt (1 / (ell : ℝ) ^ 3) * Real.sqrt (bondEnergy Bt) := by
    rw [← Real.sqrt_mul (by positivity)]; exact Real.sqrt_le_sqrt hq
  have hN1' : N1 ≤ (1 + (ell : ℝ) ^ 3 * Real.sqrt (1 / (ell : ℝ) ^ 3)) * Real.sqrt (bondEnergy Bt) := by
    have h3 : (0:ℝ) ≤ (ell : ℝ) ^ 3 := by positivity
    nlinarith [mul_le_mul_of_nonneg_left hq' h3]
  have hNU' : NU * (1 - dC) ≤ (1 + (ell : ℝ) ^ 3 * Real.sqrt (1 / (ell : ℝ) ^ 3)) * Real.sqrt (bondEnergy Bt) := by
    nlinarith
  have h1d : 0 < 1 - dC := by linarith
  have hNU0 : 0 ≤ NU := Real.sqrt_nonneg _
  have hfin : NU ≤ (1 + (ell : ℝ) ^ 3 * Real.sqrt (1 / (ell : ℝ) ^ 3)) / (1 - dC) * Real.sqrt (bondEnergy Bt) := by
    rw [div_mul_eq_mul_div, le_div_iff₀ h1d]; linarith
  have hbe := bondEnergy_nonneg Bt
  have hsq := pow_le_pow_left₀ hNU0 hfin 2
  rw [hNU, Real.sq_sqrt hsU, mul_pow, Real.sq_sqrt hbe] at hsq
  exact hsq

#print axioms q1_flat_l2
#print axioms cop_bounds

end AdalyFormal.M0Finish.R7
