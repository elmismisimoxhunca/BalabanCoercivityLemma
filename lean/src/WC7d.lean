import WC7c

/-!
# WC7d -- **`qs_injective_charts`** (M2 W6 lane)
No sorry / native_decide / axiom.
-/
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 8000
set_option synthInstance.maxHeartbeats 400000
noncomputable section
namespace AdalyFormal.M2W6

open Finset
open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2 RMap)
open AdalyFormal.Balaban.SuTwoLogExp (SU2 M2)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond CoarseLattice mem_CoarseLattice)
open AdalyFormal.Balaban.RMapLipschitz (frobNorm)
open AdalyFormal.Balaban.CovariantHjMinimizer (trivialU)
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
open AdalyFormal.Balaban.AlphaAnalyticity (GaugeFn)
open AdalyFormal.NonflatJet
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.StatementLane (Tower Admissible scaleUp pdist)
open AdalyFormal.StatementLaneR8
open AdalyFormal.StatementLaneG (gparams)
open AdalyFormal.SliceCoerc (GF)
open AdalyFormal.BondComposite
open SmallnessBridge.Assemble (loopFactorBound)
open AdalyFormal.W6
open AdalyFormal.TowerLoc
open AdalyFormal.GaugeCov (adBL adFL adGen_symm_apply)

section main
variable {ell M R k : ℕ} {Lu : PeriodicLatticeExtent} {S : Tower (scaleUp ell k Lu)}

/-- **chart hypothesis**: row `p` has a gauge `γ_p` whose gauge-transformed configuration has its blocked links within `ε j' l`
of the identity on the ball `Ball z_p (20 ℓ^{lev p + 1})`, for the interacting levels `j'` (`|j' - lev p| ≤ 1`). -/
def ChartHyp (ell k : ℕ) (Lu : PeriodicLatticeExtent) (S : Tower (scaleUp ell k Lu)) (U : LinkCfg (scaleUp ell k Lu))
    (γ : BIdx (geomOf ell k S) → GaugeFn (scaleUp ell k Lu)) (ε : ℕ → ℕ → ℝ) : Prop :=
  ∀ p : BIdx (geomOf ell k S), ∀ j' : ℕ, (p.1 : ℕ) ≤ j' + 1 → j' ≤ (p.1 : ℕ) + 1 → ∀ l, l < k → l < j' →
    ∀ z ∈ Ball p.2.1.1 (20 * ell ^ ((p.1 : ℕ) + 1)), z ∈ CoarseLattice (scaleUp ell k Lu) (ell ^ l) → ∀ μ : Fin 3,
      frobNorm (((bgTower (GF ell k Lu) (periodicGaugeTransform (γ p) U) l (z, μ) : SU2) : M2) - 1) ≤ ε j' l

variable (hell2 : 2 ≤ ell) (hS : Admissible ell M R k S) (hM : 0 < M) (hroom : 17 * ell ≤ R * M)
  (U : LinkCfg (scaleUp ell k Lu)) (γ : BIdx (geomOf ell k S) → GaugeFn (scaleUp ell k Lu)) (ε : ℕ → ℕ → ℝ)
  (hch : ChartHyp ell k Lu S U γ ε)
  (hε0 : ∀ j' l, l < k → 0 ≤ ε j' l) (hsm : ∀ j' l, l < k → rhoOf ell (ε j' l) < Real.pi / 2)
  (hr : ∀ j' l, l < k → Real.pi / 2 * ((loopFactorBound ell : ℝ) * ε j' l) < r0)
  (Sstar : ℝ) (hSstar : ∀ j' : ℕ, j' ≤ k → ∑ l ∈ range j', thetaOf ell (ε j' l) ≤ Sstar)

include hell2 hS hM hroom hch hε0 hsm hr hSstar in
theorem nF_Dvec (p : BIdx (geomOf ell k S)) (w : SuTwo) :
    nF (Dvec (by omega : 0 < ell) U γ p w) ≤ 3 * delStar ell Sstar ^ 2 * CE * (wF p * ‖w‖ ^ 2) := by
  have hell : 0 < ell := by omega
  have h1 : nF (Dvec hell U γ p w) = nF (Dfun hell U γ p (RMap ((γ p) p.2.1.1) w)) :=
    nF_rot hell (fun p' => ((γ p) p'.2.1.1)⁻¹) _
  rw [h1]
  have h2 := (source_bounds hell2 hS hM hroom (periodicGaugeTransform (γ p) U) p ε (hch p) hε0 hsm hr Sstar hSstar
    (RMap ((γ p) p.2.1.1) w)).1
  have h3 := psiL_norm_sq hell hell2 hS p (RMap ((γ p) p.2.1.1) w)
  rw [norm_RMap] at h3
  have h4 : 0 ≤ 3 * delStar ell Sstar ^ 2 := by positivity
  calc _ ≤ _ := h2
    _ ≤ 3 * delStar ell Sstar ^ 2 * (CE * (wF p * ‖w‖ ^ 2)) := mul_le_mul_of_nonneg_left h3 h4
    _ = _ := by ring

include hell2 hS hM hroom hch hε0 hsm hr hSstar in
theorem nF_Tvec (p : BIdx (geomOf ell k S)) (w : SuTwo) :
    nF (Tvec (by omega : 0 < ell) U γ p w) ≤ 3 * (Real.exp (Sstar / rr ell)) ^ 2 * CE * (wF p * ‖w‖ ^ 2) := by
  have hell : 0 < ell := by omega
  have h1 : nF (Tvec hell U γ p w) = nF ((bondSectorOf (geomOf ell k S) (periodicGaugeTransform (γ p) U)).Qfull
        (psiL hell p (RMap ((γ p) p.2.1.1) w))) := by
    have : Tvec hell U γ p w = WithLp.toLp 2 (fun p' : BIdx (geomOf ell k S) =>
        RMap (((γ p) p'.2.1.1)⁻¹) (((bondSectorOf (geomOf ell k S) (periodicGaugeTransform (γ p) U)).Qfull
        (psiL hell p (RMap ((γ p) p.2.1.1) w))) p')) := PiLp.ext (fun p' => Tvec_eq hell U γ p p' w)
    rw [this]
    exact nF_rot hell (fun p' => ((γ p) p'.2.1.1)⁻¹) _
  rw [h1]
  have h2 := (source_bounds hell2 hS hM hroom (periodicGaugeTransform (γ p) U) p ε (hch p) hε0 hsm hr Sstar hSstar
    (RMap ((γ p) p.2.1.1) w)).2
  have h3 := psiL_norm_sq hell hell2 hS p (RMap ((γ p) p.2.1.1) w)
  rw [norm_RMap] at h3
  have h4 : 0 ≤ 3 * (Real.exp (Sstar / rr ell)) ^ 2 := by positivity
  calc _ ≤ _ := h2
    _ ≤ 3 * (Real.exp (Sstar / rr ell)) ^ 2 * (CE * (wF p * ‖w‖ ^ 2)) := mul_le_mul_of_nonneg_left h3 h4
    _ = _ := by ring

include hell2 hS hM hroom hch hε0 hsm hr hSstar in
theorem nF_Sfun (y : FSp (geomOf ell k S)) :
    nF (Sfun (by omega : 0 < ell) U γ y) ≤ CsrcS ell Sstar * nF y := by
  classical
  have hell : 0 < ell := by omega
  rw [Sfun_eq_sum]
  have hsupp : ∀ p p' : BIdx (geomOf ell k S), ¬ Inter p' p → (Dvec hell U γ p (y p)) p' = 0 := by
    intro p p' hI
    show RMap _ ((Dfun hell U γ p (RMap ((γ p) p.2.1.1) (y p))) p') = 0
    unfold Dfun
    rw [PiLp.sub_apply, Qfull_zero_of_not_inter hell2 hS hM hroom (periodicGaugeTransform (γ p) U) p p' hI _,
      Qfull_zero_of_not_inter hell2 hS hM hroom (trivialU _) p p' hI _, sub_zero, map_zero]
  have hsp := nF_sum_sparse hell (9 * (24 * ell + 1) ^ 3) (fun p => Dvec hell U γ p (y p)) hsupp
    (fun p' => card_inter hell p')
  refine hsp.trans ?_
  have hc : (((9 * (24 * ell + 1) ^ 3 : ℕ)) : ℝ) = mult0 ell := by unfold mult0; push_cast; ring
  rw [hc]
  have : ∑ p, nF (Dvec hell U γ p (y p)) ≤ 3 * delStar ell Sstar ^ 2 * CE * nF y := by
    unfold nF
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum (fun p _ => (nF_Dvec hell2 hS hM hroom U γ ε hch hε0 hsm hr Sstar hSstar p (y p)).trans
      (le_of_eq (by ring)))
  unfold CsrcS
  calc mult0 ell * ∑ p, nF (Dvec hell U γ p (y p)) ≤ mult0 ell * (3 * delStar ell Sstar ^ 2 * CE * nF y) :=
        mul_le_mul_of_nonneg_left this (by unfold mult0; positivity)
    _ = _ := by ring

include hell2 hS hM hroom hch hε0 hsm hr hSstar in
theorem nF_Tlin (y : FSp (geomOf ell k S)) :
    nF (Tlin (by omega : 0 < ell) U γ y) ≤ CsrcT ell Sstar * nF y := by
  classical
  have hell : 0 < ell := by omega
  rw [Tlin_eq_sum]
  have hsupp : ∀ p p' : BIdx (geomOf ell k S), ¬ Inter p' p → (Tvec hell U γ p (y p)) p' = 0 := by
    intro p p' hI
    rw [Tvec_eq, Qfull_zero_of_not_inter hell2 hS hM hroom (periodicGaugeTransform (γ p) U) p p' hI _, map_zero]
  have hsp := nF_sum_sparse hell (9 * (24 * ell + 1) ^ 3) (fun p => Tvec hell U γ p (y p)) hsupp
    (fun p' => card_inter hell p')
  refine hsp.trans ?_
  have hc : (((9 * (24 * ell + 1) ^ 3 : ℕ)) : ℝ) = mult0 ell := by unfold mult0; push_cast; ring
  rw [hc]
  have : ∑ p, nF (Tvec hell U γ p (y p)) ≤ 3 * (Real.exp (Sstar / rr ell)) ^ 2 * CE * nF y := by
    unfold nF
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum (fun p _ => (nF_Tvec hell2 hS hM hroom U γ ε hch hε0 hsm hr Sstar hSstar p (y p)).trans
      (le_of_eq (by ring)))
  unfold CsrcT
  calc mult0 ell * ∑ p, nF (Tvec hell U γ p (y p)) ≤ mult0 ell * (3 * (Real.exp (Sstar / rr ell)) ^ 2 * CE * nF y) :=
        mul_le_mul_of_nonneg_left this (by unfold mult0; positivity)
    _ = _ := by ring

end main

end AdalyFormal.M2W6

#print axioms AdalyFormal.M2W6.nF_Sfun
#print axioms AdalyFormal.M2W6.nF_Tlin
