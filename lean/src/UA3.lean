import UA2
import DK3

/-!
# UA3 -- the unit-level `Q₁` drift, row-local, in ℓ² form (lane m2_unit_20261014)

* `q1jet_congr_ball` : row `c` of `Q1jet ℓ W` reads `W` only on `Ball(c₀, 4ℓ)` (as DK3 `Q1jet_cut`, for any agreeing pair).
* `q1_drift_row` : if `‖W(z,μ) − 1‖_F ≤ κ` on `Ball(c₀, 4ℓ)` only (and the two k-free numeric conditions on `κ`), then
  `‖Q1jet ℓ W Z c − q₁ Z c‖² ≤ κ'² Σ_{e visible from c} ‖Z e‖²`, `κ' = 8ℓκ + 8 e2Majorant(ρ(κ))`.
  (Cut configuration `W` on the ball, `1` elsewhere; MF6b `Q1jet_sub_flat_le` in sup form with `M = (Σ_vis ‖Z‖²)^{1/2}`.)
* `sum_vis_sq_le` : `Σ_c Σ_{e visible from c} ‖Z e‖² ≤ 192 Σ_b ‖Z b‖²` (DLR68 `sum_vis_le`).
-/
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 8000
namespace AdalyFormal.M2Unit

open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.LatticeOperators (CoarseBond)
open AdalyFormal.Balaban.CovariantOperators (SuTwo)
open AdalyFormal.Balaban.SuTwoLogExp (SU2 M2)
open AdalyFormal.Balaban.RMapLipschitz (frobNorm frobSq)
open AdalyFormal.StatementLaneR8 (Ball AgreeAt QlinStepL_congr_bg suCoordFInv_apply_congr)
open AdalyFormal.IngredientFamilyR2 (RegBg Q1jet QlinStepL suCoordF suCoordFInv flatCfg)
open AdalyFormal.NonflatJet (rhoOf r0)
open SmallnessBridge.Assemble (loopFactorBound)
open EstimatesLayer.E1E3 (e2Majorant e2Majorant_nonneg)
open AdalyFormal.DLayer (VisStep)

variable {L : PeriodicLatticeExtent}

/-- the drift constant `κ' = 8ℓκ + 8 e2Majorant(ρ(κ))`. -/
noncomputable def kapQ (ell : ℕ) (κ : ℝ) : ℝ := 8 * ell * κ + 8 * e2Majorant (rhoOf ell κ)

theorem q1jet_congr_ball (ell : ℕ) {W V : PeriodicLinkConfiguration SU2 L} (B : Bond L → SuTwo) (c : CoarseBond L ell)
    (h : AgreeAt (Ball c.1.1 (4 * (1 * ell))) W V) : Q1jet ell W B c = Q1jet ell V B c := by
  have hrow : QlinStepL 1 ell W (suCoordF B) (c.1.1, c.2) = QlinStepL 1 ell V (suCoordF B) (c.1.1, c.2) :=
    QlinStepL_congr_bg 1 ell one_pos (c.1.1, c.2) h _
  show ((ell : ℝ)⁻¹) • (suCoordFInv (QlinStepL 1 ell W (suCoordF B))) (c.1.1, c.2)
    = ((ell : ℝ)⁻¹) • (suCoordFInv (QlinStepL 1 ell V (suCoordF B))) (c.1.1, c.2)
  rw [suCoordFInv_apply_congr hrow]

open Classical in
/-- the cut configuration: `W` on the ball, `1` elsewhere. -/
noncomputable def cutBall (y : PeriodicLatticeSite L) (r : ℕ) (W : PeriodicLinkConfiguration SU2 L) :
    PeriodicLinkConfiguration SU2 L :=
  fun e => if e.1 ∈ Ball y r then W e else 1

theorem cutBall_agree (y : PeriodicLatticeSite L) (r : ℕ) (W : PeriodicLinkConfiguration SU2 L) :
    AgreeAt (Ball y r) W (cutBall y r W) := by
  intro z hz μ
  show W (z, μ) = cutBall y r W (z, μ)
  unfold cutBall
  rw [if_pos hz]

theorem cutBall_small (y : PeriodicLatticeSite L) (r : ℕ) (W : PeriodicLinkConfiguration SU2 L) (κ : ℝ) (hκ : 0 ≤ κ)
    (hnear : ∀ z ∈ Ball y r, ∀ μ : Fin 3, frobNorm (((W (z, μ) : SU2) : M2) - 1) ≤ κ)
    (e : PeriodicLatticeEdge L) : frobNorm (((cutBall y r W e : SU2) : M2) - 1) ≤ κ := by
  unfold cutBall
  split_ifs with h
  · exact hnear e.1 h e.2
  · have : frobNorm (((1 : SU2) : M2) - 1) = 0 := by simp [frobNorm, frobSq]
    rw [this]; exact hκ

open Classical in
/-- **the row-local `Q₁` drift, ℓ² form.** -/
theorem q1_drift_row {ell : ℕ} (hell : 0 < ell) (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1))
    (W : PeriodicLinkConfiguration SU2 L) (κ : ℝ) (hκ : 0 ≤ κ) (hρ : rhoOf ell κ < Real.pi / 2)
    (hrg : Real.pi / 2 * ((loopFactorBound ell : ℝ) * κ) < r0) (c : CoarseBond L ell)
    (hnear : ∀ z ∈ Ball c.1.1 (4 * (1 * ell)), ∀ μ : Fin 3, frobNorm (((W (z, μ) : SU2) : M2) - 1) ≤ κ)
    (Z : Bond L → SuTwo) :
    ‖Q1jet ell W Z c - AdalyFormal.IngredientFamily.q1SU2 ell Z c‖ ^ 2
      ≤ kapQ ell κ ^ 2 * ∑ e ∈ Finset.univ.filter (fun e => VisStep 1 ell (c.1.1, c.2) e), ‖Z e‖ ^ 2 := by
  set V := cutBall c.1.1 (4 * (1 * ell)) W with hVdef
  have hWV : Q1jet ell W Z c = Q1jet ell V Z c := q1jet_congr_ball ell Z c (cutBall_agree _ _ W)
  have hV : ∀ e, frobNorm (((V e : SU2) : M2) - 1) ≤ κ := cutBall_small _ _ W κ hκ hnear
  have hreg : RegBg 1 ell V := AdalyFormal.NonflatJet.regBg_of_small Nat.one_pos V κ hκ hV hrg
  set Z' : Bond L → SuTwo := fun e => if VisStep 1 ell (c.1.1, c.2) e then Z e else 0 with hZ'
  have h1 := AdalyFormal.DLayer.Q1jet_row_congr ell V hreg Z Z' c (fun e he => by simp [hZ', he])
  have h2 := AdalyFormal.DLayer.Q1jet_row_congr ell flatCfg (AdalyFormal.NonflatJet.regBg_flat ell) Z Z' c
    (fun e he => by simp [hZ', he])
  have hflat : Q1jet ell flatCfg Z c = AdalyFormal.IngredientFamily.q1SU2 ell Z c :=
    AdalyFormal.IngredientFamilyR2.Q1jet_flat ell hell hdvd Z c
  set S := ∑ e ∈ Finset.univ.filter (fun e => VisStep 1 ell (c.1.1, c.2) e), ‖Z e‖ ^ 2 with hS
  have hS0 : 0 ≤ S := Finset.sum_nonneg (fun e _ => sq_nonneg _)
  set M := Real.sqrt S with hM
  have hM0 : 0 ≤ M := Real.sqrt_nonneg _
  have hbd : ∀ b, ‖Z' b‖ ≤ M := by
    intro b
    by_cases hb : VisStep 1 ell (c.1.1, c.2) b
    · simp only [hZ', if_pos hb]
      rw [hM]
      apply Real.le_sqrt_of_sq_le
      exact Finset.single_le_sum (f := fun e => ‖Z e‖ ^ 2) (fun e _ => sq_nonneg _)
        (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hb⟩)
    · simp only [hZ', if_neg hb, norm_zero]; exact hM0
  have hdr := AdalyFormal.M0Finish.R7.Q1jet_sub_flat_le hell hdvd V κ hκ hV hρ hreg Z' M hM0 hbd c
  rw [hWV, ← hflat, h1, h2]
  have hk0 : 0 ≤ kapQ ell κ := by
    unfold kapQ
    have : 0 ≤ e2Majorant (rhoOf ell κ) := e2Majorant_nonneg (by unfold rhoOf; positivity)
    positivity
  have hdr' : ‖Q1jet ell V Z' c - Q1jet ell flatCfg Z' c‖ ≤ kapQ ell κ * M := hdr
  have h0 := norm_nonneg (Q1jet ell V Z' c - Q1jet ell flatCfg Z' c)
  have hsq := pow_le_pow_left₀ h0 hdr' 2
  rw [mul_pow, hM, Real.sq_sqrt hS0] at hsq
  exact hsq

open Classical in
/-- double counting: `Σ_c Σ_{e visible from c} ‖Z e‖² ≤ 192 Σ_b ‖Z b‖²`. -/
theorem sum_vis_sq_le {ell : ℕ} (hell : 0 < ell) (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1)) (Z : Bond L → SuTwo) :
    ∑ c : CoarseBond L ell, ∑ e ∈ Finset.univ.filter (fun e => VisStep 1 ell (c.1.1, c.2) e), ‖Z e‖ ^ 2
      ≤ 192 * ∑ b : Bond L, ‖Z b‖ ^ 2 := by
  have hn : ∀ ν, 1 * ell ∣ L ν + 1 := fun ν => by rw [one_mul]; exact hdvd ν
  have h3 := AdalyFormal.DLayer.sum_vis_le 1 ell Nat.one_pos hell hn (fun e => ‖Z e‖ ^ 2) (fun e => sq_nonneg _)
  have h4 := AdalyFormal.DLayer.sum_one_mul (Lq := L) ell
    (fun y μ => ∑ e ∈ Finset.univ.filter (fun e => VisStep 1 ell (y, μ) e), ‖Z e‖ ^ 2)
  have h5 : ∑ e : CoarseBond L 1, ‖Z (e.1.1, e.2)‖ ^ 2 = ∑ e : Bond L, ‖Z e‖ ^ 2 :=
    (AdalyFormal.BondComposite.sum_edge_eq_coarse1 (fun e => ‖Z e‖ ^ 2)).symm
  rw [h4]
  rw [h5] at h3
  exact h3

end AdalyFormal.M2Unit

#print axioms AdalyFormal.M2Unit.q1jet_congr_ball
#print axioms AdalyFormal.M2Unit.cutBall_small
#print axioms AdalyFormal.M2Unit.q1_drift_row
#print axioms AdalyFormal.M2Unit.sum_vis_sq_le
