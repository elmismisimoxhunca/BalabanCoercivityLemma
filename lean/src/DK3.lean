import DK1
import DLR76

/-!
# DK3 -- `Σ_e ‖D̃⁽²⁾(B)(e)‖ ≤ KDfree ℓ ‖B‖²` when the unit background is small ONLY on the balls the rows of `Λ'` read

`D2in B = ℓ⁻¹ h(C̃⁽²⁾(B))` reads the unit background `Ū^k = P.unitBgU` only on the balls `Ball(c₋, 4ℓ)` of the coarse bonds
`c` touching `Λ'` (r8 `QlinStepL_congr_bg`, `C2StepL_congr_bg`, `hLift_congr_rows`).
* `Vcut ℓ Λ W` : `W` on those balls, `1` elsewhere; `Vcut_agree`, `Q1jet_cut`, `C2tilde_cut`, `Vcut_small` (globally `≤ κ`).
* `H0_bij_of_drift` : an `ℓ¹` drift `δ < ℓ⁻³` of `H₀(Q)` from `H₀(1) = ℓ⁻³ id` makes `H₀(Q)` injective, hence bijective
  (finite dimension) -- no `IngrBParams` needed (unlike MF6d `hb_of_small`).
* **`D2in_l1_near`** : for any `P` with `ℓ ≥ 2`, `ℓ ∣ Lu_μ + 1`, and `‖Ū^k(z,μ) − 1‖ ≤ κ` on those balls, with the three
  k-free unit conditions on `κ` (`u1`, `u2` of `UnitSmall` form and DL76's `hKDc`): the DL76 bound (constant `KDfree ℓ`).
No sorry / native_decide / axiom.
-/
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 8000

namespace AdalyFormal.M1DK

open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane (CRowIn scaleUp)
open AdalyFormal.StatementLaneR8 (Ball AgreeAt QlinStepL_congr_bg C2StepL_congr_bg suCoordFInv_apply_congr hLift_congr_rows)
open AdalyFormal.Balaban.RMapLipschitz (frobSq frobNorm frobSq_nonneg frobNorm_nonneg frobNorm_sq)
open AdalyFormal.Balaban.SuTwoLogExp (SU2 M2)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.LatticeOperators (CoarseBond)
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.IngredientFamilyR2 (RegBg Q1jet H0 C2tilde hLift IngrBParams Dset QlinStepL C2StepL suCoordF suCoordFInv)
open AdalyFormal.NonflatJet (rhoOf r0)
open EstimatesLayer.E1E3 (e2Majorant e2Majorant_nonneg)
open AdalyFormal.DLayer (KDfree K2s H0_drift_l1 hLift_l1 C2tilde_l1)

variable {Lu : PeriodicLatticeExtent}

open Classical in
/-- the unit background cut to the balls read by the rows of `Λ'` -/
noncomputable def Vcut (ell : ℕ) (Lam : Set (PeriodicLatticeSite Lu)) (W : PeriodicLinkConfiguration SU2 Lu) :
    PeriodicLinkConfiguration SU2 Lu :=
  fun e => if (∃ c : CoarseBond Lu ell, CRowIn ell Lam c ∧ e.1 ∈ Ball c.1.1 (4 * (1 * ell))) then W e else 1

theorem Vcut_agree (ell : ℕ) (Lam : Set (PeriodicLatticeSite Lu)) (W : PeriodicLinkConfiguration SU2 Lu)
    {c : CoarseBond Lu ell} (hc : CRowIn ell Lam c) : AgreeAt (Ball c.1.1 (4 * (1 * ell))) W (Vcut ell Lam W) := by
  intro z hz μ
  show W (z, μ) = Vcut ell Lam W (z, μ)
  unfold Vcut
  rw [if_pos ⟨c, hc, hz⟩]

theorem Q1jet_cut (ell : ℕ) (Lam : Set (PeriodicLatticeSite Lu)) (W : PeriodicLinkConfiguration SU2 Lu)
    (B : Bond Lu → SuTwo) {c : CoarseBond Lu ell} (hc : CRowIn ell Lam c) :
    Q1jet ell W B c = Q1jet ell (Vcut ell Lam W) B c := by
  have hrow : QlinStepL 1 ell W (suCoordF B) (c.1.1, c.2) = QlinStepL 1 ell (Vcut ell Lam W) (suCoordF B) (c.1.1, c.2) :=
    QlinStepL_congr_bg 1 ell one_pos (c.1.1, c.2) (Vcut_agree ell Lam W hc) _
  show ((ell : ℝ)⁻¹) • (suCoordFInv (QlinStepL 1 ell W (suCoordF B))) (c.1.1, c.2)
    = ((ell : ℝ)⁻¹) • (suCoordFInv (QlinStepL 1 ell (Vcut ell Lam W) (suCoordF B))) (c.1.1, c.2)
  rw [suCoordFInv_apply_congr hrow]

theorem C2tilde_cut (ell : ℕ) (Lam : Set (PeriodicLatticeSite Lu)) (W : PeriodicLinkConfiguration SU2 Lu)
    (B : Bond Lu → SuTwo) {c : CoarseBond Lu ell} (hc : CRowIn ell Lam c) :
    C2tilde ell W B c = C2tilde ell (Vcut ell Lam W) B c := by
  have hrow : C2StepL 1 ell W (suCoordF B) (c.1.1, c.2) = C2StepL 1 ell (Vcut ell Lam W) (suCoordF B) (c.1.1, c.2) :=
    C2StepL_congr_bg 1 ell one_pos (c.1.1, c.2) (Vcut_agree ell Lam W hc) _
  show (suCoordFInv (C2StepL 1 ell W (suCoordF B))) (c.1.1, c.2)
    = (suCoordFInv (C2StepL 1 ell (Vcut ell Lam W) (suCoordF B))) (c.1.1, c.2)
  rw [suCoordFInv_apply_congr hrow]

theorem Vcut_small (ell : ℕ) (Lam : Set (PeriodicLatticeSite Lu)) (W : PeriodicLinkConfiguration SU2 Lu) (κ : ℝ)
    (hκ : 0 ≤ κ)
    (hnear : ∀ c : CoarseBond Lu ell, CRowIn ell Lam c → ∀ z ∈ Ball c.1.1 (4 * (1 * ell)), ∀ μ : Fin 3,
      frobNorm (((W (z, μ) : SU2) : M2) - 1) ≤ κ)
    (e : PeriodicLatticeEdge Lu) : frobNorm (((Vcut ell Lam W e : SU2) : M2) - 1) ≤ κ := by
  unfold Vcut
  split_ifs with h
  · obtain ⟨c, hc, hz⟩ := h
    exact hnear c hc e.1 hz e.2
  · have : frobNorm (((1 : SU2) : M2) - 1) = 0 := by
      simp [frobNorm, frobSq]
    rw [this]; exact hκ

/-- **`H₀` bijective from its `ℓ¹` drift.** -/
theorem H0_bij_of_drift {ell : ℕ} (hell : 0 < ell) (hdvd : ∀ μ : Fin 3, ell ∣ (Lu μ + 1))
    (Lam : Set (PeriodicLatticeSite Lu)) (Q : (Bond Lu → SuTwo) →ₗ[ℝ] (CoarseBond Lu ell → SuTwo)) (δ : ℝ)
    (hδ : δ < 1 / (ell : ℝ) ^ 3)
    (hdrift : ∀ w : Dset Lu ell Lam → SuTwo, ∑ d, ‖H0 Lam Q w d - H0 Lam (AdalyFormal.IngredientFamily.q1SU2 ell) w d‖
      ≤ δ * ∑ d, ‖w d‖) :
    Function.Bijective (H0 Lam Q) := by
  classical
  have hinj : Function.Injective (H0 Lam Q) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro w hw
    have hflat : ∀ d, H0 Lam (AdalyFormal.IngredientFamily.q1SU2 ell) w d = ((1 : ℝ) / (ell : ℝ) ^ 3) • w d :=
      fun d => AdalyFormal.IngredientFamilyR2.H0_q1SU2_apply hell hdvd Lam w d
    have hpt : ∀ d, ‖H0 Lam Q w d - H0 Lam (AdalyFormal.IngredientFamily.q1SU2 ell) w d‖
        = ((1 : ℝ) / (ell : ℝ) ^ 3) * ‖w d‖ := by
      intro d
      rw [hw, hflat d]
      simp only [Pi.zero_apply, zero_sub, norm_neg, norm_smul]
      rw [Real.norm_of_nonneg (by positivity)]
    have h1 := hdrift w
    rw [Finset.sum_congr rfl (fun d _ => hpt d), ← Finset.mul_sum] at h1
    have hS0 : 0 ≤ ∑ d, ‖w d‖ := Finset.sum_nonneg (fun d _ => norm_nonneg _)
    have hS : ∑ d, ‖w d‖ = 0 := by
      by_contra hne
      have hpos : 0 < ∑ d, ‖w d‖ := lt_of_le_of_ne hS0 (Ne.symm hne)
      have := mul_lt_mul_of_pos_right hδ hpos
      linarith
    funext d
    have hd := (Finset.sum_eq_zero_iff_of_nonneg (fun d _ => norm_nonneg (w d))).mp hS d (Finset.mem_univ _)
    simpa using hd
  exact ⟨hinj, LinearMap.injective_iff_surjective.mp hinj⟩

/-- **the D2-premise at a generic `P`, from smallness of `Ū^k` on the read balls only.** -/
theorem D2in_l1_near (P : IngrBParams) (hd : ∀ μ, P.ell ∣ P.Lu μ + 1) (hell2 : 2 ≤ P.ell) (κ : ℝ) (hκ0 : 0 ≤ κ)
    (hnear : ∀ c : CoarseBond P.Lu P.ell, CRowIn P.ell P.Lam c → ∀ z ∈ Ball c.1.1 (4 * (1 * P.ell)), ∀ μ : Fin 3,
      frobNorm (((P.unitBgU (z, μ) : SU2) : M2) - 1) ≤ κ)
    (u1 : κ ≤ 1 / (1000 * (P.ell : ℝ) ^ 4))
    (u2 : Real.pi / 2 * ((SmallnessBridge.Assemble.loopFactorBound P.ell : ℝ) * κ) < r0)
    (hKDc : 192 * (8 * (P.ell : ℝ) * κ + 8 * e2Majorant (rhoOf P.ell κ)) ≤ 1 / (2 * (P.ell : ℝ) ^ 3))
    (B : BondFnL2 P.Lu) :
    ∑ e', ‖(P.D2in B) e'‖ ≤ KDfree P.ell * ‖B‖ ^ 2 := by
  have hell : 0 < P.ell := P.hell
  set ell := P.ell with hellP
  have hellR : (0 : ℝ) < ell := by exact_mod_cast hell
  set Lam := P.Lam with hLam
  set V := Vcut ell Lam P.unitBgU with hVdef
  have hV : ∀ e', frobNorm (((V e' : SU2) : M2) - 1) ≤ κ := Vcut_small ell Lam P.unitBgU κ hκ0 hnear
  have hns := AdalyFormal.NonflatJet.numeric_small hell κ hκ0 u1
  have hreg1 : RegBg 1 ell V := AdalyFormal.NonflatJet.regBg_of_small Nat.one_pos V κ hκ0 hV u2
  set δ := 192 * (8 * (ell : ℝ) * κ + 8 * e2Majorant (rhoOf ell κ)) with hδ
  have hδlt : δ < 1 / (ell : ℝ) ^ 3 := by
    have : 1 / (2 * (ell : ℝ) ^ 3) < 1 / (ell : ℝ) ^ 3 := by
      rw [div_lt_div_iff₀ (by positivity) (by positivity)]; nlinarith [pow_pos hellR 3]
    linarith
  have hdrift := fun w => H0_drift_l1 hell hd Lam V κ hκ0 hV hns.1 hreg1 w
  have hbV : Function.Bijective (H0 Lam (Q1jet ell V)) := H0_bij_of_drift hell hd Lam (Q1jet ell V) δ hδlt hdrift
  have hL := hLift_l1 hell hd Lam V δ hbV hδlt hdrift (C2tilde ell V (WithLp.ofLp B))
  -- loops
  have hloop : 8 * (ell : ℝ) * κ ≤ 1 / 16 := by
    have h1 := u1
    have hl2 : (2 : ℝ) ≤ ell := by exact_mod_cast hell2
    have hl3 : (8 : ℝ) * ell ≤ 8 * (ell : ℝ) ^ 4 := by nlinarith [pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 2) hl2 3]
    have h5 : 8 * (ell : ℝ) * κ ≤ 8 * (ell : ℝ) ^ 4 * (1 / (1000 * (ell : ℝ) ^ 4)) := by
      have := mul_le_mul hl3 h1 hκ0 (by positivity); linarith
    have h6 : 8 * (ell : ℝ) ^ 4 * (1 / (1000 * (ell : ℝ) ^ 4)) = 8 / 1000 := by field_simp
    linarith
  have hC := C2tilde_l1 hell hd V hreg1 κ hκ0 hV hloop (WithLp.ofLp B)
  -- the cut background reproduces `D2in`
  have hcong : hLift Lam P.Q1 (C2tilde ell P.unitBgU (WithLp.ofLp B))
      = hLift Lam (Q1jet ell V) (C2tilde ell V (WithLp.ofLp B)) :=
    hLift_congr_rows Lam (fun B' c hc => Q1jet_cut ell Lam P.unitBgU B' hc)
      (fun c hc => C2tilde_cut ell Lam P.unitBgU _ hc)
  -- assemble (as DL76)
  have hpos : 0 < 1 / (ell : ℝ) ^ 3 - δ := by linarith
  have hinv : 1 / (1 / (ell : ℝ) ^ 3 - δ) ≤ 2 * (ell : ℝ) ^ 3 := by
    rw [div_le_iff₀ hpos]
    have : 1 / (ell : ℝ) ^ 3 - δ ≥ 1 / (2 * (ell : ℝ) ^ 3) := by
      have e1 : 1 / (ell : ℝ) ^ 3 = 2 * (1 / (2 * (ell : ℝ) ^ 3)) := by field_simp
      linarith
    have e2 : 2 * (ell : ℝ) ^ 3 * (1 / (2 * (ell : ℝ) ^ 3)) = 1 := by field_simp
    nlinarith [pow_pos hellR 3]
  have hB2 : ∑ b : Bond P.Lu, ‖(WithLp.ofLp B) b‖ ^ 2 = ‖B‖ ^ 2 := by
    rw [PiLp.norm_sq_eq_of_L2]
  have hpt : ∀ e', ‖(P.D2in B) e'‖ = (ell : ℝ)⁻¹ * ‖hLift Lam (Q1jet ell V) (C2tilde ell V (WithLp.ofLp B)) e'‖ := by
    intro e'
    show ‖((ell : ℝ)⁻¹ • hLift Lam P.Q1 (C2tilde ell P.unitBgU (WithLp.ofLp B))) e'‖ = _
    rw [hcong, Pi.smul_apply, norm_smul, Real.norm_of_nonneg (by positivity)]
  rw [Finset.sum_congr rfl fun e' _ => hpt e', ← Finset.mul_sum]
  set S1 := ∑ c, ‖C2tilde ell V (WithLp.ofLp B) c‖ with hS1
  have hS10 : 0 ≤ S1 := Finset.sum_nonneg fun c _ => norm_nonneg _
  have hL' : ∑ b : Bond P.Lu, ‖hLift Lam (Q1jet ell V) (C2tilde ell V (WithLp.ofLp B)) b‖
      ≤ 2 * (ell : ℝ) ^ 3 * S1 := by
    refine hL.trans ?_
    rw [div_eq_mul_one_div, mul_comm]
    exact mul_le_mul_of_nonneg_right hinv hS10
  rw [hB2] at hC
  have hK0 : 0 ≤ K2s ell := by unfold K2s; positivity
  calc (ell : ℝ)⁻¹ * ∑ b : Bond P.Lu, ‖hLift Lam (Q1jet ell V) (C2tilde ell V (WithLp.ofLp B)) b‖
      ≤ (ell : ℝ)⁻¹ * (2 * (ell : ℝ) ^ 3 * S1) := mul_le_mul_of_nonneg_left hL' (by positivity)
    _ ≤ (ell : ℝ)⁻¹ * (2 * (ell : ℝ) ^ 3 * (K2s ell * ‖B‖ ^ 2)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hC (by positivity)) (by positivity)
    _ = KDfree ell * ‖B‖ ^ 2 := by unfold KDfree; field_simp

#print axioms Vcut
#print axioms Vcut_agree
#print axioms Q1jet_cut
#print axioms C2tilde_cut
#print axioms Vcut_small
#print axioms H0_bij_of_drift
#print axioms D2in_l1_near

end AdalyFormal.M1DK
