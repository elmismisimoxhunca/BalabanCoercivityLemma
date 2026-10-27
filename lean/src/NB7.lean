import NB6
/-!
# NB7 -- `log_ubar_lin`: linearisation of one blocked link (piece N4a)

If every bond read by the blocking of `c` is a chart bond (`W b = exp (A b)`, `A b ∈ 𝔰𝔲(2)`,
`‖A b‖_F ≤ k`) and `8·ell·k ≤ 1/(8π)`, then `exp (log Ū_c) = Ū_c` and
`‖log Ū_c − blkM s ell A c‖_F ≤ 200 π ell² k²`, `Ū_c = ubarSU2 s ell W c`.

No sorry / native_decide / axioms.
-/
set_option autoImplicit false
noncomputable section
namespace AdalyFormal.CurvBlock
open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.SuTwoLogExp (SU2 M2 su2Log su2Exp)
open AdalyFormal.Balaban.RMapLipschitz (frobNorm frobNorm_nonneg)
open AdalyFormal.Balaban.TowerLawCov (coarsePathHolonomy coarseGammaPath)
open AdalyFormal.Balaban.QjComposite (stepBlockOf)
open AdalyFormal.Balaban.UbarTowerCov (cPlusS coarseBondVar gammaVarStrided loopVar)
open AdalyFormal.Balaban.BlockedBackground (ubarSU2 ubarSU2_eq_blockedLink)
open AdalyFormal.Balaban.BlockingLinkEstimate (blockExponent)
open AdalyFormal.Balaban.Bch2 (IsSu2)

variable {L : PeriodicLatticeExtent}

theorem log_ubar_lin (s ell : ℕ) (hs : 0 < s) (hell : 0 < ell)
    (W : PeriodicLinkConfiguration SU2 L) (A : PeriodicLatticeEdge L → M2) (k : ℝ) (hk : 0 ≤ k)
    (hsm : 8 * (ell : ℝ) * k ≤ 1 / (8 * Real.pi)) (c : PeriodicLatticeEdge L)
    (h : ∀ x ∈ stepBlockOf c.1 s ell, ∀ b ∈ loopBonds s ell c x, Chart W A k b)
    (hc : ∀ b ∈ pathBonds s c.1 (List.replicate ell c.2), Chart W A k b) :
    su2Exp (su2Log (ubarSU2 s ell W c)) = ubarSU2 s ell W c ∧
    frobNorm (su2Log (ubarSU2 s ell W c) - blkM s ell A c)
      ≤ 200 * Real.pi * ((ell : ℝ) ^ 2 * k ^ 2) := by
  have hpi := Real.pi_gt_three
  have hellR : (1 : ℝ) ≤ ell := by exact_mod_cast hell
  set κ : ℝ := 8 * (ell : ℝ) * k
  have hκ0 : 0 ≤ κ := by positivity
  have hκ : 2 * Real.pi * κ ≤ 1 / 4 := by
    have := mul_le_mul_of_nonneg_left hsm (by positivity : (0:ℝ) ≤ 2 * Real.pi)
    have e : 2 * Real.pi * (1 / (8 * Real.pi)) = 1 / 4 := by field_simp; ring
    linarith
  have hκ' : κ ≤ 1 / (2 * Real.pi) := by
    rw [le_div_iff₀ (by positivity)]; nlinarith
  set S := stepBlockOf c.1 s ell
  set w : PeriodicLatticeSite L → ℝ := fun _ => ((ell : ℝ) ^ 3)⁻¹
  have hw0 : ∀ x, 0 ≤ w x := fun x => by positivity
  have hwsum := AdalyFormal.Balaban.ClassPropagationUbar.weight_sum_le_one c.1 hs hell
  -- each block loop
  have hloop : ∀ x ∈ S, IsSu2 (su2Log (loopVar s ell W c x)) ∧
      frobNorm (su2Log (loopVar s ell W c x) - loopM s ell A c x) ≤ 2 * Real.pi * κ ^ 2 ∧
      frobNorm (loopM s ell A c x) ≤ κ := by
    intro x hx
    obtain ⟨hp, hsum, hsu, hn⟩ := loopList_facts s ell hs W A k hk c x hx (h x hx)
    have hn' : ((loopList s ell A c x).map frobNorm).sum ≤ 1 / (2 * Real.pi) := le_trans hn hκ'
    obtain ⟨-, hb⟩ := multi_bch _ hsu hn'
    refine ⟨AdalyFormal.Balaban.Bch2.isSu2_su2Log _, ?_, ?_⟩
    · rw [hp, ← hsum]
      refine le_trans hb ?_
      have h0 : 0 ≤ ((loopList s ell A c x).map frobNorm).sum := le_trans (frobNorm_nonneg _)
        (frob_sum_le _)
      have hn2 : ((loopList s ell A c x).map frobNorm).sum ≤ κ := hn
      have hsq := mul_le_mul hn2 hn2 h0 hκ0
      have := mul_le_mul_of_nonneg_left hsq (by positivity : (0:ℝ) ≤ 2 * Real.pi)
      nlinarith
    · rw [← hsum]; exact le_trans (frob_sum_le _) (show _ ≤ κ from hn)
  -- the block exponent
  set H := blockExponent S w (fun x => loopVar s ell W c x)
  have hHe : H = ∑ x ∈ S, w x • su2Log (loopVar s ell W c x) := by
    simp only [H, blockExponent, real_csmul]
  have hHsu : IsSu2 H := ⟨AdalyFormal.Balaban.ClassPropagationUbar.blockExponent_antiHerm _ _ _,
    AdalyFormal.Balaban.ClassPropagationUbar.blockExponent_trace _ _ _⟩
  set Lm : M2 := ∑ x ∈ S, w x • loopM s ell A c x
  have hHL : frobNorm (H - Lm) ≤ 2 * Real.pi * κ ^ 2 := by
    rw [hHe, ← Finset.sum_sub_distrib]
    refine le_trans (AdalyFormal.Balaban.BlockingLinkEstimate.frobNorm_sum_le _ _) ?_
    calc ∑ x ∈ S, frobNorm (w x • su2Log (loopVar s ell W c x) - w x • loopM s ell A c x)
        ≤ ∑ x ∈ S, w x * (2 * Real.pi * κ ^ 2) := by
          refine Finset.sum_le_sum (fun x hx => ?_)
          rw [← smul_sub, AdalyFormal.Balaban.Bch2.frobNorm_smul, abs_of_nonneg (hw0 x)]
          exact mul_le_mul_of_nonneg_left (hloop x hx).2.1 (hw0 x)
      _ = (∑ x ∈ S, w x) * (2 * Real.pi * κ ^ 2) := by rw [Finset.sum_mul]
      _ ≤ 1 * (2 * Real.pi * κ ^ 2) := mul_le_mul_of_nonneg_right hwsum (by positivity)
      _ = 2 * Real.pi * κ ^ 2 := one_mul _
  have hLn : frobNorm Lm ≤ κ := by
    refine le_trans (AdalyFormal.Balaban.BlockingLinkEstimate.frobNorm_sum_le _ _) ?_
    calc ∑ x ∈ S, frobNorm (w x • loopM s ell A c x) ≤ ∑ x ∈ S, w x * κ := by
          refine Finset.sum_le_sum (fun x hx => ?_)
          rw [AdalyFormal.Balaban.Bch2.frobNorm_smul, abs_of_nonneg (hw0 x)]
          exact mul_le_mul_of_nonneg_left (hloop x hx).2.2 (hw0 x)
      _ = (∑ x ∈ S, w x) * κ := by rw [Finset.sum_mul]
      _ ≤ 1 * κ := mul_le_mul_of_nonneg_right hwsum hκ0
      _ = κ := one_mul _
  have hHn : frobNorm H ≤ 2 * κ := by
    have := AdalyFormal.Balaban.Bch2.frobNorm_add_le (H - Lm) Lm
    rw [sub_add_cancel] at this
    nlinarith
  -- the coarse bond
  obtain ⟨pc, -, sc, -, uc, -, nc, -⟩ := pl_facts s W A k _ _ hc
  rw [List.length_replicate] at nc
  have hkc : (ell : ℝ) * k ≤ κ := by simp only [κ]; nlinarith
  obtain ⟨hce, hcb⟩ := multi_bch _ uc (le_trans (le_trans nc hkc) hκ')
  set Y := su2Log ((List.map su2Exp (pl s A c.1 (List.replicate ell c.2))).prod)
  have hYsu : IsSu2 Y := AdalyFormal.Balaban.Bch2.isSu2_su2Log _
  have h0c : 0 ≤ ((pl s A c.1 (List.replicate ell c.2)).map frobNorm).sum :=
    le_trans (frobNorm_nonneg _) (frob_sum_le _)
  have hYB : frobNorm (Y - bondM s ell A c) ≤ 2 * Real.pi * ((ell : ℝ) * k) ^ 2 := by
    rw [bondM, ← sc]
    refine le_trans hcb ?_
    have := mul_le_mul nc nc h0c (by positivity)
    nlinarith
  have hYn : frobNorm Y ≤ 2 * ((ell : ℝ) * k) := by
    have t := AdalyFormal.Balaban.Bch2.frobNorm_add_le (Y - bondM s ell A c) (bondM s ell A c)
    rw [sub_add_cancel] at t
    have hb : frobNorm (bondM s ell A c) ≤ (ell : ℝ) * k := by
      rw [bondM, ← sc]; exact le_trans (frob_sum_le _) nc
    have : 2 * Real.pi * ((ell : ℝ) * k) ^ 2 ≤ (ell : ℝ) * k := by
      have h1 : 2 * Real.pi * ((ell : ℝ) * k) ≤ 1 := by nlinarith
      nlinarith [mul_nonneg (by positivity : (0:ℝ) ≤ (ell : ℝ) * k) (by linarith : (0:ℝ) ≤ 1 - 2 * Real.pi * ((ell : ℝ) * k))]
    linarith
  -- assemble: Ū = exp H · exp Y
  have hshape : ubarSU2 s ell W c = su2Exp H * su2Exp Y := by
    rw [ubarSU2_eq_blockedLink]
    show su2Exp H * coarseBondVar s ell W c = _
    congr 1
    show coarsePathHolonomy s W c.1 (List.replicate ell c.2) = _
    rw [pc, hce]
  have hdom : frobNorm H + frobNorm Y ≤ 2 := by nlinarith
  have hbch := AdalyFormal.Balaban.Bch2.bch2_frobNorm hHsu hYsu hdom
  have hnu : AdalyFormal.Balaban.Bch2.nu H + AdalyFormal.Balaban.Bch2.nu Y ≤ Real.pi / 2 := by
    have := nu_le_frob H; have := nu_le_frob Y; nlinarith
  have hne := AdalyFormal.Balaban.Bch2.ne_negOne_of_angle_le
    (AdalyFormal.Balaban.Bch2.angle_prod_le hHsu hYsu hnu)
  refine ⟨?_, ?_⟩
  · rw [hshape]; exact AdalyFormal.Balaban.RegularityGap.su2_exp_log_of_ne_negOne _ hne
  · rw [hshape]
    have e : su2Log (su2Exp H * su2Exp Y) - blkM s ell A c
        = (su2Log (su2Exp H * su2Exp Y) - (H + Y)) + (H - Lm) + (Y - bondM s ell A c) := by
      simp only [blkM, Lm]; abel
    rw [e]
    have t1 := AdalyFormal.Balaban.Bch2.frobNorm_add_le
      (su2Log (su2Exp H * su2Exp Y) - (H + Y) + (H - Lm)) (Y - bondM s ell A c)
    have t2 := AdalyFormal.Balaban.Bch2.frobNorm_add_le
      (su2Log (su2Exp H * su2Exp Y) - (H + Y)) (H - Lm)
    have hHY : frobNorm H * frobNorm Y ≤ (2 * κ) * (2 * ((ell : ℝ) * k)) :=
      mul_le_mul hHn hYn (frobNorm_nonneg _) (by positivity)
    have hκe : κ = 8 * ((ell : ℝ) * k) := by simp only [κ]; ring
    rw [hκe] at hHY hHL
    have e2 : 2 * Real.pi * ((2 * (8 * ((ell : ℝ) * k))) * (2 * ((ell : ℝ) * k)))
        + 2 * Real.pi * (8 * ((ell : ℝ) * k)) ^ 2 + 2 * Real.pi * ((ell : ℝ) * k) ^ 2
        = 194 * Real.pi * ((ell : ℝ) ^ 2 * k ^ 2) := by ring
    have hbch' : 2 * Real.pi * (frobNorm H * frobNorm Y)
        ≤ 2 * Real.pi * ((2 * (8 * ((ell : ℝ) * k))) * (2 * ((ell : ℝ) * k))) :=
      mul_le_mul_of_nonneg_left hHY (by positivity)
    have hpos : 0 ≤ Real.pi * ((ell : ℝ) ^ 2 * k ^ 2) := by positivity
    linarith

end AdalyFormal.CurvBlock

#print axioms AdalyFormal.CurvBlock.log_ubar_lin
