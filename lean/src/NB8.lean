import NB7
/-!
# NB8 -- plaquette linearisation at stride `s` and a norm bound for `blkM` (pieces of N4b)

* `curlM_le_plaq`: if the four bonds of the stride-`s` plaquette word `t` are chart bonds with bound `k`
  (`4k ≤ 1/(2π)`) and `dv (pw s W t) ≤ P ≤ 1`, then `‖curlM s A t‖_F ≤ P + P³/8 + 32π k²`.
* `blkM_norm`: chart bonds on the blocking of `c` give `‖blkM s ell A c‖_F ≤ 9 ell k`.

No sorry / native_decide / axioms.
-/
set_option autoImplicit false
noncomputable section
namespace AdalyFormal.CurvBlock
open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.SuTwoLogExp (SU2 M2 su2Log su2Exp)
open AdalyFormal.Balaban.RMapLipschitz (frobNorm frobNorm_nonneg)
open AdalyFormal.Balaban.CoarseCurl (coarseShift)
open AdalyFormal.Balaban.TowerLawCov (coarseGammaPath)
open AdalyFormal.Balaban.QjComposite (stepBlockOf)
open AdalyFormal.Balaban.Bch2 (IsSu2)

variable {L : PeriodicLatticeExtent}

theorem four_list (a b c e : M2) (ha : IsSu2 a) (hb : IsSu2 b) (hc : IsSu2 c) (he : IsSu2 e) :
    (([a, b, -c, -e] : List M2).map su2Exp).prod
      = su2Exp a * su2Exp b * (su2Exp c)⁻¹ * (su2Exp e)⁻¹ := by
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one,
    su2Exp_neg_eq_inv hc, su2Exp_neg_eq_inv he]
  group

theorem curlM_le_plaq (s : ℕ) (W : PeriodicLinkConfiguration SU2 L) (A : PeriodicLatticeEdge L → M2)
    (k P : ℝ) (hk : 0 ≤ k) (hk4 : 4 * k ≤ 1 / (2 * Real.pi)) (hP : P ≤ 1)
    (y : PeriodicLatticeSite L) (ν μ : Fin 3)
    (h1 : Chart W A k (y, ν)) (h2 : Chart W A k (coarseShift y s ν, μ))
    (h3 : Chart W A k (coarseShift y s μ, ν)) (h4 : Chart W A k (y, μ))
    (hpw : dv (pw s W y ν μ) ≤ P) :
    frobNorm (curlM s A y ν μ) ≤ P + P ^ 3 / 8 + 32 * Real.pi * k ^ 2 := by
  set l : List M2 := [A (y, ν), A (coarseShift y s ν, μ), -A (coarseShift y s μ, ν), -A (y, μ)]
  have hsu : ∀ a ∈ l, IsSu2 a := by
    intro a ha
    simp only [l, List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl
    · exact h1.2.1
    · exact h2.2.1
    · exact h3.2.1.neg
    · exact h4.2.1.neg
  have hn : (l.map frobNorm).sum ≤ 4 * k := by
    simp only [l, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      AdalyFormal.Balaban.RegularityGap.frobNorm_neg]
    linarith [h1.2.2, h2.2.2, h3.2.2, h4.2.2]
  have h0 : 0 ≤ (l.map frobNorm).sum := le_trans (frobNorm_nonneg _) (frob_sum_le _)
  obtain ⟨-, hb⟩ := multi_bch l hsu (le_trans hn hk4)
  have hprod : (l.map su2Exp).prod = pw s W y ν μ := by
    rw [four_list _ _ _ _ h1.2.1 h2.2.1 h3.2.1 h4.2.1]
    unfold pw; rw [h1.1, h2.1, h3.1, h4.1]
  have hsum : l.sum = curlM s A y ν μ := by
    simp only [l, List.sum_cons, List.sum_nil, curlM]; abel
  rw [hprod, hsum] at hb
  have hlog := log_le_dv (pw s W y ν μ) (le_trans hpw hP)
  have hdv0 := dv_nonneg (pw s W y ν μ)
  have hmono : dv (pw s W y ν μ) + dv (pw s W y ν μ) ^ 3 / 8 ≤ P + P ^ 3 / 8 := by
    have := pow_le_pow_left₀ hdv0 hpw 3
    linarith
  have t := AdalyFormal.Balaban.Bch2.frobNorm_add_le
    (curlM s A y ν μ - su2Log (pw s W y ν μ)) (su2Log (pw s W y ν μ))
  rw [sub_add_cancel] at t
  have hs : frobNorm (curlM s A y ν μ - su2Log (pw s W y ν μ))
      = frobNorm (su2Log (pw s W y ν μ) - curlM s A y ν μ) := by
    rw [← neg_sub, AdalyFormal.Balaban.RegularityGap.frobNorm_neg]
  have hsq : 2 * Real.pi * (l.map frobNorm).sum ^ 2 ≤ 32 * Real.pi * k ^ 2 := by
    have := mul_le_mul hn hn h0 (by positivity)
    nlinarith [Real.pi_pos]
  linarith

theorem blkM_norm (s ell : ℕ) (hs : 0 < s) (hell : 0 < ell) (W : PeriodicLinkConfiguration SU2 L)
    (A : PeriodicLatticeEdge L → M2) (k : ℝ) (hk : 0 ≤ k) (c : PeriodicLatticeEdge L)
    (h : ∀ x ∈ stepBlockOf c.1 s ell, ∀ b ∈ loopBonds s ell c x, Chart W A k b)
    (hc : ∀ b ∈ pathBonds s c.1 (List.replicate ell c.2), Chart W A k b) :
    frobNorm (blkM s ell A c) ≤ 9 * ell * k := by
  have hwsum := AdalyFormal.Balaban.ClassPropagationUbar.weight_sum_le_one c.1 hs hell
  have hloop : ∀ x ∈ stepBlockOf c.1 s ell, frobNorm (loopM s ell A c x) ≤ 8 * ell * k := by
    intro x hx
    obtain ⟨-, hsum, -, hn⟩ := loopList_facts s ell hs W A k hk c x hx (h x hx)
    rw [← hsum]; exact le_trans (frob_sum_le _) hn
  obtain ⟨-, -, sc, -, -, -, nc, -⟩ := pl_facts s W A k _ _ hc
  rw [List.length_replicate] at nc
  have hb : frobNorm (bondM s ell A c) ≤ ell * k := by
    rw [bondM, ← sc]; exact le_trans (frob_sum_le _) nc
  have hsumb : frobNorm (∑ x ∈ stepBlockOf c.1 s ell, ((ell : ℝ) ^ 3)⁻¹ • loopM s ell A c x)
      ≤ 8 * ell * k := by
    refine le_trans (AdalyFormal.Balaban.BlockingLinkEstimate.frobNorm_sum_le _ _) ?_
    calc ∑ x ∈ stepBlockOf c.1 s ell, frobNorm (((ell : ℝ) ^ 3)⁻¹ • loopM s ell A c x)
        ≤ ∑ x ∈ stepBlockOf c.1 s ell, ((ell : ℝ) ^ 3)⁻¹ * (8 * ell * k) := by
          refine Finset.sum_le_sum (fun x hx => ?_)
          rw [AdalyFormal.Balaban.Bch2.frobNorm_smul, abs_of_nonneg (by positivity)]
          exact mul_le_mul_of_nonneg_left (hloop x hx) (by positivity)
      _ = (∑ x ∈ stepBlockOf c.1 s ell, ((ell : ℝ) ^ 3)⁻¹) * (8 * ell * k) := by
          rw [Finset.sum_mul]
      _ ≤ 1 * (8 * ell * k) := mul_le_mul_of_nonneg_right hwsum (by positivity)
      _ = 8 * ell * k := one_mul _
  have := AdalyFormal.Balaban.Bch2.frobNorm_add_le
    (∑ x ∈ stepBlockOf c.1 s ell, ((ell : ℝ) ^ 3)⁻¹ • loopM s ell A c x) (bondM s ell A c)
  unfold blkM
  linarith

end AdalyFormal.CurvBlock

#print axioms AdalyFormal.CurvBlock.curlM_le_plaq
#print axioms AdalyFormal.CurvBlock.blkM_norm
