import NB8
/-!
# NB9 -- one step of nonabelian curvature blocking in a chart (CMP98 Prop. 1 mechanism, piece N4b)

`prop1_chart`: at a coarse-aligned plaquette `(y; ν, μ)` (stride `m = s·ell`, `y ∈ CoarseLattice L m`,
`m ∣ L ρ + 1`), if every bond read by the blocking of its four coarse bonds is a chart bond
(`W b = exp (A b)`, `A b ∈ 𝔰𝔲(2)`, `‖A b‖ ≤ k`), and every stride-`s` plaquette enclosed by the
`ell × ell` ladders of the identity (48) is a chart plaquette with defect `≤ P ≤ 1`, then

  `dv (pw m (ubarSU2 s ell W) y ν μ) ≤ ell²(P + P³/8 + 32π k²) + 800π ell² k² + 2π(4R)²`,
  `R = 9 ell k + 200π ell² k²`,

under the smallness `8 ell k ≤ 1/(8π)`, `4R ≤ 1/(2π)`.  The linear term has coefficient exactly
`ell²`; everything else is quadratic in `(k, P)` (with `P³` cubic).

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
open AdalyFormal.Balaban.BlockedBackground (ubarSU2)
open AdalyFormal.Balaban.AdmissibleSubspace (CoarseLattice coarseLattice_mem_fits)
open AdalyFormal.Balaban.Bch2 (IsSu2)

variable {L : PeriodicLatticeExtent}

/-- All bonds read by the blocking of `c` are chart bonds. -/
def BondOK (s ell : ℕ) (W : PeriodicLinkConfiguration SU2 L) (A : PeriodicLatticeEdge L → M2)
    (k : ℝ) (c : PeriodicLatticeEdge L) : Prop :=
  (∀ x ∈ stepBlockOf c.1 s ell, ∀ b ∈ loopBonds s ell c x, Chart W A k b) ∧
    ∀ b ∈ pathBonds s c.1 (List.replicate ell c.2), Chart W A k b

/-- A chart plaquette with defect `≤ P`. -/
def PlaqOK (s : ℕ) (W : PeriodicLinkConfiguration SU2 L) (A : PeriodicLatticeEdge L → M2)
    (k P : ℝ) (t : PlaqT L) : Prop :=
  Chart W A k (t.1, t.2.1) ∧ Chart W A k (coarseShift t.1 s t.2.1, t.2.2) ∧
    Chart W A k (coarseShift t.1 s t.2.2, t.2.1) ∧ Chart W A k (t.1, t.2.2) ∧
    dv (pw s W t.1 t.2.1 t.2.2) ≤ P

theorem prop1_chart (s ell : ℕ) (hs : 0 < s) (hell : 0 < ell)
    (W : PeriodicLinkConfiguration SU2 L) (A : PeriodicLatticeEdge L → M2) (k P : ℝ)
    (hk : 0 ≤ k) (hP0 : 0 ≤ P) (hP1 : P ≤ 1)
    (hsm : 8 * (ell : ℝ) * k ≤ 1 / (8 * Real.pi))
    (hR : 4 * (9 * (ell : ℝ) * k + 200 * Real.pi * ((ell : ℝ) ^ 2 * k ^ 2)) ≤ 1 / (2 * Real.pi))
    (y : PeriodicLatticeSite L) (ν μ : Fin 3)
    (hdvd : ∀ ρ, s * ell ∣ L ρ + 1) (hy : y ∈ CoarseLattice L (s * ell))
    (h1 : BondOK s ell W A k (y, ν)) (h2 : BondOK s ell W A k (coarseShift y (s * ell) ν, μ))
    (h3 : BondOK s ell W A k (coarseShift y (s * ell) μ, ν)) (h4 : BondOK s ell W A k (y, μ))
    (hq : ∀ x ∈ stepBlockOf y s ell, ∀ t ∈ ladPlaqs s μ ell x (List.replicate ell ν),
      PlaqOK s W A k P t) :
    dv (pw (s * ell) (ubarSU2 s ell W) y ν μ)
      ≤ (ell : ℝ) ^ 2 * (P + P ^ 3 / 8 + 32 * Real.pi * k ^ 2)
        + 800 * Real.pi * ((ell : ℝ) ^ 2 * k ^ 2)
        + 2 * Real.pi * (4 * (9 * (ell : ℝ) * k + 200 * Real.pi * ((ell : ℝ) ^ 2 * k ^ 2))) ^ 2 := by
  have hpi := Real.pi_gt_three
  have hellR : (1 : ℝ) ≤ ell := by exact_mod_cast hell
  set R : ℝ := 9 * (ell : ℝ) * k + 200 * Real.pi * ((ell : ℝ) ^ 2 * k ^ 2)
  set E : ℝ := 200 * Real.pi * ((ell : ℝ) ^ 2 * k ^ 2)
  -- the four blocked links
  have link : ∀ c, BondOK s ell W A k c →
      su2Exp (su2Log (ubarSU2 s ell W c)) = ubarSU2 s ell W c ∧
      frobNorm (su2Log (ubarSU2 s ell W c) - blkM s ell A c) ≤ E ∧
      frobNorm (su2Log (ubarSU2 s ell W c)) ≤ R := by
    intro c hc
    obtain ⟨he, hb⟩ := log_ubar_lin s ell hs hell W A k hk hsm c hc.1 hc.2
    refine ⟨he, hb, ?_⟩
    have hn := blkM_norm s ell hs hell W A k hk c hc.1 hc.2
    have t := AdalyFormal.Balaban.Bch2.frobNorm_add_le
      (su2Log (ubarSU2 s ell W c) - blkM s ell A c) (blkM s ell A c)
    rw [sub_add_cancel] at t
    simp only [R]; linarith
  obtain ⟨e1, r1, n1⟩ := link _ h1
  obtain ⟨e2, r2, n2⟩ := link _ h2
  obtain ⟨e3, r3, n3⟩ := link _ h3
  obtain ⟨e4, r4, n4⟩ := link _ h4
  set U := ubarSU2 s ell W
  set X1 := su2Log (U (y, ν))
  set X2 := su2Log (U (coarseShift y (s * ell) ν, μ))
  set X3 := su2Log (U (coarseShift y (s * ell) μ, ν))
  set X4 := su2Log (U (y, μ))
  have i1 : IsSu2 X1 := AdalyFormal.Balaban.Bch2.isSu2_su2Log _
  have i2 : IsSu2 X2 := AdalyFormal.Balaban.Bch2.isSu2_su2Log _
  have i3 : IsSu2 X3 := AdalyFormal.Balaban.Bch2.isSu2_su2Log _
  have i4 : IsSu2 X4 := AdalyFormal.Balaban.Bch2.isSu2_su2Log _
  set l : List M2 := [X1, X2, -X3, -X4]
  have hsu : ∀ a ∈ l, IsSu2 a := by
    intro a ha
    simp only [l, List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl
    · exact i1
    · exact i2
    · exact i3.neg
    · exact i4.neg
  have hn : (l.map frobNorm).sum ≤ 4 * R := by
    simp only [l, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      AdalyFormal.Balaban.RegularityGap.frobNorm_neg]
    linarith
  have h0 : 0 ≤ (l.map frobNorm).sum := le_trans (frobNorm_nonneg _) (frob_sum_le _)
  obtain ⟨hpe, hpb⟩ := multi_bch l hsu (le_trans hn hR)
  have hprod : (l.map su2Exp).prod = pw (s * ell) U y ν μ := by
    rw [four_list _ _ _ _ i1 i2 i3 i4]
    unfold pw; rw [e1, e2, e3, e4]
  rw [hprod] at hpe hpb
  -- the linear part
  have hfit := coarseLattice_mem_fits hdvd hy
  have hcard := AdalyFormal.Balaban.QjComposite.card_stepBlockOf y s ell hs hfit
  have hQ : ∀ x ∈ stepBlockOf y s ell,
      frobNorm (ladAM s A x (List.replicate ell ν) μ ell)
        ≤ (ell : ℝ) * ((ell : ℝ) * (P + P ^ 3 / 8 + 32 * Real.pi * k ^ 2)) := by
    intro x hx
    have := ladAM_le s A μ ell (P + P ^ 3 / 8 + 32 * Real.pi * k ^ 2) (List.replicate ell ν) x
      (fun t ht => by
        obtain ⟨c1, c2, c3, c4, hd⟩ := hq x hx t ht
        have hk4 : 4 * k ≤ 1 / (2 * Real.pi) := by
          have : 4 * k ≤ 8 * (ell : ℝ) * k := by nlinarith
          have hb : 1 / (8 * Real.pi) ≤ 1 / (2 * Real.pi) := by
            rw [div_le_div_iff₀ (by positivity) (by positivity)]; nlinarith
          linarith
        exact curlM_le_plaq s W A k P hk hk4 hP1 t.1 t.2.1 t.2.2 c1 c2 c3 c4 hd)
    rwa [List.length_replicate] at this
  have hcurl : frobNorm (curlM (s * ell) (blkM s ell A) y ν μ)
      ≤ (ell : ℝ) ^ 2 * (P + P ^ 3 / 8 + 32 * Real.pi * k ^ 2) := by
    rw [curlM_blk_identity s ell hs hell A y ν μ hdvd hy]
    refine le_trans (AdalyFormal.Balaban.BlockingLinkEstimate.frobNorm_sum_le _ _) ?_
    calc ∑ x ∈ stepBlockOf y s ell, frobNorm (((ell : ℝ) ^ 3)⁻¹ • ladAM s A x (List.replicate ell ν) μ ell)
        ≤ ∑ x ∈ stepBlockOf y s ell, ((ell : ℝ) ^ 3)⁻¹
            * ((ell : ℝ) * ((ell : ℝ) * (P + P ^ 3 / 8 + 32 * Real.pi * k ^ 2))) := by
          refine Finset.sum_le_sum (fun x hx => ?_)
          rw [AdalyFormal.Balaban.Bch2.frobNorm_smul, abs_of_nonneg (by positivity)]
          exact mul_le_mul_of_nonneg_left (hQ x hx) (by positivity)
      _ = (ell : ℝ) ^ 2 * (P + P ^ 3 / 8 + 32 * Real.pi * k ^ 2) := by
          rw [Finset.sum_const, hcard, nsmul_eq_mul]; push_cast
          have : (0 : ℝ) < (ell : ℝ) ^ 3 := by positivity
          field_simp
  -- assemble
  have hsplit : su2Log (pw (s * ell) U y ν μ)
      = (su2Log (pw (s * ell) U y ν μ) - l.sum) + curlM (s * ell) (blkM s ell A) y ν μ
        + ((X1 - blkM s ell A (y, ν)) + (X2 - blkM s ell A (coarseShift y (s * ell) ν, μ))
          - (X3 - blkM s ell A (coarseShift y (s * ell) μ, ν)) - (X4 - blkM s ell A (y, μ))) := by
    simp only [l, List.sum_cons, List.sum_nil, curlM]; abel
  have hlog : frobNorm (su2Log (pw (s * ell) U y ν μ))
      ≤ 2 * Real.pi * (l.map frobNorm).sum ^ 2
        + (ell : ℝ) ^ 2 * (P + P ^ 3 / 8 + 32 * Real.pi * k ^ 2) + 4 * E := by
    rw [hsplit]
    have a1 := AdalyFormal.Balaban.Bch2.frobNorm_add_le
      ((su2Log (pw (s * ell) U y ν μ) - l.sum) + curlM (s * ell) (blkM s ell A) y ν μ)
      ((X1 - blkM s ell A (y, ν)) + (X2 - blkM s ell A (coarseShift y (s * ell) ν, μ))
          - (X3 - blkM s ell A (coarseShift y (s * ell) μ, ν)) - (X4 - blkM s ell A (y, μ)))
    have a2 := AdalyFormal.Balaban.Bch2.frobNorm_add_le
      (su2Log (pw (s * ell) U y ν μ) - l.sum) (curlM (s * ell) (blkM s ell A) y ν μ)
    have a3 := AdalyFormal.Balaban.RegularityGap.frobNorm_sub_le
      ((X1 - blkM s ell A (y, ν)) + (X2 - blkM s ell A (coarseShift y (s * ell) ν, μ))
          - (X3 - blkM s ell A (coarseShift y (s * ell) μ, ν))) (X4 - blkM s ell A (y, μ))
    have a4 := AdalyFormal.Balaban.RegularityGap.frobNorm_sub_le
      ((X1 - blkM s ell A (y, ν)) + (X2 - blkM s ell A (coarseShift y (s * ell) ν, μ)))
      (X3 - blkM s ell A (coarseShift y (s * ell) μ, ν))
    have a5 := AdalyFormal.Balaban.Bch2.frobNorm_add_le
      (X1 - blkM s ell A (y, ν)) (X2 - blkM s ell A (coarseShift y (s * ell) ν, μ))
    linarith
  have hdv : dv (pw (s * ell) U y ν μ) ≤ frobNorm (su2Log (pw (s * ell) U y ν μ)) := by
    have := dv_exp_le (AdalyFormal.Balaban.Bch2.isSu2_su2Log (pw (s * ell) U y ν μ))
    rwa [hpe] at this
  have hsq : 2 * Real.pi * (l.map frobNorm).sum ^ 2 ≤ 2 * Real.pi * (4 * R) ^ 2 := by
    have := mul_le_mul hn hn h0 (by positivity)
    nlinarith [Real.pi_pos]
  simp only [E] at hlog
  linarith

end AdalyFormal.CurvBlock

#print axioms AdalyFormal.CurvBlock.prop1_chart
