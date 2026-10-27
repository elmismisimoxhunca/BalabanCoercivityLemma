import CB8
/-!
# NB1 -- multi-factor BCH on `𝔰𝔲(2)` (piece N1 of the nonabelian Prop. 1 route)

For `a₁,…,aₙ ∈ 𝔰𝔲(2)` with `S = Σ‖aᵢ‖_F ≤ 1/(2π)`, the product `g = exp a₁ ⋯ exp aₙ` satisfies
`exp (log g) = g` and `‖log g − Σ aᵢ‖_F ≤ 2π S²` (`multi_bch`), by induction from the tree's
two-factor `Bch2.bch2_frobNorm` (`‖log(e^A e^B) − (A+B)‖ ≤ 2π‖A‖‖B‖` on `‖A‖+‖B‖ ≤ 2`).

No sorry / native_decide / axioms.
-/
set_option autoImplicit false
noncomputable section
namespace AdalyFormal.CurvBlock
open AdalyFormal.Balaban.SuTwoLogExp (SU2 M2 su2Log su2Exp)
open AdalyFormal.Balaban.RMapLipschitz (frobNorm frobNorm_nonneg)
open AdalyFormal.Balaban.Bch2 (IsSu2)

theorem nu_le_frob (X : M2) : AdalyFormal.Balaban.Bch2.nu X ≤ frobNorm X := by
  have e := AdalyFormal.Balaban.Bch2.frobNorm_eq_sqrt_two_mul_nu X
  have h1 : (1 : ℝ) ≤ Real.sqrt 2 := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]; exact Real.sqrt_le_sqrt (by norm_num)
  nlinarith [AdalyFormal.Balaban.Bch2.nu_nonneg X]

theorem frob_sum_le : ∀ l : List M2, frobNorm l.sum ≤ (l.map frobNorm).sum := by
  intro l
  induction l with
  | nil => simp
  | cons b r ihl =>
      simp only [List.sum_cons, List.map_cons]
      exact le_trans (AdalyFormal.Balaban.Bch2.frobNorm_add_le _ _) (by linarith)

/-- **Multi-factor BCH.** -/
theorem multi_bch : ∀ (as : List M2), (∀ a ∈ as, IsSu2 a) →
    (as.map frobNorm).sum ≤ 1 / (2 * Real.pi) →
    su2Exp (su2Log ((as.map su2Exp).prod)) = (as.map su2Exp).prod ∧
    frobNorm (su2Log ((as.map su2Exp).prod) - as.sum)
      ≤ 2 * Real.pi * ((as.map frobNorm).sum) ^ 2 := by
  intro as
  induction as with
  | nil =>
      intro _ _
      simp
  | cons a rest ih =>
      intro hsu hS
      have ha : IsSu2 a := hsu a (List.mem_cons_self ..)
      have hrest : ∀ b ∈ rest, IsSu2 b := fun b hb => hsu b (List.mem_cons_of_mem _ hb)
      have hpi := Real.pi_gt_three
      simp only [List.map_cons, List.sum_cons] at hS
      set S' := (rest.map frobNorm).sum
      have hS' : 0 ≤ S' := List.sum_nonneg (fun x hx => by
        obtain ⟨b, _, rfl⟩ := List.mem_map.mp hx; exact frobNorm_nonneg b)
      have hna := frobNorm_nonneg a
      have hS'1 : S' ≤ 1 / (2 * Real.pi) := by linarith
      obtain ⟨hexp, hbd⟩ := ih hrest hS'1
      set g' := (rest.map su2Exp).prod
      set X := su2Log g'
      have hX : IsSu2 X := AdalyFormal.Balaban.Bch2.isSu2_su2Log g'
      have h2pS : 2 * Real.pi * S' ≤ 1 := by
        rw [le_div_iff₀ (by positivity)] at hS'1; linarith
      have hXn : frobNorm X ≤ 2 * S' := by
        have t := AdalyFormal.Balaban.Bch2.frobNorm_add_le (X - rest.sum) rest.sum
        rw [sub_add_cancel] at t
        have hsum : frobNorm rest.sum ≤ S' := frob_sum_le rest
        nlinarith
      have h1 : frobNorm a + S' ≤ 1 / 6 := le_trans hS (by
        rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith)
      have hdom : frobNorm a + frobNorm X ≤ 2 := by linarith
      have hb := AdalyFormal.Balaban.Bch2.bch2_frobNorm ha hX hdom
      have hprod : ((a :: rest).map su2Exp).prod = su2Exp a * su2Exp X := by
        simp only [List.map_cons, List.prod_cons]; rw [hexp]
      have hnu : AdalyFormal.Balaban.Bch2.nu a + AdalyFormal.Balaban.Bch2.nu X ≤ Real.pi / 2 := by
        have := nu_le_frob a; have := nu_le_frob X; linarith
      have hne := AdalyFormal.Balaban.Bch2.ne_negOne_of_angle_le
        (AdalyFormal.Balaban.Bch2.angle_prod_le ha hX hnu)
      refine ⟨?_, ?_⟩
      · rw [hprod]; exact AdalyFormal.Balaban.RegularityGap.su2_exp_log_of_ne_negOne _ hne
      · rw [hprod, List.sum_cons]
        simp only [List.map_cons, List.sum_cons]
        have t := AdalyFormal.Balaban.Bch2.frobNorm_add_le
          (su2Log (su2Exp a * su2Exp X) - (a + X)) (X - rest.sum)
        have he : su2Log (su2Exp a * su2Exp X) - (a + X) + (X - rest.sum)
            = su2Log (su2Exp a * su2Exp X) - (a + rest.sum) := by abel
        rw [he] at t
        have hm : frobNorm a * frobNorm X ≤ frobNorm a * (2 * S') :=
          mul_le_mul_of_nonneg_left hXn hna
        have hm' : 2 * Real.pi * (frobNorm a * frobNorm X) ≤ 2 * Real.pi * (frobNorm a * (2 * S')) :=
          mul_le_mul_of_nonneg_left hm (by positivity)
        have hq : 2 * Real.pi * (frobNorm a * (2 * S')) + 2 * Real.pi * S' ^ 2
            ≤ 2 * Real.pi * (frobNorm a + S') ^ 2 := by
          have e : 2 * Real.pi * (frobNorm a + S') ^ 2
              - (2 * Real.pi * (frobNorm a * (2 * S')) + 2 * Real.pi * S' ^ 2)
              = 2 * Real.pi * frobNorm a ^ 2 := by ring
          have : 0 ≤ 2 * Real.pi * frobNorm a ^ 2 := by positivity
          linarith
        linarith

end AdalyFormal.CurvBlock

#print axioms AdalyFormal.CurvBlock.multi_bch
