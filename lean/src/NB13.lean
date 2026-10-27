import NB12
/-!
# NB13 -- corner-gauge chart (piece N2, part 3)

* `pw_cgauge` / `dv_pw_cgauge`: stride-`m` plaquette words are conjugated by `γ(y)` under the
  stride-`m` gauge transformation; defects are invariant.
* `chart_small`: `dv g ≤ 1` ⟹ `exp (log g) = g`, `log g ∈ 𝔰𝔲(2)`, `‖log g‖ ≤ 2 dv g`.
* `axial_link`: in the corner gauge `W = coarseGaugeTransform s (cornerGauge s V y) V`,
  `dv (W (x, ρ)) ≤ (off₀(x)/s + off₁(x)/s) · P` (hypotheses as in NB11).

No sorry / native_decide / axioms.
-/
set_option autoImplicit false
noncomputable section
namespace AdalyFormal.CurvBlock
open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.SuTwoLogExp (SU2 M2 su2Log su2Exp)
open AdalyFormal.Balaban.RMapLipschitz (frobNorm)
open AdalyFormal.Balaban.CoarseCurl (coarseShift)
open AdalyFormal.Balaban.QjComposite (coarseGaugeTransform)
open AdalyFormal.Balaban.AdmissibleSubspace (CoarseLattice)
open AdalyFormal.Balaban.Bch2 (IsSu2)

variable {L : PeriodicLatticeExtent}

theorem pw_cgauge (m : ℕ) (γ : PeriodicLatticeSite L → SU2) (U : PeriodicLinkConfiguration SU2 L)
    (y : PeriodicLatticeSite L) (ν μ : Fin 3) :
    pw m (coarseGaugeTransform m γ U) y ν μ = γ y * pw m U y ν μ * (γ y)⁻¹ := by
  have hc := AdalyFormal.Balaban.U1AnchorPoincare.coarseShift_comm_gen y m m ν μ
  unfold pw coarseGaugeTransform
  show γ y * U (y, ν) * (γ (coarseShift y m ν))⁻¹
      * (γ (coarseShift y m ν) * U (coarseShift y m ν, μ) * (γ (coarseShift (coarseShift y m ν) m μ))⁻¹)
      * (γ (coarseShift y m μ) * U (coarseShift y m μ, ν) * (γ (coarseShift (coarseShift y m μ) m ν))⁻¹)⁻¹
      * (γ y * U (y, μ) * (γ (coarseShift y m μ))⁻¹)⁻¹ = _
  rw [hc]
  group

theorem dv_pw_cgauge (m : ℕ) (γ : PeriodicLatticeSite L → SU2) (U : PeriodicLinkConfiguration SU2 L)
    (y : PeriodicLatticeSite L) (ν μ : Fin 3) :
    dv (pw m (coarseGaugeTransform m γ U) y ν μ) = dv (pw m U y ν μ) := by
  rw [pw_cgauge, dv_conj]

theorem chart_small (g : SU2) (h : dv g ≤ 1) :
    su2Exp (su2Log g) = g ∧ IsSu2 (su2Log g) ∧ frobNorm (su2Log g) ≤ 2 * dv g := by
  have hne : g ≠ AdalyFormal.Balaban.SuTwoLogExp.su2NegOne := by
    intro hg
    rw [hg] at h
    have e : dv AdalyFormal.Balaban.SuTwoLogExp.su2NegOne = 2 * Real.sqrt 2 :=
      AdalyFormal.Balaban.AlphaAnalyticity.frobNorm_negOne_sub_one
    rw [e] at h
    have : (1 : ℝ) < Real.sqrt 2 := by
      rw [show (1 : ℝ) = Real.sqrt 1 by simp]; exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
    linarith
  refine ⟨AdalyFormal.Balaban.RegularityGap.su2_exp_log_of_ne_negOne g hne,
    AdalyFormal.Balaban.Bch2.isSu2_su2Log g, ?_⟩
  have hl := log_le_dv g h
  have h0 := dv_nonneg g
  have : dv g ^ 3 / 8 ≤ dv g := by
    have h2 : dv g ^ 2 ≤ 1 := by nlinarith
    nlinarith
  linarith

theorem axial_link (s : ℕ) (hs : 0 < s) (V : PeriodicLinkConfiguration SU2 L)
    (y : PeriodicLatticeSite L) (hy : y ∈ CoarseLattice L s) (hdvd : ∀ ρ, s ∣ L ρ + 1)
    (P : ℝ) (hP : ∀ z ∈ CoarseLattice L s, ∀ ν μ : Fin 3, dv (pw s V z ν μ) ≤ P)
    (x : PeriodicLatticeSite L) (ρ : Fin 3) (hal : ∀ σ, s ∣ off y x σ)
    (hnw : off y x ρ + s < L ρ + 1) :
    dv (coarseGaugeTransform s (cornerGauge s V y) V (x, ρ))
      ≤ (((off y x 0 / s : ℕ) : ℝ) + ((off y x 1 / s : ℕ) : ℝ)) * P := by
  have hP0 : 0 ≤ P := le_trans (dv_nonneg _) (hP y hy 0 0)
  have ha0 : (0 : ℝ) ≤ ((off y x 0 / s : ℕ) : ℝ) := Nat.cast_nonneg _
  have ha1 : (0 : ℝ) ≤ ((off y x 1 / s : ℕ) : ℝ) := Nat.cast_nonneg _
  show dv (cornerGauge s V y x * V (x, ρ) * (cornerGauge s V y (coarseShift x s ρ))⁻¹) ≤ _
  have hz : coarseShift y (s * (off y x 2 / s)) 2 ∈ CoarseLattice L s :=
    shift_mul_aligned s hdvd 2 _ y hy
  have hz1 : coarseShift (coarseShift y (s * (off y x 2 / s)) 2) (s * (off y x 1 / s)) 1
      ∈ CoarseLattice L s := shift_mul_aligned s hdvd 1 _ _ hz
  fin_cases ρ
  · show dv (cornerGauge s V y x * V (x, 0) * (cornerGauge s V y (coarseShift x s 0))⁻¹) ≤ _
    rw [axial0 s hs V y x hal hnw, dv_one]; positivity
  · show dv (cornerGauge s V y x * V (x, 1) * (cornerGauge s V y (coarseShift x s 1))⁻¹) ≤ _
    obtain ⟨g, hg⟩ := axial1 s hs V y x hal hnw
    rw [hg, dv_conj]
    have hl := ladS_le s V 1 1 P (List.replicate (off y x 0 / s) 0) _
      (fun t ht => hP t.1 (ladPlaqs_aligned s hdvd 1 1 _ _ hz1 t ht) t.2.1 t.2.2)
    rw [List.length_replicate] at hl
    push_cast at hl ⊢
    nlinarith
  · show dv (cornerGauge s V y x * V (x, 2) * (cornerGauge s V y (coarseShift x s 2))⁻¹) ≤ _
    obtain ⟨g, hg⟩ := axial2 s hs V y x hal hnw
    rw [hg, dv_conj]
    have hl := ladS_le s V 2 1 P
      (List.replicate (off y x 1 / s) 1 ++ List.replicate (off y x 0 / s) 0) _
      (fun t ht => hP t.1 (ladPlaqs_aligned s hdvd 2 1 _ _ hz t ht) t.2.1 t.2.2)
    rw [List.length_append, List.length_replicate, List.length_replicate] at hl
    push_cast at hl ⊢
    nlinarith

end AdalyFormal.CurvBlock

#print axioms AdalyFormal.CurvBlock.dv_pw_cgauge
#print axioms AdalyFormal.CurvBlock.chart_small
#print axioms AdalyFormal.CurvBlock.axial_link
