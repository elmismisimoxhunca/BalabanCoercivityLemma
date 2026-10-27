import CB6
import AdalyFormal.Balaban.Bch2
/-!
# CB8 -- fine plaquette defect from the (3.35) chart (first + second clause), any cube gauge

* `pw_gauge` / `dv_pw_gauge`: the stride-1 plaquette word is gauge covariant, its defect gauge invariant.
* `dv_exp_div_le`: for `X, Y ∈ 𝔰𝔲(2)` with `‖X‖ + ‖Y‖ ≤ 2`:
  `dv (exp X · (exp Y)⁻¹) ≤ ‖X − Y‖ + 2π‖X‖‖Y‖` (tree's `Bch2.bch2_frobNorm`).
* `dv_comm_le`: `dv (c e c⁻¹ e⁻¹) ≤ 2 dv(c) dv(e)`.
* `dv_pw_of_chart`: if the four links of a plaquette are `exp X_b` with `‖X_b‖ ≤ ε₁ ≤ 1` and the two
  parallel differences are `≤ ε₂`, then `dv (pw 1 V y ν μ) ≤ 2 ε₂ + (4π + 2) ε₁²`.

No sorry / native_decide / axioms.
-/
set_option autoImplicit false
noncomputable section
namespace AdalyFormal.CurvBlock
open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.SuTwoLogExp (SU2 M2 su2Log su2Exp)
open AdalyFormal.Balaban.RMapLipschitz (frobNorm frobSq frobSq_nonneg frobNorm_nonneg)
open AdalyFormal.Balaban.CoarseCurl (coarseShift)
open AdalyFormal.Balaban.Bch2 (IsSu2)
open scoped Matrix

variable {L : PeriodicLatticeExtent}

theorem pw_gauge (γ : PeriodicLatticeSite L → SU2) (U : PeriodicLinkConfiguration SU2 L)
    (y : PeriodicLatticeSite L) (ν μ : Fin 3) :
    pw 1 (periodicGaugeTransform γ U) y ν μ = γ y * pw 1 U y ν μ * (γ y)⁻¹ := by
  have hc := AdalyFormal.Balaban.U1AnchorPoincare.coarseShift_comm_gen y 1 1 ν μ
  unfold pw periodicGaugeTransform
  show γ y * U (y, ν) * (γ (coarseShift y 1 ν))⁻¹
      * (γ (coarseShift y 1 ν) * U (coarseShift y 1 ν, μ) * (γ (coarseShift (coarseShift y 1 ν) 1 μ))⁻¹)
      * (γ (coarseShift y 1 μ) * U (coarseShift y 1 μ, ν) * (γ (coarseShift (coarseShift y 1 μ) 1 ν))⁻¹)⁻¹
      * (γ y * U (y, μ) * (γ (coarseShift y 1 μ))⁻¹)⁻¹ = _
  rw [hc]
  group

theorem dv_pw_gauge (γ : PeriodicLatticeSite L → SU2) (U : PeriodicLinkConfiguration SU2 L)
    (y : PeriodicLatticeSite L) (ν μ : Fin 3) :
    dv (pw 1 (periodicGaugeTransform γ U) y ν μ) = dv (pw 1 U y ν μ) := by
  rw [pw_gauge, dv_conj]

theorem su2Exp_neg_eq_inv {Y : M2} (hY : IsSu2 Y) : su2Exp (-Y) = (su2Exp Y)⁻¹ := by
  symm
  refine inv_eq_of_mul_eq_one_right ?_
  apply Subtype.ext
  rw [AdalyFormal.Balaban.SuTwoLogExp.coe_mul, AdalyFormal.Balaban.Bch2.exp_mul_exp_neg hY]
  rfl

theorem dv_exp_le {X : M2} (hX : IsSu2 X) : dv (su2Exp X) ≤ frobNorm X :=
  AdalyFormal.Balaban.ClassPropagationUbar.frobNorm_su2Exp_sub_one_le_uncond hX.1 hX.2

/-- **First difference of `exp` on `𝔰𝔲(2)`.** -/
theorem dv_exp_div_le {X Y : M2} (hX : IsSu2 X) (hY : IsSu2 Y)
    (hd : frobNorm X + frobNorm Y ≤ 2) :
    dv (su2Exp X * (su2Exp Y)⁻¹) ≤ frobNorm (X - Y) + 2 * Real.pi * (frobNorm X * frobNorm Y) := by
  have hYn : IsSu2 (-Y) := hY.neg
  have hfn : frobNorm (-Y) = frobNorm Y := by
    unfold frobNorm frobSq; simp [Complex.normSq_neg]
  rw [← su2Exp_neg_eq_inv hY]
  set g := su2Exp X * su2Exp (-Y)
  have hb := AdalyFormal.Balaban.Bch2.bch2_frobNorm hX hYn (by rw [hfn]; exact hd)
  rw [hfn] at hb
  -- g is not the antipode
  have hnu : AdalyFormal.Balaban.Bch2.nu X + AdalyFormal.Balaban.Bch2.nu (-Y) ≤ Real.pi / 2 := by
    have e1 := AdalyFormal.Balaban.Bch2.frobNorm_eq_sqrt_two_mul_nu X
    have e2 := AdalyFormal.Balaban.Bch2.frobNorm_eq_sqrt_two_mul_nu (-Y)
    have h2 : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
    have hss : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
    have hp := AdalyFormal.Balaban.Bch2.sqrt_two_le_pi_div_two
    rw [hfn] at e2
    have hsum : Real.sqrt 2 * (AdalyFormal.Balaban.Bch2.nu X + AdalyFormal.Balaban.Bch2.nu (-Y)) ≤ 2 := by
      linarith
    nlinarith [AdalyFormal.Balaban.Bch2.nu_nonneg X, AdalyFormal.Balaban.Bch2.nu_nonneg (-Y)]
  have hang := AdalyFormal.Balaban.Bch2.angle_prod_le hX hYn hnu
  have hne := AdalyFormal.Balaban.Bch2.ne_negOne_of_angle_le hang
  have hge : su2Exp (su2Log g) = g :=
    AdalyFormal.Balaban.RegularityGap.su2_exp_log_of_ne_negOne g hne
  have hL := AdalyFormal.Balaban.Bch2.isSu2_su2Log g
  have h1 : dv g ≤ frobNorm (su2Log g) := by
    have := dv_exp_le hL; rwa [hge] at this
  have htri : frobNorm (su2Log g) ≤ frobNorm (X - Y) + frobNorm (su2Log g - (X + -Y)) := by
    have := AdalyFormal.Balaban.Bch2.frobNorm_add_le (X - Y) (su2Log g - (X + -Y))
    have he : X - Y + (su2Log g - (X + -Y)) = su2Log g := by abel
    rwa [he] at this
  linarith

theorem frobNorm_mul_le' (A B : M2) : frobNorm (A * B) ≤ frobNorm A * frobNorm B := by
  have h := AdalyFormal.Balaban.RMapLipschitz.frobSq_mul_le A B
  unfold frobNorm
  rw [← Real.sqrt_mul (frobSq_nonneg A)]
  exact Real.sqrt_le_sqrt h

theorem su_mul_star (W : SU2) : (W : M2) * (W : M2)ᴴ = 1 := by
  have h := Matrix.mem_unitaryGroup_iff.mp (Matrix.specialUnitaryGroup_le_unitaryGroup W.2)
  simpa [Matrix.star_eq_conjTranspose] using h

/-- **Commutator bound.** -/
theorem dv_comm_le (c e : SU2) : dv (c * e * c⁻¹ * e⁻¹) ≤ 2 * (dv c * dv e) := by
  have hW : ((c⁻¹ * e⁻¹ : SU2) : M2) * ((c⁻¹ * e⁻¹ : SU2) : M2)ᴴ = 1 := su_mul_star (c⁻¹ * e⁻¹)
  have hEC : (e : M2) * (c : M2) * ((c⁻¹ * e⁻¹ : SU2) : M2) = 1 := by
    rw [← AdalyFormal.Balaban.SuTwoLogExp.coe_mul, ← AdalyFormal.Balaban.SuTwoLogExp.coe_mul,
      show e * c * (c⁻¹ * e⁻¹) = 1 by group]
    rfl
  have hcoe : ((c * e * c⁻¹ * e⁻¹ : SU2) : M2) = (c : M2) * (e : M2) * ((c⁻¹ * e⁻¹ : SU2) : M2) := by
    rw [show c * e * c⁻¹ * e⁻¹ = (c * e) * (c⁻¹ * e⁻¹) by group]
    rfl
  have hkey : ((c * e * c⁻¹ * e⁻¹ : SU2) : M2) - 1
      = (((c : M2) - 1) * ((e : M2) - 1) - ((e : M2) - 1) * ((c : M2) - 1))
          * ((c⁻¹ * e⁻¹ : SU2) : M2) := by
    rw [hcoe]
    have : (((c : M2) - 1) * ((e : M2) - 1) - ((e : M2) - 1) * ((c : M2) - 1))
          * ((c⁻¹ * e⁻¹ : SU2) : M2)
        = (c : M2) * (e : M2) * ((c⁻¹ * e⁻¹ : SU2) : M2)
          - (e : M2) * (c : M2) * ((c⁻¹ * e⁻¹ : SU2) : M2) := by noncomm_ring
    rw [this, hEC]
  unfold dv
  rw [hkey]
  have hiso : frobNorm ((((c : M2) - 1) * ((e : M2) - 1) - ((e : M2) - 1) * ((c : M2) - 1))
          * ((c⁻¹ * e⁻¹ : SU2) : M2))
      = frobNorm (((c : M2) - 1) * ((e : M2) - 1) - ((e : M2) - 1) * ((c : M2) - 1)) := by
    unfold frobNorm
    rw [AdalyFormal.Balaban.RMapLipschitz.frobSq_mul_right_isometry _ _ hW]
  rw [hiso]
  have hs := AdalyFormal.Balaban.RegularityGap.frobNorm_sub_le (((c : M2) - 1) * ((e : M2) - 1))
    (((e : M2) - 1) * ((c : M2) - 1))
  have m1 := frobNorm_mul_le' ((c : M2) - 1) ((e : M2) - 1)
  have m2 := frobNorm_mul_le' ((e : M2) - 1) ((c : M2) - 1)
  nlinarith [m1, m2, hs]

/-- **Fine plaquette defect from the chart.** -/
theorem dv_pw_of_chart (V : PeriodicLinkConfiguration SU2 L) (y : PeriodicLatticeSite L)
    (ν μ : Fin 3) (Xa Xb Xc Xe : M2) (ε1 ε2 : ℝ)
    (ha : IsSu2 Xa) (hb : IsSu2 Xb) (hc : IsSu2 Xc) (he : IsSu2 Xe)
    (va : V (y, ν) = su2Exp Xa) (vb : V (coarseShift y 1 ν, μ) = su2Exp Xb)
    (vc : V (coarseShift y 1 μ, ν) = su2Exp Xc) (ve : V (y, μ) = su2Exp Xe)
    (na : frobNorm Xa ≤ ε1) (nb : frobNorm Xb ≤ ε1) (nc : frobNorm Xc ≤ ε1) (ne : frobNorm Xe ≤ ε1)
    (h1 : ε1 ≤ 1) (dac : frobNorm (Xa - Xc) ≤ ε2) (dbe : frobNorm (Xb - Xe) ≤ ε2) :
    dv (pw 1 V y ν μ) ≤ 2 * ε2 + (4 * Real.pi + 2) * ε1 ^ 2 := by
  have hpi := Real.pi_pos
  have n0a := frobNorm_nonneg Xa
  have n0b := frobNorm_nonneg Xb
  have n0c := frobNorm_nonneg Xc
  have n0e := frobNorm_nonneg Xe
  set a := su2Exp Xa
  set b := su2Exp Xb
  set c := su2Exp Xc
  set e := su2Exp Xe
  have hid : pw 1 V y ν μ = (a * c⁻¹) * (c * (b * e⁻¹) * c⁻¹) * (c * e * c⁻¹ * e⁻¹) := by
    unfold pw; rw [va, vb, vc, ve]; group
  rw [hid]
  have t1 := dv_mul ((a * c⁻¹) * (c * (b * e⁻¹) * c⁻¹)) (c * e * c⁻¹ * e⁻¹)
  have t2 := dv_mul (a * c⁻¹) (c * (b * e⁻¹) * c⁻¹)
  rw [dv_conj] at t2
  have kac := dv_exp_div_le ha hc (by linarith)
  have kbe := dv_exp_div_le hb he (by linarith)
  have kc := dv_comm_le c e
  have ec := dv_exp_le hc
  have ee := dv_exp_le he
  have hce : dv c * dv e ≤ ε1 * ε1 :=
    mul_le_mul (le_trans ec nc) (le_trans ee ne) (dv_nonneg _) (le_trans n0c nc)
  have hac : frobNorm Xa * frobNorm Xc ≤ ε1 * ε1 := mul_le_mul na nc n0c (le_trans n0a na)
  have hbe : frobNorm Xb * frobNorm Xe ≤ ε1 * ε1 := mul_le_mul nb ne n0e (le_trans n0b nb)
  nlinarith [t1, t2, kac, kbe, kc, hce, hac, hbe]

end AdalyFormal.CurvBlock

#print axioms AdalyFormal.CurvBlock.dv_pw_gauge
#print axioms AdalyFormal.CurvBlock.dv_exp_div_le
#print axioms AdalyFormal.CurvBlock.dv_comm_le
#print axioms AdalyFormal.CurvBlock.dv_pw_of_chart
