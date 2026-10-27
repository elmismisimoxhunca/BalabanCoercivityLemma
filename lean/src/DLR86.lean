import DLR85

/-!
# DL86 -- numerics, part 2: the `G⁻¹` error constant `EG` and the Schur error constant `EN` in the small regime

`GinvSmall I` : `GamSmall I.Gm`, `δC ≤ 7θ₀`, `κ, δK, ν, δν ≤ 10⁻¹⁰⁰`, `δB ≤ 200θ₀`, `M = 1`  (θ₀ = 10⁻⁴⁵) ⟹
  `nW ≤ 4·10¹²`, `δCW ≤ 8θ₀`, `EA2 ≤ 10⁻⁶⁰`, **`EG ≤ 10⁻³⁶`**;
`NSmall J` : `GinvSmall`, `cg ≥ 2.4·10⁻⁴`, `qb ≤ 1.02`, `bN ≤ 2·10⁷` ⟹ **`EN ≤ 10⁻¹²`**, hence `EN < 1/bN`.
-/
set_option autoImplicit false
set_option maxHeartbeats 8000000

namespace AdalyFormal.DLayer

local notation "θ₀" => ((1 : ℝ) / 10 ^ 45)

structure GinvSmall {S E Y P B : Type*} [NormedAddCommGroup S] [InnerProductSpace ℝ S]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [NormedAddCommGroup Y] [InnerProductSpace ℝ Y]
    [NormedAddCommGroup P] [InnerProductSpace ℝ P] [NormedAddCommGroup B] [InnerProductSpace ℝ B]
    [CompleteSpace S] [CompleteSpace E] [CompleteSpace Y] [CompleteSpace P] [CompleteSpace B]
    (I : GinvHyp S E Y P B) : Prop where
  gam : GamSmall I.Gm
  hδC : I.δC ≤ 7 * θ₀
  hκ : I.κ ≤ 1 / 10 ^ 100
  hδK : I.δK ≤ 1 / 10 ^ 100
  hν : I.ν ≤ 1 / 10 ^ 100
  hδν : I.δν ≤ 1 / 10 ^ 100
  hδB : I.δB ≤ 200 * θ₀
  hM : I.M = 1

namespace GinvSmall
variable {S E Y P B : Type*} [NormedAddCommGroup S] [InnerProductSpace ℝ S]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [NormedAddCommGroup Y] [InnerProductSpace ℝ Y]
    [NormedAddCommGroup P] [InnerProductSpace ℝ P] [NormedAddCommGroup B] [InnerProductSpace ℝ B]
    [CompleteSpace S] [CompleteSpace E] [CompleteSpace Y] [CompleteSpace P] [CompleteSpace B]
    {I : GinvHyp S E Y P B} (h : GinvSmall I)
include h

theorem dZs : 0 ≤ I.Gm.dZ ∧ 0 ≤ I.Gm.dDZ ∧ 0 ≤ I.Gm.kZ ∧ 0 ≤ I.Gm.kDZ ∧ 0 ≤ I.Gm.dW ∧ 0 ≤ I.Gm.dT :=
  I.dZ_nonneg

theorem nW_le : I.nW ≤ 4e12 := by
  unfold GinvHyp.nW
  have := h.gam.kDZ_le; have := h.gam.dDZ_le
  nlinarith

theorem nW_nonneg' : 0 ≤ I.nW := by
  obtain ⟨-, hdDZ, -, hkDZ, -, -⟩ := h.dZs
  unfold GinvHyp.nW; linarith

theorem δCW_le : I.δCW ≤ 8 * θ₀ := by
  unfold GinvHyp.δCW
  obtain ⟨hdZ0, -, hkZ0, -, -, -⟩ := h.dZs
  have t1 : I.δK * I.Gm.kZ ≤ (1 / 10 ^ 100) * 1.2e13 := mul_le_mul h.hδK h.gam.kZ_le hkZ0 (by norm_num)
  have t2 : I.κ * I.Gm.dZ ≤ (1 / 10 ^ 100) * (2.1e27 * θ₀) := mul_le_mul h.hκ h.gam.dZ_le hdZ0 (by norm_num)
  have := h.hδC
  nlinarith

theorem δCW_nonneg : 0 ≤ I.δCW := by
  unfold GinvHyp.δCW
  obtain ⟨hdZ0, -, hkZ0, -, -, -⟩ := h.dZs
  have := I.hδC; have := I.hδK; have := I.hκ
  have := mul_nonneg I.hδK hkZ0; have := mul_nonneg I.hκ hdZ0
  linarith

theorem EA2_le : I.EA2 ≤ 1 / 10 ^ 60 := by
  unfold GinvHyp.EA2
  obtain ⟨-, -, -, -, hdW0, -⟩ := h.dZs
  have hnW := h.nW_le; have hnW0 := h.nW_nonneg'
  have hdW := h.gam.dW_le
  have hν0 := I.hν; have hδν0 := I.hδν
  have a1 : I.nW * I.ν * I.Gm.dW ≤ 4e12 * (1 / 10 ^ 100) * (8.1e26 * θ₀) :=
    mul_le_mul (mul_le_mul hnW h.hν hν0 (by norm_num)) hdW hdW0 (by norm_num)
  have a2 : I.nW * I.δν * (I.nW + I.Gm.dW) ≤ 4e12 * (1 / 10 ^ 100) * (4e12 + 8.1e26 * θ₀) :=
    mul_le_mul (mul_le_mul hnW h.hδν hδν0 (by norm_num)) (add_le_add hnW hdW) (by positivity) (by norm_num)
  have a3 : I.Gm.dW * (I.ν + I.δν) * (I.nW + I.Gm.dW) ≤ (8.1e26 * θ₀) * (2 / 10 ^ 100) * (4e12 + 8.1e26 * θ₀) := by
    refine mul_le_mul (mul_le_mul hdW (by linarith [h.hν, h.hδν]) (by positivity) (by norm_num))
      (add_le_add hnW hdW) (by positivity) (by norm_num)
  nlinarith

theorem EA2_nonneg : 0 ≤ I.EA2 := by
  unfold GinvHyp.EA2
  obtain ⟨-, -, -, -, hdW0, -⟩ := h.dZs
  have hnW0 := h.nW_nonneg'
  have := I.hν; have := I.hδν
  positivity

theorem EG_le : I.EG ≤ 1 / 10 ^ 36 := by
  unfold GinvHyp.EG
  obtain ⟨-, -, -, -, -, hdT0⟩ := h.dZs
  have hnW := h.nW_le; have hnW0 := h.nW_nonneg'
  have hν0 := I.hν
  have e1 : (1 / 4) * I.ν * I.nW ^ 2 ≤ (1 / 4) * (1 / 10 ^ 100) * (4e12) ^ 2 := by
    have := pow_le_pow_left₀ hnW0 hnW 2
    have := mul_le_mul h.hν this (sq_nonneg _) (by norm_num)
    nlinarith
  have e2 : 5 * I.δCW ^ 2 ≤ 5 * (8 * θ₀) ^ 2 := by
    have := pow_le_pow_left₀ h.δCW_nonneg h.δCW_le 2; linarith
  have e3 : 5 * I.Gm.dT ^ 2 ≤ 5 * (3e26 * θ₀) ^ 2 := by
    have := pow_le_pow_left₀ hdT0 h.gam.dT_le 2; linarith
  have e4 : 5 * I.M * I.δB ^ 2 ≤ 5 * 1 * (200 * θ₀) ^ 2 := by
    rw [h.hM]; have := pow_le_pow_left₀ I.hδB h.hδB 2; linarith
  have e5 := h.EA2_le
  nlinarith

theorem EG_nonneg : 0 ≤ I.EG := by
  unfold GinvHyp.EG
  have := h.EA2_nonneg; have := I.hν; have := I.hM; have := h.nW_nonneg'
  positivity

end GinvSmall

structure NSmall {S E Y P B : Type*} [NormedAddCommGroup S] [InnerProductSpace ℝ S]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [NormedAddCommGroup Y] [InnerProductSpace ℝ Y]
    [NormedAddCommGroup P] [InnerProductSpace ℝ P] [NormedAddCommGroup B] [InnerProductSpace ℝ B]
    [CompleteSpace S] [CompleteSpace E] [CompleteSpace Y] [CompleteSpace P] [CompleteSpace B]
    (J : NHyp S E Y P B) : Prop where
  ginv : GinvSmall J.toGinvHyp
  hcg : 2.4e-4 ≤ J.cg
  hqb : J.qb ≤ 1.02
  hbN : J.bN ≤ 2e7

namespace NSmall
variable {S E Y P B : Type*} [NormedAddCommGroup S] [InnerProductSpace ℝ S]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [NormedAddCommGroup Y] [InnerProductSpace ℝ Y]
    [NormedAddCommGroup P] [InnerProductSpace ℝ P] [NormedAddCommGroup B] [InnerProductSpace ℝ B]
    [CompleteSpace S] [CompleteSpace E] [CompleteSpace Y] [CompleteSpace P] [CompleteSpace B]
    {J : NHyp S E Y P B} (h : NSmall J)
include h

theorem X0_le : J.X0 ≤ 4250 := by
  unfold NHyp.X0
  rw [div_le_iff₀ (lt_of_lt_of_le (by norm_num) h.hcg)]
  nlinarith [h.hqb, h.hcg]
theorem X0_nonneg : 0 ≤ J.X0 := by
  unfold NHyp.X0; exact div_nonneg J.hqb (le_trans (by norm_num) h.hcg)
theorem Y0_le : J.Y0 ≤ 8600 := by
  unfold NHyp.Y0
  have hcg := h.hcg
  have hcgp : 0 < J.cg := lt_of_lt_of_le (by norm_num) hcg
  have h2 : 2 / J.cg ≤ 2 / 2.4e-4 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hcg
  have h3 : J.qb + J.δB ≤ 1.02 + 200 * θ₀ := add_le_add h.hqb h.ginv.hδB
  have h4 : 0 ≤ J.qb + J.δB := add_nonneg J.hqb J.hδB
  have := mul_le_mul h2 h3 h4 (by positivity)
  nlinarith
theorem Y0_nonneg : 0 ≤ J.Y0 := by
  unfold NHyp.Y0
  have hcgp : 0 < J.cg := lt_of_lt_of_le (by norm_num) h.hcg
  have := J.hqb; have := J.hδB
  positivity
theorem Ex_le : J.Ex ≤ 4335 := by
  unfold NHyp.Ex
  have := mul_le_mul h.hqb h.X0_le h.X0_nonneg (by norm_num); linarith
theorem Ex_nonneg : 0 ≤ J.Ex := by unfold NHyp.Ex; exact mul_nonneg J.hqb h.X0_nonneg
theorem Ey_le : J.Ey ≤ 11800 := by
  unfold NHyp.Ey
  have hEG := h.ginv.EG_le; have hEG0 := h.ginv.EG_nonneg
  have hY := h.Y0_le; have hY0 := h.Y0_nonneg
  have h1 : J.Iv.EG * J.Y0 ^ 2 ≤ (1 / 10 ^ 36) * 8600 ^ 2 :=
    mul_le_mul hEG (pow_le_pow_left₀ hY0 hY 2) (sq_nonneg _) (by norm_num)
  have h2 : J.Y0 * (J.qb + J.δB) ≤ 8600 * (1.02 + 200 * θ₀) :=
    mul_le_mul hY (add_le_add h.hqb h.ginv.hδB) (add_nonneg J.hqb J.hδB) (by norm_num)
  nlinarith
theorem Ey_nonneg : 0 ≤ J.Ey := by
  unfold NHyp.Ey
  have := h.ginv.EG_nonneg; have := h.Y0_nonneg; have := J.hqb; have := J.hδB
  positivity
theorem νnW : J.ν * J.Iv.nW ^ 2 ≤ (1 / 10 ^ 100) * (4e12) ^ 2 := by
  have := pow_le_pow_left₀ h.ginv.nW_nonneg' h.ginv.nW_le 2
  exact mul_le_mul h.ginv.hν this (sq_nonneg _) (by norm_num)
theorem Px_le : J.Px ≤ 66 := by
  unfold NHyp.Px
  refine sqrt_le_of _ _ (by norm_num) ?_
  have h1 := h.Ex_le
  have h2 := h.νnW
  have h3 : J.X0 ^ 2 ≤ 4250 ^ 2 := pow_le_pow_left₀ h.X0_nonneg h.X0_le 2
  have h4 : J.ν * J.Iv.nW ^ 2 * J.X0 ^ 2 ≤ (1 / 10 ^ 100) * (4e12) ^ 2 * 4250 ^ 2 :=
    mul_le_mul h2 h3 (sq_nonneg _) (by positivity)
  nlinarith
theorem Py_le : J.Py ≤ 109 := by
  unfold NHyp.Py
  refine sqrt_le_of _ _ (by norm_num) ?_
  have h1 := h.Ey_le
  have h2 := h.νnW
  have h3 : J.Y0 ^ 2 ≤ 8600 ^ 2 := pow_le_pow_left₀ h.Y0_nonneg h.Y0_le 2
  have h4 : J.ν * J.Iv.nW ^ 2 * J.Y0 ^ 2 ≤ (1 / 10 ^ 100) * (4e12) ^ 2 * 8600 ^ 2 :=
    mul_le_mul h2 h3 (sq_nonneg _) (by positivity)
  nlinarith
theorem KD_le : J.KD ≤ 1 / 10 ^ 60 := by
  unfold NHyp.KD
  obtain ⟨-, -, -, -, hdW0, -⟩ := h.ginv.dZs
  have hnW := h.ginv.nW_le; have hnW0 := h.ginv.nW_nonneg'
  have hdW := h.ginv.gam.dW_le
  have hν0 := J.hν; have hδν0 := J.hδν
  have a1 : J.Iv.Gm.dW * ((J.ν + J.δν) * (J.Iv.nW + J.Iv.Gm.dW))
      ≤ (8.1e26 * θ₀) * ((2 / 10 ^ 100) * (4e12 + 8.1e26 * θ₀)) :=
    mul_le_mul hdW (mul_le_mul (by linarith [h.ginv.hν, h.ginv.hδν]) (add_le_add hnW hdW) (by positivity)
      (by norm_num)) (by positivity) (by norm_num)
  have a2 : J.Iv.nW * (J.δν * (J.Iv.nW + J.Iv.Gm.dW) + J.ν * J.Iv.Gm.dW)
      ≤ 4e12 * ((1 / 10 ^ 100) * (4e12 + 8.1e26 * θ₀) + (1 / 10 ^ 100) * (8.1e26 * θ₀)) := by
    refine mul_le_mul hnW (add_le_add (mul_le_mul h.ginv.hδν (add_le_add hnW hdW) (by positivity) (by norm_num))
      (mul_le_mul h.ginv.hν hdW hdW0 (by norm_num))) (by positivity) (by norm_num)
  nlinarith
theorem KD_nonneg : 0 ≤ J.KD := by
  unfold NHyp.KD
  obtain ⟨-, -, -, -, hdW0, -⟩ := h.ginv.dZs
  have hnW0 := h.ginv.nW_nonneg'; have := J.hν; have := J.hδν
  positivity

theorem EN_le : J.EN ≤ 1 / 10 ^ 12 := by
  unfold NHyp.EN
  obtain ⟨-, -, -, -, -, hdT0⟩ := h.ginv.dZs
  have hX := h.X0_le; have hX0 := h.X0_nonneg; have hY := h.Y0_le; have hY0 := h.Y0_nonneg
  have hPx := h.Px_le; have hPx0 : 0 ≤ J.Px := Real.sqrt_nonneg _
  have hPy := h.Py_le; have hPy0 : 0 ≤ J.Py := Real.sqrt_nonneg _
  have hB := h.ginv.hδB; have hB0 := J.hδB
  have hC := h.ginv.δCW_le; have hC0 := h.ginv.δCW_nonneg
  have hT := h.ginv.gam.dT_le
  have hKD := h.KD_le; have hKD0 := h.KD_nonneg
  have hM : J.M = 1 := h.ginv.hM
  rw [hM, Real.sqrt_one]
  -- each product, bounded by the product of the bounds
  have p1 : J.δB * J.Y0 ≤ (200 * θ₀) * 8600 := mul_le_mul hB hY hY0 (by positivity)
  have p2 : J.X0 * J.δB ≤ 4250 * (200 * θ₀) := mul_le_mul hX hB hB0 (by norm_num)
  have p3 : J.Iv.δCW * J.X0 * (J.Py + J.Iv.δCW * J.Y0) ≤ (8 * θ₀) * 4250 * (109 + (8 * θ₀) * 8600) :=
    mul_le_mul (mul_le_mul hC hX hX0 (by positivity)) (add_le_add hPy (mul_le_mul hC hY hY0 (by positivity)))
      (by positivity) (by positivity)
  have p4 : J.Px * (J.Iv.δCW * J.Y0) ≤ 66 * ((8 * θ₀) * 8600) :=
    mul_le_mul hPx (mul_le_mul hC hY hY0 (by positivity)) (by positivity) (by norm_num)
  have p5 : J.KD * J.X0 * J.Y0 ≤ (1 / 10 ^ 60) * 4250 * 8600 :=
    mul_le_mul (mul_le_mul hKD hX hX0 (by positivity)) hY hY0 (by positivity)
  have p6 : J.Iv.Gm.dT * J.X0 * (J.Py + J.Iv.Gm.dT * J.Y0) ≤ (3e26 * θ₀) * 4250 * (109 + (3e26 * θ₀) * 8600) :=
    mul_le_mul (mul_le_mul hT hX hX0 (by positivity)) (add_le_add hPy (mul_le_mul hT hY hY0 (by positivity)))
      (by positivity) (by positivity)
  have p7 : J.Px * (J.Iv.Gm.dT * J.Y0) ≤ 66 * ((3e26 * θ₀) * 8600) :=
    mul_le_mul hPx (mul_le_mul hT hY hY0 (by positivity)) (by positivity) (by norm_num)
  have p8 : J.δB * J.X0 * (1 * J.Py) ≤ (200 * θ₀) * 4250 * (1 * 109) :=
    mul_le_mul (mul_le_mul hB hX hX0 (by positivity)) (by linarith) (by positivity) (by positivity)
  have p9 : 1 * J.δB ^ 2 * J.X0 * J.Y0 ≤ 1 * (200 * θ₀) ^ 2 * 4250 * 8600 := by
    have := pow_le_pow_left₀ hB0 hB 2
    exact mul_le_mul (mul_le_mul (by linarith) hX hX0 (by positivity)) hY hY0 (by positivity)
  have p10 : 1 * J.Px * J.δB * J.Y0 ≤ 1 * 66 * (200 * θ₀) * 8600 :=
    mul_le_mul (mul_le_mul (by linarith) hB hB0 (by positivity)) hY hY0 (by positivity)
  nlinarith

theorem EN_lt : J.EN < 1 / J.bN := by
  have h1 := h.EN_le
  have hb := h.hbN
  have hbp : 0 < J.bN := J.hbN
  have : 1 / (2e7 : ℝ) ≤ 1 / J.bN := one_div_le_one_div_of_le hbp hb
  have : (1 / 10 ^ 12 : ℝ) < 1 / 2e7 := by norm_num
  linarith

end NSmall

#print axioms GinvSmall.EG_le
#print axioms NSmall.EN_le
#print axioms NSmall.EN_lt

end AdalyFormal.DLayer
