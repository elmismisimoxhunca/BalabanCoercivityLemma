import AdalyFormal.Balaban.Bch2

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-!
# Discrete SU(2) product-angle bounds

All angles and lengths below are the existing `su2Angle` and `Bch2.nu`.
No logarithm or small-angle assumption is needed for the product triangle inequality.
-/

namespace SmallnessBridge.ProdBound

open Matrix
open AdalyFormal.Balaban.SuTwoLogExp
open AdalyFormal.Balaban.Bch2
open AdalyFormal.Balaban.RMapLipschitz
open AdalyFormal.Balaban.RegularityGap (Yof su2_trace_eq)
open AdalyFormal.Balaban.BlockingLinkEstimate (cos_su2Angle)
open scoped Matrix

/-- Scalar part of a product, derived from the certified su(2) anticommutator. -/
theorem cos_su2Angle_mul (g h : SU2) :
    Real.cos (su2Angle (g * h)) =
      Real.cos (su2Angle g) * Real.cos (su2Angle h) - ip (Yof g) (Yof h) / 2 := by
  have hYg := isSu2_Yof g
  have hYh := isSu2_Yof h
  have ht : Matrix.trace ((g : M2) * (h : M2)) =
      (((2 * (Real.cos (su2Angle g) * Real.cos (su2Angle h)) -
        ip (Yof g) (Yof h) : ℝ) : ℂ)) := by
    conv_lhs => rw [su2_decomp g, su2_decomp h]
    simp only [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul,
      Matrix.one_mul, Matrix.mul_one, Matrix.trace_add, Matrix.trace_smul,
      hYg.2, hYh.2, smul_zero, add_zero, zero_add]
    rw [mul_eq hYg hYh, Matrix.trace_add, (hYg.comm2 hYh).2,
      Matrix.trace_smul, Matrix.trace_one]
    simp only [Fintype.card_fin, smul_eq_mul, add_zero, Complex.real_smul]
    push_cast
    ring
  have ht' := su2_trace_eq (g * h)
  rw [coe_mul, ht] at ht'
  have hr := congrArg Complex.re ht'
  simp only [Complex.ofReal_re] at hr
  linarith

/-- Global triangle inequality, including products crossing the principal cut. -/
theorem su2Angle_mul_le (g h : SU2) :
    su2Angle (g * h) ≤ su2Angle g + su2Angle h := by
  by_cases hab : su2Angle g + su2Angle h ≤ Real.pi
  · have hip := abs_ip_le (isSu2_Yof g) (isSu2_Yof h)
    rw [nu_Yof, nu_Yof] at hip
    have hcos : Real.cos (su2Angle g + su2Angle h) ≤ Real.cos (su2Angle (g * h)) := by
      rw [Real.cos_add, cos_su2Angle_mul]
      linarith [le_abs_self (ip (Yof g) (Yof h))]
    have hh := Real.arccos_le_arccos hcos
    rw [Real.arccos_cos (su2Angle_nonneg _) (su2Angle_le_pi _),
      Real.arccos_cos (add_nonneg (su2Angle_nonneg g) (su2Angle_nonneg h)) hab] at hh
    exact hh
  · exact (su2Angle_le_pi _).trans (le_of_not_ge hab)

/-- An arbitrary list product has angle at most the sum of the individual angles. -/
theorem su2Angle_list_prod_le_sum (gs : List SU2) :
    su2Angle gs.prod ≤ (gs.map su2Angle).sum := by
  induction gs with
  | nil => simp [su2Angle_one]
  | cons g gs ih =>
      simpa only [List.prod_cons, List.map_cons, List.sum_cons] using
        (su2Angle_mul_le g gs.prod).trans (add_le_add (le_refl _) ih)

/-- Uniform bound, with no sign hypothesis on delta needed for the empty list. -/
theorem su2Angle_list_prod_le_length_mul (gs : List SU2) (delta : ℝ)
    (h : ∀ g ∈ gs, su2Angle g ≤ delta) :
    su2Angle gs.prod ≤ (gs.length : ℝ) * delta := by
  induction gs with
  | nil => simp [su2Angle_one]
  | cons g gs ih =>
      have hg := h g (by simp)
      have hgs := ih (fun x hx => h x (by simp [hx]))
      have hp := (su2Angle_mul_le g gs.prod).trans (add_le_add hg hgs)
      simpa only [List.prod_cons, List.length_cons, Nat.cast_add, Nat.cast_one,
        add_mul, one_mul, add_comm] using hp

/-- Requested ordering: reverse `[g₁,...,gₙ]` before taking the list product. -/
theorem su2Angle_reverse_prod_le_length_mul (gs : List SU2) (delta : ℝ)
    (h : ∀ g ∈ gs, su2Angle g ≤ delta) :
    su2Angle gs.reverse.prod ≤ (gs.length : ℝ) * delta := by
  simpa only [List.length_reverse] using
    su2Angle_list_prod_le_length_mul gs.reverse delta (fun g hg => h g (List.mem_reverse.mp hg))

/-- The global range bound may be combined with the linear discrete estimate. -/
theorem su2Angle_list_prod_le_min (gs : List SU2) (delta : ℝ)
    (h : ∀ g ∈ gs, su2Angle g ≤ delta) :
    su2Angle gs.prod ≤ min Real.pi ((gs.length : ℝ) * delta) :=
  le_min (su2Angle_le_pi _) (su2Angle_list_prod_le_length_mul gs delta h)

/-- The logarithm has exactly the principal angle as its nu-length on the closed half cap. -/
theorem nu_su2Log_eq_angle {g : SU2} (h : su2Angle g ≤ Real.pi / 2) :
    nu (su2Log g) = su2Angle g := by
  unfold nu
  rw [frobSq_su2Log h, show 2 * su2Angle g ^ 2 / 2 = su2Angle g ^ 2 by ring,
    Real.sqrt_sq (su2Angle_nonneg g)]

/-- Strictness is required only for the final strict ball, not the individual factor bounds. -/
theorem list_prod_small_log (gs : List SU2) (delta : ℝ)
    (h : ∀ g ∈ gs, su2Angle g ≤ delta)
    (hsmall : (gs.length : ℝ) * delta < Real.pi / 2) :
    nu (su2Log gs.prod) ≤ (gs.length : ℝ) * delta ∧
      nu (su2Log gs.prod) < Real.pi / 2 := by
  have ha := su2Angle_list_prod_le_length_mul gs delta h
  rw [nu_su2Log_eq_angle (ha.trans (le_of_lt hsmall))]
  exact ⟨ha, ha.trans_lt hsmall⟩

/-- Orientation reversal leaves the principal angle unchanged. -/
theorem su2Angle_inv (g : SU2) : su2Angle g⁻¹ = su2Angle g := by
  simp [su2Angle, coe_inv, Matrix.trace_conjTranspose]

/-- A global Frobenius near-identity estimate; no small-cap premise is hidden here. -/
theorem su2Angle_le_frobNorm (g : SU2) :
    su2Angle g ≤ (Real.pi / (2 * Real.sqrt 2)) * frobNorm ((g : M2) - 1) := by
  have hs := Real.mul_le_sin
    (show 0 ≤ su2Angle g / 2 by linarith [su2Angle_nonneg g])
    (show su2Angle g / 2 ≤ Real.pi / 2 by linarith [su2Angle_le_pi g])
  rw [AdalyFormal.Balaban.BlockingLinkEstimate.frobNorm_sub_one_eq]
  calc
    su2Angle g = Real.pi * (2 / Real.pi * (su2Angle g / 2)) := by field_simp
    _ ≤ Real.pi * Real.sin (su2Angle g / 2) :=
      mul_le_mul_of_nonneg_left hs (le_of_lt Real.pi_pos)
    _ = (Real.pi / (2 * Real.sqrt 2)) *
        (2 * Real.sqrt 2 * Real.sin (su2Angle g / 2)) := by field_simp

/-- On `‖g-1‖_F ≤ 2` the sharper existing logarithm estimate gives angle ≤ π/4 times distance. -/
theorem su2Angle_le_frobNorm_cap {g : SU2} (h : frobNorm ((g : M2) - 1) ≤ 2) :
    su2Angle g ≤ (Real.pi / 4) * frobNorm ((g : M2) - 1) := by
  have ha := angle_le_of_frobNorm_sub_one h
  have hf := frobNorm_su2Log_le_sharp ha
  rw [frobNorm_eq_sqrt_two_mul_nu, nu_su2Log_eq_angle ha] at hf
  have hrr : Real.sqrt (2 : ℝ) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity : 0 < 2 * Real.sqrt (2 : ℝ))] at hf
  have hm : Real.sqrt 2 * su2Angle g * (2 * Real.sqrt 2) = 4 * su2Angle g := by
    calc
      _ = 2 * (Real.sqrt 2 ^ 2) * su2Angle g := by ring
      _ = 4 * su2Angle g := by rw [hrr]; ring
  rw [hm] at hf
  linarith

/-- Frobenius version of the uniform discrete product bound, valid globally. -/
theorem su2Angle_list_prod_le_frobNorm (gs : List SU2) (eps : ℝ)
    (h : ∀ g ∈ gs, frobNorm ((g : M2) - 1) ≤ eps) :
    su2Angle gs.prod ≤ (gs.length : ℝ) * ((Real.pi / (2 * Real.sqrt 2)) * eps) := by
  apply su2Angle_list_prod_le_length_mul
  intro g hg
  exact (su2Angle_le_frobNorm g).trans (mul_le_mul_of_nonneg_left (h g hg) (by positivity))

/-- Explicit sufficient global Frobenius threshold: n ε < √2. -/
theorem list_prod_small_log_of_frobNorm (gs : List SU2) (eps : ℝ)
    (h : ∀ g ∈ gs, frobNorm ((g : M2) - 1) ≤ eps)
    (hsmall : (gs.length : ℝ) * eps < Real.sqrt 2) :
    nu (su2Log gs.prod) ≤ (gs.length : ℝ) * ((Real.pi / (2 * Real.sqrt 2)) * eps) ∧
      (gs.length : ℝ) * ((Real.pi / (2 * Real.sqrt 2)) * eps) < Real.pi / 2 := by
  have hr : (gs.length : ℝ) * ((Real.pi / (2 * Real.sqrt 2)) * eps) < Real.pi / 2 := by
    calc
      (gs.length : ℝ) * ((Real.pi / (2 * Real.sqrt 2)) * eps) =
          (Real.pi / (2 * Real.sqrt 2)) * ((gs.length : ℝ) * eps) := by ring
      _ < (Real.pi / (2 * Real.sqrt 2)) * Real.sqrt 2 :=
        mul_lt_mul_of_pos_left hsmall (by positivity)
      _ = Real.pi / 2 := by field_simp
  have ha := su2Angle_list_prod_le_frobNorm gs eps h
  rw [nu_su2Log_eq_angle (ha.trans (le_of_lt hr))]
  exact ⟨ha, hr⟩

/-- Sharper Frobenius ball: with ε ≤ 2 and n ε < 2, take ρ = n π ε / 4. -/
theorem list_prod_small_log_of_frobNorm_cap (gs : List SU2) (eps : ℝ)
    (h : ∀ g ∈ gs, frobNorm ((g : M2) - 1) ≤ eps) (heps : eps ≤ 2)
    (hsmall : (gs.length : ℝ) * eps < 2) :
    nu (su2Log gs.prod) ≤ (gs.length : ℝ) * ((Real.pi / 4) * eps) ∧
      (gs.length : ℝ) * ((Real.pi / 4) * eps) < Real.pi / 2 := by
  have hr : (gs.length : ℝ) * ((Real.pi / 4) * eps) < Real.pi / 2 := by
    have hm := mul_lt_mul_of_pos_left hsmall (by positivity : 0 < Real.pi / 4)
    nlinarith [hm]
  have ha : su2Angle gs.prod ≤ (gs.length : ℝ) * ((Real.pi / 4) * eps) := by
    apply su2Angle_list_prod_le_length_mul
    intro g hg
    exact (su2Angle_le_frobNorm_cap ((h g hg).trans heps)).trans
      (mul_le_mul_of_nonneg_left (h g hg) (by positivity))
  rw [nu_su2Log_eq_angle (ha.trans (le_of_lt hr))]
  exact ⟨ha, hr⟩

/-- Perturbed-link adapter: X is already anti-Hermitian (use X=iA for Hermitian A).
The perturbation is measured in the existing nu normalization, not an unspecified norm. -/
theorem su2Angle_perturbed_link_le (g : SU2) (X : M2) (eps0 eps1 : ℝ)
    (hX : IsSu2 X) (h0 : frobNorm ((g : M2) - 1) ≤ eps0)
    (h1 : nu X ≤ eps1) (hpi : eps1 ≤ Real.pi) :
    su2Angle (su2Exp X * g) ≤ (Real.pi / (2 * Real.sqrt 2)) * eps0 + eps1 := by
  have he := angle_exp hX (h1.trans hpi)
  have hg := (su2Angle_le_frobNorm g).trans
    (mul_le_mul_of_nonneg_left h0 (by positivity))
  have hp := su2Angle_mul_le (su2Exp X) g
  rw [he] at hp
  linarith

#print axioms su2Angle_inv
#print axioms su2Angle_le_frobNorm
#print axioms su2Angle_le_frobNorm_cap
#print axioms su2Angle_list_prod_le_frobNorm
#print axioms list_prod_small_log_of_frobNorm
#print axioms list_prod_small_log_of_frobNorm_cap
#print axioms su2Angle_perturbed_link_le
#print axioms cos_su2Angle_mul
#print axioms su2Angle_mul_le
#print axioms su2Angle_list_prod_le_sum
#print axioms su2Angle_list_prod_le_length_mul
#print axioms su2Angle_reverse_prod_le_length_mul
#print axioms su2Angle_list_prod_le_min
#print axioms nu_su2Log_eq_angle
#print axioms list_prod_small_log

end SmallnessBridge.ProdBound
