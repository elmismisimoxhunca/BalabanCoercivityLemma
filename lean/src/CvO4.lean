import CvO3
import AdalyFormal.Balaban.UbarTowerCovariance

/-!
# CvO4 -- abelian calculus on the Cartan torus: `su2Log (cartan φ) = i φ σ₃` for `|φ| < π`, `su2Exp (i ψ σ₃) = cartan ψ`,
and the (43)-block average of a Cartan configuration whose loops all have `|angle| < π` (lane omega)
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace AdalyFormal.CoverOmega

open scoped Matrix
open AdalyFormal.Target.ClayStatement
open AdalyFormal.CoverNested
open AdalyFormal.CoverJacobi
open AdalyFormal.Balaban.SuTwoLogExp
open AdalyFormal.Balaban.UbarTowerCov (stridedBlockedGauge loopVar coarseBondVar)
open AdalyFormal.Balaban.QjComposite (stepBlockOf)

/-- `i a σ₃` as a `2×2` complex matrix. -/
noncomputable def dg (a : ℝ) : M2 := Matrix.diagonal ![(a : ℂ) * Complex.I, -((a : ℂ) * Complex.I)]

theorem dg_zero : dg 0 = 0 := by
  unfold dg; ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.diagonal_apply]

theorem dg_add (a b : ℝ) : dg (a + b) = dg a + dg b := by
  unfold dg; ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.diagonal_apply] <;> ring

theorem dg_sum {ι : Type*} (s : Finset ι) (f : ι → ℝ) : dg (∑ i ∈ s, f i) = ∑ i ∈ s, dg (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [dg_zero]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, dg_add, ih]

theorem dg_smul (q : ℝ) (a : ℝ) : (q : ℂ) • dg a = dg (q * a) := by
  unfold dg; ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.diagonal_apply] <;> ring

theorem dg_qsmul (q : ℚ) (a : ℝ) : q • dg a = dg ((q : ℝ) * a) := by
  rw [← dg_smul]
  ext i j; unfold dg
  fin_cases i <;> fin_cases j <;> simp [Matrix.diagonal_apply, Rat.smul_def]

theorem su2Exp_dg (a : ℝ) : su2Exp (dg a) = cartan a := by
  have hex : NormedSpace.exp (dg a) = ((cartan a : Matrix.specialUnitaryGroup (Fin 2) ℂ) : M2) := by
    rw [cartan_coe]
    unfold dg
    rw [Matrix.exp_diagonal]
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.diagonal_apply, Complex.exp_eq_exp_ℂ]
  have hmem : NormedSpace.exp (dg a) ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ := by rw [hex]; exact (cartan a).2
  apply Subtype.ext
  rw [su2Exp_of_mem hmem, hex]

theorem trace_cartan_re (φ : ℝ) : (Matrix.trace ((cartan φ : Matrix.specialUnitaryGroup (Fin 2) ℂ) : M2)).re / 2 = Real.cos φ := by
  rw [cartan_coe]
  have h2 : Complex.exp (-((φ : ℂ) * Complex.I)) = Complex.exp (((-φ : ℝ) : ℂ) * Complex.I) := by
    push_cast; ring_nf
  simp only [Matrix.trace_diagonal, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, Complex.add_re, h2,
    Complex.exp_ofReal_mul_I_re, Real.cos_neg]
  ring

theorem su2Angle_cartan (φ : ℝ) (h : |φ| ≤ Real.pi) : su2Angle (cartan φ) = |φ| := by
  unfold su2Angle
  rw [trace_cartan_re]
  rcases le_or_gt 0 φ with h0 | h0
  · rw [abs_of_nonneg h0] at h ⊢; exact Real.arccos_cos h0 h
  · rw [abs_of_neg h0] at h ⊢
    rw [← Real.cos_neg]; exact Real.arccos_cos (by linarith) h

theorem kappa_sin (φ : ℝ) (h : |φ| < Real.pi) : (|φ| / Real.sin |φ|) * Real.sin φ = φ := by
  rcases lt_trichotomy φ 0 with h0 | h0 | h0
  · have hφ : -Real.pi < φ := by have := abs_lt.mp h; linarith [this.1]
    have hs : Real.sin φ < 0 := Real.sin_neg_of_neg_of_neg_pi_lt h0 hφ
    rw [abs_of_neg h0, Real.sin_neg]
    have hne : Real.sin φ ≠ 0 := hs.ne
    field_simp
  · subst h0; simp
  · have hs : 0 < Real.sin φ := Real.sin_pos_of_pos_of_lt_pi h0 (by have := abs_lt.mp h; linarith [this.2])
    rw [abs_of_pos h0]
    field_simp

theorem exp_sub_star (φ : ℝ) :
    Complex.exp ((φ : ℂ) * Complex.I) - star (Complex.exp ((φ : ℂ) * Complex.I)) = 2 * Complex.I * (Real.sin φ : ℂ) := by
  rw [Complex.star_def, ← Complex.exp_conj, map_mul, Complex.conj_ofReal, Complex.conj_I,
    show (φ : ℂ) * -Complex.I = (-(φ : ℂ)) * Complex.I by ring, Complex.exp_mul_I, Complex.exp_mul_I, Complex.cos_neg,
    Complex.sin_neg, Complex.ofReal_sin]
  ring

/-- **`su2Log (cartan φ) = i φ σ₃` for `|φ| < π`** (the principal branch). -/
theorem su2Log_cartan (φ : ℝ) (h : |φ| < Real.pi) : su2Log (cartan φ) = dg φ := by
  unfold su2Log su2Kappa
  rw [su2Angle_cartan φ h.le]
  have hk := kappa_sin φ h
  have hkC : ((|φ| / Real.sin |φ| : ℝ) : ℂ) * (Real.sin φ : ℂ) = φ := by exact_mod_cast hk
  ext i j
  fin_cases i <;> fin_cases j
  · simp only [Fin.zero_eta, Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul, Matrix.conjTranspose_apply, cartan_coe,
      Matrix.diagonal_apply_eq, Matrix.cons_val_zero, dg]
    rw [exp_sub_star]
    linear_combination Complex.I * hkC
  · simp [dg, cartan_coe, Matrix.diagonal_apply, Matrix.conjTranspose_apply]
  · simp [dg, cartan_coe, Matrix.diagonal_apply, Matrix.conjTranspose_apply]
  · simp only [Fin.mk_one, Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul, Matrix.conjTranspose_apply, cartan_coe,
      Matrix.diagonal_apply_eq, Matrix.cons_val_one, dg]
    simp only [Matrix.cons_val_zero]
    have e := exp_sub_star (-φ)
    push_cast at e
    rw [Complex.sin_neg, neg_mul] at e
    rw [Complex.ofReal_sin] at hkC
    rw [e]
    linear_combination (-Complex.I) * hkC


/-- **the (43)-block average of a Cartan configuration whose loops all have `|angle| < π`**: the Cartan element with the
averaged angle plus the bond angle. -/
theorem blocked_cartan {L : PeriodicLatticeExtent} (s ell : ℕ) (V : PeriodicLinkConfiguration SU2 L) (c : PeriodicLatticeEdge L)
    (φ : PeriodicLatticeSite L → ℝ) (β : ℝ)
    (hloop : ∀ x ∈ stepBlockOf c.1 s ell, loopVar s ell V c x = cartan (φ x) ∧ |φ x| < Real.pi)
    (hcb : coarseBondVar s ell V c = cartan β) :
    stridedBlockedGauge su2LogExp s ell V c =
      cartan ((((ell : ℝ) ^ 3)⁻¹ * ∑ x ∈ stepBlockOf c.1 s ell, φ x) + β) := by
  unfold stridedBlockedGauge
  simp only [su2LogExp_exp, su2LogExp_log]
  have hsum : ∑ x ∈ stepBlockOf c.1 s ell, ((ell : ℚ) ^ 3)⁻¹ • su2Log (loopVar s ell V c x) =
      dg ((((ell : ℝ) ^ 3)⁻¹ * ∑ x ∈ stepBlockOf c.1 s ell, φ x)) := by
    have h1 : ∀ x ∈ stepBlockOf c.1 s ell, ((ell : ℚ) ^ 3)⁻¹ • su2Log (loopVar s ell V c x) =
        dg ((((ell : ℝ) ^ 3)⁻¹) * φ x) := by
      intro x hx
      obtain ⟨h1, h2⟩ := hloop x hx
      rw [h1, su2Log_cartan _ h2, dg_qsmul]
      push_cast; rfl
    rw [Finset.sum_congr rfl h1, ← dg_sum, ← Finset.mul_sum]
  rw [hsum, su2Exp_dg, hcb, cartan_mul]

#print axioms dg_zero
#print axioms dg_add
#print axioms dg_sum
#print axioms dg_smul
#print axioms dg_qsmul
#print axioms su2Exp_dg
#print axioms trace_cartan_re
#print axioms su2Angle_cartan
#print axioms kappa_sin
#print axioms exp_sub_star
#print axioms su2Log_cartan
#print axioms blocked_cartan

end AdalyFormal.CoverOmega
