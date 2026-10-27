import GFC6
import SC3b

/-!
# SC4a -- plane waves on the twisted cell: definitions, quasi-periodicity, eigen-relation `S_μ e_k = σ_{k,μ} e_k`.
Standard axioms only.
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000
open scoped ComplexInnerProductSpace BigOperators ComplexConjugate
open AdalyFormal.FlatCoercivity

namespace AdalyFormal.ScaledCoercivity

section PW
variable {n : ℕ}

/-- the angle of the twist, in `(-π, π]` -/
noncomputable def th (z : Fin 3 → Circle) (μ : Fin 3) : ℝ := Complex.arg (z μ : ℂ)

theorem th_mem (z : Fin 3 → Circle) (μ : Fin 3) : -Real.pi < th z μ ∧ th z μ ≤ Real.pi :=
  ⟨Complex.neg_pi_lt_arg _, Complex.arg_le_pi _⟩

theorem z_eq_exp (z : Fin 3 → Circle) (μ : Fin 3) :
    (z μ : ℂ) = Complex.exp (Complex.I * (th z μ : ℝ)) := by
  have h := Complex.norm_mul_exp_arg_mul_I (z μ : ℂ)
  rw [Circle.norm_coe, Complex.ofReal_one, one_mul] at h
  unfold th
  rw [mul_comm]
  exact h.symm

/-- the plane-wave multiplier `σ_{k,μ} = exp(i (θ_μ + 2π k_μ)/n)` -/
noncomputable def sg (n : ℕ) (z : Fin 3 → Circle) (k : Cell n) (μ : Fin 3) : ℂ :=
  Complex.exp (Complex.I * (((th z μ + 2 * Real.pi * ((k μ : ℕ) : ℝ)) / (n : ℝ) : ℝ) : ℂ))

theorem norm_sg (z : Fin 3 → Circle) (k : Cell n) (μ : Fin 3) : ‖sg n z k μ‖ = 1 :=
  Complex.norm_exp_I_mul_ofReal _

theorem sg_ne (z : Fin 3 → Circle) (k : Cell n) (μ : Fin 3) : sg n z k μ ≠ 0 :=
  Complex.exp_ne_zero _

theorem sg_pow (hn : 0 < n) (z : Fin 3 → Circle) (k : Cell n) (μ : Fin 3) :
    (sg n z k μ) ^ n = (z μ : ℂ) := by
  unfold sg
  rw [← Complex.exp_nat_mul, z_eq_exp]
  have hn' : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  have : (n : ℂ) * (Complex.I * (((th z μ + 2 * Real.pi * ((k μ : ℕ) : ℝ)) / (n : ℝ) : ℝ) : ℂ))
      = Complex.I * (th z μ : ℝ) + ((k μ : ℕ) : ℂ) * (2 * Real.pi * Complex.I) := by
    push_cast
    field_simp
  rw [this, Complex.exp_add, Complex.exp_nat_mul_two_pi_mul_I, mul_one]

/-- the (unnormalised) plane wave on `ℤ³` -/
noncomputable def pw (n : ℕ) (z : Fin 3 → Circle) (k : Cell n) (x : Z3) : ℂ :=
  ∏ μ, (sg n z k μ) ^ (x μ)

theorem pw_add (z : Fin 3 → Circle) (k : Cell n) (x y : Z3) : pw n z k (x + y) = pw n z k x * pw n z k y := by
  unfold pw
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl (fun μ _ => ?_)
  rw [Pi.add_apply, zpow_add₀ (sg_ne z k μ)]

theorem pw_ev (z : Fin 3 → Circle) (k : Cell n) (μ : Fin 3) : pw n z k (ev μ) = sg n z k μ := by
  unfold pw ev
  rw [Finset.prod_eq_single μ]
  · simp
  · intro ν _ hν; simp [Pi.single_apply, hν]
  · intro h; exact absurd (Finset.mem_univ _) h

theorem pw_nsmul (hn : 0 < n) (z : Fin 3 → Circle) (k : Cell n) (m : Z3) :
    pw n z k ((n : ℤ) • m) = phase (fun μ => (z μ : ℂ)) m := by
  unfold pw phase
  refine Finset.prod_congr rfl (fun μ _ => ?_)
  rw [Pi.smul_apply, smul_eq_mul, zpow_mul, zpow_natCast, sg_pow hn]

theorem pw_qp (hn : 0 < n) (z : Fin 3 → Circle) (k : Cell n) (x m : Z3) :
    pw n z k (x + (n : ℤ) • m) = phase (fun μ => (z μ : ℂ)) m * pw n z k x := by
  rw [pw_add, pw_nsmul hn, mul_comm]

/-- the plane wave as a cell vector (unnormalised) -/
noncomputable def pwv (n : ℕ) (z : Fin 3 → Circle) (k : Cell n) : CV n :=
  WithLp.toLp 2 (fun t => pw n z k (cc t))

theorem lift_pwv (hn : 0 < n) (z : Fin 3 → Circle) (k : Cell n) (x : Z3) :
    lift hn (fun μ => (z μ : ℂ)) (pwv n z k) x = pw n z k x := by
  unfold lift
  have h := eq_cc_modc_add hn x
  conv_rhs => rw [h]
  rw [pw_qp hn]
  rfl

theorem Su_pwv (hn : 0 < n) (z : Fin 3 → Circle) (k : Cell n) (μ : Fin 3) :
    Su hn z μ (pwv n z k) = sg n z k μ • pwv n z k := by
  ext t
  rw [Su_apply, Sl_apply, lift_pwv hn, pw_add, pw_ev]
  simp [pwv, mul_comm]

theorem norm_pw (z : Fin 3 → Circle) (k : Cell n) (x : Z3) : ‖pw n z k x‖ = 1 := by
  unfold pw
  rw [norm_prod]
  refine Finset.prod_eq_one (fun μ _ => ?_)
  rw [norm_zpow, norm_sg, one_zpow]

theorem card_cell (n : ℕ) : Fintype.card (Cell n) = n ^ 3 := by
  simp [Cell]

theorem norm_pwv_sq (z : Fin 3 → Circle) (k : Cell n) : ‖pwv n z k‖ ^ 2 = (n : ℝ) ^ 3 := by
  rw [EuclideanSpace.norm_sq_eq]
  simp only [pwv, norm_pw]
  simp [card_cell]

end PW

#print axioms Su_pwv
#print axioms norm_pwv_sq

end AdalyFormal.ScaledCoercivity
