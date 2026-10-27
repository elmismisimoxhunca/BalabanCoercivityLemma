import BC11

/-!
# BC12 -- explicit constants for the fine-level class `(e, q0)` of curvature_blocking `link_tower_na`

`ε_j = ell^j e + 3π (ell²)^j q0 ≤ ell^j η`, `η = e + 3π ell^k q0`, `n = ell^k`, `ρ = n η`.  Then (ell ≥ 2, `ε_j ≤ 1/(1000 ell⁴)`):
* `eps0Of ≤ 6 ρ · sqrt(1/n³)`  (`ε0 aFE ≤ 162 ρ` with `aFE = sqrt(729 n³)`),
* `n · deltaM ≤ √a · φ(3600 ell ρ)`, `φ(s) = (s/r) e^{s/r}`, `r = ell^{-1/2}`.
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
namespace AdalyFormal.BondComposite

theorem eps_class_le (ell k : ℕ) (hell : 1 ≤ ell) (e q0 : ℝ) (hq : 0 ≤ q0) (j : ℕ) (hj : j ≤ k) :
    (ell : ℝ) ^ j * e + 3 * Real.pi * (((ell : ℝ) ^ 2) ^ j * q0)
      ≤ (ell : ℝ) ^ j * (e + 3 * Real.pi * ((ell : ℝ) ^ k * q0)) := by
  have hl : (1 : ℝ) ≤ ell := by exact_mod_cast hell
  have h1 : (ell : ℝ) ^ j ≤ (ell : ℝ) ^ k := pow_le_pow_right₀ hl hj
  have h2 : ((ell : ℝ) ^ 2) ^ j = (ell : ℝ) ^ j * (ell : ℝ) ^ j := by rw [← pow_mul, mul_comm, pow_mul, sq]
  rw [h2]
  have hpos : 0 ≤ 3 * Real.pi * q0 := by have := Real.pi_pos; positivity
  have hj0 : (0 : ℝ) ≤ (ell : ℝ) ^ j := by positivity
  nlinarith [mul_le_mul_of_nonneg_left h1 hj0, mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h1 hj0) hpos]

theorem class_eps0_bound (ell k : ℕ) (hell : 2 ≤ ell) (e q0 : ℝ) (he : 0 ≤ e) (hq : 0 ≤ q0) :
    eps0Of ell k (fun j => (ell : ℝ) ^ j * e + 3 * Real.pi * (((ell : ℝ) ^ 2) ^ j * q0))
      ≤ 6 * ((ell : ℝ) ^ k * (e + 3 * Real.pi * ((ell : ℝ) ^ k * q0))) * Real.sqrt (1 / ((ell : ℝ) ^ k) ^ 3) := by
  have hη : 0 ≤ e + 3 * Real.pi * ((ell : ℝ) ^ k * q0) := by have := Real.pi_pos; positivity
  exact eps0Of_le ell k hell _ _ hη (fun j hj => eps_class_le ell k (by omega) e q0 hq j hj.le)

theorem class_n_deltaM_bound (ell k : ℕ) (hell : 2 ≤ ell) (a : ℝ) (ha : 0 ≤ a) (e q0 : ℝ) (he : 0 ≤ e) (hq : 0 ≤ q0)
    (hεs : ∀ j, j < k → (ell : ℝ) ^ j * e + 3 * Real.pi * (((ell : ℝ) ^ 2) ^ j * q0) ≤ 1 / (1000 * (ell : ℝ) ^ 4)) :
    (ell : ℝ) ^ k * deltaM ell k a (fun j => (ell : ℝ) ^ j * e + 3 * Real.pi * (((ell : ℝ) ^ 2) ^ j * q0)) ≤
      Real.sqrt a * (((3600 * (ell : ℝ) * ((ell : ℝ) ^ k * (e + 3 * Real.pi * ((ell : ℝ) ^ k * q0)))) / rr ell)
        * Real.exp ((3600 * (ell : ℝ) * ((ell : ℝ) ^ k * (e + 3 * Real.pi * ((ell : ℝ) ^ k * q0)))) / rr ell)) := by
  have hη : 0 ≤ e + 3 * Real.pi * ((ell : ℝ) ^ k * q0) := by have := Real.pi_pos; positivity
  exact n_deltaM_le ell k hell a ha _ _ hη (fun j _ => by have := Real.pi_pos; positivity)
    (fun j hj => eps_class_le ell k (by omega) e q0 hq j hj.le) hεs

#print axioms eps_class_le
#print axioms class_eps0_bound
#print axioms class_n_deltaM_bound

end AdalyFormal.BondComposite
