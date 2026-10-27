import TL4

/-!
# TL6a -- explicit regional scales for the M1 regime and the `k`-free sum

`rho1 f M α₀ = (4π+4) f M α₀`; for a level-`j` row region and scale `l < j`:
`epsM j l = ell^l e + 3π (ell²)^l q0`, `e = ρ1/ell^{j-1}`, `q0 = ρ1/ell^{2(j-1)}` (`0` for `l ≥ j`).
`sum_epsM`: `Σ_{l<j} epsM j l ≤ 2 (1+3π) ρ1` for every `j` (independent of `j`, `k`).
`theta_le`: `θ(ε) ≤ Cθ ell² ε` for `ε ≤ 1/(1000 ell⁴)`.   `sum_theta_epsM`: `Σ_{l<j} θ(epsM j l) ≤ SstarM`.
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
namespace AdalyFormal.TowerLoc

open Finset
open AdalyFormal.NonflatJet
open AdalyFormal.BondComposite
open EstimatesLayer.E1E3

def rho1 (f M : ℕ) (α₀ : ℝ) : ℝ := (4 * Real.pi + 4) * ((f : ℝ) * M * α₀)

def epsM (ell f M : ℕ) (α₀ : ℝ) (j l : ℕ) : ℝ :=
  if l < j then (ell : ℝ) ^ l * (rho1 f M α₀ / (ell : ℝ) ^ (j - 1))
      + 3 * Real.pi * (((ell : ℝ) ^ 2) ^ l * (rho1 f M α₀ / (ell : ℝ) ^ (2 * (j - 1))))
  else 0

/-- `Cθ = √192 + √240 · 576/5` -/
def Ctheta : ℝ := Real.sqrt 192 + Real.sqrt 240 * (576 / 5)

/-- the `k`-free bound on the level sums: `Cθ ell² · 2(1+3π) ρ1` -/
def SstarM (ell f M : ℕ) (α₀ : ℝ) : ℝ := Ctheta * (ell : ℝ) ^ 2 * (2 * (1 + 3 * Real.pi) * rho1 f M α₀)

theorem rho1_nonneg (f M : ℕ) (α₀ : ℝ) (hα : 0 ≤ α₀) : 0 ≤ rho1 f M α₀ := by
  unfold rho1; have := Real.pi_pos; positivity

theorem epsM_nonneg (ell f M : ℕ) (α₀ : ℝ) (hα : 0 ≤ α₀) (j l : ℕ) : 0 ≤ epsM ell f M α₀ j l := by
  unfold epsM
  have := rho1_nonneg f M α₀ hα
  have := Real.pi_pos
  split_ifs <;> positivity

theorem epsM_le (ell f M : ℕ) (hell : 0 < ell) (α₀ : ℝ) (hα : 0 ≤ α₀) (j l : ℕ) :
    epsM ell f M α₀ j l ≤ (1 + 3 * Real.pi) * rho1 f M α₀ := by
  have hρ := rho1_nonneg f M α₀ hα
  have hpi := Real.pi_pos
  have hellR : (1 : ℝ) ≤ ell := by exact_mod_cast hell
  unfold epsM
  split_ifs with hl
  · have hP : (0 : ℝ) < (ell : ℝ) ^ (j - 1) := by positivity
    have h1 : (ell : ℝ) ^ l ≤ (ell : ℝ) ^ (j - 1) := pow_le_pow_right₀ hellR (by omega)
    have h2 : ((ell : ℝ) ^ 2) ^ l ≤ (ell : ℝ) ^ (2 * (j - 1)) := by
      rw [← pow_mul]; exact pow_le_pow_right₀ hellR (by omega)
    have hP2 : (0 : ℝ) < (ell : ℝ) ^ (2 * (j - 1)) := by positivity
    have e1 : (ell : ℝ) ^ l * (rho1 f M α₀ / (ell : ℝ) ^ (j - 1)) ≤ rho1 f M α₀ := by
      rw [← mul_div_assoc, div_le_iff₀ hP]; nlinarith
    have e2 : ((ell : ℝ) ^ 2) ^ l * (rho1 f M α₀ / (ell : ℝ) ^ (2 * (j - 1))) ≤ rho1 f M α₀ := by
      rw [← mul_div_assoc, div_le_iff₀ hP2]; nlinarith
    nlinarith
  · positivity

theorem geom_le (x : ℝ) (hx : 2 ≤ x) (j : ℕ) (hj : 1 ≤ j) :
    ∑ l ∈ range j, x ^ l ≤ 2 * x ^ (j - 1) := by
  have hx1 : x ≠ 1 := by intro h; linarith
  have hxm : 0 < x - 1 := by linarith
  rw [geom_sum_eq hx1, div_le_iff₀ hxm]
  have hj' : x ^ j = x * x ^ (j - 1) := by
    rw [← pow_succ']; congr 1; omega
  have hp : 0 < x ^ (j - 1) := by positivity
  rw [hj']
  nlinarith [mul_nonneg hp.le (sub_nonneg.mpr hx)]

theorem sum_epsM (ell f M : ℕ) (hell2 : 2 ≤ ell) (α₀ : ℝ) (hα : 0 ≤ α₀) (j : ℕ) :
    ∑ l ∈ range j, epsM ell f M α₀ j l ≤ 2 * (1 + 3 * Real.pi) * rho1 f M α₀ := by
  have hρ := rho1_nonneg f M α₀ hα
  have hpi := Real.pi_pos
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · simp; positivity
  have hellR : (2 : ℝ) ≤ ell := by exact_mod_cast hell2
  have hP : (0 : ℝ) < (ell : ℝ) ^ (j - 1) := by positivity
  have hP2 : (0 : ℝ) < (ell : ℝ) ^ (2 * (j - 1)) := by positivity
  have hsplit : ∑ l ∈ range j, epsM ell f M α₀ j l
      = (rho1 f M α₀ / (ell : ℝ) ^ (j - 1)) * ∑ l ∈ range j, (ell : ℝ) ^ l
        + 3 * Real.pi * ((rho1 f M α₀ / (ell : ℝ) ^ (2 * (j - 1))) * ∑ l ∈ range j, ((ell : ℝ) ^ 2) ^ l) := by
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun l hl => ?_)
    unfold epsM
    rw [if_pos (Finset.mem_range.mp hl)]
    ring
  rw [hsplit]
  have g1 := geom_le (ell : ℝ) hellR j hj
  have g2 := geom_le (((ell : ℝ) ^ 2)) (by nlinarith) j hj
  have e2 : ((ell : ℝ) ^ 2) ^ (j - 1) = (ell : ℝ) ^ (2 * (j - 1)) := by rw [← pow_mul]
  rw [e2] at g2
  have a1 : (rho1 f M α₀ / (ell : ℝ) ^ (j - 1)) * ∑ l ∈ range j, (ell : ℝ) ^ l ≤ 2 * rho1 f M α₀ := by
    calc _ ≤ (rho1 f M α₀ / (ell : ℝ) ^ (j - 1)) * (2 * (ell : ℝ) ^ (j - 1)) :=
          mul_le_mul_of_nonneg_left g1 (by positivity)
      _ = 2 * rho1 f M α₀ := by field_simp
  have a2 : (rho1 f M α₀ / (ell : ℝ) ^ (2 * (j - 1))) * ∑ l ∈ range j, ((ell : ℝ) ^ 2) ^ l ≤ 2 * rho1 f M α₀ := by
    calc _ ≤ (rho1 f M α₀ / (ell : ℝ) ^ (2 * (j - 1))) * (2 * (ell : ℝ) ^ (2 * (j - 1))) :=
          mul_le_mul_of_nonneg_left g2 (by positivity)
      _ = 2 * rho1 f M α₀ := by field_simp
  nlinarith

theorem theta_le (ell : ℕ) (hell : 0 < ell) (ε : ℝ) (h0 : 0 ≤ ε) (hle : ε ≤ 1 / (1000 * (ell : ℝ) ^ 4)) :
    thetaOf ell ε ≤ Ctheta * (ell : ℝ) ^ 2 * ε := by
  have hk := e2Majorant_numeric_bc hell ε h0 hle
  have hellR : (0 : ℝ) < ell := by exact_mod_cast hell
  have s1 := Real.sqrt_nonneg 192
  have s2 := Real.sqrt_nonneg 240
  unfold thetaOf Ctheta
  calc (ell : ℝ) * (Real.sqrt 192 * ((ell : ℝ) * ε) + Real.sqrt 240 * e2Majorant (rhoOf ell ε))
      ≤ (ell : ℝ) * (Real.sqrt 192 * ((ell : ℝ) * ε) + Real.sqrt 240 * (12 * (8 * ell * (6 / 5 * ε)))) := by
        apply mul_le_mul_of_nonneg_left _ hellR.le
        have := mul_le_mul_of_nonneg_left hk s2
        linarith
    _ = (Real.sqrt 192 + Real.sqrt 240 * (576 / 5)) * (ell : ℝ) ^ 2 * ε := by ring

theorem sum_theta_epsM (ell f M : ℕ) (hell2 : 2 ≤ ell) (α₀ : ℝ) (hα : 0 ≤ α₀)
    (hsmA : (1 + 3 * Real.pi) * rho1 f M α₀ ≤ 1 / (1000 * (ell : ℝ) ^ 4)) (j : ℕ) :
    ∑ l ∈ range j, thetaOf ell (epsM ell f M α₀ j l) ≤ SstarM ell f M α₀ := by
  have hell : 0 < ell := by omega
  have hC : 0 ≤ Ctheta := by unfold Ctheta; positivity
  calc ∑ l ∈ range j, thetaOf ell (epsM ell f M α₀ j l)
      ≤ ∑ l ∈ range j, Ctheta * (ell : ℝ) ^ 2 * epsM ell f M α₀ j l :=
        Finset.sum_le_sum (fun l _ => theta_le ell hell _ (epsM_nonneg ell f M α₀ hα j l)
          ((epsM_le ell f M hell α₀ hα j l).trans hsmA))
    _ = Ctheta * (ell : ℝ) ^ 2 * ∑ l ∈ range j, epsM ell f M α₀ j l := by rw [Finset.mul_sum]
    _ ≤ Ctheta * (ell : ℝ) ^ 2 * (2 * (1 + 3 * Real.pi) * rho1 f M α₀) :=
        mul_le_mul_of_nonneg_left (sum_epsM ell f M hell2 α₀ hα j) (by positivity)
    _ = SstarM ell f M α₀ := rfl

end AdalyFormal.TowerLoc

#print axioms AdalyFormal.TowerLoc.epsM_le
#print axioms AdalyFormal.TowerLoc.geom_le
#print axioms AdalyFormal.TowerLoc.sum_epsM
#print axioms AdalyFormal.TowerLoc.theta_le
#print axioms AdalyFormal.TowerLoc.sum_theta_epsM
