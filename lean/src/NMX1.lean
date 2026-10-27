import NVC7

/-!
# NMX1 -- the mixed slab layout: a NARROW left component (lane nonvac_mixed_20261017)

The nonvac_c layout (`nvcQ*`, `nvcN`, torus `M ell² (6T+2)`) with the LEFT edge of the tower moved in: with `w = R + ell q` (`q ≥ R`) the left component `[P₀, P₂)` of `Ω₀ \ Ω₂` has width exactly `w · M`:
`P₂ = M ell² w`, `P₁ = M ((ell²-1) w + R)`, `P₀ = M ((ell²-1) w)` (`mxP2`, `mxP1`, `mxP0`); the right edge is the nonvac_c one; `mxS` is the tower.
This module: the arithmetic of the left edge (`mx_left_facts`) and `slabGeo_mix`, the proof that the layout satisfies the geometry record `SlabGeo` (hence `Admissible`).
Consumers: widths and coverage in NMX1b, non-coverage in NMX1c, right-shell cube and `Λ` in NMX2.
-/
set_option autoImplicit false
set_option maxRecDepth 8000
set_option maxHeartbeats 16000000

namespace AdalyFormal.NonVacMix

open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLane2
open AdalyFormal.NonVacC

def mxP2 (ell M R q : ℕ) : ℕ := M * ell ^ 2 * (R + ell * q)
def mxP1 (ell M R q : ℕ) : ℕ := M * ((ell ^ 2 - 1) * (R + ell * q) + R)
def mxP0 (ell M R q : ℕ) : ℕ := M * ((ell ^ 2 - 1) * (R + ell * q))

/-- the mixed tower: `Ω₀ = [P₀,Q₀)`, `Ω₁ = [P₁,Q₁)`, `Ω₂ = [P₂,Q₂)` in the coordinate `x₀`. -/
def mxS (L : PeriodicLatticeExtent) (ell M R T q : ℕ) : Tower L :=
  slab3 L (mxP0 ell M R q) (nvcQ0 ell M R T) (mxP1 ell M R q) (nvcQ1 ell M T) (mxP2 ell M R q) (nvcQ2 ell M T)

section geo
variable {ell M R T q : ℕ}

/-- the arithmetic facts of the left edge, in one place. -/
theorem mx_left_facts (hell : 2 ≤ ell) (hR : 1 ≤ R) (hq : R ≤ q) :
    ∃ d t : ℕ, ell ^ 2 = d + 1 ∧ ell ^ 2 - 1 = d ∧ ell * (R + ell * q) = q + t ∧ d * (R + ell * q) + R = ell * t ∧
      R + R * ell ≤ R + ell * q ∧ R < R + ell * q := by
  obtain ⟨d, hd⟩ : ∃ d, ell ^ 2 = d + 1 := ⟨ell ^ 2 - 1, by have : 1 ≤ ell ^ 2 := Nat.one_le_pow _ _ (by omega); omega⟩
  have hdd : ell ^ 2 - 1 = d := by omega
  have hqle : q ≤ ell * (R + ell * q) := by nlinarith
  obtain ⟨t, ht⟩ : ∃ t, ell * (R + ell * q) = q + t := ⟨ell * (R + ell * q) - q, by omega⟩
  have h1 : (d + 1) * (R + ell * q) = ell * (ell * (R + ell * q)) := by rw [← hd]; ring
  have h2 : d * (R + ell * q) + R = ell * t := by
    have : ell * (ell * (R + ell * q)) = ell * q + ell * t := by rw [ht]; ring
    nlinarith
  refine ⟨d, t, hd, hdd, ht, h2, ?_, ?_⟩
  · nlinarith
  · nlinarith

theorem slabGeo_mix (hell : 2 ≤ ell) (hdvd : ell ∣ M) (hM : 0 < M) (hR : 1 ≤ R) (hq : R ≤ q) (hT : 1 ≤ T)
    (hwT : R + ell * q ≤ T) :
    SlabGeo M ell R (nvcN ell M T) (mxP0 ell M R q) (nvcQ0 ell M R T) (mxP1 ell M R q) (nvcQ1 ell M T)
      (mxP2 ell M R q) (nvcQ2 ell M T) := by
  have hRT : R ≤ T := by nlinarith
  have G := slabGeo_inst hell hM hdvd hRT hT
  obtain ⟨d, t, hd, hdd, ht, hdt, hw2, hRw⟩ := mx_left_facts hell hR hq
  have hell0 : 0 < ell := by omega
  have hee : 0 < ell ^ 2 := pow_pos hell0 2
  have hMee : 0 < M * ell ^ 2 := Nat.mul_pos hM hee
  have e2 : M * ell ^ 2 * (R + ell * q) = M * ((d + 1) * (R + ell * q)) := by rw [← hd]; ring
  refine ⟨hM, hell0, ?_, ?_, ?_, G.nest21, G.nest10, G.QN, G.d0, G.d1, G.d2, ?_, G.b0Q, ?_, G.b1Q, ?_, G.b2Q, ?_, G.c0Q,
    ?_, ?_, G.c1Q, ?_⟩
  · simp only [mxP0, mxP1, hdd]; exact Nat.mul_le_mul_left M (Nat.le_add_right _ _)
  · simp only [mxP1, mxP2, hdd]; rw [e2]; exact Nat.mul_le_mul_left M (by nlinarith)
  · simp only [mxP2, nvcQ2]
    exact Nat.mul_lt_mul_of_pos_left (by omega) hMee
  · simp only [mxP0, hdd]; exact Dvd.intro _ rfl
  · simp only [mxP1, hdd]; exact ⟨t, by rw [hdt]; ring⟩
  · simp only [mxP2]; exact Dvd.intro _ rfl
  · simp only [mxP0, mxP1, hdd]; ring
  · simp only [mxP1, hdd]; nlinarith [Nat.zero_le (M * (d * (R + ell * q)))]
  · simp only [mxP1, mxP2, hdd]; rw [e2]
    have := Nat.mul_le_mul_left M hw2
    nlinarith
  · simp only [mxP2]
    have h1 : R * ell ≤ R + ell * q := by nlinarith
    have h2 : R + ell * q ≤ ell ^ 2 * (R + ell * q) := Nat.le_mul_of_pos_left _ hee
    have := Nat.mul_le_mul_left M (le_trans h1 h2)
    nlinarith

end geo

end AdalyFormal.NonVacMix
