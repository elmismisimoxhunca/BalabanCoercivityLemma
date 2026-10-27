import CG6b

/-!
# CG6c -- cell regions: images, preimages, wrapper of the cyclic cell-box lemma
-/
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option linter.unusedVariables false

namespace AdalyFormal.CoverGeom

open AdalyFormal.Target.ClayStatement AdalyFormal.StatementLane AdalyFormal.StatementLane2
open AdalyFormal.StatementLaneR8 (Ball)
open AdalyFormal.M2Glue3 (Z3 ev iota iota_shift iota_shift2)
open AdalyFormal.UnifLane.Z (cellZ wo div_eq_iff')

variable {L : PeriodicLatticeExtent}

theorem box_pt_near {ell M R k j : ℕ} {S : Tower L} (hadm : Admissible ell M R k S) (hell : 2 ≤ ell) (hM : 0 < M)
    (hj : 2 ≤ j) (hjk : j ≤ k) (hR : 24 * ell + 25 ≤ R) {w x₀ : PeriodicLatticeSite L} (hx₀ : x₀ ∈ S.Om j)
    (hw : pdist w x₀ ≤ 3 * (M * ell ^ j)) {p : Z3}
    (hp : ∀ μ, wo w μ / ((bigSide M ell (j - 1) : ℕ) : ℤ) - ((7 * ell : ℕ) : ℤ) ≤ cellZ ((bigSide M ell (j - 1) : ℕ) : ℤ) (wo w) p μ ∧
      cellZ ((bigSide M ell (j - 1) : ℕ) : ℤ) (wo w) p μ ≤ wo w μ / ((bigSide M ell (j - 1) : ℕ) : ℤ) + ((7 * ell : ℕ) : ℤ)) :
    pdist w (iota w p) ≤ (21 * ell + 3) * bigSide M ell (j - 1) ∧ iota w p ∈ S.Om (j - 1) := by
  have hSpos : 0 < bigSide M ell (j - 1) := Nat.mul_pos hM (pow_pos (by omega) _)
  have hb := fun μ => cell_abs hSpos (wo w) (7 * ell) (p := p) hp μ
  have hd := pdist_iota_le w p
  have hP : pdist w (iota w p) ≤ (21 * ell + 3) * bigSide M ell (j - 1) := by
    have h0 := hb 0; have h1 := hb 1; have h2 := hb 2
    have : bigSide M ell (j - 1) * (7 * ell + 1) * 3 = (21 * ell + 3) * bigSide M ell (j - 1) := by ring
    omega
  refine ⟨hP, ?_⟩
  refine near_Om_gen hadm (by omega) hjk hx₀ hw hP ?_
  have hS : bigSide M ell (j - 1) = ell * (M * ell ^ (j - 2)) := by
    unfold bigSide
    have : j - 1 = (j - 2) + 1 := by omega
    rw [this, pow_succ]; ring
  have hL : M * ell ^ j = ell * bigSide M ell (j - 1) := by
    unfold bigSide
    have : j = (j - 1) + 1 := by omega
    conv_lhs => rw [this, pow_succ]
    ring
  have := box_arith ell (bigSide M ell (j - 1)) (M * ell ^ (j - 2)) R (M * ell ^ j) hS hell hR hL
  unfold bigSide at this ⊢
  omega

theorem box_idx {ell M R k j : ℕ} {S : Tower L} (hadm : Admissible ell M R k S) (hell : 2 ≤ ell) (hM : 0 < M)
    (hj : 2 ≤ j) (hjk : j ≤ k) (hR : 24 * ell + 25 ≤ R) {w x₀ : PeriodicLatticeSite L} (hx₀ : x₀ ∈ S.Om j)
    (hw : pdist w x₀ ≤ 3 * (M * ell ^ j)) {p : Z3}
    (hp : ∀ μ, wo w μ / ((bigSide M ell (j - 1) : ℕ) : ℤ) - ((7 * ell : ℕ) : ℤ) ≤ cellZ ((bigSide M ell (j - 1) : ℕ) : ℤ) (wo w) p μ ∧
      cellZ ((bigSide M ell (j - 1) : ℕ) : ℤ) (wo w) p μ ≤ wo w μ / ((bigSide M ell (j - 1) : ℕ) : ℤ) + ((7 * ell : ℕ) : ℤ))
    {sites : Set (PeriodicLatticeSite L)} {i : ℕ} (hcl : IsClassCube ell M 12 k S sites i) (hq : iota w p ∈ sites) :
    j - 1 ≤ i := by
  obtain ⟨hP, hΩ⟩ := box_pt_near hadm hell hM hj hjk hR hx₀ hw hp
  refine idx_ge hadm (by omega) hjk hcl hq hΩ hx₀ hw hP ?_
  have hS : bigSide M ell (j - 1) = ell * (M * ell ^ (j - 2)) := by
    unfold bigSide
    have : j - 1 = (j - 2) + 1 := by omega
    rw [this, pow_succ]; ring
  have hL : M * ell ^ j = ell * bigSide M ell (j - 1) := by
    unfold bigSide
    have : j = (j - 1) + 1 := by omega
    conv_lhs => rw [this, pow_succ]
    ring
  have := box_arith ell (bigSide M ell (j - 1)) (M * ell ^ (j - 2)) R (M * ell ^ j) hS hell hR hL
  unfold bigSide at this ⊢
  omega

theorem axis_preimage {s n N v o : ℕ} {d : ℤ} (hs : 0 < s) (hN : N = s * n) (hn : 0 < n) (hv : v < N)
    (hvd : ((v / s : ℕ) : ℤ) = d % (n : ℤ)) :
    ∃ a : ℤ, (a + o) / (s : ℤ) = d ∧ ((o : ℤ) + a) % (N : ℤ) = v := by
  have hsI : (0 : ℤ) < s := by exact_mod_cast hs
  have hnI : (0 : ℤ) < n := by exact_mod_cast hn
  refine ⟨(s : ℤ) * d + ((v % s : ℕ) : ℤ) - o, ?_, ?_⟩
  · have hr : ((v % s : ℕ) : ℤ) < s := by exact_mod_cast Nat.mod_lt _ hs
    have hr0 : (0 : ℤ) ≤ ((v % s : ℕ) : ℤ) := by positivity
    have : (s : ℤ) * d + ((v % s : ℕ) : ℤ) - o + o = s * d + ((v % s : ℕ) : ℤ) := by ring
    rw [this]
    exact int_cell_div (n := 0) hsI hr0 hr
  · have hr : ((v % s : ℕ) : ℤ) < s := by exact_mod_cast Nat.mod_lt _ hs
    have hr0 : (0 : ℤ) ≤ ((v % s : ℕ) : ℤ) := by positivity
    have : (o : ℤ) + ((s : ℤ) * d + ((v % s : ℕ) : ℤ) - o) = s * d + ((v % s : ℕ) : ℤ) := by ring
    rw [this, hN, Nat.cast_mul]
    rw [int_mod_cell hsI hnI hr0 hr, ← hvd]
    have h5 : (s : ℤ) * ((v / s : ℕ) : ℤ) + ((v % s : ℕ) : ℤ) = v := by
      have := Nat.div_add_mod v s
      exact_mod_cast this
    linarith

end AdalyFormal.CoverGeom
