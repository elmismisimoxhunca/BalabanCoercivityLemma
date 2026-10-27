import GE9

/-!
# GE10 -- `cover_geometry` for balls of radius `rho * ell^j` (m2_gluegeo, 2026-10-15)

`cover_geometry_ball`: anchor `x0 in Omega_j` (`1 <= j <= k`), `24 + rho * ell <= R`, `x` with `pdist x x0 <= rho * ell^j`.  Then `x` sits in the
middle of the box of a vertex `v` of the `M ell^(j-1)`-grid, the six half-slab cubes at `v` exist, `v` is good or bad.
(`R` is chosen by the prover in `P428Target8` -- `exists R0, forall R >= R0` -- so `24 + rho * ell <= R` is available.)
No sorry / axiom.
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace AdalyFormal.M2GlueGeo

open AdalyFormal.Target.ClayStatement AdalyFormal.M2Glue3
open AdalyFormal.StatementLane AdalyFormal.StatementLane2
open AdalyFormal.StatementLaneR8 (Ball)

variable {L : PeriodicLatticeExtent}

theorem cover_geometry_ball {ell M R k : ℕ} {S : Tower L} (hS : Admissible ell M R k S)
    (hcov : CoversOm0p ell M 12 k S) (hell : 2 ≤ ell) (hM : 0 < M) {j : ℕ} (hj1 : 1 ≤ j) (hjk : j ≤ k)
    {x0 : PeriodicLatticeSite L} (hx0 : x0 ∈ S.Om j) {ρ : ℕ} (hρ : 24 + ρ * ell ≤ R)
    {x : PeriodicLatticeSite L} (hx : x ∈ Ball x0 (ρ * ell ^ j)) :
    ∃ v : PeriodicLatticeSite L, (∀ μ, (v μ).val % bigSide M ell (j - 1) = 0) ∧
      ∃ p0 : Z3, (∀ i, 2 * |p0 i| ≤ bigSide M ell (j - 1)) ∧ iota v p0 = x ∧
      (∀ p ∈ BoxS (bigSide M ell (j - 1)), pdist (iota v p) x0 + 18 * bigSide M ell (j - 1) ≤ R * bigSide M ell (j - 1)) ∧
      VertexCubes ell M k S (j - 1) v ∧
      (GoodVertex ell M k S (bigSide M ell (j - 1)) v ∨ BadVertex ell M k S (bigSide M ell (j - 1)) v) := by
  refine cover_geometry hS hcov hell hM hj1 hjk hx0 (ρ := ρ * ell ^ j) ?_ hx
  have hs : 0 < bigSide M ell (j - 1) := bigSide_pos (by omega) hM _
  have hpow : ell ^ j = ell * ell ^ (j - 1) := by
    rw [← pow_succ']; congr 1; omega
  have h1 : ell ^ (j - 1) ≤ bigSide M ell (j - 1) := by
    unfold bigSide; exact Nat.le_mul_of_pos_left _ hM
  have h2 : ρ * ell ^ j ≤ ρ * ell * bigSide M ell (j - 1) := by
    have e : ρ * ell ^ j = ρ * ell * ell ^ (j - 1) := by rw [hpow]; ring
    rw [e]; exact Nat.mul_le_mul_left _ h1
  have h3 : (24 + ρ * ell) * bigSide M ell (j - 1) ≤ R * bigSide M ell (j - 1) := Nat.mul_le_mul_right _ hρ
  nlinarith

end AdalyFormal.M2GlueGeo
