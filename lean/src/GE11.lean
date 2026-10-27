import GE10

/-!
# GE11 -- every site of the ball is the middle of a vertex box that carries a `GChart` (m2_gluegeo, 2026-10-15)

`ball_vertex_charts` composes `cover_geometry_ball` (GE10), `vertex_chart_of_tower` (GE7: six half-slab cubes -> `gchart_at_bad_vertex`) and
the non-wrap `iota_injOn`: for `x in Ball x0 (rho ell^j)` there are a grid vertex `v` (`s = M ell^(j-1)`), `p0` with `iota v p0 = x`, and a
`GChart U gv` on `iota v '' Box R'` (`R' = (s+1)/2`, so `x` is in it) at the GV13 constants (`k`-free; no dependence on `L`, `k`, `U`).
Hypotheses beyond the tower: `PerCubeRegular2` at `(alpha0, eta)`, smallness at index `m = j-1`, `6 <= s`, torus sides `> 2 (R'+3)`.
No sorry / axiom.
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace AdalyFormal.M2GlueGeo

open AdalyFormal.Target.ClayStatement AdalyFormal.M2Glue3 AdalyFormal.M2Glue2
open AdalyFormal.StatementLane AdalyFormal.StatementLane2
open AdalyFormal.StatementLaneR8 (Ball)
open AdalyFormal.Balaban.SuTwoLogExp (SU2)

variable {L : PeriodicLatticeExtent}

/-- `t1 = 12 M alpha0 ell^{-m}`. -/
noncomputable def tOne (ell M m : ℕ) (α₀ : ℝ) : ℝ := (12 : ℝ) * M * α₀ * ((ell : ℝ) ^ m)⁻¹

/-- `t2 = (1 + 4 t1) 12 M alpha0 ell^{-2m}`. -/
noncomputable def tTwo (ell M m : ℕ) (α₀ : ℝ) : ℝ :=
  (1 + 4 * tOne ell M m α₀) * ((12 : ℝ) * M * α₀ * (((ell : ℝ) ^ m)⁻¹) ^ 2)

theorem ball_vertex_charts {ell M R k : ℕ} {S : Tower L} (hS : Admissible ell M R k S)
    (hcov : CoversOm0p ell M 12 k S) (hell : 2 ≤ ell) (hM : 0 < M) {j : ℕ} (hj1 : 1 ≤ j) (hjk : j ≤ k)
    {x0 : PeriodicLatticeSite L} (hx0 : x0 ∈ S.Om j) {ρ : ℕ} (hρ : 24 + ρ * ell ≤ R)
    {x : PeriodicLatticeSite L} (hx : x ∈ Ball x0 (ρ * ell ^ j))
    {α₀ η : ℝ} (hη : 0 < η) (hα : 0 ≤ α₀) {U : LinkCfg L} (hP : PerCubeRegular2 ell M 12 k S α₀ η U)
    (hsm : tOne ell M (j - 1) α₀ + (12 : ℝ) * M * α₀ * (((ell : ℝ) ^ (j - 1))⁻¹) ^ 2 ≤ 1)
    (hs6 : 6 ≤ bigSide M ell (j - 1))
    (hthin : ∀ μ, 2 * ((bigSide M ell (j - 1) + 1) / 2 + 3) < L μ + 1)
    (ht12 : tOne ell M (j - 1) α₀ ≤ 2)
    (hsmall : (4 * cB 1152 5 + 1) * (3 * (((bigSide M ell (j - 1) + 1) / 2 : ℕ) : ℝ) + 2) ^ 2 *
      (tTwo ell M (j - 1) α₀ + 43 * tOne ell M (j - 1) α₀ ^ 2) ≤ 1) :
    ∃ v : PeriodicLatticeSite L, (∀ μ, (v μ).val % bigSide M ell (j - 1) = 0) ∧
      ∃ p0 : Z3, iota v p0 = x ∧ p0 ∈ Box ((bigSide M ell (j - 1) + 1) / 2) ∧
      ∃ gv : PeriodicLatticeSite L → SU2,
        GChart U gv (lift v (Box ((bigSide M ell (j - 1) + 1) / 2)))
          (KT1 4 1152 * (3 * (((bigSide M ell (j - 1) + 1) / 2 : ℕ) : ℝ) + 2) *
            (tTwo ell M (j - 1) α₀ + 43 * tOne ell M (j - 1) α₀ ^ 2))
          (KT2 4 1152 * (tTwo ell M (j - 1) α₀ + 43 * tOne ell M (j - 1) α₀ ^ 2)) := by
  obtain ⟨v, hv, p0, hp0, hxe, hnear, -, -⟩ := cover_geometry_ball hS hcov hell hM hj1 hjk hx0 hρ hx
  have hmk : j - 1 ≤ k := by omega
  have hx0' : x0 ∈ S.Om (j - 1 + 1) := by rw [Nat.sub_add_cancel hj1]; exact hx0
  set s := bigSide M ell (j - 1) with hsdef
  set R' := (s + 1) / 2 with hR'
  have hR'1 : 1 ≤ R' := by omega
  have hRs : R' + 3 ≤ s := by omega
  have hinj : Set.InjOn (iota v) (Box (R' + 3)) := iota_injOn v hthin
  obtain ⟨gv, hgv⟩ := vertex_chart_of_tower hS hcov hell hM hmk hx0' hv hnear hη hα hP hsm hR'1 hRs hinj ht12 hsmall
  refine ⟨v, hv, p0, hxe, ?_, gv, hgv⟩
  intro i
  have := hp0 i
  have h1 := neg_abs_le (p0 i)
  have h2 := le_abs_self (p0 i)
  have h3 : (|p0 i|) ≤ (R' : ℤ) := by
    have : 2 * |p0 i| ≤ (s : ℤ) := hp0 i
    have h4 : (s : ℤ) ≤ 2 * R' := by
      have : s ≤ 2 * R' := by omega
      exact_mod_cast this
    omega
  exact h3

end AdalyFormal.M2GlueGeo
