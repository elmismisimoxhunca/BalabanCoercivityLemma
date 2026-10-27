import GE5
import AC_GE4
import AC_Base

/-! AC copy of GE5: affected declarations only (lane allc_20261016); 12 literal kept (control build). -/
set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace AdalyFormal.M2GlueGeo

open AdalyFormal.AllC
variable {fc : ℕ} [CubeFactor fc]

open AdalyFormal.Target.ClayStatement AdalyFormal.M2Glue3
open AdalyFormal.StatementLane AdalyFormal.StatementLane2
open AdalyFormal.StatementLaneR8 (pdist_comm pdist_triangle Ball)
open AdalyFormal.M1 (om_anti)
open AdalyFormal.M2Bridge (pdist_lt_three_s')

variable {L : PeriodicLatticeExtent}

/-- the six half-slab cubes at a vertex. -/
def VertexCubesAC (fc ell M k : ℕ) (S : Tower L) (m : ℕ) (v : PeriodicLatticeSite L) : Prop :=
  ∀ (σ : Fin 3) (b : Bool), ∃ (sites : Set (PeriodicLatticeSite L)) (j : ℕ),
    IsClassCube ell M fc k S sites j ∧ m ≤ j ∧ ∀ p ∈ HSlab (bigSide M ell m) σ b, iota v p ∈ sites

theorem slab_cubeAC {ell M R k : ℕ} {S : Tower L} (hS : Admissible ell M R k S)
    (hcov : CoversOm0p ell M fc k S) (hell : 2 ≤ ell) (hM : 0 < M) {m : ℕ} (hmk : m ≤ k)
    {x0 : PeriodicLatticeSite L} (hx0 : x0 ∈ S.Om (m + 1)) {v : PeriodicLatticeSite L}
    (hv : ∀ μ, (v μ).val % bigSide M ell m = 0)
    (hnear : ∀ p ∈ BoxS (bigSide M ell m), 2 * pdist (iota v p) x0 + 3 * (fc * bigSide M ell m) ≤ 2 * (R * bigSide M ell m)) :
    VertexCubesAC fc ell M k S m v := by
  intro σ b
  have hs : 0 < bigSide M ell m := bigSide_pos (by omega) hM m
  have key : ∀ (μ ν : Fin 3), μ < ν → σ ≠ μ → σ ≠ ν → ∃ (sites : Set (PeriodicLatticeSite L)) (j : ℕ),
      IsClassCube ell M fc k S sites j ∧ m ≤ j ∧ ∀ p ∈ HSlab (bigSide M ell m) σ b, iota v p ∈ sites := by
    intro μ ν hμν h1 h2
    obtain ⟨sites, j, hq, hjm, hall⟩ := slab_cube_auxAC hS hcov hell hM hmk hx0 hv hnear hμν h1 h2
      (cσ := if b then 0 else -1) (by cases b <;> simp)
    refine ⟨sites, j, hq, hjm, fun p hp => hall p (hp.1 μ) (hp.1 ν) ?_⟩
    rcases hp with ⟨hb, hsp⟩
    cases b
    · have h' : p σ ≤ -1 := by
        rcases hsp with ⟨h, -⟩ | ⟨-, h⟩
        · exact absurd h (by simp)
        · exact h
      simp only [Bool.false_eq_true, if_false]
      exact blk_idx_neg hs (hb σ).1 (by omega)
    · have h' : 0 ≤ p σ := by
        rcases hsp with ⟨-, h⟩ | ⟨h, -⟩
        · exact h
        · exact absurd h (by simp)
      simp only [if_true]
      exact blk_idx_nonneg hs h' (hb σ).2
  fin_cases σ
  · exact key 1 2 (by decide) (by decide) (by decide)
  · exact key 0 2 (by decide) (by decide) (by decide)
  · exact key 0 1 (by decide) (by decide) (by decide)

end AdalyFormal.M2GlueGeo

