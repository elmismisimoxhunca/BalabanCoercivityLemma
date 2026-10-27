import R7Fork.DM7b

/-!
# DM7c -- rows of `Q` at every level: the row functional at `<j, b>` is the `ell^j`-block line average at the coarse bond `b-hat`
(flat `U`, any tower).
-/
set_option autoImplicit false
set_option maxRecDepth 8000
set_option maxHeartbeats 8000000
namespace AdalyFormal.DirichletMono

open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane (scaleUp)
open AdalyFormal.StatementLaneG
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.GenuineU1
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond blockOf mem_blockOf CoarseLattice mem_CoarseLattice)
open AdalyFormal.Balaban.CoarseCurl (coarseShift coarseShift_apply_ne coarseShift_val_eq)
open AdalyFormal.Balaban.LatticeOperators (CoarseBond)
open AdalyFormal.Balaban.LineIntegralCovariant (lineCoarseRestrictSuTwo)

section rows
variable (P : IngrBParams)

theorem lev_dvd (j : ℕ) (hj : j ≤ P.k) (ν : Fin 3) : P.ell ^ j ∣ scaleUp P.ell P.k P.Lu ν + 1 := by
  rw [scaleUp_succ P.ell P.k P.Lu P.hell ν]
  exact Dvd.dvd.mul_left (pow_dvd_pow P.ell hj) _

theorem bond_coarse_site (j : ℕ) (hj : j ≤ P.k) (b : Bond (scaleUp P.ell P.k P.Lu))
    (hb : b ∈ bondsLam P.G j) : b.1 ∈ CoarseLattice (scaleUp P.ell P.k P.Lu) (P.ell ^ j) := by
  rw [mem_CoarseLattice]
  intro ρ
  apply Nat.mod_eq_zero_of_dvd
  rcases hb.1 with h | h
  · exact h.1 ρ
  · have h' : coarseShift b.1 (P.ell ^ j) b.2 ∈ P.G.Lam j := h
    by_cases hρ : ρ = b.2
    · have h1 := h'.1 b.2
      rw [coarseShift_val_eq] at h1
      have h2 : P.ell ^ j ∣ (b.1 b.2).val + P.ell ^ j :=
        (Nat.dvd_mod_iff (lev_dvd P j hj b.2)).mp h1
      rw [hρ]
      exact Nat.dvd_add_self_right.mp h2
    · have h1 := h'.1 ρ
      rwa [coarseShift_apply_ne b.1 (P.ell ^ j) b.2 ρ hρ] at h1

/-- the coarse bond (stride `ell^j`) underlying a `frakB`-bond of level `j` -/
def bhat (j : ℕ) (hj : j ≤ P.k) (b : Bond (scaleUp P.ell P.k P.Lu)) (hb : b ∈ bondsLam P.G j) :
    CoarseBond (scaleUp P.ell P.k P.Lu) (P.ell ^ j) :=
  (⟨b.1, bond_coarse_site P j hj b hb⟩, b.2)

theorem Qfull_row (hU : P.U = flatCfg) (A : BondFnL2 (scaleUp P.ell P.k P.Lu)) (j : Fin (P.k + 1))
    (b : Bond (scaleUp P.ell P.k P.Lu)) (hb : b ∈ bondsLam P.G j) :
    (P.sector.Qfull A) ⟨j, ⟨b, hb⟩⟩
      = lineCoarseRestrictSuTwo (P.ell ^ (j : ℕ)) (WithLp.ofLp A) (bhat P j (Nat.lt_succ_iff.mp j.2) b hb) := by
  have hj : (j : ℕ) ≤ P.k := Nat.lt_succ_iff.mp j.2
  have hell' : (P.ell : ℝ) ≠ 0 := by exact_mod_cast P.hell.ne'
  have key := Qcomp_closed P.ell P.hell (bgTower P.G P.U) (bgTower_flat P hU) P.k
    (scaleUp_tiling P.ell P.k P.Lu P.hell)
    (suCoordF (WithLp.ofLp A)) (j : ℕ) hj (P.ell ^ (j : ℕ)) rfl (bhat P j hj b hb)
  rw [suCoordFInv_suCoordF] at key
  show (((P.G.ell : ℝ) ^ (j : ℕ))⁻¹) • (WithLp.ofLp (QlinB P.G P.U (j : ℕ) A)) b = _
  have hQ : (WithLp.ofLp (QlinB P.G P.U (j : ℕ) A)) b = suCoordFInv (QlinCompX P.ell
        (bgTower P.G P.U) (j : ℕ) (suCoordF (WithLp.ofLp A))) ((bhat P j hj b hb).1.1, (bhat P j hj b hb).2) := rfl
  rw [hQ, key]
  show ((P.ell : ℝ) ^ (j : ℕ))⁻¹ • ((((P.ell ^ (j : ℕ) : ℕ)) : ℝ) • _) = _
  rw [smul_smul]
  push_cast
  rw [inv_mul_cancel₀ (pow_ne_zero _ hell'), one_smul]

end rows

#print axioms bond_coarse_site
#print axioms Qfull_row

end AdalyFormal.DirichletMono
