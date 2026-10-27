import TL8a

/-!
# TL8b -- `Lam`, `OmGe`, `bondsOm0`, `bondsLam` of the pulled-back tower
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace AdalyFormal.Thin
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.CoarseCurl (coarseShift)
open AdalyFormal.IngredientFamilyR2

section geom
variable {Lt L : PeriodicLatticeExtent} {h : Covers Lt L} {o : Fin 3 → ℕ} {ell k : ℕ} {S : Tower L}

theorem phiOK_le {hp : PhiOK h o (ell ^ k)} {j : ℕ} (hj : j ≤ k) : PhiOK h o (ell ^ j) :=
  PhiOK.mono hp (pow_dvd_pow ell hj)

theorem lam_iff (hp : PhiOK h o (ell ^ k)) {j : ℕ} (hj : j ≤ k) (x : PeriodicLatticeSite Lt) :
    x ∈ (geomOf ell k (towerPull h o S)).Lam j ↔ phiS h o x ∈ (geomOf ell k S).Lam j := by
  have hal := aligned_phiS (phiOK_le (hp := hp) hj) x
  simp only [geomOf, Set.mem_setOf_eq, towerPull, Set.mem_preimage]
  exact and_congr hal.symm Iff.rfl

theorem omGe_iff (hp : PhiOK h o (ell ^ k)) (hell : 0 < ell) (j : ℕ) (x : PeriodicLatticeSite Lt) :
    OmGe (geomOf ell k (towerPull h o S)) j x ↔ OmGe (geomOf ell k S) j (phiS h o x) := by
  unfold OmGe
  simp only [geomOf]
  constructor
  · rintro ⟨i, hji, hik, y, hy, hyx⟩
    refine ⟨i, hji, hik, phiS h o y, (lam_iff hp hik y).mp hy, fun μ => ?_⟩
    have hal : Aligned (ell ^ i) y := ((Set.mem_setOf_eq.mp hy).1)
    have hv := phiS_val_in_block (phiOK_le (hp := hp) hik) (pow_pos hell i) hal μ (hyx μ).1 (hyx μ).2
    have h1 := (hyx μ).1
    have h2 := (hyx μ).2
    omega
  · rintro ⟨i, hji, hik, y, hy, hyx⟩
    have hyal : Aligned (ell ^ i) y := ((Set.mem_setOf_eq.mp hy).1)
    obtain ⟨y', hy'al, hy'y, hy'x⟩ := exists_lift_block (phiOK_le (hp := hp) hik) (pow_pos hell i) x y hyal hyx
    refine ⟨i, hji, hik, y', (lam_iff hp hik y').mpr (by rw [hy'y]; exact hy), hy'x⟩

theorem bondsOm0_iff (b : Bond Lt) :
    b ∈ bondsOm0 (geomOf ell k (towerPull h o S)) ↔ phiE h o b ∈ bondsOm0 (geomOf ell k S) := by
  simp only [bondsOm0, geomOf, Set.mem_setOf_eq, towerPull, Set.mem_preimage, phiE, phiS_shift]

theorem bondsLam_iff (hp : PhiOK h o (ell ^ k)) (hell : 0 < ell) {j : ℕ} (hj : j ≤ k) (b : Bond Lt) :
    b ∈ bondsLam (geomOf ell k (towerPull h o S)) j ↔ phiE h o b ∈ bondsLam (geomOf ell k S) j := by
  simp only [bondsLam, Set.mem_setOf_eq]
  have e : (geomOf ell k (towerPull h o S)).ell = ell := rfl
  have e' : (geomOf ell k S).ell = ell := rfl
  rw [e, e']
  simp only [phiE]
  rw [lam_iff hp hj, lam_iff hp hj, omGe_iff hp hell, omGe_iff hp hell]
  simp only [coarseShift_nat]

end geom

end AdalyFormal.Thin
