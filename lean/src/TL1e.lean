import TL1d

set_option autoImplicit false
namespace AdalyFormal.Thin
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLaneG
open AdalyFormal.Balaban.AdmissibleSubspace (blockOf CoarseLattice)

theorem scaleUp_add_one (ell k : ℕ) (hell : 0 < ell) (Lu : PeriodicLatticeExtent) (μ : Fin 3) :
    scaleUp ell k Lu μ + 1 = (Lu μ + 1) * ell ^ k := by
  have : 0 < (Lu μ + 1) * ell ^ k := Nat.mul_pos (Nat.succ_pos _) (pow_pos hell k)
  simp only [scaleUp]; omega

theorem covers_scaleUp (ell k : ℕ) (hell : 0 < ell) {Lut Lu : PeriodicLatticeExtent} (h : Covers Lut Lu) :
    Covers (scaleUp ell k Lut) (scaleUp ell k Lu) := by
  intro μ
  rw [scaleUp_add_one ell k hell, scaleUp_add_one ell k hell]
  exact Nat.mul_dvd_mul_right (h μ) _

theorem torusOK_lift {Lut Lu : PeriodicLatticeExtent} (h : Covers Lut Lu) {ell M : ℕ}
    (hT : TorusOK ell M Lu) : TorusOK ell M Lut := by
  obtain ⟨h1, h2, h3⟩ := hT
  refine ⟨fun μ => (h1 μ).trans (h μ), fun μ => lt_of_lt_of_le (h2 μ) (Nat.le_of_dvd (Nat.succ_pos _) (h μ)),
    fun μ => (h3 μ).trans (h μ)⟩

/-- the unit-to-fine embedding of the statement (coordinates multiplied by `ell^k`). -/
theorem lambdaOK_lift {Lut Lu : PeriodicLatticeExtent} (hu : Covers Lut Lu) {ell M R k : ℕ} (hell : 0 < ell)
    (hT : TorusOK ell M Lu) {S : Tower (scaleUp ell k Lu)} {Lam : Set (PeriodicLatticeSite Lu)}
    (hL : LambdaOK ell M R k S Lam) :
    LambdaOK ell M R k (liftTower (covers_scaleUp ell k hell hu) S) (projS hu ⁻¹' Lam) := by
  obtain ⟨hB, emb, he1, he2, he3⟩ := hL
  refine ⟨blockClosed_lift hu M hT.2.2 Lam hB, ?_⟩
  -- the lifted embedding
  have hlt : ∀ (y : PeriodicLatticeSite Lut) (μ : Fin 3), ell ^ k * (y μ).val < scaleUp ell k Lut μ + 1 := by
    intro y μ
    rw [scaleUp_add_one ell k hell, mul_comm]
    exact Nat.mul_lt_mul_of_pos_right (y μ).isLt (pow_pos hell k)
  have hcomm : ∀ y : PeriodicLatticeSite Lut,
      projS (covers_scaleUp ell k hell hu) (fun μ => (⟨ell ^ k * (y μ).val, hlt y μ⟩ : Fin (scaleUp ell k Lut μ + 1)))
        = emb (projS hu y) := by
    intro y
    funext μ
    apply Fin.ext
    rw [he1, projS_val, projS_val]
    show (ell ^ k * (y μ).val) % (scaleUp ell k Lu μ + 1) = ell ^ k * ((y μ).val % (Lu μ + 1))
    rw [scaleUp_add_one ell k hell, mul_comm (Lu μ + 1), Nat.mul_mod_mul_left]
  refine ⟨fun y μ => ⟨ell ^ k * (y μ).val, hlt y μ⟩, fun y μ => rfl, ?_, ?_⟩
  · intro y hy
    show projS _ _ ∈ S.Om k
    rw [hcomm]; exact he2 _ hy
  · intro y hy y' hy'
    have h1 : emb (projS hu y') ∉ S.Om k := by
      rw [← hcomm]; exact hy'
    exact lt_of_lt_of_le (he3 _ hy _ h1) (pdist_proj_le hu y y')

end AdalyFormal.Thin
