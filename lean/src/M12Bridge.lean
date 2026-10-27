import P4L4
import M12_F
set_option autoImplicit false
open AdalyFormal.P409L AdalyFormal.GeneralClass AdalyFormal.Target.ClayStatement AdalyFormal.StatementLane AdalyFormal.StatementLane2 AdalyFormal.StatementLaneG AdalyFormal.P409C5

-- bridge: the p.409 class box is a triple usable in the Mixed/Family class predicates (same IsClassCube)
theorem bridge {L : PeriodicLatticeExtent} {ell M R k j : ℕ} {S : Tower L} {c : PeriodicLatticeSite L}
    (hell : 2 ≤ ell) (hM : 0 < M) (hR : 21 * ell ≤ R)
    (hA : Admissible ell M R k S) (hgt : ∀ μ : Fin 3, bigSide M ell k < L μ + 1)
    (hD : IsDCube ell M k S j c) (hj : 1 ≤ j) :
    ∃ i f : ℕ, (f = 12 ∨ f = 12 * ell) ∧
      MXP.AllC.IsClassCubeΦ ell M (M12.Phi12 ell) k S (printedCube5 (bigSide M ell j) c) i := by
  obtain ⟨i, f, h1, h2, h3, h4⟩ := cube5_is_class_box hell hM hR hA hgt hD hj
  have hmono := hA.1
  refine ⟨i, f, ?_, f, ?_, (isClassCube_iff hmono _ _).2 h3⟩
  · rcases h1 with ⟨-, h⟩ | ⟨-, h⟩ <;> simp [h]
  · rcases h1 with ⟨-, h⟩ | ⟨-, h⟩ <;> simp [h, M12.Phi12]
#print axioms bridge
-- regularity consumed by Mixed is body at own factor:
#check @MXP.AllC.PerCubeRegularΦ
