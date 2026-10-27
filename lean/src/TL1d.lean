import TL1c

set_option autoImplicit false
namespace AdalyFormal.Thin
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane

theorem admissible_lift {Lt L : PeriodicLatticeExtent} (h : Covers Lt L) {ell M R k : ℕ} {S : Tower L}
    (hS : Admissible ell M R k S) : Admissible ell M R k (liftTower h S) := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hS
  have hM : M ∣ L 0 + 1 := by simpa [bigSide] using h3 0 (Nat.zero_le _) 0
  have hM0 : 0 < M := Nat.pos_of_dvd_of_pos hM (Nat.succ_pos _)
  refine ⟨fun j x hx => h1 j hx, fun j hj => ?_, fun j hj μ => (h3 j hj μ).trans (h μ), fun j hj => ?_, fun j hj x hx y hy => ?_, fun x => ?_⟩
  · ext x; exact ⟨fun hx => by have := h2 j hj; rw [Set.eq_empty_iff_forall_notMem] at this; exact (this _ hx).elim, fun hx => hx.elim⟩
  · exact blockClosed_lift h _ (fun μ => h3 j hj μ) _ (h4 j hj)
  · have := h5 j hj (projS h x) hx (projS h y) hy
    exact lt_of_lt_of_le this (pdist_proj_le h x y)
  · have hMs : ∀ μ : Fin 3, M ∣ L μ + 1 := fun μ => by simpa [bigSide] using h3 0 (Nat.zero_le _) μ
    show x ∈ (liftTower h S).Om 0 ↔ ∃ y ∈ (liftTower h S).Om 1, ∃ z : PeriodicLatticeSite Lt,
      (∀ μ : Fin 3, (z μ).val / M = (x μ).val / M) ∧ pdist z y ≤ R * M
    show projS h x ∈ S.Om 0 ↔ _
    rw [h6 (projS h x)]
    constructor
    · rintro ⟨y, hy, z, hz1, hz2⟩
      obtain ⟨w, hw1, hw2⟩ := exists_lift_in_block h M hM0 hMs x z hz1
      obtain ⟨y', hy1, hy2⟩ := exists_lift_site h w y
      refine ⟨y', ?_, w, hw2, ?_⟩
      · show projS h y' ∈ S.Om 1
        rw [hy1]; exact hy
      · rw [hw1] at hy2
        exact le_trans hy2 hz2
    · rintro ⟨y, hy, z, hz1, hz2⟩
      refine ⟨projS h y, hy, projS h z, fun μ => (projS_block h M hMs x z hz1 μ), le_trans (pdist_proj_le h z y) hz2⟩

end AdalyFormal.Thin
