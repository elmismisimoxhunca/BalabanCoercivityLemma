import TL1a

set_option autoImplicit false
namespace AdalyFormal.Thin
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane

theorem pcd_proj (m N a b : ℕ) (hmN : m ∣ N) (hm : 0 < m) (ha : a < N) (hb : b < N) :
    pcd m (a % m) (b % m) ≤ pcd N a b := by
  obtain ⟨n, rfl⟩ := hmN
  exact pcd_mod_le m n a b hm (Nat.pos_of_ne_zero (by rintro rfl; simp at ha)) ha hb

theorem pdist_proj_le {Lt L : PeriodicLatticeExtent} (h : Covers Lt L) (x y : PeriodicLatticeSite Lt) :
    pdist (projS h x) (projS h y) ≤ pdist x y := by
  unfold pdist
  refine Finset.sum_le_sum (fun μ _ => ?_)
  exact pcd_proj (L μ + 1) (Lt μ + 1) _ _ (h μ) (Nat.succ_pos _) (x μ).isLt (y μ).isLt

/-- lift of a site over `y` with the same circular distance from `z̃`. -/
theorem exists_lift_site {Lt L : PeriodicLatticeExtent} (h : Covers Lt L) (z : PeriodicLatticeSite Lt)
    (y : PeriodicLatticeSite L) :
    ∃ w : PeriodicLatticeSite Lt, projS h w = y ∧ pdist z w ≤ pdist (projS h z) y := by
  have key : ∀ μ : Fin 3, ∃ b : Fin (Lt μ + 1), b.val % (L μ + 1) = (y μ).val ∧
      pcd (Lt μ + 1) (z μ).val b.val ≤ pcd (L μ + 1) ((z μ).val % (L μ + 1)) (y μ).val := by
    intro μ
    obtain ⟨b, hb1, hb2, hb3⟩ := pcd_lift (Lt μ + 1) (L μ + 1) (z μ).val (y μ).val (h μ) (Nat.succ_pos _)
      (z μ).isLt (y μ).isLt
    exact ⟨⟨b, hb1⟩, hb2, hb3⟩
  choose w hw1 hw2 using key
  refine ⟨w, ?_, ?_⟩
  · funext μ; exact Fin.ext (by simp only [projS_val]; exact hw1 μ)
  · unfold pdist
    refine Finset.sum_le_sum (fun μ _ => ?_)
    exact hw2 μ

end AdalyFormal.Thin
