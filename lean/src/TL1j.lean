import TL1i

set_option autoImplicit false
namespace AdalyFormal.Thin
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLane2

theorem lift1 (N m z y s : ℕ) (hm : 0 < m) (hmN : m ∣ N) (hz : z < N) (hy : y < m) (hs : off m (z % m) y < s) :
    ∃ b, b < N ∧ b % m = y ∧ off N z b < s := by
  set d := off m (z % m) y with hd
  have hdm : d < m := off_lt m _ _ hm
  have hmle : m ≤ N := Nat.le_of_dvd (by omega) hmN
  have hyd : (z % m + d) % m = y := by
    have := off_spec m (z % m) y hm (Nat.mod_lt _ hm)
    rw [← hd] at this
    rw [this, Nat.mod_eq_of_lt hy]
  obtain ⟨b, hb1, hb2, hb3⟩ := lift_off N m z y d hmN hz (by omega) hyd
  refine ⟨b, hb1, hb2, ?_⟩
  unfold off; rw [hb3]; exact hs

/-- compatibility of a lifted corner with the base corner `z` and side `s` -/
def CompatCorner {Lt L : PeriodicLatticeExtent} (h : Covers Lt L) (zt : PeriodicLatticeSite Lt)
    (z : PeriodicLatticeSite L) (s : ℕ) : Prop :=
  ∀ μ : Fin 3, projS h zt μ = z μ ∨ L μ + 1 ≤ s

theorem compat_subset {Lt L : PeriodicLatticeExtent} (h : Covers Lt L) {zt : PeriodicLatticeSite Lt}
    {z : PeriodicLatticeSite L} {s : ℕ} (hc : CompatCorner h zt z s) {x : PeriodicLatticeSite Lt}
    (hx : x ∈ siteBox zt s) : projS h x ∈ siteBox z s := by
  intro μ
  have hsub := box_proj_subset h zt x s hx μ
  rcases hc μ with h1 | h1
  · rw [← h1]; exact hsub
  · exact lt_of_lt_of_le (off_lt _ _ _ (Nat.succ_pos _)) h1

theorem compat_surj {Lt L : PeriodicLatticeExtent} (h : Covers Lt L) {zt : PeriodicLatticeSite Lt}
    {z : PeriodicLatticeSite L} {s : ℕ} (hc : CompatCorner h zt z s) {y : PeriodicLatticeSite L}
    (hy : y ∈ siteBox z s) : ∃ x ∈ siteBox zt s, projS h x = y := by
  have key : ∀ μ : Fin 3, ∃ b : Fin (Lt μ + 1), b.val % (L μ + 1) = (y μ).val ∧
      off (Lt μ + 1) (zt μ).val b.val < s := by
    intro μ
    have hm : 0 < L μ + 1 := Nat.succ_pos _
    have hlt : off (L μ + 1) ((zt μ).val % (L μ + 1)) (y μ).val < s := by
      rcases hc μ with h1 | h1
      · have : (zt μ).val % (L μ + 1) = (z μ).val := by
          have := congrArg Fin.val h1
          simpa [projS_val] using this
        rw [this]; exact hy μ
      · exact lt_of_lt_of_le (off_lt _ _ _ hm) h1
    obtain ⟨b, hb1, hb2, hb3⟩ := lift1 (Lt μ + 1) (L μ + 1) (zt μ).val (y μ).val s hm (h μ) (zt μ).isLt (y μ).isLt hlt
    exact ⟨⟨b, hb1⟩, hb2, hb3⟩
  choose w hw1 hw2 using key
  refine ⟨w, hw2, ?_⟩
  funext μ; exact Fin.ext (by simp only [projS_val]; exact hw1 μ)

theorem described_lift {Lt L : PeriodicLatticeExtent} (h : Covers Lt L) {ell M f k : ℕ} {S : Tower L}
    {z : PeriodicLatticeSite L} {zt : PeriodicLatticeSite Lt} {j : ℕ}
    (hd : DescribedAt ell M f k S (siteBox z (f * bigSide M ell j)) j)
    (hgrid : GridCorner (bigSide M ell j) zt) (hc : CompatCorner h zt z (f * bigSide M ell j)) :
    DescribedAt ell M f k (liftTower h S) (siteBox zt (f * bigSide M ell j)) j := by
  obtain ⟨hj, -, hsub, ⟨y, hy1, hy2⟩⟩ := hd
  refine ⟨hj, ⟨zt, hgrid, rfl⟩, fun x hx => ?_, ?_⟩
  · have := hsub (compat_subset h hc hx)
    exact this
  · obtain ⟨x, hx, hxy⟩ := compat_surj h hc hy1
    refine ⟨x, hx, ?_⟩
    show projS h x ∈ towerBj S j
    rw [hxy]; exact hy2

end AdalyFormal.Thin
