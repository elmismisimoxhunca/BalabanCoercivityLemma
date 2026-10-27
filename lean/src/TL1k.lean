import TL1j

set_option autoImplicit false
namespace AdalyFormal.Thin
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLane2

theorem corner_site {Lt L : PeriodicLatticeExtent} (h : Covers Lt L) (hstrict : ∀ μ : Fin 3, L μ + 1 < Lt μ + 1)
    (b s : ℕ) (hb : 0 < b) (hbs : b < s) (hbd : ∀ μ : Fin 3, b ∣ L μ + 1)
    (z : PeriodicLatticeSite L) (hzb : GridCorner b z) (x : PeriodicLatticeSite Lt) (pf : Fin 3 → ℕ)
    (hin0 : ∀ μ : Fin 3, off (L μ + 1) (z μ).val ((x μ).val % (L μ + 1)) < s)
    (hin1 : ∀ μ : Fin 3, pf μ = 1 → off (L μ + 1) (z μ).val (((x μ).val + 1) % (L μ + 1)) < s) :
    ∃ zt : PeriodicLatticeSite Lt, GridCorner b zt ∧ CompatCorner h zt z s ∧
      ∀ μ : Fin 3, off (Lt μ + 1) (zt μ).val (x μ).val < s ∧
        (pf μ = 1 → off (Lt μ + 1) (zt μ).val (((x μ).val + 1) % (Lt μ + 1)) < s) := by
  have key : ∀ μ : Fin 3, ∃ w : Fin (Lt μ + 1), w.val % b = 0 ∧ (w.val % (L μ + 1) = (z μ).val ∨ L μ + 1 ≤ s) ∧
      off (Lt μ + 1) w.val (x μ).val < s ∧ (pf μ = 1 → off (Lt μ + 1) w.val (((x μ).val + 1) % (Lt μ + 1)) < s) := by
    intro μ
    have hbm := hbd μ
    have hbN : b < Lt μ + 1 := lt_of_le_of_lt (Nat.le_of_dvd (Nat.succ_pos _) hbm) (hstrict μ)
    obtain ⟨w, hw1, hw2, hw3, hw4, hw5⟩ := corner_nat b (L μ + 1) (Lt μ + 1) s (x μ).val (z μ).val hb hbm (h μ) hbN hbs
      (Nat.succ_pos _) (z μ).isLt (hzb μ) (x μ).isLt (pf μ) (hin0 μ) (hin1 μ)
    exact ⟨⟨w, hw1⟩, hw2, hw3, hw4, hw5⟩
  choose w hw1 hw2 hw3 hw4 using key
  refine ⟨w, hw1, fun μ => ?_, fun μ => ⟨hw3 μ, hw4 μ⟩⟩
  rcases hw2 μ with h1 | h1
  · left; exact Fin.ext (by simpa [projS_val] using h1)
  · right; exact h1

end AdalyFormal.Thin
