import TL1b

set_option autoImplicit false
namespace AdalyFormal.Thin
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane

/-- preimage tower -/
def liftTower {Lt L : PeriodicLatticeExtent} (h : Covers Lt L) (S : Tower L) : Tower Lt :=
  ⟨fun j => projS h ⁻¹' S.Om j⟩

theorem mem_liftTower {Lt L : PeriodicLatticeExtent} (h : Covers Lt L) (S : Tower L) (j : ℕ)
    (x : PeriodicLatticeSite Lt) : x ∈ (liftTower h S).Om j ↔ projS h x ∈ S.Om j := Iff.rfl

theorem div_mod_block (s m a b : ℕ) (hsm : s ∣ m) (hab : a / s = b / s) :
    (a % m) / s = (b % m) / s := by
  obtain ⟨t, rfl⟩ := hsm
  rw [Nat.mod_mul_right_div_self, Nat.mod_mul_right_div_self, hab]

theorem projS_block {Lt L : PeriodicLatticeExtent} (h : Covers Lt L) (s : ℕ) (hs : ∀ μ : Fin 3, s ∣ L μ + 1)
    (x y : PeriodicLatticeSite Lt) (hxy : ∀ μ : Fin 3, (y μ).val / s = (x μ).val / s) (μ : Fin 3) :
    (projS h y μ).val / s = (projS h x μ).val / s := by
  simp only [projS_val]
  exact div_mod_block s (L μ + 1) _ _ (hs μ) (hxy μ)

theorem blockClosed_lift {Lt L : PeriodicLatticeExtent} (h : Covers Lt L) (s : ℕ) (hs : ∀ μ : Fin 3, s ∣ L μ + 1)
    (A : Set (PeriodicLatticeSite L)) (hA : BlockClosed s A) : BlockClosed s (projS h ⁻¹' A) := by
  intro x hx y hxy
  exact hA _ hx _ (fun μ => projS_block h s hs x y hxy μ)

theorem block_lift_nat (s m N a z : ℕ) (hs0 : 0 < s) (hsm : s ∣ m) (hmN : m ∣ N) (ha : a < N)
    (hz : z < m) (hzb : z / s = (a % m) / s) : ∃ b, b < N ∧ b % m = z ∧ b / s = a / s := by
  obtain ⟨t, rfl⟩ := hsm
  have hsN : s ∣ N := (Dvd.intro t rfl).trans hmN
  obtain ⟨u, hu⟩ := hsN
  have hr : z % s < s := Nat.mod_lt _ hs0
  have hq : a / s < u := by
    rw [Nat.div_lt_iff_lt_mul hs0]; rw [hu] at ha; linarith [Nat.mul_comm s u]
  refine ⟨s * (a / s) + z % s, ?_, ?_, ?_⟩
  · rw [hu]
    calc s * (a / s) + z % s < s * (a / s) + s := by omega
      _ = s * (a / s + 1) := by ring
      _ ≤ s * u := Nat.mul_le_mul_left s hq
  · have e1 : (s * (a / s) + z % s) % s = z % s := by
      rw [Nat.mul_add_mod, Nat.mod_mod]
    have e2 : (s * (a / s) + z % s) / s = a / s := by
      rw [Nat.mul_add_div hs0, Nat.div_eq_of_lt hr, add_zero]
    rw [Nat.mod_mul, e1, e2]
    have hz1 : z / s = (a / s) % t := by
      rw [hzb, Nat.mod_mul_right_div_self]
    have := Nat.mod_add_div z s
    rw [← hz1]
    exact this
  · rw [Nat.mul_add_div hs0, Nat.div_eq_of_lt hr, add_zero]

/-- a lift `w` of `z` in the prescribed `s`-block of `x̃`. -/
theorem exists_lift_in_block {Lt L : PeriodicLatticeExtent} (h : Covers Lt L) (s : ℕ) (hs0 : 0 < s)
    (hs : ∀ μ : Fin 3, s ∣ L μ + 1) (x : PeriodicLatticeSite Lt) (z : PeriodicLatticeSite L)
    (hz : ∀ μ : Fin 3, (z μ).val / s = (projS h x μ).val / s) :
    ∃ w : PeriodicLatticeSite Lt, projS h w = z ∧ ∀ μ : Fin 3, (w μ).val / s = (x μ).val / s := by
  have key : ∀ μ : Fin 3, ∃ b : Fin (Lt μ + 1), b.val % (L μ + 1) = (z μ).val ∧ b.val / s = (x μ).val / s := by
    intro μ
    obtain ⟨b, hb1, hb2, hb3⟩ := block_lift_nat s (L μ + 1) (Lt μ + 1) (x μ).val (z μ).val hs0 (hs μ) (h μ)
      (x μ).isLt (z μ).isLt (hz μ)
    exact ⟨⟨b, hb1⟩, hb2, hb3⟩
  choose w hw1 hw2 using key
  refine ⟨w, ?_, hw2⟩
  funext μ; exact Fin.ext (by simp only [projS_val]; exact hw1 μ)

end AdalyFormal.Thin
