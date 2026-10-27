import TL4a

/-!
# TL4b -- the deck cover of sites
-/
set_option autoImplicit false
namespace AdalyFormal.Thin
open AdalyFormal.Target.ClayStatement

def nn (Lt L : PeriodicLatticeExtent) (μ : Fin 3) : ℕ := (Lt μ + 1) / (L μ + 1)

theorem mul_nn {Lt L : PeriodicLatticeExtent} (h : Covers Lt L) (μ : Fin 3) : (L μ + 1) * nn Lt L μ = Lt μ + 1 :=
  Nat.mul_div_cancel' (h μ)

theorem nn_pos {Lt L : PeriodicLatticeExtent} (h : Covers Lt L) (μ : Fin 3) : 0 < nn Lt L μ := by
  have := mul_nn h μ
  rcases Nat.eq_zero_or_pos (nn Lt L μ) with h0 | h0
  · rw [h0] at this; simp at this
  · exact h0

abbrev DeckIdx (Lt L : PeriodicLatticeExtent) : Type := ∀ μ : Fin 3, Fin (nn Lt L μ)

theorem deckIdx_nonempty {Lt L : PeriodicLatticeExtent} (h : Covers Lt L) : Nonempty (DeckIdx Lt L) :=
  ⟨fun μ => ⟨0, nn_pos h μ⟩⟩

/-- deck translation of sites -/
def tauS {Lt L : PeriodicLatticeExtent} (h : Covers Lt L) (d : DeckIdx Lt L) :
    Equiv.Perm (PeriodicLatticeSite Lt) where
  toFun x := fun μ => ⟨((x μ).val + (d μ).val * (L μ + 1)) % (Lt μ + 1), Nat.mod_lt _ (Nat.succ_pos _)⟩
  invFun x := fun μ => ⟨((x μ).val + (nn Lt L μ - (d μ).val) * (L μ + 1)) % (Lt μ + 1), Nat.mod_lt _ (Nat.succ_pos _)⟩
  left_inv x := by
    funext μ
    apply Fin.ext
    show (((x μ).val + (d μ).val * (L μ + 1)) % (Lt μ + 1) + (nn Lt L μ - (d μ).val) * (L μ + 1)) % (Lt μ + 1) = (x μ).val
    exact tau_inv_left' (x μ).val (Lt μ + 1) (L μ + 1) (nn Lt L μ) (d μ).val (mul_nn h μ) (Nat.succ_pos _) (nn_pos h μ)
      (x μ).isLt (le_of_lt (d μ).isLt)
  right_inv x := by
    funext μ
    apply Fin.ext
    show (((x μ).val + (nn Lt L μ - (d μ).val) * (L μ + 1)) % (Lt μ + 1) + (d μ).val * (L μ + 1)) % (Lt μ + 1) = (x μ).val
    have := tau_inv_left' (x μ).val (Lt μ + 1) (L μ + 1) (nn Lt L μ) (nn Lt L μ - (d μ).val) (mul_nn h μ) (Nat.succ_pos _)
      (nn_pos h μ) (x μ).isLt (Nat.sub_le _ _)
    rwa [Nat.sub_sub_self (le_of_lt (d μ).isLt)] at this

theorem tauS_val {Lt L : PeriodicLatticeExtent} (h : Covers Lt L) (d : DeckIdx Lt L) (x : PeriodicLatticeSite Lt) (μ : Fin 3) :
    (tauS h d x μ).val = ((x μ).val + (d μ).val * (L μ + 1)) % (Lt μ + 1) := rfl

theorem projS_tauS {Lt L : PeriodicLatticeExtent} (h : Covers Lt L) (d : DeckIdx Lt L) (x : PeriodicLatticeSite Lt) :
    projS h (tauS h d x) = projS h x := by
  funext μ
  apply Fin.ext
  rw [projS_val, tauS_val, projS_val]
  rw [Nat.mod_mod_of_dvd _ (h μ), Nat.add_mul_mod_self_right]

theorem projS_surj {Lt L : PeriodicLatticeExtent} (h : Covers Lt L) : Function.Surjective (projS h) := by
  intro y
  obtain ⟨w, hw, -⟩ := exists_lift_site h (fun μ => ⟨0, Nat.succ_pos _⟩) y
  exact ⟨w, hw⟩

theorem site_free {Lt L : PeriodicLatticeExtent} (h : Covers Lt L) (x y : PeriodicLatticeSite Lt)
    (hxy : projS h x = projS h y) : ∃! d : DeckIdx Lt L, tauS h d x = y := by
  have key : ∀ μ : Fin 3, ∃! d : Fin (nn Lt L μ), ((x μ).val + d.val * (L μ + 1)) % (Lt μ + 1) = (y μ).val := by
    intro μ
    have hm : (x μ).val % (L μ + 1) = (y μ).val % (L μ + 1) := by
      have := congrArg Fin.val (congrFun hxy μ); simpa [projS_val] using this
    obtain ⟨d, hd, hdy⟩ := tau_free' (x μ).val (y μ).val (Lt μ + 1) (L μ + 1) (nn Lt L μ) (mul_nn h μ) (Nat.succ_pos _)
      (nn_pos h μ) (x μ).isLt (y μ).isLt hm
    refine ⟨⟨d, hd⟩, hdy, fun d' hd' => ?_⟩
    apply Fin.ext
    exact tau_unique' (x μ).val (Lt μ + 1) (L μ + 1) (nn Lt L μ) d'.val d (mul_nn h μ) (Nat.succ_pos _) (x μ).isLt d'.isLt hd
      (hd'.trans hdy.symm)
  choose dd hdd huniq using key
  refine ⟨dd, ?_, ?_⟩
  · funext μ; exact Fin.ext (hdd μ)
  · intro d' hd'
    funext μ
    apply huniq μ
    have := congrArg Fin.val (congrFun hd' μ)
    exact this

end AdalyFormal.Thin
