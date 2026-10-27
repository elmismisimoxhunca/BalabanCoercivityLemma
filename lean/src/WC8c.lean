import M2B8

/-!
# WC8c -- ball-in-a-class-cube geometry (M2 W6 lane): a grid `12·B`-box around any ball of radius `≤ 5B`

* `win_ball` : one coordinate, the cyclic window of `12 B` starting `5` blocks before the block of `X` contains every `W` with `pcd ≤ r ≤ 5B`.
* `box_ball`  : there is a grid corner `z` with `Ball x r ⊆ siteBox z (12 B)` for `r ≤ 5 B`.
No sorry / native_decide / axiom.
-/
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 8000

namespace AdalyFormal.M2W6

open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane (Tower Admissible scaleUp pdist pcd siteBox GridCorner bigSide)
open AdalyFormal.StatementLaneR8 (Ball)

theorem mod_cases (V T : ℕ) (hT : 0 < T) (hV : V < 3 * T) :
    (V < T ∧ V % T = V) ∨ (T ≤ V ∧ V < 2 * T ∧ V % T = V - T) ∨ (2 * T ≤ V ∧ V % T = V - 2 * T) := by
  have h := Nat.mod_add_div V T
  have hr : V % T < T := Nat.mod_lt _ hT
  obtain ⟨q, hq⟩ : ∃ q, q = V / T := ⟨_, rfl⟩
  obtain ⟨r, hrr⟩ : ∃ r, r = V % T := ⟨_, rfl⟩
  rw [← hq, ← hrr] at h
  rw [← hrr] at hr
  have hq3 : q < 3 := by
    by_contra hc
    push Not at hc
    have : T * 3 ≤ T * q := Nat.mul_le_mul_left T hc
    omega
  rw [← hrr]
  rcases (by omega : q = 0 ∨ q = 1 ∨ q = 2) with rfl | rfl | rfl
  · left; omega
  · right; left; omega
  · right; right; omega

/-- one coordinate -/
theorem win_ball {n B N r : ℕ} (hB : 0 < B) (hT : n + 1 = N * B) (hr : r ≤ 5 * B) (X : Fin (n + 1)) :
    ∃ b : ℕ, b < N ∧ ∀ W : Fin (n + 1), pcd (n + 1) X.val W.val ≤ r →
      (W.val + N * B - B * b) % (N * B) < 12 * B := by
  have hN : 0 < N := by
    rcases Nat.eq_zero_or_pos N with h | h
    · subst h; simp at hT
    · exact h
  have hTpos : 0 < N * B := Nat.mul_pos hN hB
  by_cases hsm : N * B ≤ 12 * B
  · exact ⟨0, hN, fun W _ => lt_of_lt_of_le (Nat.mod_lt _ hTpos) hsm⟩
  push Not at hsm
  have hX : X.val < N * B := hT ▸ X.isLt
  have hN12 : 12 < N := by
    by_contra hc
    push Not at hc
    have := Nat.mul_le_mul_right B hc
    omega
  obtain ⟨bx, o, hXo, ho⟩ : ∃ bx o, X.val = B * bx + o ∧ o < B :=
    ⟨X.val / B, X.val % B, (Nat.div_add_mod _ _).symm, Nat.mod_lt _ hB⟩
  have hbx : bx < N := by
    by_contra hc
    push Not at hc
    have : N * B ≤ B * bx := by rw [mul_comm]; exact Nat.mul_le_mul_left B hc
    omega
  by_cases h5 : 5 ≤ bx
  · obtain ⟨b, rfl⟩ : ∃ b, bx = b + 5 := ⟨bx - 5, by omega⟩
    have e : B * (b + 5) = B * b + 5 * B := by ring
    refine ⟨b, by omega, fun W hW => ?_⟩
    have hWl : W.val < N * B := hT ▸ W.isLt
    have hM := mod_cases (W.val + N * B - B * b) (N * B) hTpos (by omega)
    have hbN : B * b ≤ N * B := by omega
    unfold pcd at hW
    split_ifs at hW <;> omega
  · push Not at h5
    have e : B * (bx + N - 5) + 5 * B = B * bx + N * B := by
      have h1 : B * (bx + N - 5) + 5 * B = B * (bx + N - 5 + 5) := by ring
      rw [h1, show bx + N - 5 + 5 = bx + N by omega]; ring
    have hbN : bx + N - 5 < N := by omega
    refine ⟨bx + N - 5, hbN, fun W hW => ?_⟩
    have hWl : W.val < N * B := hT ▸ W.isLt
    have hlt : B * (bx + N - 5) < N * B := by
      rw [mul_comm]; exact Nat.mul_lt_mul_of_pos_right hbN hB
    have hM := mod_cases (W.val + N * B - B * (bx + N - 5)) (N * B) hTpos (by omega)
    unfold pcd at hW
    split_ifs at hW <;> omega

/-- a grid `12 B`-box around the ball of radius `r ≤ 5 B` -/
theorem box_ball {L : PeriodicLatticeExtent} {B : ℕ} (hB : 0 < B) (hdvd : ∀ σ, B ∣ L σ + 1)
    (x : PeriodicLatticeSite L) {r : ℕ} (hr : r ≤ 5 * B) :
    ∃ z : PeriodicLatticeSite L, GridCorner B z ∧ Ball x r ⊆ siteBox z (12 * B) := by
  have hT : ∀ σ, L σ + 1 = ((L σ + 1) / B) * B := fun σ => (Nat.div_mul_cancel (hdvd σ)).symm
  have hw := fun σ => win_ball (r := r) hB (hT σ) hr (x σ)
  choose b hb hwin using hw
  have hzl : ∀ σ, B * b σ < L σ + 1 := fun σ => by
    have := Nat.mul_lt_mul_of_pos_left (hb σ) hB
    rw [hT σ, mul_comm ((L σ + 1) / B) B]; exact this
  refine ⟨fun σ => ⟨B * b σ, hzl σ⟩, fun σ => Nat.mul_mod_right _ _, fun w hw' => ?_⟩
  intro σ
  show ((w σ).val + (L σ + 1) - B * b σ) % (L σ + 1) < 12 * B
  have hp : pcd (L σ + 1) (x σ).val (w σ).val ≤ r := by
    have h0 : pdist x w ≤ r := hw'
    refine le_trans ?_ h0
    unfold pdist
    exact Finset.single_le_sum (f := fun μ : Fin 3 => pcd (L μ + 1) (x μ).val (w μ).val)
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ σ)
  have := hwin σ (w σ) hp
  rw [← hT σ] at this
  exact this

end AdalyFormal.M2W6

#print axioms AdalyFormal.M2W6.mod_cases
#print axioms AdalyFormal.M2W6.win_ball
#print axioms AdalyFormal.M2W6.box_ball
