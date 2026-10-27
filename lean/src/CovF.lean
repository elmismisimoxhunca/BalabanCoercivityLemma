import CovA

/-!
# CovF -- away from `Ω_kᶜ` every `ddA` stencil lies in one index-`k` class cube (m2_coverage, 2026-10-14)

`near_clause3` : for any admissible tower (`36 ≤ R·ell`) and any fine site `x` whose fine ℓ¹-ball of radius
`36·M·ell^k` lies in `Ω_k`, there is ONE class cube of index `k` (factor `12`) that contains every `CurlReads` of the `ddA`
stencils at `x` in all three directions: clause 3 of `PerCubeRegular2` applies at `x`.
So the sites where the printed class gives no `ddA` bound (CovC) lie within fine distance `36·M·ell^k` of `Ω_kᶜ`.
-/
set_option autoImplicit false
set_option maxHeartbeats 16000000

namespace AdalyFormal.M2Coverage

open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane AdalyFormal.StatementLane2
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.M2Bridge (cube_isClass pdist_lt_three_s')
open AdalyFormal.Balaban.CovariantHjMinimizer (periodicLatticeShiftBack periodicLatticeShift_shiftBack)

variable {L : PeriodicLatticeExtent}

/-- `w` is within one step of `x` in every coordinate. -/
def Near1 (x w : PeriodicLatticeSite L) : Prop := ∀ σ, w σ = x σ ∨ w σ = x σ + 1 ∨ w σ = x σ - 1

theorem near1_self (x : PeriodicLatticeSite L) : Near1 x x := fun _ => Or.inl rfl

theorem shift_apply (x : PeriodicLatticeSite L) (μ σ : Fin 3) :
    periodicLatticeShift x μ σ = if σ = μ then x σ + 1 else x σ := by
  unfold periodicLatticeShift
  by_cases h : σ = μ
  · subst h; rw [Function.update_self, if_pos rfl]
  · rw [Function.update_of_ne h, if_neg h]

theorem back_apply (x : PeriodicLatticeSite L) (μ σ : Fin 3) :
    periodicLatticeShiftBack x μ σ = if σ = μ then x σ - 1 else x σ := by
  unfold periodicLatticeShiftBack
  by_cases h : σ = μ
  · subst h; rw [Function.update_self, if_pos rfl]
  · rw [Function.update_of_ne h, if_neg h]

theorem near1_shift (x : PeriodicLatticeSite L) (μ : Fin 3) : Near1 x (periodicLatticeShift x μ) := by
  intro σ; rw [shift_apply]; split_ifs
  · exact Or.inr (Or.inl rfl)
  · exact Or.inl rfl

theorem near1_back (x : PeriodicLatticeSite L) (μ : Fin 3) : Near1 x (periodicLatticeShiftBack x μ) := by
  intro σ; rw [back_apply]; split_ifs
  · exact Or.inr (Or.inr rfl)
  · exact Or.inl rfl

theorem near1_shift_shift (x : PeriodicLatticeSite L) {μ ν : Fin 3} (h : μ ≠ ν) :
    Near1 x (periodicLatticeShift (periodicLatticeShift x ν) μ) := by
  intro σ; rw [shift_apply, shift_apply]; split_ifs with h1 h2
  · exact absurd (h1.symm.trans h2) h
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inl rfl)
  · exact Or.inl rfl

theorem near1_shift_back (x : PeriodicLatticeSite L) {μ ν : Fin 3} (h : μ ≠ ν) :
    Near1 x (periodicLatticeShift (periodicLatticeShiftBack x ν) μ) := by
  intro σ; rw [shift_apply, back_apply]; split_ifs with h1 h2
  · exact absurd (h1.symm.trans h2) h
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr rfl)
  · exact Or.inl rfl

theorem val_succ (n : ℕ) (a : Fin (n + 1)) : (a + 1).val = (a.val + 1) % (n + 1) := by
  rw [Fin.val_add_one]
  split_ifs with h
  · rw [h, Fin.val_last, Nat.mod_self]
  · have : a.val ≠ n := fun h2 => h (Fin.ext (by rw [h2, Fin.val_last]))
    have := a.isLt
    rw [Nat.mod_eq_of_lt (by omega)]

/-- one coordinate: the blocks of `x - 1, x, x + 1` lie in the 12-block window starting one block before `x`'s block. -/
theorem win_near {n B N : ℕ} (hB : 0 < B) (hT : n + 1 = N * B) (X : Fin (n + 1)) :
    ∃ b : ℕ, b < N ∧ ∀ W : Fin (n + 1), (W = X ∨ W = X + 1 ∨ W = X - 1) →
      (W.val + N * B - B * b) % (N * B) < 12 * B := by
  have hN : 0 < N := by
    rcases Nat.eq_zero_or_pos N with h | h
    · subst h; simp at hT
    · exact h
  have hXl : X.val < N * B := hT ▸ X.isLt
  obtain ⟨bx, hbx⟩ : ∃ bx, bx = X.val / B := ⟨_, rfl⟩
  have hbxl : bx < N := hbx ▸ blk_lt B N _ hB hXl
  refine ⟨(bx + N - 1) % N, Nat.mod_lt _ hN, fun W hW => ?_⟩
  have hWl : W.val < N * B := hT ▸ W.isLt
  rw [modK B N _ _ 12 hB hWl (Nat.mod_lt _ hN)]
  by_cases hsm : N ≤ 12
  · unfold inB; exact lt_of_lt_of_le (Nat.mod_lt _ hN) hsm
  push Not at hsm
  have hbmod : (bx + N - 1) % N = if bx = 0 then N - 1 else bx - 1 := by
    split_ifs with h0
    · rw [h0, Nat.zero_add, Nat.mod_eq_of_lt (by omega)]
    · rw [show bx + N - 1 = (bx - 1) + N by omega, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
  have hbl : (bx + N - 1) % N < N := Nat.mod_lt _ hN
  have hWb : W.val / B < N := blk_lt B N _ hB hWl
  have hsucc : ∀ t, t < N → (t + 1) % N = if t + 1 < N then t + 1 else 0 := by
    intro t ht
    split_ifs with h
    · exact Nat.mod_eq_of_lt h
    · rw [show t + 1 = N by omega, Nat.mod_self]
  -- the block of `W`: `bx`, the next block, or the previous block
  have hblk : W.val / B = bx ∨ W.val / B = (bx + 1) % N ∨ bx = (W.val / B + 1) % N := by
    rcases hW with rfl | rfl | rfl
    · left; exact hbx.symm
    · have hv : (X + 1).val = (X.val + 1) % (N * B) := by
        rw [val_succ]; exact congrArg (fun m => (X.val + 1) % m) hT
      rw [hv]
      rcases shift_blk B N X.val hB hXl with h | h
      · left; rw [h, hbx]
      · right; left; rw [h, hbx]
    · have hv2 : X.val = ((X - 1).val + 1) % (N * B) := by rw [← hT, ← val_succ, sub_add_cancel]
      have hl' : (X - 1).val < N * B := hT ▸ (X - 1).isLt
      rcases shift_blk B N (X - 1).val hB hl' with h | h
      · left; rw [hbx, hv2, h]
      · right; right; rw [hbx, hv2, h]
  have h1 := hsucc bx hbxl
  have h2 := hsucc (W.val / B) hWb
  rw [inB_iff hWb hbl, hbmod]
  generalize W.val / B = bW at hblk h1 h2 hWb ⊢
  generalize (bx + 1) % N = s1 at hblk h1
  generalize (bW + 1) % N = s2 at hblk h2
  split_ifs at h1 h2 ⊢ <;> omega

/-- a box of side `12 B` (grid corner) containing the one-step neighbourhood of `x`. -/
theorem near_box {B : ℕ} (hB : 0 < B) (hdvd : ∀ σ, B ∣ L σ + 1) (x : PeriodicLatticeSite L) :
    ∃ z : PeriodicLatticeSite L, GridCorner B z ∧ ∀ w, Near1 x w → w ∈ siteBox z (12 * B) := by
  have hT : ∀ σ, L σ + 1 = ((L σ + 1) / B) * B := fun σ => (Nat.div_mul_cancel (hdvd σ)).symm
  have hw := fun σ => win_near hB (hT σ) (x σ)
  choose b hb hwin using hw
  have hzl : ∀ σ, B * b σ < L σ + 1 := fun σ => by
    have := Nat.mul_lt_mul_of_pos_left (hb σ) hB
    rw [hT σ, mul_comm ((L σ + 1) / B) B]; exact this
  refine ⟨fun σ => ⟨B * b σ, hzl σ⟩, fun σ => Nat.mul_mod_right _ _, fun w hnear => ?_⟩
  intro σ
  show ((w σ).val + (L σ + 1) - B * b σ) % (L σ + 1) < 12 * B
  have := hwin σ (w σ) (hnear σ)
  rw [← hT σ] at this
  exact this

theorem near1_back_shift_shift (x : PeriodicLatticeSite L) {μ ν : Fin 3} (h : μ ≠ ν) :
    Near1 x (periodicLatticeShift (periodicLatticeShift (periodicLatticeShiftBack x ν) μ) ν) := by
  intro σ; rw [shift_apply, shift_apply, back_apply]
  by_cases h1 : σ = ν
  · have h2 : σ ≠ μ := fun h2 => h (h2.symm.trans h1)
    rw [if_pos h1, if_neg h2, if_pos h1, sub_add_cancel]; exact Or.inl rfl
  · rw [if_neg h1, if_neg h1]
    split_ifs
    · exact Or.inr (Or.inl rfl)
    · exact Or.inl rfl

/-- **near `Ω_k`'s interior every `ddA` stencil is in one index-`k` class cube** (clause 3 applies). -/
theorem near_clause3 {ell M R k : ℕ} {S : Tower L} (hS : Admissible ell M R k S) (hR : 3 * 12 ≤ R * ell)
    (hB : 0 < bigSide M ell k) (x : PeriodicLatticeSite L)
    (hx : ∀ w, pdist x w < 36 * bigSide M ell k → w ∈ S.Om k) :
    ∃ sites : Set (PeriodicLatticeSite L), IsClassCube ell M 12 k S sites k ∧
      ∀ μ ν : Fin 3, ν ≠ μ → CurlReads sites (periodicLatticeShiftBack x ν) ν μ ∧ CurlReads sites x ν μ := by
  obtain ⟨z, hgrid, hbox⟩ := near_box hB (fun σ => hS.2.2.1 k le_rfl σ) x
  have hxb : x ∈ siteBox z (12 * bigSide M ell k) := hbox x (near1_self x)
  have hsub : siteBox z (12 * bigSide M ell k) ⊆ S.Om k := by
    intro w hw
    apply hx
    have := pdist_lt_three_s' hxb hw
    omega
  have hx0 : x ∈ S.Om k := hx x (by
    have : pdist x x = 0 := by unfold pdist pcd; simp
    omega)
  have hxt : x ∈ towerBj S k := ⟨hx0, by rw [hS.2.1 (k + 1) (by omega)]; exact fun h => h⟩
  refine ⟨siteBox z (12 * bigSide M ell k), cube_isClass hS le_rfl hgrid hsub hxb hxt hR, fun μ ν hνμ => ?_⟩
  have hμν : μ ≠ ν := fun h => hνμ h.symm
  have m := fun w (h : Near1 x w) => hbox w h
  have e1 : periodicLatticeShift (periodicLatticeShiftBack x ν) ν = x := periodicLatticeShift_shiftBack x ν
  refine ⟨⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩, ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩⟩
  · show periodicLatticeShift (periodicLatticeShiftBack x ν) ν ∈ _; rw [e1]; exact m _ (near1_self x)
  · show periodicLatticeShift (periodicLatticeShift (periodicLatticeShiftBack x ν) ν) μ ∈ _
    rw [e1]; exact m _ (near1_shift x μ)
  · exact m _ (near1_back x ν)
  · exact m _ (near1_shift_back x hμν)
  · exact m _ (near1_shift_back x hμν)
  · exact m _ (near1_back_shift_shift x hμν)
  · exact m _ (near1_back x ν)
  · show periodicLatticeShift (periodicLatticeShiftBack x ν) ν ∈ _; rw [e1]; exact m _ (near1_self x)
  · exact m _ (near1_shift x ν)
  · exact m _ (near1_shift_shift x hμν)
  · exact m _ (near1_self x)
  · exact m _ (near1_shift x μ)
  · exact m _ (near1_shift x μ)
  · exact m _ (near1_shift_shift x (fun h => hμν h.symm))
  · exact m _ (near1_self x)
  · exact m _ (near1_shift x ν)

end AdalyFormal.M2Coverage
