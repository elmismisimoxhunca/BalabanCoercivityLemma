import CG6c
import UZ5

/-!
# CG6d -- images and preimages of unions of two adjacent ball-coordinate cells
-/
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option linter.unusedVariables false

namespace AdalyFormal.CoverGeom

open AdalyFormal.Target.ClayStatement AdalyFormal.StatementLane AdalyFormal.StatementLane2
open AdalyFormal.M2Glue3 (Z3 ev iota iota_shift iota_shift2)
open AdalyFormal.UnifLane.Z (cellZ wo cellBox)

variable {L : PeriodicLatticeExtent}

theorem emod_succ (a n : ℤ) : (a % n + 1) % n = (a + 1) % n := by
  rw [Int.add_emod, Int.emod_emod, ← Int.add_emod]

/-- the cell vector `u`: the torus cell indices of the ball-coordinate cell `c`. -/
noncomputable def cellU (s : ℕ) (L : PeriodicLatticeExtent) (c : Z3) (τ : Fin 3) : ℕ :=
  (c τ % (((L τ + 1) / s : ℕ) : ℤ)).toNat

theorem cellU_cast {s : ℕ} {c : Z3} {τ : Fin 3} (hn : 0 < (L τ + 1) / s) :
    ((cellU s L c τ : ℕ) : ℤ) = c τ % (((L τ + 1) / s : ℕ) : ℤ) := by
  unfold cellU
  exact Int.toNat_of_nonneg (Int.emod_nonneg _ (by exact_mod_cast hn.ne'))

theorem cellU_lt {s : ℕ} {c : Z3} {τ : Fin 3} (hn : 0 < (L τ + 1) / s) : cellU s L c τ < (L τ + 1) / s := by
  have h := cellU_cast (s := s) (c := c) hn
  have h2 : c τ % (((L τ + 1) / s : ℕ) : ℤ) < (((L τ + 1) / s : ℕ) : ℤ) := Int.emod_lt_of_pos _ (by exact_mod_cast hn)
  omega

theorem image_cell (w : PeriodicLatticeSite L) {s : ℕ} (hs : 0 < s) (hN : ∀ τ, s ∣ L τ + 1) (hn : ∀ τ, 0 < (L τ + 1) / s)
    {d : Z3} {p : Z3} (hp : ∀ τ, cellZ (s : ℤ) (wo w) p τ = d τ) (τ : Fin 3) :
    (iota w p τ).val / s = cellU s L d τ := by
  have := iota_cell w hs τ (hN τ) p
  rw [hp τ] at this
  rw [← cellU_cast (s := s) (c := d) (hn τ)] at this
  exact_mod_cast this

theorem image_cell_succ (w : PeriodicLatticeSite L) {s : ℕ} (hs : 0 < s) (hN : ∀ τ, s ∣ L τ + 1) (hn : ∀ τ, 0 < (L τ + 1) / s)
    {c c' : Z3} (τ : Fin 3) (h : c' τ = c τ + 1) :
    cellU s L c' τ = (cellU s L c τ + 1) % ((L τ + 1) / s) := by
  have h1 := cellU_cast (s := s) (c := c) (hn τ)
  have h2 := cellU_cast (s := s) (c := c') (hn τ)
  generalize (L τ + 1) / s = n at h1 h2 ⊢
  generalize cellU s L c τ = a at h1 ⊢
  generalize cellU s L c' τ = b at h2 ⊢
  have : (b : ℤ) = (((a + 1) % n : ℕ) : ℤ) := by
    rw [h2, h, Int.natCast_mod, Int.natCast_add, Nat.cast_one, h1, emod_succ]
  exact_mod_cast this


theorem succ_of_ne {c c' : Z3} (hcc' : c' = c ∨ ∃ μ, c' = c + ev μ) {τ : Fin 3} (h : c' τ ≠ c τ) : c' τ = c τ + 1 := by
  rcases hcc' with rfl | ⟨μ, rfl⟩
  · exact absurd rfl h
  · by_cases hτ : τ = μ
    · subst hτ; simp [ev]
    · exfalso; apply h; simp [ev, hτ]

theorem region_image (w : PeriodicLatticeSite L) {s : ℕ} (hs : 0 < s) (hN : ∀ τ, s ∣ L τ + 1) (hn : ∀ τ, 0 < (L τ + 1) / s)
    {c c' : Z3} (hcc' : c' = c ∨ ∃ μ, c' = c + ev μ) {p : Z3}
    (hp : p ∈ cellBox (s : ℤ) (wo w) c ∪ cellBox (s : ℤ) (wo w) c') :
    iota w p ∈ CellReg s (fun τ => (L τ + 1) / s) (cellU s L c) (fun τ => c' τ ≠ c τ) := by
  intro τ
  rcases hp with hp | hp
  · exact Or.inl (image_cell w hs hN hn hp τ)
  · by_cases h : c' τ = c τ
    · left
      have := image_cell w hs hN hn hp τ
      rw [this]; unfold cellU; rw [h]
    · right
      refine ⟨h, ?_⟩
      rw [image_cell w hs hN hn hp τ]
      exact image_cell_succ w hs hN hn τ (succ_of_ne hcc' h)

theorem region_preimage (w : PeriodicLatticeSite L) {s : ℕ} (hs : 0 < s) (hN : ∀ τ, s ∣ L τ + 1) (hn : ∀ τ, 0 < (L τ + 1) / s)
    {c c' : Z3} (hcc' : c' = c ∨ ∃ μ, c' = c + ev μ) {y : PeriodicLatticeSite L}
    (hy : y ∈ CellReg s (fun τ => (L τ + 1) / s) (cellU s L c) (fun τ => c' τ ≠ c τ)) :
    ∃ p, p ∈ cellBox (s : ℤ) (wo w) c ∪ cellBox (s : ℤ) (wo w) c' ∧ iota w p = y := by
  classical
  -- the cell vector
  let d : Z3 := fun τ => if (y τ).val / s = cellU s L c τ then c τ else c' τ
  have hdc : ∀ τ, (y τ).val / s = cellU s L c τ → d τ = c τ := fun τ h => by simp [d, h]
  have hdc' : ∀ τ, ¬ (y τ).val / s = cellU s L c τ → d τ = c' τ := fun τ h => by simp [d, h]
  have hd : ∀ τ, ((y τ).val / s : ℕ) = cellU s L d τ := by
    intro τ
    by_cases h : (y τ).val / s = cellU s L c τ
    · rw [h]; unfold cellU; rw [hdc τ h]
    · rcases hy τ with h' | ⟨hne, h'⟩
      · exact absurd h' h
      · rw [h']
        have e := image_cell_succ w hs hN hn τ (succ_of_ne hcc' hne)
        have e2 : cellU s L d τ = cellU s L c' τ := by unfold cellU; rw [hdc' τ h]
        rw [e2]; exact e.symm
  have hax : ∀ τ, ∃ a : ℤ, (a + (w τ).val) / (s : ℤ) = d τ ∧ (((w τ).val : ℤ) + a) % ((L τ + 1 : ℕ) : ℤ) = (y τ).val := by
    intro τ
    obtain ⟨n, hn'⟩ := hN τ
    have hnn : (L τ + 1) / s = n := by
      rw [hn']; exact Nat.mul_div_cancel_left _ hs
    refine axis_preimage (s := s) (n := n) (N := L τ + 1) (v := (y τ).val) (o := (w τ).val) (d := d τ) hs hn' ?_ (y τ).isLt ?_
    · have := hn τ; rw [hnn] at this; exact this
    · rw [hd τ, cellU_cast (hn τ), hnn]
  choose a ha using hax
  have hp : ∀ τ, cellZ (s : ℤ) (wo w) a τ = d τ := fun τ => (ha τ).1
  have hmem : a ∈ cellBox (s : ℤ) (wo w) c ∪ cellBox (s : ℤ) (wo w) c' := by
    by_cases hall : ∀ τ, (y τ).val / s = cellU s L c τ
    · left; intro τ; rw [hp τ]; exact hdc τ (hall τ)
    · right
      have hex : ∃ τ0, ¬ (y τ0).val / s = cellU s L c τ0 := by
        by_contra hh; exact hall (fun τ => by by_contra h2; exact hh ⟨τ, h2⟩)
      obtain ⟨τ0, hτ0⟩ := hex
      have hne : c' τ0 ≠ c τ0 := by
        intro heq
        rcases hy τ0 with h' | ⟨hne, -⟩
        · exact hτ0 h'
        · exact hne heq
      rcases hcc' with rfl | ⟨μ, rfl⟩
      · exact absurd rfl hne
      · have hτ0μ : τ0 = μ := by
          by_contra hh; apply hne; simp [ev, hh]
        intro τ
        rw [hp τ]
        by_cases h : (y τ).val / s = cellU s L c τ
        · rw [hdc τ h]
          have hτμ : τ ≠ μ := by
            intro hh; subst hh; subst hτ0μ; exact hτ0 h
          simp [ev, hτμ]
        · exact hdc' τ h
  refine ⟨a, hmem, ?_⟩
  funext τ
  apply Fin.ext
  have := AdalyFormal.M2GlueGeo.iota_val_int w a τ
  rw [(ha τ).2] at this
  exact_mod_cast this

end AdalyFormal.CoverGeom
