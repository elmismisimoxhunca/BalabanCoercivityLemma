import NB15
/-!
# NB16 -- the identity's ladder plaquettes lie in the box (piece N2, part 6)

No sorry / native_decide / axioms.
-/
set_option autoImplicit false
noncomputable section
namespace AdalyFormal.CurvBlock
open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.CoarseCurl (coarseShift)
open AdalyFormal.Balaban.QjComposite (stepBlockOf)

variable {L : PeriodicLatticeExtent}

theorem mem_rungPlaqs (s : ℕ) (ν μ : Fin 3) : ∀ (n : ℕ) (z : PeriodicLatticeSite L) (t : PlaqT L),
    t ∈ rungPlaqs s ν μ z n → ∃ j < n, t = (coarseShift z (s * j) μ, ν, μ) := by
  intro n
  induction n with
  | zero => intro z t ht; simp [rungPlaqs] at ht
  | succ k ih =>
      intro z t ht
      rcases List.mem_cons.mp ht with h | h
      · exact ⟨0, by omega, by rw [h]; rfl⟩
      · obtain ⟨j, hj, rfl⟩ := ih _ t h
        exact ⟨j + 1, by omega, by rw [Nat.mul_succ, shift_add]⟩

theorem mem_ladPlaqs_rep (s : ℕ) (ν μ : Fin 3) (n : ℕ) : ∀ (n' : ℕ) (x : PeriodicLatticeSite L)
    (t : PlaqT L), t ∈ ladPlaqs s μ n x (List.replicate n' ν) →
      ∃ i < n', ∃ j < n, t = (coarseShift (coarseShift x (s * i) ν) (s * j) μ, ν, μ) := by
  intro n'
  induction n' with
  | zero => intro x t ht; simp [ladPlaqs] at ht
  | succ k ih =>
      intro x t ht
      rw [List.replicate_succ] at ht
      rcases List.mem_append.mp ht with h | h
      · obtain ⟨j, hj, rfl⟩ := mem_rungPlaqs s ν μ n x t h
        exact ⟨0, by omega, j, hj, rfl⟩
      · obtain ⟨i, hi, j, hj, rfl⟩ := ih _ t h
        exact ⟨i + 1, by omega, j, hj, by rw [Nat.mul_succ, shift_add]⟩

/-- For `ν ≠ μ`, the four bond bases of every plaquette of the identity's ladders are in the box. -/
theorem ladder_box (s ell : ℕ) (y : PeriodicLatticeSite L) (ν μ : Fin 3) (hνμ : ν ≠ μ)
    (hN : ∀ ρ, 2 * (s * ell) < L ρ + 1)
    (hfit : ∀ σ, (y σ).val + s * ell ≤ L σ + 1)
    (x : PeriodicLatticeSite L) (hx : x ∈ stepBlockOf y s ell)
    (t : PlaqT L) (ht : t ∈ ladPlaqs s μ ell x (List.replicate ell ν)) :
    Box y s (2 * (s * ell) - s) t.1 ∧ Box y s (2 * (s * ell) - s) (coarseShift t.1 s t.2.1) ∧
    Box y s (2 * (s * ell) - s) (coarseShift t.1 s t.2.2) := by
  obtain ⟨i, hi, j, hj, rfl⟩ := mem_ladPlaqs_rep s ν μ ell ell x t ht
  have hxo := block_offsets s ell y x hfit hx
  have hoff : ∀ σ, off y x σ = off y x σ := fun _ => rfl
  have hxy : ∀ σ, off y x σ = off y x σ := hoff
  -- offsets of x from y are block offsets (y is the base)
  have hsi : s * i + s ≤ s * ell := by
    have := Nat.mul_le_mul_left s (Nat.succ_le_of_lt hi); rwa [Nat.mul_succ] at this
  have hsj : s * j + s ≤ s * ell := by
    have := Nat.mul_le_mul_left s (Nat.succ_le_of_lt hj); rwa [Nat.mul_succ] at this
  set B := 2 * (s * ell) - s
  have hxB : Box y s B x := fun σ => ⟨(hxo σ).1, by have := (hxo σ).2; omega⟩
  have h1 : Box y s B (coarseShift x (s * i) ν) :=
    box_shift y x s B i ν hxB (by have := (hxo ν).2; omega) (by have := hN ν; omega)
  have o1 : off y (coarseShift x (s * i) ν) μ = off y x μ := off_shift_ne _ _ _ (Ne.symm hνμ)
  have o1' : off y (coarseShift x (s * i) ν) ν = off y x ν + s * i :=
    off_shift_val _ _ _ _ (by have := (hxo ν).2; have := hN ν; omega)
  have h2 : Box y s B (coarseShift (coarseShift x (s * i) ν) (s * j) μ) :=
    box_shift y _ s B j μ h1 (by rw [o1]; have := (hxo μ).2; omega) (by have := hN μ; omega)
  have o2ν : off y (coarseShift (coarseShift x (s * i) ν) (s * j) μ) ν = off y x ν + s * i := by
    rw [off_shift_ne _ _ _ hνμ, o1']
  have o2μ : off y (coarseShift (coarseShift x (s * i) ν) (s * j) μ) μ = off y x μ + s * j := by
    rw [off_shift_val _ _ _ _ (by rw [o1]; have := (hxo μ).2; have := hN μ; omega), o1]
  refine ⟨h2, ?_, ?_⟩
  · have := box_shift y _ s B 1 ν h2 (by rw [o2ν]; have := (hxo ν).2; omega) (by have := hN ν; omega)
    rwa [Nat.mul_one] at this
  · have := box_shift y _ s B 1 μ h2 (by rw [o2μ]; have := (hxo μ).2; omega) (by have := hN μ; omega)
    rwa [Nat.mul_one] at this

end AdalyFormal.CurvBlock

#print axioms AdalyFormal.CurvBlock.ladder_box
