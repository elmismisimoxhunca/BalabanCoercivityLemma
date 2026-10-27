import NB21
/-!
# NB22 -- LOCAL corner-gauge link bound: only plaquettes in the box enter

`axial_link_loc`: as `axial_link`, but the plaquette hypothesis is only required at `s`-aligned sites in
`Box y s B` (`x` itself in `Box y s B`).

No sorry / native_decide / axioms.
-/
set_option autoImplicit false
noncomputable section
namespace AdalyFormal.CurvBlock
open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.SuTwoLogExp (SU2)
open AdalyFormal.Balaban.CoarseCurl (coarseShift)
open AdalyFormal.Balaban.TowerLawCov (coarseGammaPath coarsePathEndpoint)
open AdalyFormal.Balaban.QjComposite (coarseGaugeTransform coarsePathEndpoint_append)
open AdalyFormal.Balaban.AdmissibleSubspace (CoarseLattice)

variable {L : PeriodicLatticeExtent}

/-- The plaquettes of a unit-rung ladder sit at the bases of the path's bonds. -/
theorem ladPlaqs_one_base (s : ℕ) (μ : Fin 3) : ∀ (p : List (Fin 3)) (z : PeriodicLatticeSite L)
    (t : PlaqT L), t ∈ ladPlaqs s μ 1 z p → ∃ b ∈ pathBonds s z p, t.1 = b.1 := by
  intro p
  induction p with
  | nil => intro z t ht; simp [ladPlaqs] at ht
  | cons ν rest ih =>
      intro z t ht
      rcases List.mem_append.mp ht with h | h
      · simp only [rungPlaqs, List.mem_cons, List.not_mem_nil, or_false] at h
        exact ⟨(z, ν), List.mem_cons_self .., by rw [h]⟩
      · obtain ⟨b, hb, hbt⟩ := ih _ t h
        exact ⟨b, List.mem_cons_of_mem _ hb, hbt⟩

theorem axial_link_loc (s : ℕ) (hs : 0 < s) (V : PeriodicLinkConfiguration SU2 L)
    (y : PeriodicLatticeSite L) (hy : y ∈ CoarseLattice L s) (hdvd : ∀ ρ, s ∣ L ρ + 1)
    (B : ℕ) (hB : ∀ ρ, B < L ρ + 1) (P : ℝ) (hP0 : 0 ≤ P)
    (hP : ∀ z ∈ CoarseLattice L s, Box y s B z → ∀ ν μ : Fin 3, dv (pw s V z ν μ) ≤ P)
    (x : PeriodicLatticeSite L) (ρ : Fin 3) (hx : Box y s B x)
    (hnw : off y x ρ + s < L ρ + 1) :
    dv (coarseGaugeTransform s (cornerGauge s V y) V (x, ρ))
      ≤ (((off y x 0 / s : ℕ) : ℝ) + ((off y x 1 / s : ℕ) : ℝ)) * P := by
  have hal : ∀ σ, s ∣ off y x σ := fun σ => (hx σ).1
  have ha0 : (0 : ℝ) ≤ ((off y x 0 / s : ℕ) : ℝ) := Nat.cast_nonneg _
  have ha1 : (0 : ℝ) ≤ ((off y x 1 / s : ℕ) : ℝ) := Nat.cast_nonneg _
  have hmul : ∀ σ, s * (off y x σ / s) = off y x σ := fun σ => Nat.mul_div_cancel' (hal σ)
  -- every bond base of the staircase y → x is in the box
  have hy0 : Box y s B y := fun σ => by rw [off_self]; exact ⟨dvd_zero s, Nat.zero_le _⟩
  have hstair : ∀ b ∈ pathBonds s y (coarseGammaPath s y x), Box y s B b.1 := by
    rw [gamma_eq]
    refine box_stair y y s B _ _ _ hy0 ?_ ?_ ?_ hB
    · rw [off_self, hmul]; simpa using (hx 2).2
    · rw [off_self, hmul]; simpa using (hx 1).2
    · rw [off_self, hmul]; simpa using (hx 0).2
  have hstair' : ∀ b ∈ pathBonds s y (List.replicate (off y x 2 / s) 2 ++
      (List.replicate (off y x 1 / s) 1 ++ List.replicate (off y x 0 / s) 0)), Box y s B b.1 := by
    rw [← gamma_eq]; exact hstair
  have hz : coarseShift y (s * (off y x 2 / s)) 2 ∈ CoarseLattice L s :=
    shift_mul_aligned s hdvd 2 _ y hy
  have hz1 : coarseShift (coarseShift y (s * (off y x 2 / s)) 2) (s * (off y x 1 / s)) 1
      ∈ CoarseLattice L s := shift_mul_aligned s hdvd 1 _ _ hz
  show dv (cornerGauge s V y x * V (x, ρ) * (cornerGauge s V y (coarseShift x s ρ))⁻¹) ≤ _
  fin_cases ρ
  · show dv (cornerGauge s V y x * V (x, 0) * (cornerGauge s V y (coarseShift x s 0))⁻¹) ≤ _
    rw [axial0 s hs V y x hal hnw, dv_one]; positivity
  · show dv (cornerGauge s V y x * V (x, 1) * (cornerGauge s V y (coarseShift x s 1))⁻¹) ≤ _
    obtain ⟨g, hg⟩ := axial1 s hs V y x hal hnw
    rw [hg, dv_conj]
    have hl := ladS_le s V 1 1 P (List.replicate (off y x 0 / s) 0) _ (fun t ht => by
      obtain ⟨b, hb, hbt⟩ := ladPlaqs_one_base s 1 _ _ t ht
      have hbB : Box y s B b.1 := hstair' b (by
        rw [pathBonds_append, pathBonds_append, endpoint_rep, endpoint_rep]
        exact List.mem_append_right _ (List.mem_append_right _ hb))
      rw [hbt]
      exact hP b.1 (pathBonds_aligned s hdvd _ _ hz1 b hb) hbB _ _)
    rw [List.length_replicate] at hl
    push_cast at hl ⊢
    nlinarith
  · show dv (cornerGauge s V y x * V (x, 2) * (cornerGauge s V y (coarseShift x s 2))⁻¹) ≤ _
    obtain ⟨g, hg⟩ := axial2 s hs V y x hal hnw
    rw [hg, dv_conj]
    have hl := ladS_le s V 2 1 P
      (List.replicate (off y x 1 / s) 1 ++ List.replicate (off y x 0 / s) 0) _ (fun t ht => by
      obtain ⟨b, hb, hbt⟩ := ladPlaqs_one_base s 2 _ _ t ht
      have hbB : Box y s B b.1 := hstair' b (by
        rw [pathBonds_append, endpoint_rep]
        exact List.mem_append_right _ hb)
      rw [hbt]
      exact hP b.1 (pathBonds_aligned s hdvd _ _ hz b hb) hbB _ _)
    rw [List.length_append, List.length_replicate, List.length_replicate] at hl
    push_cast at hl ⊢
    nlinarith

end AdalyFormal.CurvBlock

#print axioms AdalyFormal.CurvBlock.axial_link_loc
