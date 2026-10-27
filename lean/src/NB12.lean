import NB11
/-!
# NB12 -- `axial_link`: link defects in the corner gauge are bounded by curvature (piece N2)

`dv (γ_y(x) V(x,ρ) γ_y(x + s e_ρ)⁻¹) ≤ (off_0(x)/s + off_1(x)/s) · P` under: `y` `s`-aligned, `s ∣ N`,
offsets of `x` from `y` multiples of `s`, no wrap `off_ρ(x) + s < N_ρ`, all `s`-aligned stride-`s`
plaquettes have defect `≤ P`.  (`γ_y = cornerGauge s V y`.)

No sorry / native_decide / axioms.
-/
set_option autoImplicit false
noncomputable section
namespace AdalyFormal.CurvBlock
open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.SuTwoLogExp (SU2)
open AdalyFormal.Balaban.CoarseCurl (coarseShift coarseShift_mem_coarseLattice)
open AdalyFormal.Balaban.TowerLawCov (coarseGammaPath coarsePathEndpoint coarsePathHolonomy)
open AdalyFormal.Balaban.QjComposite (coarsePathEndpoint_append coarsePathHolonomy_append)
open AdalyFormal.Balaban.AdmissibleSubspace (CoarseLattice)

variable {L : PeriodicLatticeExtent}

theorem shift_mul_aligned (s : ℕ) (hdvd : ∀ ρ, s ∣ L ρ + 1) (ρ : Fin 3) :
    ∀ (a : ℕ) (z : PeriodicLatticeSite L), z ∈ CoarseLattice L s →
      coarseShift z (s * a) ρ ∈ CoarseLattice L s := by
  intro a
  induction a with
  | zero => intro z hz; exact hz
  | succ k ih =>
      intro z hz
      rw [Nat.mul_succ, shift_add]
      exact ih _ (coarseShift_mem_coarseLattice hdvd hz ρ)

theorem hol_one_step (s : ℕ) (V : PeriodicLinkConfiguration SU2 L) (z : PeriodicLatticeSite L)
    (ρ : Fin 3) : coarsePathHolonomy s V z [ρ] = V (z, ρ) := by
  show V (z, ρ) * 1 = _; rw [mul_one]

theorem off_step_self (s : ℕ) (hs : 0 < s) (y x : PeriodicLatticeSite L) (ρ : Fin 3)
    (hnw : off y x ρ + s < L ρ + 1) :
    off y (coarseShift x s ρ) ρ / s = off y x ρ / s + 1 := by
  rw [off_shift_self, Nat.mod_eq_of_lt hnw, Nat.add_div_right _ hs]

theorem off_step_ne (s : ℕ) (y x : PeriodicLatticeSite L) {ρ σ : Fin 3} (h : σ ≠ ρ) :
    off y (coarseShift x s ρ) σ / s = off y x σ / s := by
  rw [off_shift_ne _ _ _ h]

theorem endpoint_one (s : ℕ) (z : PeriodicLatticeSite L) (ρ : Fin 3) :
    coarsePathEndpoint s z [ρ] = coarseShift z s ρ := rfl

/-- The staircase ends at `x`. -/
theorem gamma_ends (s : ℕ) (y x : PeriodicLatticeSite L) (hal : ∀ σ, s ∣ off y x σ) :
    coarseShift (coarseShift (coarseShift y (s * (off y x 2 / s)) 2) (s * (off y x 1 / s)) 1)
      (s * (off y x 0 / s)) 0 = x := by
  have h := gamma_end s y x hal
  simp only [gamma_eq, coarsePathEndpoint_append, endpoint_rep] at h
  exact h

theorem axial0 (s : ℕ) (hs : 0 < s) (V : PeriodicLinkConfiguration SU2 L)
    (y x : PeriodicLatticeSite L) (hal : ∀ σ, s ∣ off y x σ) (hnw : off y x 0 + s < L 0 + 1) :
    cornerGauge s V y x * V (x, 0) * (cornerGauge s V y (coarseShift x s 0))⁻¹ = 1 := by
  have e2 := off_step_ne s y x (by decide : (2 : Fin 3) ≠ 0)
  have e1 := off_step_ne s y x (by decide : (1 : Fin 3) ≠ 0)
  have e0 := off_step_self s hs y x 0 hnw
  have hend := gamma_ends s y x hal
  unfold cornerGauge
  rw [gamma_eq s y (coarseShift x s 0), e2, e1, e0, gamma_eq s y x, List.replicate_succ']
  simp only [List.append_assoc, coarsePathHolonomy_append, coarsePathEndpoint_append, endpoint_rep,
    hend, hol_one_step]
  group

theorem axial1 (s : ℕ) (hs : 0 < s) (V : PeriodicLinkConfiguration SU2 L)
    (y x : PeriodicLatticeSite L) (hal : ∀ σ, s ∣ off y x σ) (hnw : off y x 1 + s < L 1 + 1) :
    ∃ g : SU2, cornerGauge s V y x * V (x, 1) * (cornerGauge s V y (coarseShift x s 1))⁻¹
      = g * ladS s V (coarseShift (coarseShift y (s * (off y x 2 / s)) 2) (s * (off y x 1 / s)) 1)
          (List.replicate (off y x 0 / s) 0) 1 1 * g⁻¹ := by
  have e2 := off_step_ne s y x (by decide : (2 : Fin 3) ≠ 1)
  have e0 := off_step_ne s y x (by decide : (0 : Fin 3) ≠ 1)
  have e1 := off_step_self s hs y x 1 hnw
  have hend := gamma_ends s y x hal
  refine ⟨coarsePathHolonomy s V y (List.replicate (off y x 2 / s) 2)
    * coarsePathHolonomy s V (coarseShift y (s * (off y x 2 / s)) 2)
        (List.replicate (off y x 1 / s) 1), ?_⟩
  unfold cornerGauge ladS
  rw [gamma_eq s y (coarseShift x s 1), e2, e1, e0, gamma_eq s y x, List.replicate_succ']
  simp only [List.append_assoc, coarsePathHolonomy_append, coarsePathEndpoint_append, endpoint_rep,
    endpoint_one, hend, hol_one_step, Nat.mul_one, List.replicate_one]
  group

theorem axial2 (s : ℕ) (hs : 0 < s) (V : PeriodicLinkConfiguration SU2 L)
    (y x : PeriodicLatticeSite L) (hal : ∀ σ, s ∣ off y x σ) (hnw : off y x 2 + s < L 2 + 1) :
    ∃ g : SU2, cornerGauge s V y x * V (x, 2) * (cornerGauge s V y (coarseShift x s 2))⁻¹
      = g * ladS s V (coarseShift y (s * (off y x 2 / s)) 2)
          (List.replicate (off y x 1 / s) 1 ++ List.replicate (off y x 0 / s) 0) 2 1 * g⁻¹ := by
  have e1 := off_step_ne s y x (by decide : (1 : Fin 3) ≠ 2)
  have e0 := off_step_ne s y x (by decide : (0 : Fin 3) ≠ 2)
  have e2 := off_step_self s hs y x 2 hnw
  have hend := gamma_ends s y x hal
  refine ⟨coarsePathHolonomy s V y (List.replicate (off y x 2 / s) 2), ?_⟩
  unfold cornerGauge ladS
  rw [gamma_eq s y (coarseShift x s 2), e2, e1, e0, gamma_eq s y x, List.replicate_succ']
  simp only [List.append_assoc, coarsePathHolonomy_append, coarsePathEndpoint_append, endpoint_rep,
    endpoint_one, hend, hol_one_step, Nat.mul_one, List.replicate_one]
  group

end AdalyFormal.CurvBlock

#print axioms AdalyFormal.CurvBlock.axial0
#print axioms AdalyFormal.CurvBlock.axial1
#print axioms AdalyFormal.CurvBlock.axial2
