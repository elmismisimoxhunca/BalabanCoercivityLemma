import NtCvO21

/-!
# CvO36 -- conservation of the transverse sum under one abelian raw step (lane omega)

For `s, ell > 0` with `s*ell ∣ N_μ`, any angle field `θ` and any weight `h : ℕ → ℝ` of the slice only:
`Σ_{y : Crs (s ell)} h(y₀) Rsig s ell θ (y,1) = ell⁻² Σ_{x : Crs s} h(s ell ⌊x₀/(s ell)⌋) θ(x,1)`.
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace AdalyFormal.CoverOmega


set_option linter.unusedSectionVars false
variable [CfData]
open scoped Matrix
open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.UbarTowerCov (cPlusS cPlusS_eq)
open AdalyFormal.Balaban.TowerLawCov (coarsePathEndpoint coarseGammaPath coarseCoordSteps coarseStraightSegment)
open AdalyFormal.Balaban.CoarseCurl (coarseShift coarseShift_apply_ne coarseShift_val_eq)
open AdalyFormal.Balaban.QjComposite (stepBlockOf mem_stepBlockOf)
open AdalyFormal.Balaban.CovariantHjMinimizer (periodicLatticeShiftEquiv)

variable {L : PeriodicLatticeExtent}

theorem crs_coarseShift_iff {s : ℕ} (hdiv : ∀ μ, s ∣ L μ + 1) (x : PeriodicLatticeSite L) (μ : Fin 3) (m : ℕ) (hm : s ∣ m) :
    Crs s (coarseShift x m μ) ↔ Crs s x := by
  constructor
  · intro h ν
    by_cases hν : ν = μ
    · subst hν
      have := h ν
      rw [coarseShift_val_eq] at this
      have h2 := (Nat.dvd_mod_iff (hdiv ν)).mp this
      exact (Nat.dvd_add_left hm).mp h2
    · have := h ν
      rwa [coarseShift_apply_ne x m μ ν hν] at this
  · intro h; exact Crs_shift hdiv h μ m hm

/-- the stride-`s` shift in direction `μ` as a permutation of the sites. -/
noncomputable def sPerm (μ : Fin 3) (s : ℕ) : Equiv.Perm (PeriodicLatticeSite L) := (periodicLatticeShiftEquiv μ) ^ s

theorem sPerm_apply (μ : Fin 3) (s : ℕ) (x : PeriodicLatticeSite L) : sPerm μ s x = coarseShift x s μ := by
  unfold sPerm coarseShift
  rw [Equiv.Perm.coe_pow]
  rfl

theorem sPerm_coord_ne (μ : Fin 3) (s : ℕ) (i : ℕ) (x : PeriodicLatticeSite L) (ν : Fin 3) (hν : ν ≠ μ) :
    ((sPerm μ s ^ i) x) ν = x ν := by
  induction i generalizing x with
  | zero => rfl
  | succ i ih =>
    rw [pow_succ, Equiv.Perm.mul_apply, ih, sPerm_apply, coarseShift_apply_ne x s μ ν hν]

theorem sPerm_crs_iff {s : ℕ} (hdiv : ∀ μ, s ∣ L μ + 1) (μ : Fin 3) (i : ℕ) (x : PeriodicLatticeSite L) :
    Crs s ((sPerm μ s ^ i) x) ↔ Crs s x := by
  induction i generalizing x with
  | zero => rfl
  | succ i ih =>
    rw [pow_succ, Equiv.Perm.mul_apply, ih, sPerm_apply]
    exact crs_coarseShift_iff hdiv x μ s dvd_rfl

theorem pathAngG_rep_sum (s : ℕ) (θ : PeriodicLatticeEdge L → ℝ) (μ : Fin 3) (n : ℕ) (x : PeriodicLatticeSite L) :
    pathAngG s θ x (List.replicate n μ) = ∑ i ∈ Finset.range n, θ (((sPerm μ s) ^ i) x, μ) := by
  induction n generalizing x with
  | zero => simp [pathAngG]
  | succ n ih =>
    rw [List.replicate_succ, pathAngG, ih, Finset.sum_range_succ' _ n]
    simp only [pow_zero, Equiv.Perm.one_apply, pow_succ, Equiv.Perm.mul_apply, sPerm_apply]
    rw [add_comm]

#print axioms crs_coarseShift_iff
#print axioms sPerm_crs_iff

end AdalyFormal.CoverOmega
