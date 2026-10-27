import DrEquiv
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 8000
noncomputable section
namespace AdalyFormal.Round10.Dictionary.PhaseSource
open scoped RealInnerProductSpace Matrix
open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.CovariantOperators
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.CovariantHjMinimizer (periodicLatticeShiftBack)
open AdalyFormal.Balaban.SuTwoInner
variable {L : PeriodicLatticeExtent}
def circulation (f : Bond L → ℝ) (p : PeriodicLatticePlaquette L) : ℝ :=
  f (p.1, p.2.1.1) + f (periodicLatticeShift p.1 p.2.1.1, p.2.1.2) -
    f (periodicLatticeShift p.1 p.2.1.2, p.2.1.1) - f (p.1, p.2.1.2)
def oriented (P : Set (PeriodicLatticePlaquette L)) (g : PeriodicLatticePlaquette L → ℝ)
    (ν μ : Fin 3) (x : PeriodicLatticeSite L) : ℝ := by
  classical
  exact if h : ν < μ then (if (x, ⟨(ν, μ), h⟩) ∈ P then g (x, ⟨(ν, μ), h⟩) else 0)
    else if h' : μ < ν then (if (x, ⟨(μ, ν), h'⟩) ∈ P then -g (x, ⟨(μ, ν), h'⟩) else 0)
    else 0

def scalarDiv (g : Fin 3 → Fin 3 → PeriodicLatticeSite L → ℝ) (b : Bond L) : ℝ :=
  ∑ ν : Fin 3, if ν = b.2 then 0 else g ν b.2 (periodicLatticeShiftBack b.1 ν) - g ν b.2 b.1
def linearSourceScalar (P : Set (PeriodicLatticePlaquette L)) (f : Bond L → ℝ) (b : Bond L) : ℝ :=
  scalarDiv (oriented P (circulation f)) b
def sourceLinear (P : Set (PeriodicLatticePlaquette L)) (f : Bond L → ℝ) : BondFnL2 L :=
  WithLp.toLp 2 (fun b => linearSourceScalar P f b • pauliE3)
end AdalyFormal.Round10.Dictionary.PhaseSource

/-! Summation by parts for the actual diagonal source stencil. -/
noncomputable section
namespace AdalyFormal.Round10.Dictionary.SourceEnergy
open scoped BigOperators RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.CovariantOperators (BondFnL2 SuTwo)
open AdalyFormal.Balaban.CovariantHjMinimizer
open AdalyFormal.Balaban.SuTwoInner
open AdalyFormal.Round10.Dictionary.PhaseSource
variable {L : PeriodicLatticeExtent}
attribute [local instance] Classical.propDecidable

theorem sum_backward (f g : PeriodicLatticeSite L → ℝ) (ν : Fin 3) :
    (∑ x, f x * g (periodicLatticeShiftBack x ν)) =
      ∑ x, f (periodicLatticeShift x ν) * g x := by
  have h := Equiv.sum_comp (periodicLatticeShiftEquiv (L := L) ν)
    (fun x => f x * g (periodicLatticeShiftBack x ν))
  simpa only [periodicLatticeShiftEquiv_apply, periodicLatticeShiftBack_shift] using h.symm

theorem sum_backward_diff (f g : PeriodicLatticeSite L → ℝ) (ν : Fin 3) :
    (∑ x, f x * (g (periodicLatticeShiftBack x ν) - g x)) =
      ∑ x, (f (periodicLatticeShift x ν) - f x) * g x := by
  simp only [mul_sub, sub_mul, Finset.sum_sub_distrib, sum_backward]

theorem sum_dirs (f : PeriodicPlaquetteDirections → ℝ) :
    ∑ d, f d = f ⟨(0,1), by decide⟩ + f ⟨(0,2), by decide⟩ + f ⟨(1,2), by decide⟩ := by
  have hu : (Finset.univ : Finset PeriodicPlaquetteDirections) =
      {⟨(0,1), by decide⟩, ⟨(0,2), by decide⟩, ⟨(1,2), by decide⟩} := by decide
  rw [hu, Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  ring

theorem oriented_diag (P : Set (PeriodicLatticePlaquette L))
    (g : PeriodicLatticePlaquette L → ℝ) (ν : Fin 3) (x : PeriodicLatticeSite L) :
    oriented P g ν ν x = 0 := by
  simp [oriented]

theorem div_sum (P : Set (PeriodicLatticePlaquette L))
    (f : Bond L → ℝ) (g : PeriodicLatticePlaquette L → ℝ) :
    (∑ b : Bond L, f b * scalarDiv (oriented P g) b) =
      ∑ x : PeriodicLatticeSite L, ∑ μ : Fin 3, ∑ ν : Fin 3,
        (f (periodicLatticeShift x ν, μ) - f (x, μ)) * oriented P g ν μ x := by
  classical
  rw [Fintype.sum_prod_type]
  simp only [scalarDiv, Finset.mul_sum]
  rw [Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro μ _
  rw [Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro ν _
  by_cases h : ν = μ
  · subst ν
    simp only [ite_true, mul_zero, oriented_diag, Finset.sum_const_zero]
  · simp only [if_neg h]
    exact sum_backward_diff (fun x => f (x, μ)) (oriented P g ν μ) ν

theorem oriented_curl_point (P : Set (PeriodicLatticePlaquette L))
    (f : Bond L → ℝ) (g : PeriodicLatticePlaquette L → ℝ) (x : PeriodicLatticeSite L) :
    (∑ μ : Fin 3, ∑ ν : Fin 3,
      (f (periodicLatticeShift x ν, μ) - f (x, μ)) * oriented P g ν μ x) =
    ∑ d : PeriodicPlaquetteDirections, if (x,d) ∈ P then circulation f (x,d) * g (x,d) else 0 := by
  classical
  have h01 : oriented P g 0 1 x = if (x, ⟨(0,1), by decide⟩) ∈ P then g (x, ⟨(0,1), by decide⟩) else 0 := by simp [oriented]
  have h02 : oriented P g 0 2 x = if (x, ⟨(0,2), by decide⟩) ∈ P then g (x, ⟨(0,2), by decide⟩) else 0 := by simp [oriented]
  have h12 : oriented P g 1 2 x = if (x, ⟨(1,2), by decide⟩) ∈ P then g (x, ⟨(1,2), by decide⟩) else 0 := by simp [oriented]
  have h10 : oriented P g 1 0 x = if (x, ⟨(0,1), by decide⟩) ∈ P then -g (x, ⟨(0,1), by decide⟩) else 0 := by simp [oriented]
  have h20 : oriented P g 2 0 x = if (x, ⟨(0,2), by decide⟩) ∈ P then -g (x, ⟨(0,2), by decide⟩) else 0 := by simp [oriented]
  have h21 : oriented P g 2 1 x = if (x, ⟨(1,2), by decide⟩) ∈ P then -g (x, ⟨(1,2), by decide⟩) else 0 := by simp [oriented]
  rw [sum_dirs]
  simp only [Fin.sum_univ_three, oriented_diag, h01, h02, h12, h10, h20, h21, circulation]
  split_ifs <;> ring

/-- Exact localized Stokes identity; no boundary term on the physical torus. -/
theorem source_sbp (P : Set (PeriodicLatticePlaquette L)) (f g : Bond L → ℝ) :
    (∑ b : Bond L, f b * linearSourceScalar P g b) =
      ∑ p : PeriodicLatticePlaquette L, if p ∈ P then circulation f p * circulation g p else 0 := by
  classical
  change (∑ b : Bond L, f b * scalarDiv (oriented P (circulation g)) b) = _
  rw [div_sum, Fintype.sum_prod_type]
  exact Finset.sum_congr rfl (fun x _ => oriented_curl_point P f (circulation g) x)

theorem source_reciprocity (P : Set (PeriodicLatticePlaquette L)) (f g : Bond L → ℝ) :
    (∑ b, f b * linearSourceScalar P g b) = ∑ b, g b * linearSourceScalar P f b := by
  rw [source_sbp, source_sbp]
  simp only [mul_comm]

def curlEnergy (P : Set (PeriodicLatticePlaquette L)) (f : Bond L → ℝ) : ℝ :=
  ∑ p : PeriodicLatticePlaquette L, if p ∈ P then circulation f p ^ 2 else 0

theorem source_energy (P : Set (PeriodicLatticePlaquette L)) (f : Bond L → ℝ) :
    (∑ b, f b * linearSourceScalar P f b) = curlEnergy P f := by
  rw [source_sbp]
  simp only [curlEnergy, pow_two]

theorem curlEnergy_nonneg (P : Set (PeriodicLatticePlaquette L)) (f : Bond L → ℝ) :
    0 ≤ curlEnergy P f := by
  apply Finset.sum_nonneg
  intro p _
  split_ifs <;> positivity

theorem curlEnergy_eq_zero_iff (P : Set (PeriodicLatticePlaquette L)) (f : Bond L → ℝ) :
    curlEnergy P f = 0 ↔ ∀ p ∈ P, circulation f p = 0 := by
  classical
  unfold curlEnergy
  rw [Finset.sum_eq_zero_iff_of_nonneg (fun p _ => by split_ifs <;> positivity)]
  constructor
  · intro h p hp
    have hz := h p (Finset.mem_univ p)
    simpa only [if_pos hp, sq_eq_zero_iff] using hz
  · intro h p _
    by_cases hp : p ∈ P
    · simp only [if_pos hp, h p hp, zero_pow (by decide : 2 ≠ 0)]
    · simp only [if_neg hp]

theorem curlEnergy_pos_iff (P : Set (PeriodicLatticePlaquette L)) (f : Bond L → ℝ) :
    0 < curlEnergy P f ↔ ∃ p ∈ P, circulation f p ≠ 0 := by
  have h : 0 < curlEnergy P f ↔ curlEnergy P f ≠ 0 :=
    lt_iff_le_and_ne.trans (and_iff_right (curlEnergy_nonneg P f)) |>.trans ne_comm
  rw [h, ne_eq, curlEnergy_eq_zero_iff]
  simp only [not_forall, exists_prop]

def neutralCoordinate (w : BondFnL2 L) (b : Bond L) : ℝ := ⟪pauliE3, w b⟫

/-- The R2 source stencil is the actual positive scalar curl-square operator. -/
theorem inner_sourceLinear (P : Set (PeriodicLatticePlaquette L))
    (w : BondFnL2 L) (f : Bond L → ℝ) :
    ⟪w, sourceLinear P f⟫ = ∑ p : PeriodicLatticePlaquette L,
      if p ∈ P then circulation (neutralCoordinate w) p * circulation f p else 0 := by
  rw [PiLp.inner_apply]
  have h (b : Bond L) : ⟪w b, sourceLinear P f b⟫ =
      neutralCoordinate w b * linearSourceScalar P f b := by
    change ⟪w b, linearSourceScalar P f b • pauliE3⟫ = _
    rw [inner_smul_right, real_inner_comm]
    exact mul_comm _ _
  simp_rw [h]
  exact source_sbp P (neutralCoordinate w) f

#print axioms sum_backward
#print axioms sum_backward_diff
#print axioms sum_dirs
#print axioms oriented_diag
#print axioms div_sum
#print axioms oriented_curl_point
#print axioms source_sbp
#print axioms source_reciprocity
#print axioms curlEnergy
#print axioms source_energy
#print axioms curlEnergy_nonneg
#print axioms curlEnergy_eq_zero_iff
#print axioms curlEnergy_pos_iff
#print axioms neutralCoordinate
#print axioms inner_sourceLinear
end AdalyFormal.Round10.Dictionary.SourceEnergy
