import SourcePredicate
set_option autoImplicit false
noncomputable section
namespace HConstruction.Nonflat.Reproduced
open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban
open AdalyFormal.Balaban.AdmissibleSubspace
open AdalyFormal.Balaban.CovariantOperators
open AdalyFormal.Balaban.DeltaPrime
open AdalyFormal.Balaban.NormalizationAudit
open AdalyFormal.Balaban.CovariantHj
open AdalyFormal.Balaban.NormalizedCounterexampleSearch
variable {L : PeriodicLatticeExtent}

noncomputable def holonomyDefectSq
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (p : PeriodicLatticePlaquette L) : ℝ :=
  4 - 2 * (Matrix.trace (holonomyElem U p : Matrix (Fin 2) (Fin 2) ℂ)).re

noncomputable def IsRegularHolonomy
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) (Mα₀ : ℝ) : Prop :=
  ∀ p : PeriodicLatticePlaquette L, holonomyDefectSq U p ≤ Mα₀

theorem holonomyDefectSq_witnessU_witnessPlaquette :
    holonomyDefectSq witnessU witnessPlaquette = 4 := by
  unfold holonomyDefectSq
  rw [holonomy_witnessU_witnessPlaquette]
  norm_num [witnessMElem, witnessM, Matrix.trace, Matrix.diag, Fin.sum_univ_two]

theorem witnessU_elsewhere {e : Bond AdmissibleSubspace.witnessL}
    (h : e ≠ (AdmissibleSubspace.witnessY, (0 : Fin 3))) : witnessU e = 1 := by
  simp [witnessU, h]

theorem holonomy_witnessU_eq_one {p : PeriodicLatticePlaquette AdmissibleSubspace.witnessL}
    (hp1 : p ≠ witnessPlaquette) (hp2 : p ≠ myWitnessPlaquette2) (hp3 : p ≠ p3) (hp4 : p ≠ p4) :
    holonomyElem witnessU p = 1 := by
  show witnessU (p.1, p.2.1.1) * witnessU (periodicLatticeShift p.1 p.2.1.1, p.2.1.2) *
      (witnessU (periodicLatticeShift p.1 p.2.1.2, p.2.1.1))⁻¹ *
      (witnessU (p.1, p.2.1.2))⁻¹ = 1
  have e1 : witnessU (p.1, p.2.1.1) = 1 := by
    apply witnessU_elsewhere
    intro hcon
    rcases eq_witnessPlaquette_or_myWitnessPlaquette2 (congrArg Prod.fst hcon)
        (congrArg Prod.snd hcon) with h | h
    · exact hp1 h
    · exact hp2 h
  have e2 : witnessU (periodicLatticeShift p.1 p.2.1.1, p.2.1.2) = 1 := by
    apply witnessU_elsewhere
    intro hcon
    exact plaquette_snd_dir_ne_zero p (congrArg Prod.snd hcon)
  have e3 : witnessU (periodicLatticeShift p.1 p.2.1.2, p.2.1.1) = 1 := by
    apply witnessU_elsewhere
    intro hcon
    rcases eq_p3_or_p4 (congrArg Prod.fst hcon) (congrArg Prod.snd hcon) with h | h
    · exact hp3 h
    · exact hp4 h
  have e4 : witnessU (p.1, p.2.1.2) = 1 := by
    apply witnessU_elsewhere
    intro hcon
    exact plaquette_snd_dir_ne_zero p (congrArg Prod.snd hcon)
  rw [e1, e2, e3, e4]
  simp

theorem holonomyDefectSq_witnessU_eq_zero_elsewhere
    {p : PeriodicLatticePlaquette AdmissibleSubspace.witnessL}
    (hp1 : p ≠ witnessPlaquette) (hp2 : p ≠ myWitnessPlaquette2) (hp3 : p ≠ p3) (hp4 : p ≠ p4) :
    holonomyDefectSq witnessU p = 0 := by
  unfold holonomyDefectSq
  rw [holonomy_witnessU_eq_one hp1 hp2 hp3 hp4]
  norm_num [Matrix.trace, Matrix.diag, Fin.sum_univ_two, Matrix.one_apply]

theorem holonomyDefectSq_witnessU_myWitnessPlaquette2 :
    holonomyDefectSq witnessU myWitnessPlaquette2 = 4 := by
  unfold holonomyDefectSq
  rw [holonomy_witnessU_myWitnessPlaquette2]
  norm_num [witnessMElem, witnessM, Matrix.trace, Matrix.diag, Fin.sum_univ_two]

theorem holonomyDefectSq_witnessU_p3 : holonomyDefectSq witnessU p3 = 4 := by
  unfold holonomyDefectSq
  rw [holonomy_witnessU_p3, trace_inv_re_eq_trace_re witnessMElem]
  norm_num [witnessMElem, witnessM, Matrix.trace, Matrix.diag, Fin.sum_univ_two]

theorem holonomyDefectSq_witnessU_p4 : holonomyDefectSq witnessU p4 = 4 := by
  unfold holonomyDefectSq
  rw [holonomy_witnessU_p4, trace_inv_re_eq_trace_re witnessMElem]
  norm_num [witnessMElem, witnessM, Matrix.trace, Matrix.diag, Fin.sum_univ_two]

theorem witnessU_isRegularHolonomy_four : IsRegularHolonomy witnessU (4 : ℝ) := by
  intro p
  by_cases h1 : p = witnessPlaquette
  · rw [h1, holonomyDefectSq_witnessU_witnessPlaquette]
  by_cases h2 : p = myWitnessPlaquette2
  · rw [h2, holonomyDefectSq_witnessU_myWitnessPlaquette2]
  by_cases h3 : p = p3
  · rw [h3, holonomyDefectSq_witnessU_p3]
  by_cases h4 : p = p4
  · rw [h4, holonomyDefectSq_witnessU_p4]
  · rw [holonomyDefectSq_witnessU_eq_zero_elsewhere h1 h2 h3 h4]
    norm_num

theorem witness_curvature_ne_zero :
    curlValueCovariant witnessU (gradValueCovariant witnessU witnessLam) witnessPlaquette ≠ 0 := by
  rw [curlValueCovariant_gradValueCovariant]
  change RMap (witnessU (AdmissibleSubspace.witnessY, (0 : Fin 3)) *
        witnessU (periodicLatticeShift AdmissibleSubspace.witnessY 0, (1 : Fin 3)))
      (witnessLam witnessZPoint) -
    RMap (witnessU (AdmissibleSubspace.witnessY, (1 : Fin 3)) *
        witnessU (periodicLatticeShift AdmissibleSubspace.witnessY 1, (0 : Fin 3)))
      (witnessLam witnessZPoint) ≠ 0
  rw [witnessU_at_x_mu, witnessU_at_y_nu, witnessU_at_x_nu, witnessU_at_w_mu, witnessLam_at_z,
    mul_one, one_mul, RMap_witnessMElem, RMap_one]
  simp only [LinearMap.id_coe, id_eq]
  rw [sub_ne_zero]
  exact fun h => suTwoWitness_ne_neg_self h.symm

def loopSurfaceBound (ell : ℕ) : ℕ := 3 * ell * (ell - 1)

def loopRhoPlaq (eps0 : ℝ) (ell : ℕ) : ℝ :=
  (loopSurfaceBound ell : ℝ) * ((Real.pi / (2 * Real.sqrt 2)) * eps0)

def loopRhoPlaqCap (eps0 : ℝ) (ell : ℕ) : ℝ :=
  (loopSurfaceBound ell : ℝ) * ((Real.pi / 4) * eps0)

end HConstruction.Nonflat.Reproduced
