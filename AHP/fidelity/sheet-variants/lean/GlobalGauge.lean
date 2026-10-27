import ZT5A

set_option autoImplicit false

namespace AdalyFormal.Fidelity.SheetVariants

open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLane2
open AdalyFormal.StatementLaneG
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
open AdalyFormal.Balaban.RMapLipschitz (frobNorm)
open AdalyFormal.Balaban.CovariantHjMinimizer (periodicLatticeShiftBack)

def GlobalRegular {L : PeriodicLatticeExtent} (ell M f k : ℕ) (S : Tower L)
    (α₀ η : ℝ) (U : LinkCfg L) : Prop :=
  ∃ g : PeriodicLatticeSite L → Matrix.specialUnitaryGroup (Fin 2) ℂ,
    ∀ (sites : Set (PeriodicLatticeSite L)) (j : ℕ),
      IsClassCube ell M f k S sites j →
      ∃ A : Bond L → Matrix (Fin 2) (Fin 2) ℂ,
        (∀ e : Bond L, CubeBond sites e →
          HT (A e) ∧
          ((periodicGaugeTransform g U e : Matrix.specialUnitaryGroup (Fin 2) ℂ) :
            Matrix (Fin 2) (Fin 2) ℂ) =
              NormedSpace.exp (((η : ℂ) * Complex.I) • A e) ∧
          frobNorm (A e) < (f : ℝ) * M * α₀ * (((ell : ℝ) ^ j * η)⁻¹ ^ 1)) ∧
        (∀ (μ ν : Fin 3) (x : PeriodicLatticeSite L),
          CubeBond sites ((x, ν) : Bond L) →
          CubeBond sites ((periodicLatticeShift x μ, ν) : Bond L) →
          frobNorm ((η⁻¹ : ℝ) • (A (periodicLatticeShift x μ, ν) - A (x, ν))) <
            (f : ℝ) * M * α₀ * (((ell : ℝ) ^ j * η)⁻¹ ^ 2)) ∧
        (∀ (μ : Fin 3) (x : PeriodicLatticeSite L),
          (∀ ν : Fin 3, ν ≠ μ →
            CurlReads sites (periodicLatticeShiftBack x ν) ν μ ∧ CurlReads sites x ν μ) →
          frobNorm (ddA η A x μ) <
            (f : ℝ) * M * α₀ * (((ell : ℝ) ^ j * η)⁻¹ ^ 3))

def ClassCoupledGlobal {L : PeriodicLatticeExtent}
    (ell M c k : ℕ) (S : Tower L) (α₀ η : ℝ) (U : LinkCfg L) : Prop :=
  CoversOm0p ell M c k S ∧ GlobalRegular ell M c k S α₀ η U

theorem global_imp_perCube {L : PeriodicLatticeExtent} (ell M f k : ℕ) (S : Tower L)
    (α₀ η : ℝ) (U : LinkCfg L) :
    GlobalRegular ell M f k S α₀ η U → PerCubeRegular2 ell M f k S α₀ η U := by
  rintro ⟨g, hg⟩ sites j hcube
  obtain ⟨A, hA⟩ := hg sites j hcube
  exact ⟨g, A, hA⟩

theorem globalClass_imp_frozenClass {L : PeriodicLatticeExtent} (ell M c k : ℕ)
    (S : Tower L) (α₀ η : ℝ) (U : LinkCfg L) :
    ClassCoupledGlobal ell M c k S α₀ η U → ClassCoupled ell M c k S α₀ η U := by
  intro h
  exact ⟨h.1, global_imp_perCube ell M c k S α₀ η U h.2⟩

theorem global_flat {L : PeriodicLatticeExtent} (ell M f k : ℕ) (S : Tower L)
    (α₀ η : ℝ) (hell : 0 < ell) (hM : 0 < M) (hf : 0 < f)
    (hα : 0 < α₀) (hη : 0 < η) :
    GlobalRegular ell M f k S α₀ η (fun _ => 1) := by
  refine ⟨fun _ => 1, ?_⟩
  intro sites j _
  have hpos : ∀ n : ℕ, 0 < (f : ℝ) * M * α₀ * (((ell : ℝ) ^ j * η)⁻¹ ^ n) := by
    intro n
    have : (0 : ℝ) < (ell : ℝ) ^ j * η := mul_pos (pow_pos (by exact_mod_cast hell) j) hη
    have hf' : (0 : ℝ) < f := by exact_mod_cast hf
    have hM' : (0 : ℝ) < M := by exact_mod_cast hM
    positivity
  refine ⟨fun _ => 0, ?_, ?_, ?_⟩
  · intro e _
    refine ⟨⟨by simp, by simp⟩, ?_, ?_⟩
    · simp [periodicGaugeTransform]
    · simpa using hpos 1
  · intro μ ν x _ _
    simpa using hpos 2
  · intro μ x _
    simpa [ddA, curlA] using hpos 3

end AdalyFormal.Fidelity.SheetVariants

#print axioms AdalyFormal.Fidelity.SheetVariants.global_imp_perCube
#print axioms AdalyFormal.Fidelity.SheetVariants.globalClass_imp_frozenClass
#print axioms AdalyFormal.Fidelity.SheetVariants.global_flat
