import D2Main

/-!
# D2Geo1 -- central (`±1`) configurations: transports are the identity, every holonomy is `±1`, `Δ` contributes `ε_p ‖curl_p‖²`.
-/
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 8000
set_option linter.unusedSectionVars false

namespace AdalyFormal.D1Literal

open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.StatementLaneR8
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2 RMap curlValueCovariant)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.DeltaPrime
open AdalyFormal.Balaban.DeltaPrimeOperator
open AdalyFormal.Balaban.SuTwoInner (hsInner)
open AdalyFormal.StatementLaneR6
open AdalyFormal.Balaban.CovariantHjMinimizer (gradCovariantAdjointValue)

variable {L : PeriodicLatticeExtent}

/-- the matrix of `g` is the centre element `1` or `-1`. -/
def PM (g : SU2m) : Prop := ((g : SU2m) : Matrix (Fin 2) (Fin 2) ℂ) = 1 ∨ ((g : SU2m) : Matrix (Fin 2) (Fin 2) ℂ) = -1

theorem PM_one : PM (1 : SU2m) := Or.inl rfl

theorem PM_uπ : PM (uθ Real.pi) := Or.inr uθ_pi_coe

theorem PM_inv {g : SU2m} (h : PM g) : PM g⁻¹ := by
  unfold PM at *
  have : ((g⁻¹ : SU2m) : Matrix (Fin 2) (Fin 2) ℂ) = star ((g : SU2m) : Matrix (Fin 2) (Fin 2) ℂ) := rfl
  rw [this]
  rcases h with h | h <;> rw [h] <;> simp

theorem PM_mul {g h : SU2m} (hg : PM g) (hh : PM h) : PM (g * h) := by
  unfold PM at *
  have : ((g * h : SU2m) : Matrix (Fin 2) (Fin 2) ℂ) = (g : Matrix (Fin 2) (Fin 2) ℂ) * (h : Matrix (Fin 2) (Fin 2) ℂ) := rfl
  rw [this]
  rcases hg with h1 | h1 <;> rcases hh with h2 | h2 <;> rw [h1, h2] <;> simp

theorem RMap_PM {g : SU2m} (h : PM g) (X : SuTwo) : RMap g X = X := by
  apply Subtype.ext
  rw [AdalyFormal.Balaban.CovariantOperators.RMap_coe_apply]
  rcases h with h | h <;> rw [h] <;> simp

theorem Uth_PM (Om : Set (PeriodicLatticeSite L)) (e : Bond L) : PM (Uth Om Real.pi e) := by
  unfold Uth
  split_ifs
  · exact PM_uπ
  · exact PM_one

theorem holonomy_PM (U : PeriodicLinkConfiguration SU2m L) (hU : ∀ e, PM (U e)) (p : PeriodicLatticePlaquette L) :
    PM (holonomyElem U p) := by
  unfold holonomyElem periodicPlaquetteHolonomy
  exact PM_mul (PM_mul (PM_mul (hU _) (hU _)) (PM_inv (hU _))) (PM_inv (hU _))

/-- holonomy `+1`: the plaquette contributes its curl energy. -/
theorem plaq_flat (U : PeriodicLinkConfiguration SU2m L) (p : PeriodicLatticePlaquette L) (A : Bond L → SuTwo)
    (h : ((holonomyElem U p : SU2m) : Matrix (Fin 2) (Fin 2) ℂ) = 1) :
    hsInner (curlValueCovariant U A p) (curlValueCovariant U A p) + (1 / 2 : ℝ) * bilPlaq U p A A
      = hsInner (curlValueCovariant U A p) (curlValueCovariant U A p) := by
  have hinv : ((holonomyElemInv U p : SU2m) : Matrix (Fin 2) (Fin 2) ℂ) = 1 := by
    have : ((holonomyElemInv U p : SU2m) : Matrix (Fin 2) (Fin 2) ℂ) = star ((holonomyElem U p : SU2m) : Matrix (Fin 2) (Fin 2) ℂ) := rfl
    rw [this, h]; simp
  have hre : reHolonomy U p = 1 := by
    unfold reHolonomy; rw [h, hinv]
    ext i j; fin_cases i <;> fin_cases j <;> simp <;> norm_num
  have him : imHolonomy U p = 0 := by
    unfold imHolonomy; rw [h, hinv]; simp
  rw [bilPlaq_atoms, him, hre]
  simp

/-- contribution of a `±1` plaquette: `±` its curl energy. -/
theorem plaq_PM (U : PeriodicLinkConfiguration SU2m L) (p : PeriodicLatticePlaquette L) (A : Bond L → SuTwo)
    (h : PM (holonomyElem U p)) :
    (hsInner (curlValueCovariant U A p) (curlValueCovariant U A p) + (1 / 2 : ℝ) * bilPlaq U p A A
      = hsInner (curlValueCovariant U A p) (curlValueCovariant U A p) ∧
      ((holonomyElem U p : SU2m) : Matrix (Fin 2) (Fin 2) ℂ) = 1) ∨
    (hsInner (curlValueCovariant U A p) (curlValueCovariant U A p) + (1 / 2 : ℝ) * bilPlaq U p A A
      = - hsInner (curlValueCovariant U A p) (curlValueCovariant U A p) ∧
      ((holonomyElem U p : SU2m) : Matrix (Fin 2) (Fin 2) ℂ) = -1) := by
  rcases h with h | h
  · exact Or.inl ⟨plaq_flat U p A h, h⟩
  · exact Or.inr ⟨plaq_central U p A h, h⟩

/-- a plaquette with `±1` holonomy and zero curl contributes `0`. -/
theorem plaq_PM_zero (U : PeriodicLinkConfiguration SU2m L) (p : PeriodicLatticePlaquette L) (A : Bond L → SuTwo)
    (h : PM (holonomyElem U p)) (hc : curlValueCovariant U A p = 0) :
    hsInner (curlValueCovariant U A p) (curlValueCovariant U A p) + (1 / 2 : ℝ) * bilPlaq U p A A = 0 := by
  rcases plaq_PM U p A h with ⟨h1, -⟩ | ⟨h1, -⟩ <;> rw [h1, hc] <;> unfold hsInner <;> simp

/-- `D*` of a bond field which is a function of layer on the `ν`-bonds only vanishes for a central configuration (helper form). -/
theorem gradAdjValue_PM (U : PeriodicLinkConfiguration SU2m L) (hU : ∀ e, PM (U e)) (A : Bond L → SuTwo)
    (z : PeriodicLatticeSite L)
    (hA : ∀ μ : Fin 3, RMap (U (AdalyFormal.Balaban.CovariantHjMinimizer.periodicLatticeShiftBack z μ, μ))⁻¹
        (A (AdalyFormal.Balaban.CovariantHjMinimizer.periodicLatticeShiftBack z μ, μ)) - A (z, μ) = 0) :
    gradCovariantAdjointValue U A z = 0 := by
  unfold gradCovariantAdjointValue
  exact Finset.sum_eq_zero (fun μ _ => hA μ)

#print axioms plaq_PM_zero
#print axioms holonomy_PM

end AdalyFormal.D1Literal
