import PGFC19

/-!
# GFC20 -- repo bridge, part 4: `NQp` membership, flat formulas for `gradAdj`, `lapFull`.  Standard axioms only.
-/
set_option autoImplicit false
set_option maxRecDepth 8000
set_option maxHeartbeats 8000000
open scoped ComplexInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane (scaleUp)
open AdalyFormal.StatementLaneG
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.GenuineU1
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond blockOf CoarseLattice mem_CoarseLattice)
open AdalyFormal.Balaban.CovariantHjMinimizer (trivialU)

namespace AdalyFormal.FlatCoercivity

/-- block-mean-zero site fields lie in `N(Q')` of the flat full tower at level `k` -/
theorem mem_NQp_of_blocks (ell k : ℕ) (Lu : PeriodicLatticeExtent) (hell : 0 < ell)
    (φ : SiteL2 (scaleUp ell k Lu))
    (hker : ∀ z ∈ CoarseLattice (scaleUp ell k Lu) (ell ^ k), ∑ x ∈ blockOf z (ell ^ k), WithLp.ofLp φ x = 0) :
    φ ∈ NQp (geomOf ell k (fullTower ell k Lu)) (flatCfg : PeriodicLinkConfiguration
      (Matrix.specialUnitaryGroup (Fin 2) ℂ) (scaleUp ell k Lu)) := by
  set G := geomOf ell k (fullTower ell k Lu) with hG
  have hbg : ∀ j, bgTower G (flatCfg : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) (scaleUp ell k Lu)) j
      = (trivialU (scaleUp ell k Lu)) := by
    intro j
    unfold bgTower
    exact Ubar_flat _ j
  refine ⟨fun x hx => absurd (by rw [hG, G_Om0]; exact Set.mem_univ x) hx, ?_⟩
  intro j hj y hy
  by_cases hjk : j < k
  · exfalso
    have : G.Lam j = ∅ := fullTower_lam_lt ell k Lu j hjk
    rw [this] at hy
    exact hy
  · have hjk' : j = k := le_antisymm hj (not_lt.mp hjk)
    subst hjk'
    have hyc : y ∈ CoarseLattice (scaleUp ell j Lu) (ell ^ j) := by
      rw [mem_CoarseLattice]
      intro ν
      exact Nat.mod_eq_zero_of_dvd (((fullTower_lam_k ell j Lu y).mp hy) ν)
    rw [Qlev_apply]
    have hq := Qcomposite_closed ell hell (bgTower G flatCfg) hbg j (scaleUp_tiling ell j Lu hell)
      (WithLp.ofLp φ) j le_rfl (ell ^ j) rfl y hyc
    exact hq.trans (by rw [hker y hyc, smul_zero])

theorem lapDir_flat (ell k : ℕ) (Lu : PeriodicLatticeExtent) :
    lapDir (geomOf ell k (fullTower ell k Lu)) (flatCfg : PeriodicLinkConfiguration
      (Matrix.specialUnitaryGroup (Fin 2) ℂ) (scaleUp ell k Lu)) = lapFull flatCfg := by
  ext f : 1
  unfold lapDir
  simp only [ContinuousLinearMap.comp_apply]
  rw [G_Om0, siteMask_univ, siteMask_univ]

open AdalyFormal.GenuineU1H (gradL2_flat_apply flatU)
open AdalyFormal.Balaban.CovariantHjMinimizer (periodicLatticeShiftBack gradCovariantAdjointValue)

theorem shiftBack_eq {L : PeriodicLatticeExtent} (y : Site L) (μ : Fin 3) : periodicLatticeShiftBack y μ = y - eU L μ := by
  unfold periodicLatticeShiftBack eU
  funext ν
  by_cases h : ν = μ
  · subst h; simp
  · simp [h]

theorem gradAdj_flat_apply {L : PeriodicLatticeExtent} (A : BondFnL2 L) (x : Site L) :
    (gradAdj (flatCfg : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) A) x
      = ∑ μ : Fin 3, (WithLp.ofLp A (x - eU L μ, μ) - WithLp.ofLp A (x, μ)) := by
  have h := congrArg (fun f => f x) (gradAdj_apply (flatCfg : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) A)
  simp only at h
  rw [show (gradAdj flatCfg A) x = ((gradAdj flatCfg) A).ofLp x from rfl, h]
  simp [gradCovariantAdjointValue, flatCfg, AdalyFormal.Balaban.CovariantOperators.RMap_one, shiftBack_eq]

theorem lapFull_flat_apply {L : PeriodicLatticeExtent} (φ : SiteL2 L) (x : Site L) :
    (lapFull (flatCfg : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) φ) x
      = ∑ μ : Fin 3, (2 • WithLp.ofLp φ x - WithLp.ofLp φ (x + eU L μ) - WithLp.ofLp φ (x - eU L μ)) := by
  have h := gradAdj_flat_apply (gradL2 (flatCfg : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) φ) x
  rw [show (lapFull flatCfg φ) x = (gradAdj flatCfg (gradL2 flatCfg φ)) x from rfl, h]
  refine Finset.sum_congr rfl (fun μ _ => ?_)
  have e1 := gradL2_flat_apply (L := L) φ (x - eU L μ, μ)
  have e2 := gradL2_flat_apply (L := L) φ (x, μ)
  simp only [flatU] at e1 e2
  rw [show (WithLp.ofLp (gradL2 flatCfg φ)) (x - eU L μ, μ) = gradL2 flatCfg φ (x - eU L μ, μ) from rfl, e1,
    show (WithLp.ofLp (gradL2 flatCfg φ)) (x, μ) = gradL2 flatCfg φ (x, μ) from rfl, e2, shift_eq, shift_eq]
  simp only [sub_add_cancel]
  rw [two_smul]
  abel

#print axioms mem_NQp_of_blocks
#print axioms lapDir_flat

end AdalyFormal.FlatCoercivity
