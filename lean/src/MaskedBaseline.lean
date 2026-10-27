import MaskedQ
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000
noncomputable section
namespace HConstruction.TransversePos
open HConstruction.Covariance HConstruction.SmallNF HConstruction.Carrier
open HConstruction.DRepair HConstruction.G0Final.Locality
open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.AdmissibleSubspace (witnessL)
open AdalyFormal.Balaban.CovariantOperators (SuTwo)
open AdalyFormal.Balaban.CovariantHjMinimizer (trivialU)
open AdalyFormal.Balaban.LatticeOperators (CoarseBond)
open AdalyFormal.Balaban.DeltaKUnified (bfl2Equiv)

/-- Erases exactly the five coefficient-active output rows. -/
def maskQ : K →L[ℝ] K :=
  LinearMap.toContinuousLinearMap
    ((cfl2Equiv 2).symm.toLinearMap.comp
      ((LinearMap.pi fun c => if c ∈ activeRows then 0 else LinearMap.proj c).comp
        (cfl2Equiv 2).toLinearMap))

theorem maskQ_value (B : K) (c : Output) :
    cfl2Equiv 2 (maskQ B) c = if c ∈ activeRows then 0 else cfl2Equiv 2 B c := by
  classical
  unfold maskQ
  change (if c ∈ activeRows then (0 : (Output → SuTwo) →ₗ[ℝ] SuTwo) else LinearMap.proj c) _ = _
  split_ifs <;> rfl

theorem maskQ_norm_sq_le (B : K) : ‖maskQ B‖^2 ≤ ‖B‖^2 := by
  rw [← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq]
  change (∑ c : Output, inner ℝ (cfl2Equiv 2 (maskQ B) c) (cfl2Equiv 2 (maskQ B) c)) ≤
    ∑ c : Output, inner ℝ (cfl2Equiv 2 B c) (cfl2Equiv 2 B c)
  apply Finset.sum_le_sum
  intro c _
  rw [maskQ_value]
  split_ifs
  · simpa using real_inner_self_nonneg (cfl2Equiv 2 B c)
  · exact le_rfl

theorem maskedQ_flat (t : ℝ) (A : H) :
    maskQ (nativeLinearQ (HConstruction.NfRepair.Reproduced.nonflatU t) 2 A) =
      maskQ (nativeLinearQ (trivialU witnessL) 2 A) := by
  apply (cfl2Equiv 2).injective
  funext c
  rw [maskQ_value, maskQ_value]
  split_ifs with hc
  · rfl
  · exact q124_inactive_flat t (fineCoordinates A) c hc

def cv (a b d : Fin 2) : HConstruction.DRepair.CS := (coarseOutput a b d 0).1

theorem cv_cases : ∀ y : HConstruction.DRepair.CS, ∃ a b d, y = cv a b d := by decide +kernel

theorem cv_moves : ∀ a b d : Fin 2,
    csMove (cv a b d) 0 = cv (1-a) b d ∧
    csMove (cv a b d) 1 = cv a (1-b) d ∧
    csMove (cv a b d) 2 = cv a b (1-d) := by decide +kernel

/-- The nineteen retained rows contain direction cycles and a connected site tree. -/
theorem masked_coarse_kernel (g : HConstruction.DRepair.CS → SuTwo) (c : Fin 3 → SuTwo)
    (h : ∀ y mu, (y,mu) ∉ activeRows → g (csMove y mu) - g y + c mu = 0) :
    (∀ mu, c mu = 0) ∧ (∀ y, g y = g (cv 1 0 0)) := by
  have hc (mu : Fin 3) : c mu = 0 := by
    have h0 := h (cv 1 1 1) mu (by fin_cases mu <;> decide +kernel)
    have h1 := h (csMove (cv 1 1 1) mu) mu (by fin_cases mu <;> decide +kernel)
    rw [csMove_twice] at h1
    have he : (2 : ℝ) • c mu = 0 := by
      calc
        (2 : ℝ) • c mu = (g (csMove (cv 1 1 1) mu) - g (cv 1 1 1) + c mu) +
            (g (cv 1 1 1) - g (csMove (cv 1 1 1) mu) + c mu) := by module
        _ = 0 := by rw [h0, h1, add_zero]
    exact (smul_eq_zero.mp he).resolve_left (by norm_num)
  have hg (y) (mu) (hy : (y,mu) ∉ activeRows) : g (csMove y mu) = g y := by
    have he := h y mu hy
    rw [hc, add_zero] at he
    exact sub_eq_zero.mp he
  have e000 := hg (cv 1 0 0) 0 (by decide +kernel)
  have e110 := hg (cv 1 0 0) 1 (by decide +kernel)
  have e101 := hg (cv 1 0 0) 2 (by decide +kernel)
  have e010 := hg (cv 1 1 0) 0 (by decide +kernel)
  have e001 := hg (cv 1 0 1) 0 (by decide +kernel)
  have e111 := hg (cv 1 1 0) 2 (by decide +kernel)
  have e011 := hg (cv 1 1 1) 0 (by decide +kernel)
  simp only [(cv_moves _ _ _).1, (cv_moves _ _ _).2.1, (cv_moves _ _ _).2.2] at e000 e110 e101 e010 e001 e111 e011
  norm_num at e000 e110 e101 e010 e001 e111 e011
  refine ⟨hc, ?_⟩
  intro y
  obtain ⟨a,b,d,rfl⟩ := cv_cases y
  fin_cases a <;> fin_cases b <;> fin_cases d
  · exact e000
  · exact e001.trans e101
  · exact e010.trans e110
  · exact e011.trans (e111.trans e110)
  · rfl
  · exact e101
  · exact e110
  · exact e111.trans e110

/-- Full flat joint kernel still vanishes after discarding the five active rows. -/
theorem masked_joint_kernel (A : H) (hC : flatCurl A = 0) (hR : gaugeConstraint A = 0)
    (hQ : maskQ (nativeLinearQ (trivialU witnessL) 2 A) = 0) : A = 0 := by
  obtain ⟨f,c,hA⟩ := flatCurl_hodge A hC
  let g : HConstruction.DRepair.CS → SuTwo := flatSiteQ f
  have he (y : HConstruction.DRepair.CS) (mu : Fin 3) (hy : (y,mu) ∉ activeRows) :
      g (csMove y mu) - g y + c mu = 0 := by
    have h := congrArg (fun X => cfl2Equiv 2 X (y,mu)) hQ
    rw [maskQ_value, if_neg hy] at h
    rw [hA, map_add, map_add, Pi.add_apply, nativeQ_grad, nativeQ_const] at h
    exact h
  obtain ⟨hc,hg⟩ := masked_coarse_kernel g c he
  have hAz : A = flatGrad f := by
    rw [hA]
    have hh : constBond c = 0 := by
      apply bfl2Equiv.injective
      funext b
      exact hc b.2
    rw [hh, add_zero]
  let f' := f - constSite (g (cv 1 0 0))
  have hf : flatSiteQ f' = 0 := by
    rw [map_sub]
    funext y
    change g y - flatSiteQ (constSite (g (cv 1 0 0))) y = 0
    rw [flatSiteQ_const, hg, sub_self]
  have ha : A = flatGrad f' := by
    rw [map_sub, flatGrad_constSite, sub_zero]
    exact hAz
  rw [ha] at hR ⊢
  exact gauge_excludes_Qprime_gradients f' hf hR

#print axioms maskedQ_flat
#print axioms maskQ_norm_sq_le
#print axioms masked_coarse_kernel
#print axioms masked_joint_kernel
end HConstruction.TransversePos
