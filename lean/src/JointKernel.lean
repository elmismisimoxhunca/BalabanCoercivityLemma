import FiberHodge
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
namespace HConstruction.DRepair
open HConstruction.Carrier HConstruction.Covariance
open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.AdmissibleSubspace
open AdalyFormal.Balaban.CovariantOperators
open AdalyFormal.Balaban.CovariantHjMinimizer (trivialU coarseRestrictSiteCovariant)
open AdalyFormal.Balaban.CoarseCurl (coarseShift coarseShift_mem_coarseLattice)
open AdalyFormal.Balaban.DeltaKUnified (bfl2Equiv)

abbrev CS := {y : PeriodicLatticeSite witnessL // y ∈ CoarseLattice witnessL 2}
def csOrigin : CS := ⟨witnessY,by decide⟩
def csMove (y : CS) (μ : Fin 3) : CS :=
  ⟨coarseShift y.1 2 μ, coarseShift_mem_coarseLattice (by intro ν; exact ⟨2,rfl⟩) y.2 μ⟩
lemma csMove_twice : ∀ (y : CS) (μ : Fin 3), csMove (csMove y μ) μ = y := by decide
lemma cs_cases : ∀ y : CS,
    y = csOrigin ∨ y = csMove csOrigin 0 ∨ y = csMove csOrigin 1 ∨ y = csMove csOrigin 2 ∨
    y = csMove (csMove csOrigin 0) 1 ∨ y = csMove (csMove csOrigin 0) 2 ∨
    y = csMove (csMove csOrigin 1) 2 ∨ y = csMove (csMove (csMove csOrigin 0) 1) 2 := by decide

lemma coarse_constant_of_invariant (g : CS → SuTwo)
    (hg : ∀ y μ, g (csMove y μ) = g y) : ∀ y, g y = g csOrigin := by
  intro y
  rcases cs_cases y with h|h|h|h|h|h|h|h <;> rw [h] <;> simp only [hg]

noncomputable def constSite (v : SuTwo) : S := (fiberEquiv _).symm (fun _ => v)
lemma flatGrad_constSite (v : SuTwo) : flatGrad (constSite v) = 0 := by
  apply bfl2Equiv.injective
  funext b
  simp [flatGrad, constSite, gradCovariantLM, gradValueCovariant, trivialU, RMap_one]
lemma flatSiteQ_const (v : SuTwo) (y : CS) : flatSiteQ (constSite v) y = v := by
  change coarseRestrictSiteCovariant 2 (fun _ => v) y.1 = v
  simp only [coarseRestrictSiteCovariant, Finset.sum_const]
  have hc : (blockOf y.1 2).card = 8 :=
    card_blockOf_of_coarse (by intro μ; exact ⟨2,rfl⟩) y.2
  rw [hc, ← Nat.cast_smul_eq_nsmul ℝ, smul_smul]
  norm_num

/-- Native curl/Q-null fields are EXACTLY the Q'-null pure gauges in the
needed direction; no harmonic mode is discarded. -/
theorem curl_Q_kernel_potential (A : H) (hC : flatCurl A = 0)
    (hQ : nativeLinearQ (trivialU witnessL) 2 A = 0) :
    ∃ f : S, flatSiteQ f = 0 ∧ A = flatGrad f := by
  obtain ⟨f,c,hA⟩ := flatCurl_hodge A hC
  let g : CS → SuTwo := flatSiteQ f
  have he (y : CS) (μ : Fin 3) : g (csMove y μ) - g y + c μ = 0 := by
    have h := congrArg (fun X => cfl2Equiv 2 X (y,μ)) hQ
    rw [hA, map_add, map_add, Pi.add_apply, nativeQ_grad, nativeQ_const] at h
    exact h
  have hc (μ : Fin 3) : c μ = 0 := by
    have h0 := he csOrigin μ
    have h1 := he (csMove csOrigin μ) μ
    rw [csMove_twice] at h1
    have hh : (2 : ℝ) • c μ = 0 := by
      calc
        (2 : ℝ) • c μ = (g (csMove csOrigin μ) - g csOrigin + c μ) +
          (g csOrigin - g (csMove csOrigin μ) + c μ) := by module
        _ = 0 := by rw [h0,h1,add_zero]
    exact (smul_eq_zero.mp hh).resolve_left (by norm_num)
  have hg (y : CS) (μ : Fin 3) : g (csMove y μ) = g y := by
    have h := he y μ
    rw [hc, add_zero] at h
    exact sub_eq_zero.mp h
  have hgc := coarse_constant_of_invariant g hg
  have hAz : A = flatGrad f := by
    rw [hA]
    have hconst : constBond c = 0 := by
      apply bfl2Equiv.injective
      funext b
      exact hc b.2
    rw [hconst,add_zero]
  refine ⟨f - constSite (g csOrigin), ?_, ?_⟩
  · rw [map_sub]
    funext y
    change g y - flatSiteQ (constSite (g csOrigin)) y = 0
    rw [flatSiteQ_const, hgc,sub_self]
  · rw [map_sub,flatGrad_constSite,sub_zero]
    exact hAz

/-- The former finite-lattice inverse obstruction is now DISCHARGED. -/
theorem nativeJointKernel : NativeJointKernel := by
  intro A hC hR hQ
  obtain ⟨f,hf,hA⟩ := curl_Q_kernel_potential A hC hQ
  rw [hA] at hR ⊢
  exact gauge_excludes_Qprime_gradients f hf hR

theorem basePrecision_positive (a : ℝ) (ha : 0 < a) (A : H) (hA : A ≠ 0) :
    (0 : ℝ) < inner ℝ A (basePrecision a A) :=
  (basePrecision_strict_iff a ha).mpr nativeJointKernel A hA

theorem native_datum_exists (a : ℝ) (ha : 0 < a) :
    ∃ D : AdalyFormal.Balaban.VariationalProjectorH1.BalabanCovarianceData H (CFL2 witnessL 2),
      D.Ginv = basePrecision a ∧ D.Q = nativeLinearQ (trivialU witnessL) 2 ∧
      D.Qstar = (nativeLinearQ (trivialU witnessL) 2).adjoint :=
  (exists_native_datum_iff a ha).mpr nativeJointKernel
end HConstruction.DRepair
