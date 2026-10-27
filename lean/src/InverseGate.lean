import NativeSection
import Normalization
set_option autoImplicit false
namespace HConstruction.DRepair
open HConstruction.Carrier HConstruction.Covariance
open AdalyFormal.Balaban.AdmissibleSubspace (witnessL)
open AdalyFormal.Balaban.CovariantHjMinimizer (trivialU)
open AdalyFormal.Balaban.VariationalProjectorH1 (BalabanCovarianceData)

/-- The exact still-open lattice statement. It is a proposition, not an axiom. -/
def NativeJointKernel : Prop :=
  ∀ A : H, flatCurl A = 0 → gaugeConstraint A = 0 →
    nativeLinearQ (trivialU witnessL) 2 A = 0 → A = 0

/-- Finite-dimensional strictly positive precision has a genuine two-sided
inverse; no totalized inverse is mistaken for an isomorphism. -/
theorem positive_inverse {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (T : E →L[ℝ] E)
    (hp : ∀ x : E, x ≠ 0 → (0 : ℝ) < inner ℝ x (T x)) :
    ∃ G : E →L[ℝ] E,
      (∀ x, T (G x) = x) ∧ (∀ x, G (T x) = x) ∧
      (∀ x : E, x ≠ 0 → (0 : ℝ) < inner ℝ x (G x)) := by
  have hz (x : E) (hx : T x = 0) : x = 0 := by
    by_contra hn
    have h := hp x hn
    rw [hx, inner_zero_right] at h
    exact lt_irrefl _ h
  have hi : Function.Injective T := by
    intro x y hxy
    have hh : T (x-y) = 0 := by rw [map_sub, hxy, sub_self]
    exact sub_eq_zero.mp (hz _ hh)
  have hb : Function.Bijective T.toLinearMap :=
    ⟨hi, (LinearMap.injective_iff_surjective).mp hi⟩
  let e : E ≃L[ℝ] E := (LinearEquiv.ofBijective T.toLinearMap hb).toContinuousLinearEquiv
  refine ⟨e.symm.toContinuousLinearMap, ?_, ?_, ?_⟩
  · intro x
    exact e.apply_symm_apply x
  · intro x
    exact e.symm_apply_apply x
  · intro x hx
    have he : e.symm x ≠ 0 := by
      intro hz
      have h := congrArg e hz
      simp only [e.apply_symm_apply, map_zero] at h
      exact hx h
    have h := hp (e.symm x) he
    have heq : T (e.symm x) = x := e.apply_symm_apply x
    rw [heq, real_inner_comm] at h
    exact h

/-- Native-Q surjectivity discharges the full adjoint-injectivity gate. -/
theorem nativeAdjoint_injective :
    Function.Injective (nativeLinearQ (trivialU witnessL) 2).adjoint := by
  intro x y hxy
  have hz : (nativeLinearQ (trivialU witnessL) 2).adjoint (x-y) = 0 := by
    rw [map_sub, hxy, sub_self]
  obtain ⟨A,hA⟩ := nativeLinearQ_surjective (x-y)
  have h : (inner ℝ (x-y) (x-y) : ℝ) = 0 := by
    calc
      inner ℝ (x-y) (x-y) = inner ℝ ((nativeLinearQ (trivialU witnessL) 2) A) (x-y) := by
        rw [hA]
      _ = inner ℝ A ((nativeLinearQ (trivialU witnessL) 2).adjoint (x-y)) :=
        (ContinuousLinearMap.adjoint_inner_right _ _ _).symm
      _ = 0 := by rw [hz, inner_zero_right]
  exact sub_eq_zero.mp (inner_self_eq_zero.mp h)

/-- With any strictly positive supplied fine covariance, the REAL native
Schur operator is strictly positive. No source covariance is asserted here. -/
theorem nativeSchur_strict (G : H →L[ℝ] H)
    (hp : ∀ A : H, A ≠ 0 → (0 : ℝ) < inner ℝ A (G A))
    (B : CFL2 witnessL 2) (hB : B ≠ 0) :
    (0 : ℝ) < inner ℝ B (nativeLinearQ (trivialU witnessL) 2
      (G ((nativeLinearQ (trivialU witnessL) 2).adjoint B))) := by
  have hn : (nativeLinearQ (trivialU witnessL) 2).adjoint B ≠ 0 := by
    intro hz
    apply hB
    apply nativeAdjoint_injective
    simpa only [map_zero] using hz
  rw [← ContinuousLinearMap.adjoint_inner_left]
  exact hp _ hn

/-- Exact completion criterion, not a construction from assumed physical data:
the only inverse/Schur obstruction left at a>0 is this native joint kernel. -/
theorem exists_native_datum_iff (a : ℝ) (ha : 0 < a) :
    (∃ D : BalabanCovarianceData H (CFL2 witnessL 2),
      D.Ginv = basePrecision a ∧ D.Q = nativeLinearQ (trivialU witnessL) 2 ∧
      D.Qstar = (nativeLinearQ (trivialU witnessL) 2).adjoint) ↔ NativeJointKernel := by
  constructor
  · rintro ⟨D,hP,hQ,hQs⟩ A hC hR hN
    have hz : basePrecision a A = 0 := by
      simp [basePrecision, flatDelta, hC, hR, hN]
    have h := D.Gstar_Ginv A
    rw [hP, hz, map_zero] at h
    exact h.symm
  · intro hk
    have hp := (basePrecision_strict_iff a ha).mpr hk
    obtain ⟨G,hG1,hG2,hGp⟩ := positive_inverse (basePrecision a) hp
    let C : CFL2 witnessL 2 →L[ℝ] CFL2 witnessL 2 :=
      (nativeLinearQ (trivialU witnessL) 2).comp
        (G.comp (nativeLinearQ (trivialU witnessL) 2).adjoint)
    have hCp : ∀ B : CFL2 witnessL 2, B ≠ 0 → (0 : ℝ) < inner ℝ B (C B) :=
      nativeSchur_strict G hGp
    obtain ⟨CI,hC1,hC2,_⟩ := positive_inverse C hCp
    refine ⟨{
      Ginv := basePrecision a
      Gstar := G
      Ginv_Gstar := hG1
      Gstar_Ginv := hG2
      Ginv_selfAdjoint := basePrecision_selfAdjoint a
      Ginv_posSemidef := basePrecision_nonneg a ha.le
      Q := nativeLinearQ (trivialU witnessL) 2
      Qstar := (nativeLinearQ (trivialU witnessL) 2).adjoint
      Q_Qstar_adjoint := fun A B => (ContinuousLinearMap.adjoint_inner_right _ _ _).symm
      Comp := C
      Comp_eq := fun _ => rfl
      CompInv := CI
      Comp_CompInv := hC1
      CompInv_Comp := hC2 }, rfl, rfl, rfl⟩

/-- R excludes EVERY Q'-null pure gauge, not just the old test site field.
The remaining Hodge obligation is to put all curl/Q-null fields in this form. -/
theorem gauge_excludes_Qprime_gradients (f : S) (hf : flatSiteQ f = 0)
    (hg : gaugeConstraint (flatGrad f) = 0) : flatGrad f = 0 := by
  have hm : flatSiteDelta f ∈ gaugeImage := ⟨f,hf,rfl⟩
  have he : siteR (flatSiteDelta f) = flatSiteDelta f :=
    Submodule.starProjection_eq_self_iff.mpr hm
  have hd : flatSiteDelta f = 0 := he.symm.trans hg
  have h : (inner ℝ f (flatSiteDelta f) : ℝ) = 0 := by rw [hd, inner_zero_right]
  have hn : ‖flatGrad f‖ ^ 2 = 0 := by
    simpa only [flatSiteDelta, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.adjoint_inner_right, real_inner_self_eq_norm_sq] using h
  exact norm_eq_zero.mp (by nlinarith [norm_nonneg (flatGrad f)])

end HConstruction.DRepair
