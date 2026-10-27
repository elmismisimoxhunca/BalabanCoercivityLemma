import DrEquiv

/-! Symmetry infrastructure on the actual frozen carriers. No spectral assertion. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 8000
noncomputable section
namespace AdalyFormal.Round10.Dictionary
open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLane2
open AdalyFormal.StatementLaneG
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.D1Literal
open AdalyFormal.GaugeCov
open AdalyFormal.Balaban.AlphaAnalyticity (GaugeFn)
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)

section Linear
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- A symmetric quadratic form invariant under an orthogonal map determines a
commuting operator. In particular, the second jet itself need not be linear. -/
theorem comm_of_quad (T : E →L[ℝ] E) (J : E ≃ₗᵢ[ℝ] E)
    (hs : ∀ x y, ⟪T x, y⟫ = ⟪x, T y⟫)
    (hq : ∀ x, ⟪J x, T (J x)⟫ = ⟪x, T x⟫) (y : E) :
    T (J y) = J (T y) := by
  have hb (x : E) : ⟪J x, T (J y)⟫ = ⟪x, T y⟫ := by
    have h := hq (x + y)
    have hx := hq x
    have hy := hq y
    have hs1 : ⟪J y, T (J x)⟫ = ⟪J x, T (J y)⟫ := by
      rw [← hs, real_inner_comm]
    have hs2 : ⟪y, T x⟫ = ⟪x, T y⟫ := by rw [← hs, real_inner_comm]
    simp only [map_add, inner_add_left, inner_add_right] at h
    linarith
  apply ext_inner_left ℝ
  intro v
  obtain ⟨x, rfl⟩ := J.surjective v
  rw [hb, J.inner_map_map]

/-- Differentiation preserves equivariance, including the totalized derivative
at a nondifferentiable point. This does not assert differentiability. -/
theorem deriv_comm (D : ℝ → E →L[ℝ] E) (J : E ≃ₗᵢ[ℝ] E)
    (h : ∀ t x, D t (J x) = J (D t x)) (t : ℝ) (x : E) :
    deriv D t (J x) = J (deriv D t x) := by
  by_cases hd : DifferentiableAt ℝ D t
  · have hd' : HasDerivAt D (deriv D t) t := hd.hasDerivAt
    let L : (E →L[ℝ] E) →L[ℝ] E := ContinuousLinearMap.apply ℝ E (J x)
    let M : (E →L[ℝ] E) →L[ℝ] E :=
      J.toLinearIsometry.toContinuousLinearMap.comp (ContinuousLinearMap.apply ℝ E x)
    have hl := L.hasFDerivAt.comp_hasDerivAt t hd'
    have hm := M.hasFDerivAt.comp_hasDerivAt t hd'
    have he : (fun s => L (D s)) = fun s => M (D s) := funext (fun s => h s x)
    change HasDerivAt (fun s => L (D s)) (L (deriv D t)) t at hl
    rw [he] at hl
    exact hl.unique hm
  · rw [deriv_zero_of_not_differentiableAt hd]
    simp

/-- Every real eigenspace of a symmetry is invariant under a commuting map. -/
theorem real_sector_invariant (T : E →L[ℝ] E) (J : E ≃ₗᵢ[ℝ] E)
    (h : ∀ x, T (J x) = J (T x)) (c : ℝ) {x : E} (hx : J x = c • x) :
    J (T x) = c • T x := by rw [← h, hx, map_smul]

/-- Opposite charge blocks are orthogonal also for a commuting operator's
bilinear form. Symmetry of the operator is not needed. -/
theorem opposite_charge_cross_zero (T : E →L[ℝ] E) (J : E ≃ₗᵢ[ℝ] E)
    (h : ∀ x, T (J x) = J (T x)) {x y : E} (hx : J x = x) (hy : J y = -y) :
    ⟪x, T y⟫ = 0 := by
  have hi := J.inner_map_map x (T y)
  rw [hx, ← h, hy, map_neg, inner_neg_right] at hi
  linarith

/-- Full kernels, not only selected eigenvectors, are invariant. -/
theorem kernel_invariant (T : E →L[ℝ] E) (J : E ≃ₗᵢ[ℝ] E)
    (h : ∀ x, T (J x) = J (T x)) {x : E} (hx : T x = 0) : T (J x) = 0 := by
  rw [h, hx, map_zero]

/-- Exact orthogonal splitting for an involutive orthogonal symmetry. It makes
no unsupported claim that one summand of the crossing kernel vanishes. -/
theorem involution_split (J : E ≃ₗᵢ[ℝ] E) (hJ : ∀ x, J (J x) = x) (x : E) :
    ∃ xp xm : E, x = xp + xm ∧ J xp = xp ∧ J xm = -xm ∧ ⟪xp, xm⟫ = 0 := by
  let xp : E := (1 / 2 : ℝ) • (x + J x)
  let xm : E := (1 / 2 : ℝ) • (x - J x)
  have hp : J xp = xp := by simp only [xp, map_smul, map_add, hJ]; rw [add_comm]
  have hm : J xm = -xm := by
    simp only [xm, map_smul, map_sub, hJ]
    rw [← smul_neg, neg_sub]
  refine ⟨xp, xm, ?_, hp, hm, ?_⟩
  · dsimp [xp, xm]; module
  · have hi := J.inner_map_map xp xm
    rw [hp, hm, inner_neg_right] at hi
    linarith

theorem involution_kernel_split (T : E →L[ℝ] E) (J : E ≃ₗᵢ[ℝ] E)
    (hJ : ∀ x, J (J x) = x) (h : ∀ x, T (J x) = J (T x))
    {x : E} (hx : T x = 0) :
    ∃ xp xm : E, x = xp + xm ∧ J xp = xp ∧ J xm = -xm ∧
      ⟪xp, xm⟫ = 0 ∧ T xp = 0 ∧ T xm = 0 := by
  let xp : E := (1 / 2 : ℝ) • (x + J x)
  let xm : E := (1 / 2 : ℝ) • (x - J x)
  have hp : J xp = xp := by simp only [xp, map_smul, map_add, hJ]; rw [add_comm]
  have hm : J xm = -xm := by
    simp only [xm, map_smul, map_sub, hJ]
    rw [← smul_neg, neg_sub]
  refine ⟨xp, xm, ?_, hp, hm, ?_, ?_, ?_⟩
  · dsimp [xp, xm]; module
  · have hi := J.inner_map_map xp xm
    rw [hp, hm, inner_neg_right] at hi
    linarith
  · simp [xp, h, hx]
  · simp [xm, h, hx]
end Linear

/-! The next theorem is the round-9 all-plaquette covariance proof, copied
verbatim. All definitions in its statement are frozen library definitions. -/
theorem Ginv_all_gauge {ell k : ℕ} {Lu : PeriodicLatticeExtent} (hell : 0 < ell)
    (S : Tower (scaleUp ell k Lu)) (U : LinkCfg (scaleUp ell k Lu)) (a : ℝ)
    (Lam : Set (PeriodicLatticeSite Lu)) (γ : GaugeFn (scaleUp ell k Lu))
    (x : ↥(bondSupp (geomOf ell k S))) :
    (dataS selAll selAll (gparams ell k Lu hell S (periodicGaugeTransform γ U) a Lam)).Ginv
        (adEL γ (geomOf ell k S) x) =
      adEL γ (geomOf ell k S) ((dataS selAll selAll (gparams ell k Lu hell S U a Lam)).Ginv x) := by
  have hB := bondEqv_gauge (gparams ell k Lu hell S U a Lam) γ
  have hD := hB.baseEqv
  have hW : ∀ z, Wop (geomOf ell k S) (periodicGaugeTransform γ U) a (adBL γ z) =
      adBL γ (Wop (geomOf ell k S) U a z) := fun z => hB.W z
  have hΔ : ∀ z, AdalyFormal.StatementLaneR6.deltaKLocCLM (periodicGaugeTransform γ U) Set.univ
      (adBL γ z) = adBL γ (AdalyFormal.StatementLaneR6.deltaKLocCLM U Set.univ z) :=
    fun z => deltaKLocCLM_gauge γ U Set.univ z
  have hDp : ∀ z, DpiFullS selAll (geomOf ell k S) (periodicGaugeTransform γ U) a (adBL γ z) =
      adBL γ (DpiFullS selAll (geomOf ell k S) U a z) := by
    intro z
    simp only [DpiFullS, DeltaS, selAll, ContinuousLinearMap.comp_apply]
    rw [hW, hΔ]
    exact adjoint_intertwine (adBL γ) (adBL γ) hW _
  have hDpi : (dataS selAll selAll (gparams ell k Lu hell S (periodicGaugeTransform γ U) a Lam)).Dpi
      (adEL γ (geomOf ell k S) x) =
      adEL γ (geomOf ell k S) ((dataS selAll selAll (gparams ell k Lu hell S U a Lam)).Dpi x) := by
    show pE (geomOf ell k S) (DpiFullS selAll (geomOf ell k S) (periodicGaugeTransform γ U) a
        (iE (geomOf ell k S) (adEL γ (geomOf ell k S) x))) =
      adEL γ (geomOf ell k S) (pE (geomOf ell k S)
        (DpiFullS selAll (geomOf ell k S) U a (iE (geomOf ell k S) x)))
    rw [iE_adEL, hDp, pE_adBL]
  have hT : (dataS selAll selAll (gparams ell k Lu hell S (periodicGaugeTransform γ U) a Lam)).T
      (adEL γ (geomOf ell k S) x) =
      adSL γ ((dataS selAll selAll (gparams ell k Lu hell S U a Lam)).T x) := hD.T x
  have hTs : ∀ s, (dataS selAll selAll (gparams ell k Lu hell S (periodicGaugeTransform γ U) a
      Lam)).Ts (adSL γ s) =
      adEL γ (geomOf ell k S) ((dataS selAll selAll (gparams ell k Lu hell S U a Lam)).Ts s) :=
    hD.Ts
  have hM : (dataS selAll selAll (gparams ell k Lu hell S (periodicGaugeTransform γ U) a Lam)).Mass
      (adEL γ (geomOf ell k S) x) =
      adEL γ (geomOf ell k S) ((dataS selAll selAll (gparams ell k Lu hell S U a Lam)).Mass x) :=
    hD.Mass x
  simp only [BaseDataS.Ginv, add_apply, ContinuousLinearMap.comp_apply]
  rw [hDpi, hT, hTs, hM, map_add, map_add]

section FixedGauge
variable {ell k : ℕ} {Lu : PeriodicLatticeExtent} (hell : 0 < ell)
    (S : Tower (scaleUp ell k Lu)) (U : LinkCfg (scaleUp ell k Lu)) (a : ℝ)
    (Lam : Set (PeriodicLatticeSite Lu)) (γ : GaugeFn (scaleUp ell k Lu))
    (hU : periodicGaugeTransform γ U = U)
include hU

/-- A fixed gauge of the background commutes with the actual localized carrier. -/
theorem localized_comm (x : ↥(bondSupp (geomOf ell k S))) :
    (gparams ell k Lu hell S U a Lam).data.Ginv (adEL γ (geomOf ell k S) x) =
      adEL γ (geomOf ell k S) ((gparams ell k Lu hell S U a Lam).data.Ginv x) := by
  have h := (AdalyFormal.M1GaugeW4.baseEqv_gparams hell S a Lam U γ).Ginv x
  rwa [hU] at h

theorem all_comm (x : ↥(bondSupp (geomOf ell k S))) :
    (dataS selAll selAll (gparams ell k Lu hell S U a Lam)).Ginv (adEL γ (geomOf ell k S) x) =
      adEL γ (geomOf ell k S) ((dataS selAll selAll (gparams ell k Lu hell S U a Lam)).Ginv x) := by
  have h := Ginv_all_gauge hell S U a Lam γ x
  rwa [hU] at h

theorem correction_comm (x : ↥(bondSupp (geomOf ell k S))) :
    (gparams ell k Lu hell S U a Lam).data.Delta2 (gparams ell k Lu hell S U a Lam).data_laws
      (adEL γ (geomOf ell k S) x) = adEL γ (geomOf ell k S)
        ((gparams ell k Lu hell S U a Lam).data.Delta2
          (gparams ell k Lu hell S U a Lam).data_laws x) := by
  apply comm_of_quad _ (adEL γ (geomOf ell k S))
    ((gparams ell k Lu hell S U a Lam).data.Delta2_spec
      (gparams ell k Lu hell S U a Lam).data_laws).1
  intro y
  have hB := AdalyFormal.M1GaugeW4.baseEqv_gparams hell S a Lam U γ
  rw [hU] at hB
  rw [((gparams ell k Lu hell S U a Lam).data.Delta2_spec
    (gparams ell k Lu hell S U a Lam).data_laws).2,
    ((gparams ell k Lu hell S U a Lam).data.Delta2_spec
    (gparams ell k Lu hell S U a Lam).data_laws).2, hB.C2, hB.H]
  calc
    _ = 2 * ⟪adEL γ (geomOf ell k S)
        ((gparams ell k Lu hell S U a Lam).data.H ((gparams ell k Lu hell S U a Lam).data.C2 y)),
        adEL γ (geomOf ell k S) (gparams ell k Lu hell S U a Lam).data.J⟫ := by rw [← hB.J]
    _ = _ := by rw [LinearIsometryEquiv.inner_map_map]

theorem H_comm (f : FSp (geomOf ell k S)) :
    (gparams ell k Lu hell S U a Lam).data.H (adFL γ (geomOf ell k S) f) =
      adEL γ (geomOf ell k S) ((gparams ell k Lu hell S U a Lam).data.H f) := by
  have h := (AdalyFormal.M1GaugeW4.baseEqv_gparams hell S a Lam U γ).H f
  rwa [hU] at h

/-- Quadratic equivariance, deliberately NOT a linear-sector assertion. -/
theorem C2_equivariant (x : ↥(bondSupp (geomOf ell k S))) :
    (gparams ell k Lu hell S U a Lam).data.C2 (adEL γ (geomOf ell k S) x) =
      adFL γ (geomOf ell k S) ((gparams ell k Lu hell S U a Lam).data.C2 x) := by
  have h := (AdalyFormal.M1GaugeW4.baseEqv_gparams hell S a Lam U γ).C2 x
  rwa [hU] at h
end FixedGauge

def localCorrection {ell k : ℕ} {Lu : PeriodicLatticeExtent} (hell : 0 < ell)
    (S : Tower (scaleUp ell k Lu)) (U : LinkCfg (scaleUp ell k Lu)) (a : ℝ)
    (Lam : Set (PeriodicLatticeSite Lu)) :
    ↥(bondSupp (geomOf ell k S)) →L[ℝ] ↥(bondSupp (geomOf ell k S)) :=
  (gparams ell k Lu hell S U a Lam).data.Delta2 (gparams ell k Lu hell S U a Lam).data_laws

/-- Pointwise fixed-gauge families have commuting first-order correction. -/
theorem correction_deriv_comm {ell k : ℕ} {Lu : PeriodicLatticeExtent} (hell : 0 < ell)
    (S : Tower (scaleUp ell k Lu)) (V : ℝ → LinkCfg (scaleUp ell k Lu)) (a : ℝ)
    (Lam : Set (PeriodicLatticeSite Lu)) (γ : GaugeFn (scaleUp ell k Lu))
    (hV : ∀ t, periodicGaugeTransform γ (V t) = V t) (t : ℝ)
    (x : ↥(bondSupp (geomOf ell k S))) :
    deriv (fun s : ℝ => localCorrection hell S (V s) a Lam) t (adEL γ (geomOf ell k S) x) =
    adEL γ (geomOf ell k S) (deriv (fun s : ℝ => localCorrection hell S (V s) a Lam) t x) :=
  deriv_comm _ _ (fun s => correction_comm hell S (V s) a Lam γ (hV s)) t x

/-- A canonical q=1 radius cannot match BOTH longitudinal collar and core
lengths of the q-dilated geometry unless q=1. No matrix asymptotic is exactified. -/
theorem no_canonical_radius_dilation {q R R' : ℕ}
    (hc : 2 * R' = 2 * R * q) (hi : 8 * R' + 8 = (8 * R + 8) * q) : q = 1 := by
  have he : R' = R * q := by nlinarith
  rw [he, add_mul] at hi
  have hh : 8 * (R * q) = 8 * R * q := by ring
  rw [hh] at hi
  omega

#print axioms comm_of_quad
#print axioms deriv_comm
#print axioms real_sector_invariant
#print axioms opposite_charge_cross_zero
#print axioms kernel_invariant
#print axioms involution_split
#print axioms involution_kernel_split
#print axioms Ginv_all_gauge
#print axioms localized_comm
#print axioms all_comm
#print axioms correction_comm
#print axioms H_comm
#print axioms C2_equivariant
#print axioms localCorrection
#print axioms correction_deriv_comm
#print axioms no_canonical_radius_dilation
end AdalyFormal.Round10.Dictionary
