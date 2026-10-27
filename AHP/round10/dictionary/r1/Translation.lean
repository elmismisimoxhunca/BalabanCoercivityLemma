import DrEquiv

/-! Exact translation covariance of the frozen local differential operators.
The nonlinear blocking and gauge-fixing projection are not covered here. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 8000
noncomputable section
namespace AdalyFormal.Round10.Dictionary.Translation
open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2 RMap gradValueCovariant curlValueCovariant)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
open AdalyFormal.Balaban.DeltaPrimeOperator
open AdalyFormal.Balaban.DeltaPrime
open AdalyFormal.StatementLaneR6
open AdalyFormal.GaugeCov (adjoint_eqv ringInverse_intertwine)
variable {L : PeriodicLatticeExtent}

/-! These four definitions/lemmas are verbatim from round 6. -/
def siteTranslation {L : PeriodicLatticeExtent} (a : PeriodicLatticeSite L) :
    PeriodicLatticeSite L ≃ PeriodicLatticeSite L := Equiv.addRight a

def bondTranslation {L : PeriodicLatticeExtent} (a : PeriodicLatticeSite L) :
    Bond L ≃ Bond L := Equiv.prodCongr (siteTranslation a) (Equiv.refl _)

theorem translation_shift {L : PeriodicLatticeExtent}
    (a x : PeriodicLatticeSite L) (μ : Fin 3) :
    periodicLatticeShift (x + a) μ = periodicLatticeShift x μ + a := by
  funext ν
  by_cases h : ν = μ
  · subst ν
    simp [periodicLatticeShift, add_assoc, add_comm]
  · simp [periodicLatticeShift, h]

noncomputable def bondPullback {L : PeriodicLatticeExtent} (a : PeriodicLatticeSite L) :
    BondFnL2 L ≃ₗᵢ[ℝ] BondFnL2 L :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℝ SuTwo (bondTranslation a).symm

def sitePullback (a : PeriodicLatticeSite L) : SiteL2 L ≃ₗᵢ[ℝ] SiteL2 L :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℝ SuTwo (siteTranslation a).symm

def plaqTranslation (a : PeriodicLatticeSite L) :
    PeriodicLatticePlaquette L ≃ PeriodicLatticePlaquette L :=
  Equiv.prodCongr (siteTranslation a) (Equiv.refl _)

def cfgPullback (a : PeriodicLatticeSite L) (U : LinkCfg L) : LinkCfg L :=
  fun e => U (bondTranslation a e)

@[simp] theorem bondPullback_apply (a : PeriodicLatticeSite L) (v : BondFnL2 L) (e : Bond L) :
    bondPullback a v e = v (e.1 + a, e.2) := rfl

@[simp] theorem sitePullback_apply (a : PeriodicLatticeSite L) (v : SiteL2 L)
    (x : PeriodicLatticeSite L) : sitePullback a v x = v (x + a) := rfl

@[simp] theorem plaqTranslation_apply (a : PeriodicLatticeSite L) (p : PeriodicLatticePlaquette L) :
    plaqTranslation a p = (p.1 + a, p.2) := rfl

/-- Covariance requires no hypothesis on U; the background is pulled back too. -/
theorem grad_translate (a : PeriodicLatticeSite L) (U : LinkCfg L) (f : SiteL2 L) :
    gradL2 (cfgPullback a U) (sitePullback a f) = bondPullback a (gradL2 U f) := by
  apply PiLp.ext
  rintro ⟨x, μ⟩
  simp only [gradL2_apply, bondPullback_apply]
  simp [gradValueCovariant, cfgPullback, bondTranslation, siteTranslation, translation_shift]

theorem div_translate (a : PeriodicLatticeSite L) (U : LinkCfg L) (x : BondFnL2 L) :
    gradAdj (cfgPullback a U) (bondPullback a x) = sitePullback a (gradAdj U x) :=
  adjoint_eqv (sitePullback a) (bondPullback a) _ _ (grad_translate a U) x

theorem lap_translate (a : PeriodicLatticeSite L) (U : LinkCfg L) (f : SiteL2 L) :
    lapFull (cfgPullback a U) (sitePullback a f) = sitePullback a (lapFull U f) := by
  change gradAdj _ (gradL2 _ (sitePullback a f)) = sitePullback a (gradAdj U (gradL2 U f))
  rw [grad_translate, div_translate]

theorem siteMask_translate (a : PeriodicLatticeSite L) (S : Set (PeriodicLatticeSite L))
    (hS : ∀ x, x + a ∈ S ↔ x ∈ S) (f : SiteL2 L) :
    siteMask S (sitePullback a f) = sitePullback a (siteMask S f) := by
  classical
  apply PiLp.ext
  intro x
  simp only [siteMask_apply, sitePullback_apply, hS]

theorem curl_translate (a : PeriodicLatticeSite L) (U : LinkCfg L) (x : BondFnL2 L)
    (p : PeriodicLatticePlaquette L) :
    curlValueCovariant (cfgPullback a U) (WithLp.ofLp (bondPullback a x)) p =
      curlValueCovariant U (WithLp.ofLp x) (plaqTranslation a p) := by
  simp [curlValueCovariant, cfgPullback, bondTranslation, siteTranslation, translation_shift]

theorem holonomy_translate (a : PeriodicLatticeSite L) (U : LinkCfg L)
    (p : PeriodicLatticePlaquette L) :
    periodicPlaquetteHolonomy (cfgPullback a U) p = periodicPlaquetteHolonomy U (plaqTranslation a p) := by
  simp [periodicPlaquetteHolonomy, cfgPullback, bondTranslation, siteTranslation, translation_shift]

/-- The complete frozen plaquette bilinear form, including the curvature terms. -/
theorem bilPlaq_translate (a : PeriodicLatticeSite L) (U : LinkCfg L) (x y : BondFnL2 L)
    (p : PeriodicLatticePlaquette L) :
    bilPlaq (cfgPullback a U) p (WithLp.ofLp (bondPullback a x)) (WithLp.ofLp (bondPullback a y)) =
      bilPlaq U (plaqTranslation a p) (WithLp.ofLp x) (WithLp.ofLp y) := by
  rw [bilPlaq_atoms, bilPlaq_atoms]
  simp only [b1LM, b2LM, b3LM, b4LM, LinearMap.comp_apply, smulILM_apply,
    curlMatLM_apply, curl_translate]
  simp [a1LM, a2LM, a3LM, a4LM, bondMatRLM_apply, bondMatLM_apply,
    reHolonomy, imHolonomy, holonomyElemInv, holonomyElem, periodicPlaquetteHolonomy,
    cfgPullback, bondTranslation, siteTranslation, translation_shift]

theorem raw_translate (a : PeriodicLatticeSite L) (U : LinkCfg L)
    (P : Set (PeriodicLatticePlaquette L)) (hP : ∀ p, plaqTranslation a p ∈ P ↔ p ∈ P)
    (x y : BondFnL2 L) :
    deltaPrimeBilRawLoc (cfgPullback a U) P (WithLp.ofLp (bondPullback a x))
      (WithLp.ofLp (bondPullback a y)) = deltaPrimeBilRawLoc U P (WithLp.ofLp x) (WithLp.ofLp y) := by
  classical
  rw [deltaPrimeBilRawLoc_apply, deltaPrimeBilRawLoc_apply]
  simp_rw [bilPlaq_translate]
  calc
    _ = ∑ p, (if plaqTranslation a p ∈ P then
      bilPlaq U (plaqTranslation a p) (WithLp.ofLp x) (WithLp.ofLp y) else 0) := by
        apply Finset.sum_congr rfl
        intro p _
        rw [hP]
    _ = _ := Equiv.sum_comp (plaqTranslation a)
      (fun p => if p ∈ P then bilPlaq U p (WithLp.ofLp x) (WithLp.ofLp y) else 0)

theorem normalized_translate (a : PeriodicLatticeSite L) (U : LinkCfg L)
    (P : Set (PeriodicLatticePlaquette L)) (hP : ∀ p, plaqTranslation a p ∈ P ↔ p ∈ P)
    (x y : BondFnL2 L) :
    deltaPrimeBilL2NormLoc (cfgPullback a U) P (bondPullback a x) (bondPullback a y) =
      deltaPrimeBilL2NormLoc U P x y := by
  change deltaPrimeBilNormLoc (cfgPullback a U) P (WithLp.ofLp (bondPullback a x))
    (WithLp.ofLp (bondPullback a y)) = deltaPrimeBilNormLoc U P (WithLp.ofLp x) (WithLp.ofLp y)
  unfold deltaPrimeBilNormLoc
  simp only [LinearMap.smul_apply, LinearMap.add_apply, LinearMap.flip_apply, smul_eq_mul]
  rw [raw_translate a U P hP, raw_translate a U P hP]

theorem curl_form_translate (a : PeriodicLatticeSite L) (U : LinkCfg L)
    (P : Set (PeriodicLatticePlaquette L)) (hP : ∀ p, plaqTranslation a p ∈ P ↔ p ∈ P)
    (x y : BondFnL2 L) :
    ⟪plaqMask P (AdalyFormal.Balaban.DeltaKFull.curlCovariantLM_L2 (cfgPullback a U) (bondPullback a x)),
      plaqMask P (AdalyFormal.Balaban.DeltaKFull.curlCovariantLM_L2 (cfgPullback a U) (bondPullback a y))⟫ =
    ⟪plaqMask P (AdalyFormal.Balaban.DeltaKFull.curlCovariantLM_L2 U x),
      plaqMask P (AdalyFormal.Balaban.DeltaKFull.curlCovariantLM_L2 U y)⟫ := by
  classical
  simp only [PiLp.inner_apply, plaqMask_apply, AdalyFormal.GaugeCov.curlL2_apply, curl_translate]
  calc
    _ = ∑ p, ⟪(if plaqTranslation a p ∈ P then
      curlValueCovariant U (WithLp.ofLp x) (plaqTranslation a p) else 0),
      (if plaqTranslation a p ∈ P then
      curlValueCovariant U (WithLp.ofLp y) (plaqTranslation a p) else 0)⟫ := by
        apply Finset.sum_congr rfl
        intro p _
        rw [hP]
    _ = _ := Equiv.sum_comp (plaqTranslation a)
      (fun p => ⟪(if p ∈ P then curlValueCovariant U (WithLp.ofLp x) p else 0),
        (if p ∈ P then curlValueCovariant U (WithLp.ofLp y) p else 0)⟫)

/-- True operator covariance of the frozen Hessian; no compression/inverse
interchange. This is NOT yet covariance of the dressed all-plaquette carrier. -/
theorem deltaK_translate (a : PeriodicLatticeSite L) (U : LinkCfg L)
    (P : Set (PeriodicLatticePlaquette L)) (hP : ∀ p, plaqTranslation a p ∈ P ↔ p ∈ P)
    (y : BondFnL2 L) :
    deltaKLocCLM (cfgPullback a U) P (bondPullback a y) = bondPullback a (deltaKLocCLM U P y) := by
  apply AdalyFormal.GaugeCov.op_of_form (bondPullback a).toLinearEquiv.toLinearMap
    (bondPullback a).inner_map_map (bondPullback a).surjective
  intro x z
  change ⟪bondPullback a x, deltaKLocCLM (cfgPullback a U) P (bondPullback a z)⟫ = _
  rw [inner_deltaKLocCLM, inner_deltaKLocCLM, curl_form_translate a U P hP,
    normalized_translate a U P hP]

/-- An invariant background has a commuting all-plaquette Hessian. -/
theorem deltaK_all_comm (a : PeriodicLatticeSite L) (U : LinkCfg L)
    (hU : cfgPullback a U = U) (x : BondFnL2 L) :
    deltaKLocCLM U Set.univ (bondPullback a x) = bondPullback a (deltaKLocCLM U Set.univ x) := by
  have h := deltaK_translate a U Set.univ (fun _ => Iff.rfl) x
  rwa [hU] at h

#print axioms siteTranslation
#print axioms bondTranslation
#print axioms translation_shift
#print axioms bondPullback
#print axioms sitePullback
#print axioms plaqTranslation
#print axioms cfgPullback
#print axioms bondPullback_apply
#print axioms sitePullback_apply
#print axioms plaqTranslation_apply
#print axioms grad_translate
#print axioms div_translate
#print axioms lap_translate
#print axioms siteMask_translate
#print axioms curl_translate
#print axioms holonomy_translate
#print axioms bilPlaq_translate
#print axioms raw_translate
#print axioms normalized_translate
#print axioms curl_form_translate
#print axioms deltaK_translate
#print axioms deltaK_all_comm
end AdalyFormal.Round10.Dictionary.Translation
