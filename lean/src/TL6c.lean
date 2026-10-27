import TLz6b

set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace AdalyFormal.Thin
open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.Balaban.CovariantHjMinimizer (PlaqFnL2)
open AdalyFormal.Balaban.DeltaKFull (curlCovariantCLM_L2 curlCovariantLM_L2)
open AdalyFormal.Balaban.CStarDeltaKCOperator (curlAdjoint)
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.StatementLaneR6
open AdalyFormal.Balaban.DeltaPrimeOperator (bilPlaq)

theorem dstarDLoc_eq_comp {L : PeriodicLatticeExtent} (U : Cfg L) (P : Set (PeriodicLatticePlaquette L)) :
    LinearMap.toContinuousLinearMap (dstarDLoc U P) =
      (ContinuousLinearMap.adjoint (curlCovariantCLM_L2 U)).comp
        ((LinearMap.toContinuousLinearMap (plaqMask P)).comp (curlCovariantCLM_L2 U)) := by
  ext1 y
  simp only [ContinuousLinearMap.comp_apply, LinearMap.coe_toContinuousLinearMap']
  show curlAdjoint U (plaqMask P (curlCovariantLM_L2 U y)) = _
  rw [curlAdjoint, LinearMap.adjoint_eq_toCLM_adjoint]
  rfl

theorem desc_dstarDLoc {Lt L : PeriodicLatticeExtent} (h : Covers Lt L) (U : Cfg L) (P : Set (PeriodicLatticePlaquette L)) :
    Desc (covE h) (covE h) (LinearMap.toContinuousLinearMap (dstarDLoc U P))
      (LinearMap.toContinuousLinearMap (dstarDLoc (pullCfg h (fun _ => 0) U) (phiP h (fun _ => 0) ⁻¹' P))) := by
  classical
  rw [dstarDLoc_eq_comp, dstarDLoc_eq_comp]
  exact (desc_curl h U).comp ((desc_plaqMask h P).comp (desc_curl h U).adjoint)

open Classical in
theorem raw_pull {Lt L : PeriodicLatticeExtent} (h : Covers Lt L) (o : Fin 3 → ℕ) (U : Cfg L)
    (P : Set (PeriodicLatticePlaquette L)) (A B : Bond L → SuTwo) :
    deltaPrimeBilRawLoc (pullCfg h o U) (phiP h o ⁻¹' P) (pullBond h o A) (pullBond h o B) =
      ∑ p : PeriodicLatticePlaquette Lt, (fun q => if q ∈ P then bilPlaq U q A B else 0) (phiP h o p) := by
  rw [deltaPrimeBilRawLoc_apply]
  refine Finset.sum_congr rfl (fun p _ => ?_)
  simp only [Set.mem_preimage, bilPlaq_nat]

open Classical in
theorem normLoc_apply {L : PeriodicLatticeExtent} (U : Cfg L) (P : Set (PeriodicLatticePlaquette L)) (A B : Bond L → SuTwo) :
    deltaPrimeBilNormLoc U P A B = (1 / 2 : ℝ) * ((1 / 2 : ℝ) * (deltaPrimeBilRawLoc U P A B + deltaPrimeBilRawLoc U P B A)) := by
  unfold deltaPrimeBilNormLoc
  simp only [LinearMap.smul_apply, LinearMap.add_apply, LinearMap.flip_apply, smul_eq_mul]

theorem bilL2_apply {L : PeriodicLatticeExtent} (U : Cfg L) (P : Set (PeriodicLatticePlaquette L)) (x y : BondFnL2 L) :
    deltaPrimeBilL2NormLoc U P x y = deltaPrimeBilNormLoc U P (WithLp.ofLp x) (WithLp.ofLp y) := rfl

open Classical in
/-- periodic form identity -/
theorem bil_periodic {Lt L : PeriodicLatticeExtent} (h : Covers Lt L) (U : Cfg L)
    (P : Set (PeriodicLatticePlaquette L)) (y x : BondFnL2 L) :
    deltaPrimeBilL2NormLoc (pullCfg h (fun _ => 0) U) (phiP h (fun _ => 0) ⁻¹' P) (liftF (phiE h (fun _ => 0)) y)
      (liftF (phiE h (fun _ => 0)) x) = (Fintype.card (DeckIdx Lt L) : ℝ) * deltaPrimeBilL2NormLoc U P y x := by
  have hπ : FibreCount (phiP h (fun _ => 0)) (Fintype.card (DeckIdx Lt L)) := by
    rw [← covP_pi]; exact (covP h).fibreCount
  rw [bilL2_apply, bilL2_apply, normLoc_apply, normLoc_apply]
  have e1 : (WithLp.ofLp (liftF (phiE h (fun _ => 0)) y)) = pullBond h (fun _ => 0) (WithLp.ofLp y) := rfl
  have e2 : (WithLp.ofLp (liftF (phiE h (fun _ => 0)) x)) = pullBond h (fun _ => 0) (WithLp.ofLp x) := rfl
  rw [e1, e2, raw_pull, raw_pull]
  rw [sum_comp_fibre hπ (fun q => if q ∈ P then bilPlaq U q (WithLp.ofLp y) (WithLp.ofLp x) else 0),
    sum_comp_fibre hπ (fun q => if q ∈ P then bilPlaq U q (WithLp.ofLp x) (WithLp.ofLp y) else 0),
    deltaPrimeBilRawLoc_apply, deltaPrimeBilRawLoc_apply]
  ring

open Classical in
theorem raw_deck {Lt L : PeriodicLatticeExtent} (h : Covers Lt L) (d : DeckIdx Lt L) (U : Cfg L)
    (P : Set (PeriodicLatticePlaquette L)) (a b : Bond Lt → SuTwo) :
    deltaPrimeBilRawLoc (pullCfg h (fun _ => 0) U) (phiP h (fun _ => 0) ⁻¹' P)
      (pullBond (Covers.refl Lt) (fun μ => (d μ).val * (L μ + 1)) a) (pullBond (Covers.refl Lt) (fun μ => (d μ).val * (L μ + 1)) b)
    = deltaPrimeBilRawLoc (pullCfg h (fun _ => 0) U) (phiP h (fun _ => 0) ⁻¹' P) a b := by
  have key := raw_pull (Covers.refl Lt) (fun μ => (d μ).val * (L μ + 1)) (pullCfg h (fun _ => 0) U)
    (phiP h (fun _ => 0) ⁻¹' P) a b
  rw [pullCfg_tau] at key
  have hinv : phiP (Covers.refl Lt) (fun μ => (d μ).val * (L μ + 1)) ⁻¹' (phiP h (fun _ => 0) ⁻¹' P) =
      phiP h (fun _ => 0) ⁻¹' P := by
    ext p; simp only [Set.mem_preimage, phiP_tau0]
  rw [hinv] at key
  rw [key, deltaPrimeBilRawLoc_apply]
  have hτ : ∀ p, phiP (Covers.refl Lt) (fun μ => (d μ).val * (L μ + 1)) p = (covP h).τ d p := by
    intro p; exact congrFun (covP_tau h d).symm p
  simp only [hτ]
  exact Equiv.sum_comp ((covP h).τ d) (fun q => if q ∈ phiP h (fun _ => 0) ⁻¹' P then
    bilPlaq (pullCfg h (fun _ => 0) U) q a b else 0)

open Classical in
theorem bil_deck {Lt L : PeriodicLatticeExtent} (h : Covers Lt L) (d : DeckIdx Lt L) (U : Cfg L)
    (P : Set (PeriodicLatticePlaquette L)) (u v : BondFnL2 Lt) :
    deltaPrimeBilL2NormLoc (pullCfg h (fun _ => 0) U) (phiP h (fun _ => 0) ⁻¹' P) ((covE h).pull d u) ((covE h).pull d v) =
      deltaPrimeBilL2NormLoc (pullCfg h (fun _ => 0) U) (phiP h (fun _ => 0) ⁻¹' P) u v := by
  rw [bilL2_apply, bilL2_apply, normLoc_apply, normLoc_apply]
  have e : ∀ w : BondFnL2 Lt, WithLp.ofLp ((covE h).pull d w) =
      pullBond (Covers.refl Lt) (fun μ => (d μ).val * (L μ + 1)) (WithLp.ofLp w) := by
    intro w
    funext e
    show w ((covE h).τ d e) = w (phiE (Covers.refl Lt) _ e)
    rw [show ((covE h).τ d e) = phiE (Covers.refl Lt) (fun μ => (d μ).val * (L μ + 1)) e from congrFun (covE_tau h d) e]
  rw [e, e, raw_deck, raw_deck]

open Classical in
theorem desc_deltaPrimeOpLoc {Lt L : PeriodicLatticeExtent} (h : Covers Lt L) (U : Cfg L) (P : Set (PeriodicLatticePlaquette L)) :
    Desc (covE h) (covE h) (LinearMap.toContinuousLinearMap (deltaPrimeOpLoc U P))
      (LinearMap.toContinuousLinearMap (deltaPrimeOpLoc (pullCfg h (fun _ => 0) U) (phiP h (fun _ => 0) ⁻¹' P))) := by
  haveI := deckIdx_nonempty h
  refine desc_of_riesz (covE h) _ _ (fun d u v => ?_) (fun y x => ?_)
  · simp only [LinearMap.coe_toContinuousLinearMap', inner_deltaPrimeOpLoc]
    exact bil_deck h d U P u v
  · simp only [LinearMap.coe_toContinuousLinearMap', inner_deltaPrimeOpLoc]
    have := bil_periodic h U P y x
    rw [← covE_pi] at this
    exact this

open Classical in
theorem desc_deltaKLoc {Lt L : PeriodicLatticeExtent} (h : Covers Lt L) (U : Cfg L) (P : Set (PeriodicLatticePlaquette L)) :
    Desc (covE h) (covE h) (deltaKLocCLM U P)
      (deltaKLocCLM (pullCfg h (fun _ => 0) U) (phiP h (fun _ => 0) ⁻¹' P)) :=
  (desc_dstarDLoc h U P).add (desc_deltaPrimeOpLoc h U P)

end AdalyFormal.Thin
