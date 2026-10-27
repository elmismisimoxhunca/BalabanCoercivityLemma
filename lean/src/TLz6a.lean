import TL5d
import AdalyFormal.Balaban.DeltaPrimeOperator

/-!
# TL6a -- naturality of the plaquette-local bilinear summand of `Δ'`
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace AdalyFormal.Thin
open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.Balaban.DeltaPrimeOperator
open AdalyFormal.Balaban.DeltaPrime
open AdalyFormal.IngredientFamilyR2

def phiP {Lt L : PeriodicLatticeExtent} (h : Covers Lt L) (o : Fin 3 → ℕ) (p : PeriodicLatticePlaquette Lt) :
    PeriodicLatticePlaquette L := (phiS h o p.1, p.2)

theorem holonomy_nat {Lt L : PeriodicLatticeExtent} (h : Covers Lt L) (o : Fin 3 → ℕ) (U : Cfg L)
    (p : PeriodicLatticePlaquette Lt) :
    periodicPlaquetteHolonomy (pullCfg h o U) p = periodicPlaquetteHolonomy U (phiP h o p) := by
  simp only [periodicPlaquetteHolonomy, pullCfg, phiE, phiP, phiS_shift]

/-- pull a bond field (plain functions) back along `phiE` -/
def pullBond {Lt L : PeriodicLatticeExtent} (h : Covers Lt L) (o : Fin 3 → ℕ) (A : Bond L → SuTwo) : Bond Lt → SuTwo :=
  fun e => A (phiE h o e)

theorem curl_nat {Lt L : PeriodicLatticeExtent} (h : Covers Lt L) (o : Fin 3 → ℕ) (U : Cfg L)
    (p : PeriodicLatticePlaquette Lt) (A : Bond L → SuTwo) :
    AdalyFormal.Balaban.CovariantOperators.curlValueCovariant (pullCfg h o U) (pullBond h o A) p
      = AdalyFormal.Balaban.CovariantOperators.curlValueCovariant U A (phiP h o p) := by
  simp only [AdalyFormal.Balaban.CovariantOperators.curlValueCovariant, pullBond, pullCfg, phiE, phiP, phiS_shift]

theorem re_im_nat {Lt L : PeriodicLatticeExtent} (h : Covers Lt L) (o : Fin 3 → ℕ) (U : Cfg L)
    (p : PeriodicLatticePlaquette Lt) :
    reHolonomy (pullCfg h o U) p = reHolonomy U (phiP h o p) ∧ imHolonomy (pullCfg h o U) p = imHolonomy U (phiP h o p) := by
  have := holonomy_nat h o U p
  unfold reHolonomy imHolonomy holonomyElemInv holonomyElem
  rw [this]
  exact ⟨rfl, rfl⟩

theorem a_nat {Lt L : PeriodicLatticeExtent} (h : Covers Lt L) (o : Fin 3 → ℕ) (U : Cfg L)
    (p : PeriodicLatticePlaquette Lt) (A : Bond L → SuTwo) :
    a1LM (pullCfg h o U) p (pullBond h o A) = a1LM U (phiP h o p) A ∧
    a2LM p (pullBond h o A) = a2LM (phiP h o p) A ∧
    a3LM p (pullBond h o A) = a3LM (phiP h o p) A ∧
    a4LM (pullCfg h o U) p (pullBond h o A) = a4LM U (phiP h o p) A := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [a1LM, bondMatRLM_apply, LinearMap.neg_apply, pullBond, pullCfg, phiE, phiP, phiS_shift]
  · simp only [a2LM, bondMatLM_apply, LinearMap.neg_apply, pullBond, phiE, phiP]
  · simp only [a3LM, bondMatLM_apply, pullBond, phiE, phiP]
  · simp only [a4LM, bondMatRLM_apply, pullBond, pullCfg, phiE, phiP, phiS_shift]

theorem bilPlaq_nat {Lt L : PeriodicLatticeExtent} (h : Covers Lt L) (o : Fin 3 → ℕ) (U : Cfg L)
    (p : PeriodicLatticePlaquette Lt) (A B : Bond L → SuTwo) :
    bilPlaq (pullCfg h o U) p (pullBond h o A) (pullBond h o B) = bilPlaq U (phiP h o p) A B := by
  obtain ⟨hre, him⟩ := re_im_nat h o U p
  obtain ⟨a1, a2, a3, a4⟩ := a_nat h o U p A
  obtain ⟨a1', a2', a3', a4'⟩ := a_nat h o U p B
  have hc1 : curlMatLM (pullCfg h o U) p (pullBond h o A) = curlMatLM U (phiP h o p) A := by
    rw [curlMatLM_apply, curlMatLM_apply, curl_nat]
  have hc2 : curlMatLM (pullCfg h o U) p (pullBond h o B) = curlMatLM U (phiP h o p) B := by
    rw [curlMatLM_apply, curlMatLM_apply, curl_nat]
  simp only [bilPlaq, firstBilPlaq, secondBilPlaq, pairBil, traceForm_apply, LinearMap.add_apply, LinearMap.sub_apply,
    LinearMap.flip_apply, LinearMap.comp_apply, b1LM, b2LM, b3LM, b4LM, hre, him, hc1, hc2, a1, a2, a3, a4, a1', a2', a3', a4']

end AdalyFormal.Thin
