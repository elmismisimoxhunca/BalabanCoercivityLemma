import R7Fork.ZHodgeCore

/-! # HodgeFinal -- the three delivered statements, at `flatCfg`, every periodic extent `L`. -/
set_option autoImplicit false
namespace AdalyFormal.GenuineU1H

open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.CovariantOperators
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.IngredientFamilyR2 (SiteL2 gradL2 gradAdj flatCfg)
open AdalyFormal.Balaban.DeltaKFull (curlCovariantCLM_L2)

theorem hodge_K3 {L : PeriodicLatticeExtent} (φ : SiteL2 L)
    (h : gradL2 (flatCfg : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) φ = 0) :
    ∃ X : SuTwo, ∀ x : PeriodicLatticeSite L, φ x = X :=
  K3 φ h

theorem hodge_K1 {L : PeriodicLatticeExtent} (y : BondFnL2 L)
    (hc : curlCovariantCLM_L2 (flatCfg : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) y = 0)
    (hd : gradAdj (flatCfg : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) y = 0) :
    ∃ c : Fin 3 → SuTwo, ∀ b : Bond L, y b = c b.2 :=
  K1 y hc hd

theorem hodge_K2 {L : PeriodicLatticeExtent} (A : BondFnL2 L)
    (h : curlCovariantCLM_L2 (flatCfg : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) A = 0) :
    ∃ (φ : SiteL2 L) (c : Fin 3 → SuTwo),
      A = gradL2 (flatCfg : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) φ + constBond L c :=
  K2 A h

/-- L7 witness: the K1/K2 hypotheses are inhabited by every `constBond`, and the
converse directions hold (constants are flat-harmonic, constant site fields are flat-closed). -/
theorem hodge_converse {L : PeriodicLatticeExtent} (c : Fin 3 → SuTwo) (X : SuTwo) :
    curlCovariantCLM_L2 (flatCfg : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) (constBond L c) = 0 ∧
    gradAdj (flatCfg : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) (constBond L c) = 0 ∧
    gradL2 (flatCfg : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) (constSite L X) = 0 :=
  ⟨curl_flat_constBond c, gradAdj_flat_constBond c, gradL2_flat_constSite X⟩

#print axioms hodge_K3
#print axioms hodge_K1
#print axioms hodge_K2
#print axioms hodge_converse

end AdalyFormal.GenuineU1H
