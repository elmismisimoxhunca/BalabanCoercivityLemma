import R2RawX

/-!
# GCa1 -- nonlinear gauge equivariance of the raw one-step averaging `rawStep` (R2Raw1)

With `V₀' = coarseGaugeTransform s γ V₀` (stride-`s` background) and `V₁'(b) = γ(b₋) V₁(b) γ(b₋)⁻¹`
(fluctuation read in the frame of the base site):
 * `rProd_gauge`  : `rProd s V₀' V₁' y p = γ y · rProd s V₀ V₁ y p · (γ y)⁻¹`;
 * `sBlock_gauge` : `sBlock s ell V₀' V₁' y = Ad(γ y) (sBlock s ell V₀ V₁ y)` (every site `y`);
 * `rawStep_gauge`: `rawStep s ell V₀' V₁' c = γ(c₋) · rawStep s ell V₀ V₁ c · γ(c₋)⁻¹` (every `c`).
No regularity / smallness hypothesis: exact group identities plus `log_conj`, `exp_ad`.
-/
set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
namespace AdalyFormal.GaugeCov

open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.SuTwoLogExp (su2LogExp su2Log su2Exp M2 SU2 adMap su2_log_conj su2_exp_ad)
open AdalyFormal.Balaban.TowerLawCov (coarsePathHolonomy coarsePathEndpoint coarseGammaPath)
open AdalyFormal.Balaban.CoarseCurl (coarseShift)
open AdalyFormal.Balaban.QjComposite (stepBlockOf coarseGaugeTransform
  coarsePathHolonomy_coarseGaugeTransform)
open AdalyFormal.Balaban.UbarTowerCov (stridedBlockedGauge cPlusS cPlusS_eq stridedBlockedGauge_gauge)
open AdalyFormal.IngredientFamilyR2

variable {L : PeriodicLatticeExtent}

/-- a link field read in the frame of the base site of each link: `b ↦ γ(b₋) V(b) γ(b₋)⁻¹`. -/
def conjCfg (γ : PeriodicLatticeSite L → SU2) (V : PeriodicLinkConfiguration SU2 L) :
    PeriodicLinkConfiguration SU2 L :=
  fun b => γ b.1 * V b * (γ b.1)⁻¹

theorem prod_gauge (s : ℕ) (γ : PeriodicLatticeSite L → SU2) (V0 V1 : PeriodicLinkConfiguration SU2 L) :
    (fun b => conjCfg γ V1 b * coarseGaugeTransform s γ V0 b)
      = coarseGaugeTransform s γ (fun b => V1 b * V0 b) := by
  funext b
  simp only [conjCfg, coarseGaugeTransform]
  group

theorem rProd_gauge (s : ℕ) (γ : PeriodicLatticeSite L → SU2) (V0 V1 : PeriodicLinkConfiguration SU2 L)
    (y : PeriodicLatticeSite L) (p : List (Fin 3)) :
    rProd s (coarseGaugeTransform s γ V0) (conjCfg γ V1) y p = γ y * rProd s V0 V1 y p * (γ y)⁻¹ := by
  rw [rProd_eq, rProd_eq, prod_gauge, coarsePathHolonomy_coarseGaugeTransform,
    coarsePathHolonomy_coarseGaugeTransform]
  group

theorem sBlock_gauge (s ell : ℕ) (γ : PeriodicLatticeSite L → SU2)
    (V0 V1 : PeriodicLinkConfiguration SU2 L) (y : PeriodicLatticeSite L) :
    sBlock s ell (coarseGaugeTransform s γ V0) (conjCfg γ V1) y = adMap (γ y) (sBlock s ell V0 V1 y) := by
  unfold sBlock
  rw [map_sum]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  rw [rProd_gauge, su2_log_conj, LinearMap.map_smul]

theorem su2Exp_neg_ad (g : SU2) (X : M2) : su2Exp (-(adMap g X)) = g * su2Exp (-X) * g⁻¹ := by
  rw [← map_neg, su2_exp_ad]

/-- **THE RAW ONE-STEP AVERAGING IS GAUGE-EQUIVARIANT, nonlinearly, every `V₀, V₁, γ, c`.** -/
theorem rawStep_gauge (s ell : ℕ) (γ : PeriodicLatticeSite L → SU2)
    (V0 V1 : PeriodicLinkConfiguration SU2 L) (c : PeriodicLatticeEdge L) :
    rawStep s ell (coarseGaugeTransform s γ V0) (conjCfg γ V1) c
      = γ c.1 * rawStep s ell V0 V1 c * (γ c.1)⁻¹ := by
  rw [rawStep_simp, rawStep_simp, sBlock_gauge, sBlock_gauge, prod_gauge,
    stridedBlockedGauge_gauge, stridedBlockedGauge_gauge, su2Exp_neg_ad, su2_exp_ad]
  simp only [coarseGaugeTransform, cPlusS_eq]
  group

#print axioms rProd_gauge
#print axioms sBlock_gauge
#print axioms rawStep_gauge

end AdalyFormal.GaugeCov
