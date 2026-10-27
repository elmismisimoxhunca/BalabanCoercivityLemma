import W6F
import GCa4

/-!
# WC4 -- the TWISTED block-local right inverse and the exact decomposition `T = I + N + S` (M2 W6 lane)

For a family `γ p` of gauge functions (one per row `p`) put `V_p = U^{γ_p}`.
* `srcL γ p w = (adBL γ_p)⁻¹ ( ψ_p ( Ad(γ_p z_p) w ) )`, `ψ_p w = EflatL (single p w)` (the W6 flat kernel);
* `EU y = Σ_p srcL γ p (y p)`;
* `T = Q_U ∘ EU`;  `QfullOf_gauge` (global gauge, no regularity) gives `Q_U (srcL γ p w) = (adFL γ_p)⁻¹ ( Q_{V_p} ψ_p w' )`;
* `Q_{V_p} ψ_p w' = Q₁ ψ_p w' + D_p w'`, `Q₁ ψ_p w' (p') = kap p' p • w'` (`Qflat_E`);
* `T y = y + N y + S y`, `N y p' = Σ_{lev p + 1 = lev p'} kap p' p • rot(y p)`, and `N ∘ N = 0` TERMWISE (`kap_N2`).
No sorry / native_decide / axiom.
-/
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 8000

namespace AdalyFormal.M2W6

open Finset
open AdalyFormal.Target.ClayStatement
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2 RMap RMap_mul_apply RMap_one)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.CovariantHjMinimizer (trivialU)
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
open AdalyFormal.Balaban.AlphaAnalyticity (GaugeFn)
open AdalyFormal.StatementLane (Tower Admissible scaleUp)
open AdalyFormal.W6
open AdalyFormal.GaugeCov (adBL adFL adGen_symm_apply adGen_apply)

section alg
variable {ell M R k : ℕ} {Lu : PeriodicLatticeExtent} {S : Tower (scaleUp ell k Lu)}

open Classical in
/-- the single-row embedding `SuTwo → FSp` -/
noncomputable def sglL (p : BIdx (geomOf ell k S)) : SuTwo →ₗ[ℝ] FSp (geomOf ell k S) where
  toFun w := WithLp.toLp 2 (fun q => if q = p then w else 0)
  map_add' w w' := by
    refine PiLp.ext (fun q => ?_)
    simp only [PiLp.add_apply]; split_ifs <;> simp
  map_smul' c w := by
    refine PiLp.ext (fun q => ?_)
    simp only [PiLp.smul_apply, RingHom.id_apply]; split_ifs <;> simp

open Classical in
theorem sglL_apply (p q : BIdx (geomOf ell k S)) (w : SuTwo) : (sglL p w) q = if q = p then w else 0 := rfl

/-- the flat kernel of one row, as a bond field -/
noncomputable def psiL (hell : 0 < ell) (p : BIdx (geomOf ell k S)) : SuTwo →ₗ[ℝ] BondFnL2 (scaleUp ell k Lu) :=
  (EflatL hell).comp (sglL p)

open Classical in
theorem psiL_apply (hell : 0 < ell) (p : BIdx (geomOf ell k S)) (w : SuTwo) (b : Bond (scaleUp ell k Lu)) :
    (psiL hell p w) b = phiK hell p b • w := by
  show (EflatL hell (sglL p w)) b = _
  rw [EflatL_apply]
  simp only [sglL_apply, smul_ite, smul_zero]
  rw [Finset.sum_ite_eq' Finset.univ p]
  simp

/-- the twisted source of row `p`: `(adBL γ_p)⁻¹ (ψ_p (Ad(γ_p z_p) w))` -/
noncomputable def srcL (hell : 0 < ell) (γ : BIdx (geomOf ell k S) → GaugeFn (scaleUp ell k Lu))
    (p : BIdx (geomOf ell k S)) : SuTwo →ₗ[ℝ] BondFnL2 (scaleUp ell k Lu) :=
  ((adBL (γ p)).symm.toLinearEquiv.toLinearMap).comp ((psiL hell p).comp (RMap ((γ p) p.2.1.1)))

/-- the twisted right inverse -/
noncomputable def EU (hell : 0 < ell) (γ : BIdx (geomOf ell k S) → GaugeFn (scaleUp ell k Lu)) :
    FSp (geomOf ell k S) →ₗ[ℝ] BondFnL2 (scaleUp ell k Lu) where
  toFun y := ∑ p, srcL hell γ p (y p)
  map_add' y y' := by
    simp only [PiLp.add_apply, map_add, Finset.sum_add_distrib]
  map_smul' c y := by
    simp only [PiLp.smul_apply, map_smul, RingHom.id_apply, Finset.smul_sum]

theorem EU_apply (hell : 0 < ell) (γ : BIdx (geomOf ell k S) → GaugeFn (scaleUp ell k Lu))
    (y : FSp (geomOf ell k S)) : EU hell γ y = ∑ p, srcL hell γ p (y p) := rfl

/-- the chart-minus-flat defect of the flat kernel of row `p` -/
noncomputable def Dfun (hell : 0 < ell) (U : LinkCfg (scaleUp ell k Lu))
    (γ : BIdx (geomOf ell k S) → GaugeFn (scaleUp ell k Lu)) (p : BIdx (geomOf ell k S)) (w : SuTwo) :
    FSp (geomOf ell k S) :=
  (bondSectorOf (geomOf ell k S) (periodicGaugeTransform (γ p) U)).Qfull (psiL hell p w)
    - (bondSectorOf (geomOf ell k S) (trivialU _)).Qfull (psiL hell p w)

/-- the rotation between the frames at `z_p'` and `z_p` in the gauge of `p` -/
noncomputable def rotL (γ : BIdx (geomOf ell k S) → GaugeFn (scaleUp ell k Lu))
    (p' p : BIdx (geomOf ell k S)) : SuTwo →ₗ[ℝ] SuTwo :=
  RMap ((((γ p) p'.2.1.1)⁻¹) * (γ p) p.2.1.1)

theorem rotL_self (γ : BIdx (geomOf ell k S) → GaugeFn (scaleUp ell k Lu)) (p : BIdx (geomOf ell k S))
    (w : SuTwo) : rotL γ p p w = w := by
  unfold rotL
  rw [inv_mul_cancel, RMap_one]; rfl

/-- **gauge covariance of one source**: `Q_U (srcL γ p w) = (adFL γ_p)⁻¹ ( Q_{V_p} ψ_p w' )`, `w' = Ad(γ_p z_p) w`. -/
theorem Q_src (hell : 0 < ell) (U : LinkCfg (scaleUp ell k Lu))
    (γ : BIdx (geomOf ell k S) → GaugeFn (scaleUp ell k Lu)) (p : BIdx (geomOf ell k S)) (w : SuTwo) :
    (bondSectorOf (geomOf ell k S) U).Qfull (srcL hell γ p w)
      = (adFL (γ p) (geomOf ell k S)).symm
          ((bondSectorOf (geomOf ell k S) (periodicGaugeTransform (γ p) U)).Qfull
            (psiL hell p (RMap ((γ p) p.2.1.1) w))) := by
  have h := AdalyFormal.GaugeCov.QfullOf_gauge (geomOf ell k S) U (γ p) (srcL hell γ p w)
  have e : (adBL (γ p)) (srcL hell γ p w) = psiL hell p (RMap ((γ p) p.2.1.1) w) := by
    show (adBL (γ p)) ((adBL (γ p)).symm (psiL hell p (RMap ((γ p) p.2.1.1) w))) = _
    exact (adBL (γ p)).apply_symm_apply _
  rw [e] at h
  show QfullOf (geomOf ell k S) U (srcL hell γ p w) = (adFL (γ p) (geomOf ell k S)).symm
    (QfullOf (geomOf ell k S) (periodicGaugeTransform (γ p) U) (psiL hell p (RMap ((γ p) p.2.1.1) w)))
  rw [h]
  exact ((adFL (γ p) (geomOf ell k S)).symm_apply_apply _).symm


end alg

end AdalyFormal.M2W6

#print axioms AdalyFormal.M2W6.Q_src
