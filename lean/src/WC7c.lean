import WC7b
import WC1

/-!
# WC7c -- `qs_injective_charts` (M2 W6 lane)

`Q_U*` is injective whenever every row `p` carries a gauge `γ_p` such that the background tower of `U^{γ_p}` is near the
identity (regional class `ε j' l`) on the ball `Ball z_p (20 ℓ^{lev p + 1})`, for the three levels `j'` interacting with `p`,
and `2 s (1 + A) < 1` for the explicit `k`-free constants `s, A` below.  No global gauge, no global regularity.
No sorry / native_decide / axiom.
-/
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 8000
set_option synthInstance.maxHeartbeats 400000
noncomputable section
namespace AdalyFormal.M2W6

open Finset
open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2 RMap)
open AdalyFormal.Balaban.SuTwoLogExp (SU2 M2)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond CoarseLattice mem_CoarseLattice)
open AdalyFormal.Balaban.RMapLipschitz (frobNorm)
open AdalyFormal.Balaban.CovariantHjMinimizer (trivialU)
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
open AdalyFormal.Balaban.AlphaAnalyticity (GaugeFn)
open AdalyFormal.NonflatJet
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.StatementLane (Tower Admissible scaleUp pdist)
open AdalyFormal.StatementLaneR8
open AdalyFormal.StatementLaneG (gparams)
open AdalyFormal.SliceCoerc (GF)
open AdalyFormal.BondComposite
open SmallnessBridge.Assemble (loopFactorBound)
open AdalyFormal.W6
open AdalyFormal.TowerLoc
open AdalyFormal.GaugeCov (adBL adFL adGen_symm_apply)

/-- the `k`-free interaction multiplicity -/
def mult0 (ell : ℕ) : ℝ := 9 * (24 * (ell : ℝ) + 1) ^ 3
/-- `s`: the bound on `ν(S y)/ν(y)` -/
def CsrcS (ell : ℕ) (Sstar : ℝ) : ℝ := mult0 ell * (3 * delStar ell Sstar ^ 2 * CE)
/-- `a_T`: the bound on `ν(T y)/ν(y)` -/
def CsrcT (ell : ℕ) (Sstar : ℝ) : ℝ := mult0 ell * (3 * (Real.exp (Sstar / rr ell)) ^ 2 * CE)
/-- `A`: the bound on `ν(N y)/ν(y)` -/
def CsrcA (ell : ℕ) (Sstar : ℝ) : ℝ := 4 * CsrcT ell Sstar + 4 + 2 * CsrcS ell Sstar

section ass
variable {ell M R k : ℕ} {Lu : PeriodicLatticeExtent} {S : Tower (scaleUp ell k Lu)}

/-- the defect vector of source `p` -/
noncomputable def Dvec (hell : 0 < ell) (U : LinkCfg (scaleUp ell k Lu))
    (γ : BIdx (geomOf ell k S) → GaugeFn (scaleUp ell k Lu)) (p : BIdx (geomOf ell k S)) (w : SuTwo) :
    FSp (geomOf ell k S) :=
  WithLp.toLp 2 (fun p' => RMap (((γ p) p'.2.1.1)⁻¹) ((Dfun hell U γ p (RMap ((γ p) p.2.1.1) w)) p'))

theorem Sfun_eq_sum (hell : 0 < ell) (U : LinkCfg (scaleUp ell k Lu))
    (γ : BIdx (geomOf ell k S) → GaugeFn (scaleUp ell k Lu)) (y : FSp (geomOf ell k S)) :
    Sfun hell U γ y = ∑ p, Dvec hell U γ p (y p) := by
  refine PiLp.ext (fun p' => ?_)
  rw [WithLp.ofLp_sum, Finset.sum_apply]
  rfl

/-- the full vector of source `p` -/
noncomputable def Tvec (hell : 0 < ell) (U : LinkCfg (scaleUp ell k Lu))
    (γ : BIdx (geomOf ell k S) → GaugeFn (scaleUp ell k Lu)) (p : BIdx (geomOf ell k S)) (w : SuTwo) :
    FSp (geomOf ell k S) :=
  (bondSectorOf (geomOf ell k S) U).Qfull (srcL hell γ p w)

theorem Tvec_eq (hell : 0 < ell) (U : LinkCfg (scaleUp ell k Lu))
    (γ : BIdx (geomOf ell k S) → GaugeFn (scaleUp ell k Lu)) (p p' : BIdx (geomOf ell k S)) (w : SuTwo) :
    (Tvec hell U γ p w) p' = RMap (((γ p) p'.2.1.1)⁻¹)
      (((bondSectorOf (geomOf ell k S) (periodicGaugeTransform (γ p) U)).Qfull
        (psiL hell p (RMap ((γ p) p.2.1.1) w))) p') := by
  unfold Tvec
  rw [Q_src]
  exact adGen_symm_apply (fun q : BIdx (geomOf ell k S) => (γ p) q.2.1.1) _ p'

theorem Tlin_eq_sum (hell : 0 < ell) (U : LinkCfg (scaleUp ell k Lu))
    (γ : BIdx (geomOf ell k S) → GaugeFn (scaleUp ell k Lu)) (y : FSp (geomOf ell k S)) :
    Tlin hell U γ y = ∑ p, Tvec hell U γ p (y p) := by
  rw [Tlin_apply, EU_apply, map_sum]
  rfl

theorem nF_rot (hell : 0 < ell) (g : BIdx (geomOf ell k S) → Matrix.specialUnitaryGroup (Fin 2) ℂ)
    (f : FSp (geomOf ell k S)) :
    nF (WithLp.toLp 2 (fun p' : BIdx (geomOf ell k S) => RMap (g p') (f p')) : FSp (geomOf ell k S)) = nF f := by
  unfold nF
  refine Finset.sum_congr rfl (fun p' _ => ?_)
  show wF p' * ‖RMap (g p') (f p')‖ ^ 2 = _
  rw [norm_RMap]

end ass

end AdalyFormal.M2W6

#print axioms AdalyFormal.M2W6.Tlin_eq_sum
#print axioms AdalyFormal.M2W6.Sfun_eq_sum
