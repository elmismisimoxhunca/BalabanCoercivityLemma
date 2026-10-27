import StridedSurfaceFill
import AdalyFormal.Balaban.BlockedBackground
import Lean.Util.CollectAxioms

set_option autoImplicit false
set_option maxHeartbeats 4000000

/-!
A NEW target obstruction, unrelated to the refuted diagonal modified operator.
`OneStepPropagationRaw` quantifies over every output site. Actual `stepBlockOf`
uses nonwrapping coordinate inequalities, so it truncates at upper boundaries.
On the 4^3 torus an arbitrarily small abelian input has output/input curvature
ratio tending to 9/2, greater than ell^2 = 4. This file proves the general
abelian embedding; RawBoundaryWitness carries the finite computations. Both
use the imported definitions, not a replacement periodic averaging operator.
-/

noncomputable section
namespace Prop1.RawBoundary

open Matrix
open AdalyFormal.Target.ClayStatement
  (PeriodicLatticeExtent PeriodicLatticeSite PeriodicLatticeEdge PeriodicLinkConfiguration)
open AdalyFormal.Balaban.SuTwoLogExp
open AdalyFormal.Balaban.RMapLipschitz (frobNorm)
open AdalyFormal.Balaban.BlockingLinkEstimate
open AdalyFormal.Balaban.CoarseCurl (coarseShift)
open AdalyFormal.Balaban.TowerLawCov (coarsePathHolonomy coarseGammaPath)
open AdalyFormal.Balaban.QjComposite (stepBlockOf)
open AdalyFormal.Balaban.UbarTowerCov
  (coarseBondVar gammaVarStrided loopVar cPlusS stridedBlockedGauge)
open AdalyFormal.Balaban.BlockedBackground (ubarSU2)
open DepthUniformity.Strided (orientedPlaqHolS frobNorm_inv_sub_one)

/-- Real-parameter family of genuine group homomorphisms. -/
def torusScale (t : ℝ) : Multiplicative ℚ →* SU2 where
  toFun q := torus (((Multiplicative.toAdd q : ℚ) : ℝ) * t)
  map_one' := by simp
  map_mul' a b := by
    change torus (((Multiplicative.toAdd a + Multiplicative.toAdd b : ℚ) : ℝ) * t) = _
    rw [Rat.cast_add, add_mul, torus_add]

@[simp] theorem torusScale_apply (t : ℝ) (q : ℚ) :
    torusScale t (Multiplicative.ofAdd q) = torus ((q : ℝ) * t) := rfl

 theorem torus_inv (t : ℝ) : (torus t)⁻¹ = torus (-t) := by
  apply inv_eq_of_mul_eq_one_left
  rw [← torus_add, neg_add_cancel, torus_zero]

 theorem psiR_alg (t : ℝ) : IsSuTwoAlg (psiR t) := by
  constructor
  · rw [psiR_dg, dg_conjTranspose]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [dg]
  · rw [psiR_dg, dg_trace]
    simp

 theorem psiR_angle (t : ℝ) : algAngle (psiR t) = |t| := by
  simp [algAngle, psiR_dg, dg_00, dg_01, Real.sqrt_sq_eq_abs]

 theorem log_torus_signed (t : ℝ) (h : |t| < Real.pi) :
    su2Log (torus t) = psiR t := by
  rw [← su2Exp_psiR]
  exact su2Log_su2Exp_of_lt_pi (psiR_alg t) (by rwa [psiR_angle])

 def algScale (t : ℝ) : ℚ →ₗ[ℚ] M2 := LinearMap.toSpanSingleton ℚ M2 (psiR t)

 theorem algScale_apply (t : ℝ) (q : ℚ) : algScale t q = psiR ((q : ℝ) * t) := by
  change q • psiR t = _
  have hrat (M : M2) : q • M = (q : ℂ) • M := by
    ext i j
    simp [Matrix.smul_apply, Rat.smul_def]
  rw [hrat, psiR, psiR, smul_smul]
  congr 1
  push_cast
  ring

 theorem path_map {L : PeriodicLatticeExtent} {G H : Type*} [Group G] [Group H]
    (F : G →* H) (s : ℕ) (V : PeriodicLinkConfiguration G L)
    (y : PeriodicLatticeSite L) (p : List (Fin 3)) :
    coarsePathHolonomy s (fun e => F (V e)) y p = F (coarsePathHolonomy s V y p) := by
  induction p generalizing y with
  | nil => exact F.map_one.symm
  | cons mu p ih =>
    simp only [coarsePathHolonomy, ih, map_mul]

 theorem coarseBond_map {L : PeriodicLatticeExtent} {G H : Type*} [Group G] [Group H]
    (F : G →* H) (s ell : ℕ) (V : PeriodicLinkConfiguration G L)
    (c : PeriodicLatticeEdge L) :
    coarseBondVar s ell (fun e => F (V e)) c = F (coarseBondVar s ell V c) :=
  path_map F s V c.1 _

 theorem loop_map {L : PeriodicLatticeExtent} {G H : Type*} [Group G] [Group H]
    (F : G →* H) (s ell : ℕ) (V : PeriodicLinkConfiguration G L)
    (c : PeriodicLatticeEdge L) (x : PeriodicLatticeSite L) :
    loopVar s ell (fun e => F (V e)) c x = F (loopVar s ell V c x) := by
  simp only [loopVar, gammaVarStrided, coarseBondVar, path_map, map_mul, map_inv]

 theorem plaq_map {L : PeriodicLatticeExtent} {G H : Type*} [Group G] [Group H]
    (F : G →* H) (s : ℕ) (V : PeriodicLinkConfiguration G L)
    (y : PeriodicLatticeSite L) (mu nu : Fin 3) :
    orientedPlaqHolS s (fun e => F (V e)) y mu nu = F (orientedPlaqHolS s V y mu nu) := by
  simp only [orientedPlaqHolS, map_mul, map_inv]

/-- Coefficients are obtained from the ACTUAL imported group-valued geometry. -/
def qRaw {L : PeriodicLatticeExtent} (s ell : ℕ)
    (V : PeriodicLinkConfiguration (Multiplicative ℚ) L) (c : PeriodicLatticeEdge L) : ℚ :=
  (∑ x ∈ stepBlockOf c.1 s ell,
    ((ell : ℚ)^3)⁻¹ * Multiplicative.toAdd (loopVar s ell V c x)) +
    Multiplicative.toAdd (coarseBondVar s ell V c)

 theorem raw_torus {L : PeriodicLatticeExtent} (s ell : ℕ)
    (V : PeriodicLinkConfiguration (Multiplicative ℚ) L) (t : ℝ) (c : PeriodicLatticeEdge L)
    (h : ∀ x ∈ stepBlockOf c.1 s ell,
      |((Multiplicative.toAdd (loopVar s ell V c x) : ℚ) : ℝ) * t| < Real.pi) :
    ubarSU2 s ell (fun e => torusScale t (V e)) c =
      torusScale t (Multiplicative.ofAdd (qRaw s ell V c)) := by
  change su2Exp (∑ x ∈ stepBlockOf c.1 s ell,
      ((ell : ℚ)^3)⁻¹ • su2Log (loopVar s ell (fun e => torusScale t (V e)) c x)) *
        coarseBondVar s ell (fun e => torusScale t (V e)) c = _
  have hlog : ∀ x ∈ stepBlockOf c.1 s ell,
      su2Log (loopVar s ell (fun e => torusScale t (V e)) c x) =
        algScale t (Multiplicative.toAdd (loopVar s ell V c x)) := by
    intro x hx
    rw [loop_map]
    change su2Log (torus _) = _
    rw [log_torus_signed _ (h x hx), algScale_apply]
  rw [Finset.sum_congr rfl (fun x hx => congrArg (fun Z => ((ell : ℚ)^3)⁻¹ • Z) (hlog x hx))]
  simp_rw [← map_smul, ← map_sum]
  rw [algScale_apply, su2Exp_psiR, coarseBond_map]
  change torus _ * torus _ = torus _
  rw [← torus_add]
  congr 1
  simp only [qRaw, toAdd_ofAdd, smul_eq_mul, Rat.cast_add, add_mul]


end Prop1.RawBoundary

#print axioms Prop1.RawBoundary.raw_torus
