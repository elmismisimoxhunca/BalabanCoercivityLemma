/-
C1 proof, build1 replay. Owned directory: compute/m1_si1_c1_gated/build1/.
Body reused verbatim from verified repair0 source per its handoff; see REPORT.md.
All four original theorem signatures are retained. No new target hypotheses.
Paid A/B and the derivative chain are imported; C0 is not needed or rebuilt.
-/
import C1Target

set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section

open Matrix
attribute [local instance 2000] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

namespace AdalySI1.C1Proof

open AdalyFormal.Target.ClayStatement
  (PeriodicLatticeExtent PeriodicLatticeEdge PeriodicLatticeSite PeriodicLinkConfiguration)
open AdalyFormal.Balaban.SuTwoLogExp (SU2 M2 su2Exp)
open AdalyFormal.Balaban.CovariantOperators (SuTwo RMap)
open AdalyFormal.Balaban.TowerLawCov (coarsePathHolonomy coarseGammaPath)
open AdalyFormal.Balaban.UbarTowerCov (loopVar gammaVarStrided coarseBondVar cPlusS)
open AdalyFormal.Balaban.BlockedBackground (ubarSU2)
open AdalyFormal.Balaban.QjComposite (stepBlockOf)
open AdalyFormal.Balaban.Q1Real (GammaPath)
open AdalySI1.ModifiedAverageDeriv (configMul)
open AdalySI1.IngredientDeriv (dirDeriv)
open AdalySI1.RawUbarDerivNoLoop
  (ubarBracket ubarBracket_conjTranspose ubarBracket_trace)
open AdalySI1.C1Contract (rawLoopTangent C1Target)
open OneStep124 (lineIntegral adOp expOp)

open AdalyFormal.Balaban.SuTwoLogExp
  (coe_mul coe_inv coe_one su2Exp_coe_of_antiHerm_traceless)
open AdalyFormal.Balaban.CovariantOperators (RMap_coe_apply RMap_mul_apply)
open AdalySI1.RawAverageDeriv (holonomyDirDeriv)

variable {L : PeriodicLatticeExtent}

/-- Totalized ring inverse, not the separate matrix inverse notation. -/
theorem ringInverse_coe (U : SU2) : Ring.inverse (U : M2) = (U : M2)ᴴ := by
  let u : M2ˣ := ⟨(U : M2), (U : M2)ᴴ,
    AdalyFormal.Balaban.SuTwoLogExp.mul_star_self U,
    AdalyFormal.Balaban.SuTwoLogExp.star_mul_self U⟩
  exact Ring.inverse_unit u

theorem cancel_star_tail (U : SU2) (X : M2) :
    (U : M2) * ((U : M2)ᴴ * X) = X := by
  rw [← mul_assoc, AdalyFormal.Balaban.SuTwoLogExp.mul_star_self, one_mul]

theorem cancel_star_head (U : SU2) (X : M2) :
    (U : M2)ᴴ * ((U : M2) * X) = X := by
  rw [← mul_assoc, AdalyFormal.Balaban.SuTwoLogExp.star_mul_self, one_mul]

/-- L2 with the final holonomy restored; every path remains a forward list. -/
theorem holonomy_tangent (V0 : PeriodicLinkConfiguration SU2 L)
    (A : PeriodicLatticeEdge L → M2)
    (hah : ∀ e, (A e)ᴴ = -(A e)) (htr : ∀ e, Matrix.trace (A e) = 0)
    (y : PeriodicLatticeSite L) (q : List (Fin 3)) :
    holonomyDirDeriv V0 A 1 y q =
      (lineIntegral 1 V0 (fineDirToUnitBond A hah htr) y q : M2)
        * ((coarsePathHolonomy 1 V0 y q : SU2) : M2) := by
  rw [← holonomyDirDeriv_mul_holonomy_conjTranspose_eq_lineIntegral V0 A hah htr y q,
    mul_assoc, AdalyFormal.Balaban.SuTwoLogExp.star_mul_self, mul_one]

/-- Algebra helper only: used below on the literal four path tangents. -/
theorem four_leg_algebra (p s f C : SU2) (a b e d : SuTwo) :
    ((((a : M2) * (p : M2) * (s : M2) + (p : M2) * ((b : M2) * (s : M2)))
          * (f : M2)ᴴ + (p : M2) * (s : M2) * ((e : M2) * (f : M2))ᴴ)
        * (C : M2)ᴴ + ((p * s * f⁻¹ : SU2) : M2) * ((d : M2) * (C : M2))ᴴ)
      * Ring.inverse ((p * s * f⁻¹ * C⁻¹ : SU2) : M2)
      = (a : M2) + (RMap p b : M2) - (RMap (p * s * f⁻¹) e : M2)
        - (RMap (p * s * f⁻¹ * C⁻¹) d : M2) := by
  rw [ringInverse_coe]
  simp only [RMap_coe_apply, coe_mul, coe_inv, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_conjTranspose, e.2.1, d.2.1,
    add_mul, neg_mul, mul_neg, mul_assoc,
    cancel_star_tail, cancel_star_head,
    AdalyFormal.Balaban.SuTwoLogExp.mul_star_self, mul_one, sub_eq_add_neg]

/-- Negation of the fixed adjoint operator, using the paid coefficient spelling. -/
theorem adOp_neg (Z : SuTwo) : adOp (-Z) = -(adOp Z) := by
  apply ContinuousLinearMap.ext
  intro v
  apply Subtype.ext
  change (((adOp (-Z)) v : SuTwo) : M2) = -((adOp Z v : SuTwo) : M2)
  rw [AdalySI1.DexpRodrigues.adOp_apply_coe, AdalySI1.DexpRodrigues.adOp_apply_coe]
  simp only [NegMemClass.coe_neg]
  noncomm_ring

/-- Ordinary exp inverse, for arbitrary raw means, including zero. -/
theorem su2Exp_neg_mul (Z : SuTwo) :
    su2Exp ((-Z : SuTwo) : M2) * su2Exp (Z : M2) = 1 := by
  apply Subtype.ext
  change ((su2Exp ((-Z : SuTwo) : M2) * su2Exp (Z : M2) : SU2) : M2) = (1 : M2)
  rw [coe_mul, su2Exp_coe_of_antiHerm_traceless (-Z).2.1 (-Z).2.2,
    su2Exp_coe_of_antiHerm_traceless Z.2.1 Z.2.2, NegMemClass.coe_neg]
  calc
    _ = NormedSpace.exp (-(Z : M2) + (Z : M2)) :=
      (NormedSpace.exp_add_of_commute (Commute.refl (Z : M2)).neg_left).symm
    _ = 1 := by rw [neg_add_cancel, NormedSpace.exp_zero]

/-- Conjunct 1 (near-tree campaign dictionary), let-inlined spelling. -/
theorem near_dict (V0 : PeriodicLinkConfiguration SU2 L) (A : PeriodicLatticeEdge L → M2)
    (hah : ∀ e, (A e)ᴴ = -(A e)) (htr : ∀ e, Matrix.trace (A e) = 0)
    (c : PeriodicLatticeEdge L) (x : PeriodicLatticeSite L) :
    dirDeriv V0 A c.1 (GammaPath c.1 x) 1
      = ((lineIntegral 1 V0 (fineDirToUnitBond A hah htr) c.1
          (coarseGammaPath 1 c.1 x) : SuTwo) : M2) := by
  rw [GammaPath_eq_coarseGammaPath_one_map]
  exact dirDeriv_map_true_one_eq_lineIntegral V0 A hah htr c.1 (coarseGammaPath 1 c.1 x)

/-- Conjunct 2: the actual four raw right-trivialized legs. -/
theorem four_legs (V0 : PeriodicLinkConfiguration SU2 L) (A : PeriodicLatticeEdge L → M2)
    (hah : ∀ e, (A e)ᴴ = -(A e)) (htr : ∀ e, Matrix.trace (A e) = 0)
    (ell : ℕ) (c : PeriodicLatticeEdge L) (x : PeriodicLatticeSite L) :
    rawLoopTangent V0 A ell c x
        * Ring.inverse ((loopVar 1 ell V0 c x : SU2) : M2)
      = dirDeriv V0 A c.1 (GammaPath c.1 x) 1
        + ((RMap (coarsePathHolonomy 1 V0 c.1 (coarseGammaPath 1 c.1 x))
            (lineIntegral 1 V0 (fineDirToUnitBond A hah htr) x
              (List.replicate ell c.2)) : SuTwo) : M2)
        - ((RMap (coarsePathHolonomy 1 V0 c.1 (coarseGammaPath 1 c.1 x)
              * coarsePathHolonomy 1 V0 x (List.replicate ell c.2)
              * (coarsePathHolonomy 1 V0 (cPlusS 1 ell c) (coarseGammaPath 1 c.1 x))⁻¹)
            (lineIntegral 1 V0 (fineDirToUnitBond A hah htr) (cPlusS 1 ell c)
              (coarseGammaPath 1 c.1 x)) : SuTwo) : M2)
        - ((RMap (loopVar 1 ell V0 c x)
            (lineIntegral 1 V0 (fineDirToUnitBond A hah htr) c.1
              (List.replicate ell c.2)) : SuTwo) : M2) := by
  rw [near_dict V0 A hah htr c x]
  unfold rawLoopTangent
  dsimp only
  rw [holonomy_tangent V0 A hah htr c.1 (coarseGammaPath 1 c.1 x),
    holonomy_tangent V0 A hah htr x (List.replicate ell c.2),
    holonomy_tangent V0 A hah htr (cPlusS 1 ell c) (coarseGammaPath 1 c.1 x),
    holonomy_tangent V0 A hah htr c.1 (List.replicate ell c.2)]
  exact four_leg_algebra
    (coarsePathHolonomy 1 V0 c.1 (coarseGammaPath 1 c.1 x))
    (coarsePathHolonomy 1 V0 x (List.replicate ell c.2))
    (coarsePathHolonomy 1 V0 (cPlusS 1 ell c) (coarseGammaPath 1 c.1 x))
    (coarseBondVar 1 ell V0 c)
    (lineIntegral 1 V0 (fineDirToUnitBond A hah htr) c.1 (coarseGammaPath 1 c.1 x))
    (lineIntegral 1 V0 (fineDirToUnitBond A hah htr) x (List.replicate ell c.2))
    (lineIntegral 1 V0 (fineDirToUnitBond A hah htr) (cPlusS 1 ell c) (coarseGammaPath 1 c.1 x))
    (lineIntegral 1 V0 (fineDirToUnitBond A hah htr) c.1 (List.replicate ell c.2))

/-- Conjunct 3: full direct-to-blocked frame identity. -/
theorem frame_change (V0 : PeriodicLinkConfiguration SU2 L)
    (ell : ℕ) (c : PeriodicLatticeEdge L) :
    ∀ v : SuTwo,
      RMap (coarseBondVar 1 ell V0 c) v
        = expOp (-(adOp ⟨ubarBracket V0 ell c,
            ubarBracket_conjTranspose V0 ell c, ubarBracket_trace V0 ell c⟩))
          (RMap (ubarSU2 1 ell V0 c) v) := by
  intro v
  let Z : SuTwo := ⟨ubarBracket V0 ell c,
    ubarBracket_conjTranspose V0 ell c, ubarBracket_trace V0 ell c⟩
  have hC : coarseBondVar 1 ell V0 c =
      su2Exp ((-Z : SuTwo) : M2) * ubarSU2 1 ell V0 c := by
    rw [AdalySI1.RawUbarDerivNoLoop.ubarSU2_eq_exp_bracket_mul_bondVar,
      ← mul_assoc, su2Exp_neg_mul Z, one_mul]
  change RMap (coarseBondVar 1 ell V0 c) v = expOp (-(adOp Z)) (RMap (ubarSU2 1 ell V0 c) v)
  rw [hC, ← RMap_mul_apply,
    AdalySI1.Adjoint.rmap_su2Exp_apply_eq_expOp_ad (-Z), adOp_neg]

/-- Conjunct 4: actual literal loop derivative in the blocked frame. -/
theorem literal_deriv_frame (V0 : PeriodicLinkConfiguration SU2 L)
    (A : PeriodicLatticeEdge L → M2)
    (hah : ∀ e, (A e)ᴴ = -(A e)) (htr : ∀ e, Matrix.trace (A e) = 0)
    (ell : ℕ) (c : PeriodicLatticeEdge L) (x : PeriodicLatticeSite L) :
    deriv (fun t : ℝ => ((loopVar 1 ell
        (configMul (fun e => su2Exp (t • A e)) V0) c x : SU2) : M2)) 0
        * Ring.inverse ((loopVar 1 ell V0 c x : SU2) : M2)
      = dirDeriv V0 A c.1 (GammaPath c.1 x) 1
        + ((RMap (coarsePathHolonomy 1 V0 c.1 (coarseGammaPath 1 c.1 x))
            (lineIntegral 1 V0 (fineDirToUnitBond A hah htr) x
              (List.replicate ell c.2)) : SuTwo) : M2)
        - ((RMap (loopVar 1 ell V0 c x)
            (expOp (-(adOp ⟨ubarBracket V0 ell c,
                ubarBracket_conjTranspose V0 ell c, ubarBracket_trace V0 ell c⟩))
              (RMap (ubarSU2 1 ell V0 c)
                (lineIntegral 1 V0 (fineDirToUnitBond A hah htr) (cPlusS 1 ell c)
                  (coarseGammaPath 1 c.1 x)))) : SuTwo) : M2)
        - ((RMap (loopVar 1 ell V0 c x)
            (lineIntegral 1 V0 (fineDirToUnitBond A hah htr) c.1
              (List.replicate ell c.2)) : SuTwo) : M2) := by
  erw [(AdalySI1.C1Contract.hasDerivAt_actualLoop_rawLoopTangent
    V0 A hah htr ell c x).deriv, four_legs V0 A hah htr ell c x]
  have hpath : coarsePathHolonomy 1 V0 c.1 (coarseGammaPath 1 c.1 x)
        * coarsePathHolonomy 1 V0 x (List.replicate ell c.2)
        * (coarsePathHolonomy 1 V0 (cPlusS 1 ell c) (coarseGammaPath 1 c.1 x))⁻¹
      = loopVar 1 ell V0 c x * coarseBondVar 1 ell V0 c := by
    exact (inv_mul_cancel_right (gammaVarStrided 1 ell V0 c x)
      (coarseBondVar 1 ell V0 c)).symm
  let phi : SuTwo := lineIntegral 1 V0 (fineDirToUnitBond A hah htr)
    (cPlusS 1 ell c) (coarseGammaPath 1 c.1 x)
  have hfar := congrArg (fun U : SU2 => RMap U phi) hpath
  have hcompose := (RMap_mul_apply (loopVar 1 ell V0 c x)
    (coarseBondVar 1 ell V0 c) phi).symm
  have hframe := congrArg (fun v : SuTwo => RMap (loopVar 1 ell V0 c x) v)
    (frame_change V0 ell c phi)
  have hfarFinal := (hfar.trans hcompose).trans hframe
  exact congrArg (fun v : SuTwo =>
    dirDeriv V0 A c.1 (GammaPath c.1 x) 1
      + ((RMap (coarsePathHolonomy 1 V0 c.1 (coarseGammaPath 1 c.1 x))
          (lineIntegral 1 V0 (fineDirToUnitBond A hah htr) x
            (List.replicate ell c.2)) : SuTwo) : M2)
      - (v : M2)
      - ((RMap (loopVar 1 ell V0 c x)
          (lineIntegral 1 V0 (fineDirToUnitBond A hah htr) c.1
            (List.replicate ell c.2)) : SuTwo) : M2)) hfarFinal

/-- The exact immutable acceptance target, assembled from all four obligations. -/
theorem loopVar_rightTrivialized_eq_four_legs : C1Target := by
  intro L V0 A hah htr ell c x _hx
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact near_dict V0 A hah htr c x
  · exact four_legs V0 A hah htr ell c x
  · exact frame_change V0 ell c
  · exact literal_deriv_frame V0 A hah htr ell c x

#print axioms near_dict
#print axioms four_leg_algebra
#print axioms four_legs
#print axioms frame_change
#print axioms literal_deriv_frame
#print axioms loopVar_rightTrivialized_eq_four_legs

end AdalySI1.C1Proof
