import FibreActions
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
namespace HConstruction.Coeff
open AdalyFormal.Balaban.CovariantOperators (SuTwo RMap)
open AdalyFormal.Balaban.SuTwoInner
open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.AdmissibleSubspace (witnessL)
open AdalyFormal.Balaban.LatticeOperators (CoarseBond)
open AdalyFormal.Balaban.ThirdLevelArrows (unitSitesOf)
open AdalyFormal.Balaban.QjComposite (stepBlockOf)
open AdalyFormal.DeltaKR66
open AdalyFormal.DeltaKR85
open HConstruction.SmallNF
open HConstruction.Circle
open HConstruction.NfRepair.Reproduced
open EstimatesLayer.NormBounds
open OneStep124

 theorem FibreAction.add {T S : SuTwo →L[ℝ] SuTwo} {u p q v r t : ℝ}
    (hT : FibreAction T u p q) (hS : FibreAction S v r t) :
    FibreAction (T+S) (u+v) (p+r) (q+t) := by
  intro x a z
  rw [ContinuousLinearMap.add_apply, hT, hS, assemble_add]
  congr 1 <;> ring
 theorem fibre_zero : FibreAction (0 : SuTwo →L[ℝ] SuTwo) 0 0 0 := by
  intro x a z; simp [assemble]

 def ComplexAction (T : SuTwo →L[ℝ] SuTwo) (u : ℝ) (k : ℂ) : Prop :=
   FibreAction T u k.re k.im
 theorem ComplexAction.mul {T S : SuTwo →L[ℝ] SuTwo} {u v : ℝ} {k l : ℂ}
    (hT : ComplexAction T u k) (hS : ComplexAction S v l) :
    ComplexAction (T*S) (u*v) (k*l) := by
  simpa [ComplexAction, Complex.mul_re, Complex.mul_im, add_comm] using FibreAction.mul hT hS
 theorem ComplexAction.sub {T S : SuTwo →L[ℝ] SuTwo} {u v : ℝ} {k l : ℂ}
    (hT : ComplexAction T u k) (hS : ComplexAction S v l) :
    ComplexAction (T-S) (u-v) (k-l) := FibreAction.sub hT hS
 theorem ComplexAction.smul {T : SuTwo →L[ℝ] SuTwo} {u : ℝ} {k : ℂ}
    (hT : ComplexAction T u k) (r : ℝ) : ComplexAction (r • T) (r*u) (r*k) := by
  simpa [ComplexAction] using FibreAction.smul hT r
 theorem ComplexAction.sum {ι : Type*} (s : Finset ι) (T : ι → SuTwo →L[ℝ] SuTwo)
    (u : ι → ℝ) (k : ι → ℂ) (h : ∀ i ∈ s, ComplexAction (T i) (u i) (k i)) :
    ComplexAction (∑ i ∈ s, T i) (∑ i ∈ s, u i) (∑ i ∈ s, k i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa [ComplexAction] using fibre_zero
  | @insert i s hi ih =>
    simp only [Finset.sum_insert hi]
    exact (h i (Finset.mem_insert_self i s)).add (ih (fun j hj => h j (Finset.mem_insert_of_mem hj)))
 theorem complex_one : ComplexAction (1 : SuTwo →L[ℝ] SuTwo) 1 1 := fibre_one

 def gScalar (s : ℝ) : ℂ := ⟨gReal s, gImag s⟩
 def invScalar (s : ℝ) : ℂ := ⟨invReal s, s⟩
 def expScalar (s : ℝ) : ℂ := ⟨Real.cos (2*|s|), (s/|s|)*Real.sin (2*|s|)⟩
 def loopAngle (c : CoarseBond witnessL (1*2)) (x : PeriodicLatticeSite witnessL) : ℝ :=
    (loopWord c x : ℝ) * HConstruction.Circle.theta
 def coeff1Scalar (c : CoarseBond witnessL (1*2)) (x : PeriodicLatticeSite witnessL) : ℂ :=
    gScalar (meanAngle c) * star (invScalar (loopAngle c x)) - 1
 def coeff2Scalar (c : CoarseBond witnessL (1*2)) (x : PeriodicLatticeSite witnessL) : ℂ :=
    gScalar (meanAngle c) * invScalar (loopAngle c x) * expScalar (-meanAngle c) - 1
 def coeff3Scalar (c : CoarseBond witnessL (1*2)) : ℂ :=
    expScalar (meanAngle c) - gScalar (meanAngle c) *
      (∑ u ∈ unitSitesOf 1 (1*2) c.1.1, (1/8 : ℂ) * invScalar (loopAngle c u.1))

 theorem loopAngle_small (c : CoarseBond witnessL (1*2)) (x : PeriodicLatticeSite witnessL)
    (hx : x ∈ stepBlockOf c.1.1 1 2) : |loopAngle c x| < Real.pi := by
  have h := source_Zx_small c x hx
  rwa [source_Zx c x hx, nu_axis] at h

 theorem principal_E1_action (c : CoarseBond witnessL (1*2)) (x : PeriodicLatticeSite witnessL)
    (hx : x ∈ stepBlockOf c.1.1 1 2) :
    ComplexAction ((Coeff124.ofPrincipalBackground 1 2 chosenU).E1 c x) 0 (coeff1Scalar c x) := by
  change ComplexAction (gOp _ * gInvOp _ - 1) _ _
  rw [source_Z, source_Zx c x hx]
  have hg : ComplexAction (gOp (-(adOp (meanAngle c • pauliE2)))) 1 (gScalar (meanAngle c)) := g_neg_action _
  have hi : ComplexAction (gInvOp (-(adOp (loopAngle c x • pauliE2)))) 1 (star (invScalar (loopAngle c x))) := gInv_neg_action _ (loopAngle_small c x hx)
  simpa [coeff1Scalar, loopAngle] using (hg.mul hi).sub complex_one

 theorem principal_E2_action (c : CoarseBond witnessL (1*2)) (x : PeriodicLatticeSite witnessL)
    (hx : x ∈ stepBlockOf c.1.1 1 2) :
    ComplexAction ((Coeff124.ofPrincipalBackground 1 2 chosenU).E2 c x) 0 (coeff2Scalar c x) := by
  have hg : ComplexAction (gOp (-(adOp (meanAngle c • pauliE2)))) 1 (gScalar (meanAngle c)) := g_neg_action _
  have hi : ComplexAction (gInvOp (adOp (loopAngle c x • pauliE2))) 1 (invScalar (loopAngle c x)) :=
    gInv_pos_action _ (loopAngle_small c x hx)
  have he : ComplexAction (expOp (-(adOp (meanAngle c • pauliE2)))) 1 (expScalar (-meanAngle c)) := by
    simpa [neg_smul, ad_neg, ComplexAction, expScalar] using exp_action (-meanAngle c)
  change ComplexAction (gOp _ * gInvOp _ * expOp _ - 1) _ _
  rw [source_Z, source_Zx c x hx]
  simpa [coeff2Scalar, loopAngle] using ((hg.mul hi).mul he).sub complex_one

 theorem principal_E3_action (c : CoarseBond witnessL (1*2)) :
    ComplexAction ((Coeff124.ofPrincipalBackground 1 2 chosenU).E3 c) 0 (coeff3Scalar c) := by
  have hs := ComplexAction.sum (unitSitesOf 1 (1*2) c.1.1)
    (fun u => (1/8 : ℝ) • gInvOp (adOp ((sourcePrincipalLogData 1 2 chosenU).Zx c u.1)))
    (fun _ => (1/8 : ℝ)) (fun u => (1/8 : ℂ) * invScalar (loopAngle c u.1)) (by
      intro u hu
      rw [source_Zx c u.1 (unit_mem_step c u hu)]
      have hi : ComplexAction (gInvOp (adOp (loopAngle c u.1 • pauliE2))) 1 (invScalar (loopAngle c u.1)) :=
        gInv_pos_action _ (loopAngle_small c u.1 (unit_mem_step c u hu))
      simpa [loopAngle] using hi.smul (1/8))
  have ha : (∑ _u ∈ unitSitesOf 1 (1*2) c.1.1, (1/8 : ℝ)) = 1 := by
    rw [Finset.sum_const, chosen_card]
    norm_num
  rw [ha] at hs
  have hg : ComplexAction (gOp (-(adOp (meanAngle c • pauliE2)))) 1 (gScalar (meanAngle c)) := g_neg_action _
  have he : ComplexAction (expOp (adOp (meanAngle c • pauliE2))) 1 (expScalar (meanAngle c)) := exp_action _
  change ComplexAction (expOp _ - gOp _ * _) _ _
  rw [source_Z, chosen_card]
  simpa [coeff3Scalar] using he.sub (hg.mul hs)

#print axioms principal_E1_action
#print axioms principal_E2_action
#print axioms principal_E3_action
end HConstruction.Coeff
