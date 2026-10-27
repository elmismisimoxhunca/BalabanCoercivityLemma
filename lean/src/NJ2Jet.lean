import NJ1Bridge

/-!
# NJ2Jet -- the FRECHET first-order jet of the genuine R2 one-step map `qStepX` at a NON-FLAT background, stride 1

`fderiv ℝ (qStepX 1 ell V0) 0 a c = ell • fromM2 (q124Principal 1 ell V0 A' c)` : the printed CMP98 (124) linear form
(SI1, `M2.hasDerivAt_su2Log_modifiedAverageS_physical_q124`) transported to the R2 carrier by NJ1Bridge, with the
directional->Frechet step supplied by R2's `qStepX_contDiffAt` (regular background).
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace AdalyFormal.NonflatJet

open Matrix
attribute [local instance 10000] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.SuTwoLogExp (SU2 M2 su2Exp su2Log su2NegOne)
open AdalyFormal.Balaban.CovariantOperators (SuTwo)
open AdalyFormal.Balaban.LatticeOperators (CoarseBond)
open AdalyFormal.Balaban.AdmissibleSubspace (CoarseLattice)
open AdalyFormal.Balaban.QjComposite (stepBlockOf)
open AdalyFormal.Balaban.UbarTowerCov (loopVar)
open AdalyFormal.DeltaKR85 (q124Principal)
open AdalyFormal.IngredientFamilyR2
open AdalySI1Noloop.OuterLogFullDeriv (Lh)
open AdalySI1.Multiscale.M1 (modifiedAverageS)

variable {L : PeriodicLatticeExtent}

/-- `fromM2` as a continuous linear map out of `M2` (any norm; finite dimension). -/
noncomputable def fromM2Lin : M2 →L[ℝ] (Fin 3 → ℝ) := LinearMap.toContinuousLinearMap fromM2

theorem fromM2Lin_apply (X : M2) : fromM2Lin X = fromM2 X := rfl

theorem fromM2Lin_Lh (ell : ℕ) (X : M2) : fromM2Lin (Lh ell 1 • X) = (ell : ℝ) • fromM2 X := by
  rw [Lh, mul_one]
  exact fromM2Lin.map_smul _ _

theorem expCfgX_smul (a : XS L) (t : ℝ) :
    expCfgX (t • a) = fun e => su2Exp ((1 * t) • toM2 (a e)) := by
  funext e
  simp only [expCfgX, Pi.smul_apply, map_smul, one_mul]

theorem qStepX_line (ell : ℕ) (V0 : PeriodicLinkConfiguration SU2 L) (a : XS L) (t : ℝ)
    (c : PeriodicLatticeEdge L) :
    qStepX 1 ell V0 (t • a) c
      = fromM2 (su2Log (modifiedAverageS 1 V0 ell (fun e => su2Exp ((1 * t) • toM2 (a e))) c)) := by
  unfold qStepX
  rw [rawStep_eq_modifiedAverageS, expCfgX_smul]

/-- **THE FRECHET JET, exact printed (124), non-flat background, stride 1, on the R2 carrier.** -/
theorem fderiv_qStepX_one_apply (V0 : PeriodicLinkConfiguration SU2 L) (ell : ℕ)
    (hreg : RegBg 1 ell V0) (c : PeriodicLatticeEdge L)
    (hcell : c.1 ∈ CoarseLattice L ell) (hell : 0 < ell)
    (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1))
    (hnc2 : ∀ x ∈ stepBlockOf c.1 1 ell, loopVar 1 ell V0 c x ≠ su2NegOne)
    (a : XS L) :
    fderiv ℝ (qStepX 1 ell V0) 0 a c
      = (ell : ℝ) • fromM2
          ((q124Principal 1 ell V0
              (fineDirToUnitBond (fun e => toM2 (a e)) (fun e => (toM2_mem (a e)).1)
                (fun e => (toM2_mem (a e)).2))
              (⟨⟨c.1, by rw [one_mul]; exact hcell⟩, c.2⟩ : CoarseBond L (1 * ell)) : SuTwo) : M2) := by
  have hd := AdalySI1.Multiscale.M2.hasDerivAt_su2Log_modifiedAverageS_physical_q124 V0
    (fun e => toM2 (a e)) (fun e => (toM2_mem (a e)).1) (fun e => (toM2_mem (a e)).2)
    ell c hcell hell hdvd hnc2 1
  have h1 := fromM2Lin.hasFDerivAt.comp_hasDerivAt (0 : ℝ) hd
  have hdiff : DifferentiableAt ℝ (qStepX 1 ell V0) 0 :=
    (qStepX_contDiffAt 1 ell V0 hreg).differentiableAt (by simp)
  have hl : HasDerivAt (fun t : ℝ => t • a) a 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).smul_const a
  have h2 := hdiff.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hl (by simp)
  have h3 := (hasDerivAt_pi.mp h2) c
  have hfun : (fun t : ℝ => (qStepX 1 ell V0 ∘ fun t : ℝ => t • a) t c)
      = (fromM2Lin ∘ fun t : ℝ => su2Log (modifiedAverageS 1 V0 ell
          (fun e => su2Exp ((1 * t) • toM2 (a e))) c)) := by
    funext t
    exact qStepX_line ell V0 a t c
  rw [hfun] at h3
  have := h3.unique h1
  rw [this]
  exact fromM2Lin_Lh ell _

#print axioms fderiv_qStepX_one_apply

end AdalyFormal.NonflatJet
