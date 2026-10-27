import NJE4
import NJ2Jet

/-!
# NJE5 -- THE STRIDE-`s` FRECHET JET at a non-flat background: for `c = embE c'` on the stride-`s` sublattice,
`D qStepX^{(L,s)}(0) a (embE c') = ell • fromM2 (q124Principal 1 ell (resV V0) (a∘embE) c')`  (printed (124) on the sublattice torus).
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

variable {L Lq : PeriodicLatticeExtent} {s : ℕ}

/-- restriction of a coordinate field to the sublattice. -/
def resA (hs : ∀ μ, L μ + 1 = s * (Lq μ + 1)) (a : XS L) : XS Lq := fun e => a (embE hs e)

theorem resV_expCfgX (hs : ∀ μ, L μ + 1 = s * (Lq μ + 1)) (a : XS L) :
    resV hs (expCfgX a) = expCfgX (resA hs a) := rfl

theorem qStepX_emb (hs : ∀ μ, L μ + 1 = s * (Lq μ + 1)) (ell : ℕ) (V0 : PeriodicLinkConfiguration SU2 L)
    (a : XS L) (c : PeriodicLatticeEdge Lq) :
    qStepX s ell V0 a (embE hs c) = qStepX 1 ell (resV hs V0) (resA hs a) c := by
  unfold qStepX
  rw [rawStep_emb, resV_expCfgX]

theorem fderiv_qStepX_stride_apply (hs : ∀ μ, L μ + 1 = s * (Lq μ + 1)) (V0 : PeriodicLinkConfiguration SU2 L)
    (ell : ℕ) (hreg : RegBg s ell V0) (c : PeriodicLatticeEdge Lq)
    (hcell : c.1 ∈ CoarseLattice Lq ell) (hell : 0 < ell)
    (hdvd : ∀ μ : Fin 3, ell ∣ (Lq μ + 1))
    (hnc2 : ∀ x ∈ stepBlockOf c.1 1 ell, loopVar 1 ell (resV hs V0) c x ≠ su2NegOne)
    (a : XS L) :
    fderiv ℝ (qStepX s ell V0) 0 a (embE hs c)
      = (ell : ℝ) • fromM2
          ((q124Principal 1 ell (resV hs V0)
              (fineDirToUnitBond (fun e => toM2 (resA hs a e)) (fun e => (toM2_mem (resA hs a e)).1)
                (fun e => (toM2_mem (resA hs a e)).2))
              (⟨⟨c.1, by rw [one_mul]; exact hcell⟩, c.2⟩ : CoarseBond Lq (1 * ell)) : SuTwo) : M2) := by
  have hd := AdalySI1.Multiscale.M2.hasDerivAt_su2Log_modifiedAverageS_physical_q124 (resV hs V0)
    (fun e => toM2 (resA hs a e)) (fun e => (toM2_mem (resA hs a e)).1)
    (fun e => (toM2_mem (resA hs a e)).2) ell c hcell hell hdvd hnc2 1
  have h1 := fromM2Lin.hasFDerivAt.comp_hasDerivAt (0 : ℝ) hd
  have hdiff : DifferentiableAt ℝ (qStepX s ell V0) 0 :=
    (qStepX_contDiffAt s ell V0 hreg).differentiableAt (by simp)
  have hl : HasDerivAt (fun t : ℝ => t • a) a 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).smul_const a
  have h2 := hdiff.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hl (by simp)
  have h3 := (hasDerivAt_pi.mp h2) (embE hs c)
  have hfun : (fun t : ℝ => (qStepX s ell V0 ∘ fun t : ℝ => t • a) t (embE hs c))
      = (fromM2Lin ∘ fun t : ℝ => su2Log (modifiedAverageS 1 (resV hs V0) ell
          (fun e => su2Exp ((1 * t) • toM2 (resA hs a e))) c)) := by
    funext t
    show qStepX s ell V0 (t • a) (embE hs c) = _
    rw [qStepX_emb]
    exact qStepX_line ell (resV hs V0) (resA hs a) t c
  rw [hfun] at h3
  have := h3.unique h1
  rw [this]
  exact fromM2Lin_Lh ell _

#print axioms qStepX_emb
#print axioms fderiv_qStepX_stride_apply

end AdalyFormal.NonflatJet
