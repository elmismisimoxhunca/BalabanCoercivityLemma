import SectBCov
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 200000
noncomputable section
namespace HConstruction.SectBP1
open HConstruction.GenK HConstruction.SectBBase
open AdalyFormal.Target.ClayStatement
variable (M : PeriodicLatticeExtent) {n : ℕ}

/-- CMP99b (3.60) at the single occupied scale; sign convention V=Δ'(1)-Δ'(U). -/
def qDrift (U : Links M (n := n)) : Site M (n := n) →L[ℝ] CoarseSites M n :=
  covQPrime M U - flatQPrime M

def gradientDrift (U : Links M (n := n)) : Site M (n := n) →L[ℝ] Fine M (n := n) :=
  covGrad M U - grad M

def perturbation (U : Links M (n := n)) (k : ℕ) :
    Site M (n := n) →L[ℝ] Site M (n := n) :=
  flatDeltaPrime M k - covDeltaPrime M U k

/-- The averaging component of (3.60), including the quadratic term in F₂. -/
theorem qPerturbation_exact (U : Links M (n := n)) :
    ((flatQPrime M).adjoint.comp (flatQPrime M) -
      (covQPrime M U).adjoint.comp (covQPrime M U)) =
      - ((qDrift M U).adjoint.comp (flatQPrime M) +
        (flatQPrime M).adjoint.comp (qDrift M U) +
        (qDrift M U).adjoint.comp (qDrift M U)) := by
  have hc : covQPrime M U = flatQPrime M + qDrift M U := by
    unfold qDrift; module
  rw [hc]
  apply ContinuousLinearMap.ext; intro f
  simp only [map_add, add_apply, sub_apply, neg_apply,
    ContinuousLinearMap.comp_apply]
  module

/-- The Laplacian component V'₁ of (3.53), as an exact first-order-plus-square
identity. Bounding the grad*E term in operator norm needs (3.37)'s derivative clause. -/
theorem gradientPerturbation_exact (U : Links M (n := n)) :
    siteDelta M - (covGrad M U).adjoint.comp (covGrad M U) =
      - ((grad M).adjoint.comp (gradientDrift M U) +
        (gradientDrift M U).adjoint.comp (grad M) +
        (gradientDrift M U).adjoint.comp (gradientDrift M U)) := by
  have hc : covGrad M U = grad M + gradientDrift M U := by
    unfold gradientDrift; module
  rw [hc]
  apply ContinuousLinearMap.ext; intro f
  simp only [siteDelta, map_add, add_apply, sub_apply, neg_apply,
    ContinuousLinearMap.comp_apply]
  module

/-- Exact (3.60), with V₁=Δ(1)-Δ(U), without postulating a norm budget. -/
theorem perturbation_exact (U : Links M (n := n)) (k : ℕ) :
    perturbation M U k =
      (siteDelta M - (covGrad M U).adjoint.comp (covGrad M U)) -
      (topWeight k*(n:ℝ)^3) •
        ((qDrift M U).adjoint.comp (flatQPrime M) +
          (flatQPrime M).adjoint.comp (qDrift M U) +
          (qDrift M U).adjoint.comp (qDrift M U)) := by
  calc
    perturbation M U k =
        (siteDelta M - (covGrad M U).adjoint.comp (covGrad M U)) +
        (topWeight k*(n:ℝ)^3) •
          ((flatQPrime M).adjoint.comp (flatQPrime M) -
            (covQPrime M U).adjoint.comp (covQPrime M U)) := by
              unfold perturbation flatDeltaPrime covDeltaPrime
              module
    _ = _ := by
      rw [qPerturbation_exact]
      module

/-- Actual factorization (3.62): Δ'(U)=(I-VG'(1))Δ'(1). -/
theorem factorization (U : Links M (n := n)) (k : ℕ) (hn : 0 < n) :
    covDeltaPrime M U k =
      (ContinuousLinearMap.id ℝ _ - (perturbation M U k).comp (flatGPrime M hn k)).comp
        (flatDeltaPrime M k) := by
  apply ContinuousLinearMap.ext; intro f
  have h := flatGPrime_flatDeltaPrime M hn k f
  simp only [ContinuousLinearMap.comp_apply, sub_apply, ContinuousLinearMap.id_apply]
  rw [h]
  simp [perturbation]
end HConstruction.SectBP1
