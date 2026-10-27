import AstraJointKernel
set_option autoImplicit false
set_option maxHeartbeats 1200000
noncomputable section
namespace HConstruction.SectBBase
open HConstruction.GenK
open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.CovariantOperators (SuTwo)

variable (M : PeriodicLatticeExtent) {n : ℕ} (hn : 0 < n)

/-- CMP99b (3.19), flat single-stratum restriction, on exactly GenK's fine sites.
The codomain is the actual coarse-center Hilbert space, not the fine bond field. -/
abbrev CoarseSites (M : PeriodicLatticeExtent) (n : ℕ) :=
  PiLp 2 (fun _ : GenK.Centers M (n := n) => SuTwo)

/-- The Hilbert-space version of the existing (unweighted) GenK site average. -/
def flatQPrime : GenK.Site M (n := n) →L[ℝ] CoarseSites M n :=
  LinearMap.toContinuousLinearMap
    (((WithLp.linearEquiv 2 ℝ (GenK.Centers M (n := n) → SuTwo)).symm.toLinearMap).comp
      (GenK.siteAverage M (n := n)))

lemma flatQPrime_apply (f : GenK.Site M (n := n)) (y : GenK.Centers M (n := n)) :
    flatQPrime M f y = GenK.siteAverage M f y := rfl

/-- CMP99b (3.24): a₀=a₁=1 and a_{j+1}=a_j/(1/4+a_j) for j≥1. -/
def weightIter : ℕ → ℝ
  | 0 => 1
  | j + 1 => weightIter j / (1/4 + weightIter j)

def topWeight (k : ℕ) : ℝ := weightIter (k - 1)

theorem weightIter_pos (j : ℕ) : 0 < weightIter j := by
  induction j with
  | zero => norm_num [weightIter]
  | succ j ih => simp only [weightIter]; positivity

theorem topWeight_pos (k : ℕ) : 0 < topWeight k := weightIter_pos _

theorem topWeight_zero : topWeight 0 = 1 := rfl
theorem topWeight_one : topWeight 1 = 1 := rfl
theorem topWeight_next (k : ℕ) :
    topWeight (k + 2) = topWeight (k + 1) / (1/4 + topWeight (k + 1)) := by
  simp [topWeight, weightIter]

/-- CMP99b (3.23)+(3.24) on the whole periodic single-stratum torus:
η=1/n, L^k η=1 *when n=2^k*, d=3, coefficient a_k=topWeight k.
The fine-site Hilbert space has counting measure, hence n³. -/
def flatDeltaPrime (k : ℕ) : GenK.Site M (n := n) →L[ℝ] GenK.Site M (n := n) :=
  GenK.siteDelta M (n := n) + (topWeight k * (n:ℝ)^3) •
    ((flatQPrime M (n := n)).adjoint.comp (flatQPrime M (n := n)))

/-- Exact identity with the printed quadratic form (3.24), in the
single-stratum U=1 case. This is not an inverse estimate. -/
theorem flatDeltaPrime_form (k : ℕ) (f : GenK.Site M (n := n)) (hn : 0 < n) :
    (1/(n:ℝ)^3) * (inner ℝ f (flatDeltaPrime M k f) : ℝ) =
      (1/(n:ℝ)^3) * ‖GenK.grad M f‖^2 + topWeight k * ‖flatQPrime M f‖^2 := by
  simp only [flatDeltaPrime, add_apply, smul_apply,
    ContinuousLinearMap.comp_apply, inner_add_right, inner_smul_right,
    GenK.siteDelta, ContinuousLinearMap.adjoint_inner_right, real_inner_self_eq_norm_sq]
  field_simp [show (n : ℝ) ≠ 0 from Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn)]

/-- Exposes the actual n^-3 block restriction without silently using
GenK's bond Q in place of the site Q' of (3.19). -/
theorem flatQPrime_block (f : GenK.Site M (n := n)) (y : GenK.Centers M (n := n)) :
    flatQPrime M f y = (1 / (n:ℝ)^3) •
      ∑ x ∈ AdalyFormal.Balaban.AdmissibleSubspace.blockOf y.1 n, f x := by
  rw [flatQPrime_apply, GenK.siteAverage_apply]
  rfl

/-- Strict positivity is the elementary flat (3.23)+(3.24) base. It is
qualitative: this result alone supplies NO uniform inverse or gradient bound. -/
theorem flatDeltaPrime_kernel (k : ℕ) (f : GenK.Site M (n := n)) (hn : 0 < n)
    (hf : flatDeltaPrime M k f = 0) : f = 0 := by
  have hform := flatDeltaPrime_form M k f hn
  rw [hf] at hform
  simp at hform
  have hgrad : GenK.grad M f = 0 := by
    have hterm : 0 ≤ ((n:ℝ)^3)⁻¹ * ‖GenK.grad M f‖^2 :=
      mul_nonneg (by positivity) (sq_nonneg _)
    have htermQ : 0 ≤ topWeight k * ‖flatQPrime M f‖^2 :=
      mul_nonneg (le_of_lt (topWeight_pos k)) (sq_nonneg _)
    have hterm0 : ((n:ℝ)^3)⁻¹ * ‖GenK.grad M f‖^2 = 0 := by
      linarith
    have hs : ‖GenK.grad M f‖^2 = 0 :=
      (mul_eq_zero.mp hterm0).resolve_left (by positivity)
    exact norm_eq_zero.mp ((sq_eq_zero_iff).mp hs)
  have hQ : flatQPrime M f = 0 := by
    rw [hgrad, norm_zero, zero_pow (by decide : 2 ≠ 0), mul_zero, zero_add] at hform
    have hQsq : ‖flatQPrime M f‖^2 = 0 :=
      (mul_eq_zero.mp hform.symm).resolve_left (ne_of_gt (topWeight_pos k))
    exact norm_eq_zero.mp ((sq_eq_zero_iff).mp hQsq)
  let z : PeriodicLatticeSite M := fun _ => 0
  let w : PeriodicLatticeSite (GenK.fineExtent M n) := (GenK.sites M hn z).1
  have hcov : AdalyFormal.Balaban.CovariantOperators.gradValueCovariant
      (AdalyFormal.Balaban.CovariantHjMinimizer.trivialU (GenK.fineExtent M n))
      (fun x => f x) = 0 := by
    funext b
    have h := congrFun (congrArg AdalyFormal.Balaban.DeltaKUnified.bfl2Equiv hgrad) b
    rw [GenK.grad_apply] at h
    have hnR : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn)
    have hv : f (periodicLatticeShift b.1 b.2) - f b.1 = 0 := by
      exact (smul_eq_zero.mp h).resolve_left hnR
    simpa [AdalyFormal.Balaban.CovariantOperators.gradValueCovariant,
      AdalyFormal.Balaban.CovariantHjMinimizer.trivialU,
      AdalyFormal.Balaban.CovariantOperators.RMap_one] using hv
  have hc := HConstruction.G0CoerceFinal.Reproduced.const_of_grad_eq_zero
    (fun x => f x) hcov
  have hfconst : f = HConstruction.MassCMP122Astra.siteConstant M (n := n) (f w) := by
    apply (WithLp.linearEquiv 2 ℝ _).injective
    funext x
    exact hc x w
  have hz : f w = 0 := by
    have hQval : flatQPrime M f (GenK.sites M hn z) = 0 := by rw [hQ]; rfl
    rw [flatQPrime_apply, hfconst,
      HConstruction.MassCMP122Astra.siteAverage_constant M hn] at hQval
    exact hQval
  apply (WithLp.linearEquiv 2 ℝ _).injective
  funext x
  exact (hc x w).trans hz

end HConstruction.SectBBase
