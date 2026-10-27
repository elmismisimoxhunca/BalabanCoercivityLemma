import MI2
import MI14
import MI16

/-!
# MI17 -- the IMS square bound with a weaker partition hypothesis, the sandwich algebra (M1 lane E, 2026-10-13)

* `ims_sq_upper'` : MI1's square bound with the partition identity required only at `Y A`;
* `sandwich_ims` : real-number assembly of `(1−η) G0 − 2νN ≤ F ≤ (1+η) G0 + 2νN` with the IMS bound on `G0`;
* `norm_sub_sq_bounds` : `‖x − y‖² ≤ (1+ε)‖x‖² + (1+1/ε)‖y‖²` and `(1−ε)‖x‖² − (1/ε)‖y‖² ≤ ‖x − y‖²`.
(The genuine `Ginv` form `ginv_form` is MI18, the sandwich MI19, `ginvIMS_of` MI22.)
No sorry / native_decide / axiom.
-/
set_option autoImplicit false
set_option maxHeartbeats 16000000
set_option maxRecDepth 8000
set_option synthInstance.maxHeartbeats 400000

namespace AdalyFormal.M1IMS

open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.SiteCoercivity
open AdalyFormal.DLayer
open AdalyFormal.M1Site
open AdalyFormal.StatementLane (Tower Admissible bigSide scaleUp)
open AdalyFormal.StatementLaneG (gparams)
open AdalyFormal.Balaban.AdmissibleSubspace (blockOf mem_blockOf CoarseLattice mem_CoarseLattice Bond)
open AdalyFormal.Balaban.CovariantOperators (SuTwo RMap BondFnL2 curlValueCovariant)
open AdalyFormal.Balaban.CovariantHjMinimizer (PlaqFnL2)
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
open AdalyFormal.StatementLaneR6 (plaqMask plaqMask_apply deltaPrimeBilL2NormLoc)
open AdalyFormal.Balaban.DeltaKFull (curlCovariantLM_L2)

variable {L : PeriodicLatticeExtent}

/-! ## 0. abstract pieces -/

theorem ims_sq_upper' {ι E F : Type*} [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] (Y : E → F) (m : ι → E → E) (P : ι → F → F) (A : E)
    (hP : ∑ i, ‖P i (Y A)‖ ^ 2 = ‖Y A‖ ^ 2) (ε : ℝ) (hε : 0 < ε) :
    ∑ i, ‖Y (m i A)‖ ^ 2 ≤ (1 + ε) * ‖Y A‖ ^ 2 + (1 + 1 / ε) * ∑ i, ‖Y (m i A) - P i (Y A)‖ ^ 2 := by
  set u : ι → F := fun i => P i (Y A)
  set c : ι → F := fun i => Y (m i A) - P i (Y A)
  have hsplit : ∀ i, ‖Y (m i A)‖ ^ 2 = ‖u i‖ ^ 2 + 2 * ⟪u i, c i⟫ + ‖c i‖ ^ 2 := by
    intro i
    have : Y (m i A) = u i + c i := by simp [u, c]
    rw [this, norm_add_sq_real]
  have hcs := sum_inner_le u c
  rw [show ∑ i, ‖u i‖ ^ 2 = ‖Y A‖ ^ 2 from hP, Real.sqrt_sq (norm_nonneg _)] at hcs
  have hsum : ∑ i, ‖Y (m i A)‖ ^ 2 = ‖Y A‖ ^ 2 + 2 * ∑ i, ⟪u i, c i⟫ + ∑ i, ‖c i‖ ^ 2 := by
    simp only [hsplit, Finset.sum_add_distrib, ← Finset.mul_sum]
    rw [show ∑ i, ‖u i‖ ^ 2 = ‖Y A‖ ^ 2 from hP]
  set e := ∑ i, ‖c i‖ ^ 2
  have he : 0 ≤ e := Finset.sum_nonneg fun i _ => sq_nonneg _
  set s := Real.sqrt e
  have hs : s ^ 2 = e := Real.sq_sqrt he
  have hamgm : 2 * ‖Y A‖ * s ≤ ε * ‖Y A‖ ^ 2 + (1 / ε) * s ^ 2 := by
    have : 0 ≤ (ε * ‖Y A‖ - s) ^ 2 / ε := div_nonneg (sq_nonneg _) hε.le
    have e1 : (ε * ‖Y A‖ - s) ^ 2 / ε = ε * ‖Y A‖ ^ 2 - 2 * ‖Y A‖ * s + (1 / ε) * s ^ 2 := by
      field_simp; ring
    linarith
  have h1 := (abs_le.mp hcs).2
  rw [hs] at hamgm
  nlinarith

/-- real-number assembly of the sandwiched IMS. -/
theorem sandwich_ims {ι : Type*} [Fintype ι] (Gi G0 Ni : ι → ℝ) (GA G0A NA η ν C1 ε2 : ℝ)
    (hη0 : 0 ≤ η) (hη1 : η < 1) (hε2 : 0 ≤ ε2) (hν : 0 ≤ ν) (hNA : 0 ≤ NA)
    (hup : ∀ i, Gi i ≤ (1 + η) * G0 i + ν * Ni i)
    (hlow : (1 - η) * G0A - ν * NA ≤ GA)
    (hims : ∑ i, G0 i ≤ (1 + ε2) * G0A + C1 * NA)
    (hN : ∑ i, Ni i = NA) :
    ∑ i, Gi i ≤ ((1 + η) * (1 + ε2) / (1 - η)) * GA
      + ((1 + η) * (1 + ε2) * ν / (1 - η) + (1 + η) * C1 + ν) * NA := by
  have h1 : ∑ i, Gi i ≤ (1 + η) * ∑ i, G0 i + ν * NA := by
    rw [← hN, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_le_sum (fun i _ => hup i)
  have hpos : 0 < 1 - η := by linarith
  have h2 : G0A ≤ (GA + ν * NA) / (1 - η) := by rw [le_div_iff₀ hpos]; linarith
  have h3 : (1 + η) * ∑ i, G0 i ≤ (1 + η) * ((1 + ε2) * G0A + C1 * NA) :=
    mul_le_mul_of_nonneg_left hims (by linarith)
  have h4 : (1 + η) * (1 + ε2) * G0A ≤ (1 + η) * (1 + ε2) * ((GA + ν * NA) / (1 - η)) :=
    mul_le_mul_of_nonneg_left h2 (by positivity)
  have e : (1 + η) * (1 + ε2) * ((GA + ν * NA) / (1 - η))
      = ((1 + η) * (1 + ε2) / (1 - η)) * GA + ((1 + η) * (1 + ε2) * ν / (1 - η)) * NA := by
    field_simp
  nlinarith

/-- `‖x − y‖² ≤ (1+ε)‖x‖² + (1+1/ε)‖y‖²` and `≥ (1−ε)‖x‖² − (1/ε)‖y‖²` for `0 < ε`. -/
theorem norm_sub_sq_bounds {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] (x y : V) (ε : ℝ) (hε : 0 < ε) :
    ‖x - y‖ ^ 2 ≤ (1 + ε) * ‖x‖ ^ 2 + (1 + 1 / ε) * ‖y‖ ^ 2 ∧
      (1 - ε) * ‖x‖ ^ 2 - (1 / ε) * ‖y‖ ^ 2 ≤ ‖x - y‖ ^ 2 := by
  have hexp : ‖x - y‖ ^ 2 = ‖x‖ ^ 2 - 2 * ⟪x, y⟫ + ‖y‖ ^ 2 := norm_sub_sq_real x y
  have hcs : |⟪x, y⟫| ≤ ‖x‖ * ‖y‖ := abs_real_inner_le_norm x y
  have h1 : 2 * (‖x‖ * ‖y‖) ≤ ε * ‖x‖ ^ 2 + (1 / ε) * ‖y‖ ^ 2 := by
    have : 0 ≤ (ε * ‖x‖ - ‖y‖) ^ 2 / ε := div_nonneg (sq_nonneg _) hε.le
    have e1 : (ε * ‖x‖ - ‖y‖) ^ 2 / ε = ε * ‖x‖ ^ 2 - 2 * (‖x‖ * ‖y‖) + (1 / ε) * ‖y‖ ^ 2 := by field_simp; ring
    linarith
  have h2 := abs_le.mp hcs
  constructor
  · nlinarith [sq_nonneg ‖y‖]
  · nlinarith [sq_nonneg ‖y‖, show 0 ≤ ‖y‖ ^ 2 from sq_nonneg _]

end AdalyFormal.M1IMS

#print axioms AdalyFormal.M1IMS.ims_sq_upper'
#print axioms AdalyFormal.M1IMS.sandwich_ims
#print axioms AdalyFormal.M1IMS.norm_sub_sq_bounds
