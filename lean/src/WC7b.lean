import WC7a

/-!
# WC7b -- norm lemmas, sparse sums, and the bounds `ν(T y)`, `ν(S y)` of the twisted decomposition (M2 W6 lane)
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
open AdalyFormal.SliceCoerc (GF)
open AdalyFormal.BondComposite
open SmallnessBridge.Assemble (loopFactorBound)
open AdalyFormal.W6
open AdalyFormal.TowerLoc
open AdalyFormal.GaugeCov (adBL adFL adGen_symm_apply)

theorem norm_RMap (g : Matrix.specialUnitaryGroup (Fin 2) ℂ) (v : SuTwo) : ‖RMap g v‖ = ‖v‖ := by
  have h := AdalyFormal.Balaban.SuTwoInner.inner_RMap g v v
  rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq] at h
  have h1 := norm_nonneg (RMap g v)
  have h2 := norm_nonneg v
  nlinarith [sq_nonneg (‖RMap g v‖ - ‖v‖), sq_nonneg (‖RMap g v‖ + ‖v‖)]

section nrm
variable {ell M R k : ℕ} {Lu : PeriodicLatticeExtent} {S : Tower (scaleUp ell k Lu)}

theorem nF_add_le (hell : 0 < ell) (y z : FSp (geomOf ell k S)) : nF (y + z) ≤ 2 * nF y + 2 * nF z := by
  unfold nF
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum (fun p _ => ?_)
  have h := norm_add_sq_le2 (y p) (z p)
  have hw := (wF_pos hell p).le
  rw [PiLp.add_apply]
  nlinarith [mul_le_mul_of_nonneg_left h hw]

theorem nF_neg (y : FSp (geomOf ell k S)) : nF (-y) = nF y := by
  unfold nF
  refine Finset.sum_congr rfl (fun p _ => ?_)
  rw [PiLp.neg_apply, norm_neg]

/-- `nF` of a single-row vector -/
theorem nF_sglL (w : SuTwo) (p : BIdx (geomOf ell k S)) : nF (sglL p w) = wF p * ‖w‖ ^ 2 := by
  classical
  unfold nF
  simp only [sglL_apply]
  rw [Finset.sum_eq_single p]
  · simp
  · intro q _ hq; simp [hq]
  · intro h; exact absurd (Finset.mem_univ p) h

theorem psiL_norm_sq (hell : 0 < ell) (hell2 : 2 ≤ ell) (hS : Admissible ell M R k S) (p : BIdx (geomOf ell k S))
    (w : SuTwo) : ‖psiL hell p w‖ ^ 2 ≤ CE * (wF p * ‖w‖ ^ 2) := by
  have h := EflatL_norm_sq hell hell2 hS (sglL p w)
  rw [nF_sglL] at h
  exact h

open Classical in
/-- the sparse sum: each target row sees at most `m0` sources -/
theorem nF_sum_sparse (hell : 0 < ell) (m0 : ℕ) (v : BIdx (geomOf ell k S) → FSp (geomOf ell k S))
    (hsupp : ∀ p p' : BIdx (geomOf ell k S), ¬ Inter p' p → v p p' = 0)
    (hcard : ∀ p' : BIdx (geomOf ell k S), (Finset.univ.filter (fun p => Inter p' p)).card ≤ m0) :
    nF (∑ p, v p) ≤ (m0 : ℝ) * ∑ p, nF (v p) := by
  unfold nF
  have hrow : ∀ p' : BIdx (geomOf ell k S), ‖(∑ p, v p) p'‖ ^ 2 ≤ (m0 : ℝ) * ∑ p, ‖v p p'‖ ^ 2 := by
    intro p'
    have h1 : (∑ p, v p) p' = ∑ p ∈ Finset.univ.filter (fun p => Inter p' p), v p p' := by
      rw [WithLp.ofLp_sum, Finset.sum_apply]
      symm
      refine Finset.sum_subset (Finset.filter_subset _ _) (fun p _ hp => ?_)
      exact hsupp p p' (by simpa using hp)
    rw [h1]
    set I := Finset.univ.filter (fun p => Inter p' p) with hI
    have h2 : ‖∑ p ∈ I, v p p'‖ ≤ ∑ p ∈ I, ‖v p p'‖ := norm_sum_le _ _
    have h3 : (∑ p ∈ I, ‖v p p'‖) ^ 2 ≤ (I.card : ℝ) * ∑ p ∈ I, ‖v p p'‖ ^ 2 := sq_sum_le_card_mul_sum_sq
    have h4 : ‖∑ p ∈ I, v p p'‖ ^ 2 ≤ (∑ p ∈ I, ‖v p p'‖) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) h2 2
    have h5 : (I.card : ℝ) ≤ m0 := by exact_mod_cast hcard p'
    have h6 : ∑ p ∈ I, ‖v p p'‖ ^ 2 ≤ ∑ p, ‖v p p'‖ ^ 2 :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun _ _ _ => sq_nonneg _)
    have h7 : 0 ≤ ∑ p ∈ I, ‖v p p'‖ ^ 2 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
    calc _ ≤ _ := h4.trans h3
      _ ≤ (m0 : ℝ) * ∑ p ∈ I, ‖v p p'‖ ^ 2 := mul_le_mul_of_nonneg_right h5 h7
      _ ≤ (m0 : ℝ) * ∑ p, ‖v p p'‖ ^ 2 := mul_le_mul_of_nonneg_left h6 (by positivity)
  calc ∑ p', wF p' * ‖(∑ p, v p) p'‖ ^ 2 ≤ ∑ p', wF p' * ((m0 : ℝ) * ∑ p, ‖v p p'‖ ^ 2) :=
        Finset.sum_le_sum (fun p' _ => mul_le_mul_of_nonneg_left (hrow p') (wF_pos hell p').le)
    _ = ∑ p', ∑ p, (m0 : ℝ) * (wF p' * ‖v p p'‖ ^ 2) := by
        refine Finset.sum_congr rfl (fun p' _ => ?_)
        rw [Finset.mul_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl (fun p _ => ?_)
        ring
    _ = ∑ p, ∑ p', (m0 : ℝ) * (wF p' * ‖v p p'‖ ^ 2) := Finset.sum_comm
    _ = (m0 : ℝ) * ∑ p, ∑ p', wF p' * ‖v p p'‖ ^ 2 := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun p _ => ?_)
        rw [Finset.mul_sum]
    _ = _ := rfl

end nrm

end AdalyFormal.M2W6

#print axioms AdalyFormal.M2W6.nF_sum_sparse
#print axioms AdalyFormal.M2W6.psiL_norm_sq
