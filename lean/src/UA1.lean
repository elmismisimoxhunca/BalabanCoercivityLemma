import FE1c

/-!
# UA1 -- U2 `lemma24Q_su2`: CMP96 (2.128) at U = 1, su(2)-valued, WITH the Q-term (lane m2_unit_20261014)

`lemma24Q_su2`: for every axial `B : Bond L → su(2)` (staircase zeros; NO `Q₁B = 0` hypothesis),
  `(1/54) ℓ^-5 Σ_b ‖B b‖² ≤ ℓ Σ_c ‖q₁ B c‖² + Σ_p ‖flatCurl B p‖²`,
`q₁ = lineCoarseRestrictSuTwo ℓ` (the block average of line integrals).  Scalar input:
`BlockPoincareSharp.lemma24_sharpened`, lifted coordinatewise as in FE1c (which drops the Q-term under `Q₁B = 0`).
-/
set_option autoImplicit false
set_option maxHeartbeats 8000000
namespace AdalyFormal.M2Unit

open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.AdmissibleSubspace
open AdalyFormal.Balaban.LatticeOperators (curlValue CoarseBond)
open AdalyFormal.Balaban.LineIntegralAveraging (lineCoarseRestrict)
open AdalyFormal.Balaban.LineIntegralCovariant (lineCoarseRestrictSuTwo)
open AdalyFormal.Balaban.CovariantOperators (SuTwo)
open AdalyFormal.Balaban.SuTwoGeomU1
open AdalyFormal.Balaban.CovU1Reduction (flatCurlValue)
open AdalyFormal.Balaban.BlockPoincareLemma24 (coarseQEnergy totalCurlEnergy bondNormSq)

theorem lemma24Q_su2 {L : PeriodicLatticeExtent} {ell : ℕ} (hell2 : 2 ≤ ell)
    (hstrict : ∀ μ : Fin 3, ell < L μ + 1) (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1)) (B : Bond L → SuTwo)
    (hB : ∀ y ∈ CoarseLattice L ell, ∀ x ∈ blockOf y ell, ∀ b ∈ staircasePath y x, B b = 0) :
    (1 / 54 : ℝ) * (1 / (ell : ℝ) ^ 5) * ∑ b : Bond L, ‖B b‖ ^ 2 ≤
      (ell : ℝ) * ∑ c : CoarseBond L ell, ‖lineCoarseRestrictSuTwo ell B c‖ ^ 2
        + ∑ p : PeriodicLatticePlaquette L, ‖flatCurlValue B p‖ ^ 2 := by
  have hcomp : ∀ i : Fin 3, ((ell : ℝ) * coarseQEnergy ell (suComp i B) + totalCurlEnergy (suComp i B)
      ≥ (1 / 54) * (1 / (ell : ℝ) ^ 5) * bondNormSq (suComp i B)) := fun i =>
    AdalyFormal.Balaban.BlockPoincareSharp.lemma24_sharpened hell2 hstrict hdvd (suComp i B)
      (suComp_mem_admissible ell i B hB)
  have hN : ∑ b : Bond L, ‖B b‖ ^ 2 = ∑ i : Fin 3, bondNormSq (suComp i B) := by
    unfold bondNormSq
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun b _ => ?_)
    rw [AdalyFormal.FlatEllGeneral.norm_sq_suTwo_eq_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [suComp_apply]
  have hP : ∑ p : PeriodicLatticePlaquette L, ‖flatCurlValue B p‖ ^ 2 = ∑ i : Fin 3, totalCurlEnergy (suComp i B) := by
    unfold totalCurlEnergy
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun p _ => ?_)
    rw [AdalyFormal.FlatEllGeneral.norm_sq_suTwo_eq_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [suCoordLM_flatCurlValue]
  have hQ : ∑ c : CoarseBond L ell, ‖lineCoarseRestrictSuTwo ell B c‖ ^ 2
      = ∑ i : Fin 3, coarseQEnergy ell (suComp i B) := by
    unfold coarseQEnergy
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun c _ => ?_)
    rw [AdalyFormal.FlatEllGeneral.norm_sq_suTwo_eq_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [suCoordLM_lineCoarseRestrictSuTwo]
  rw [hN, hP, hQ, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum (fun i _ => ?_)
  have h := hcomp i
  rw [ge_iff_le] at h
  exact h

end AdalyFormal.M2Unit

#print axioms AdalyFormal.M2Unit.lemma24Q_su2
