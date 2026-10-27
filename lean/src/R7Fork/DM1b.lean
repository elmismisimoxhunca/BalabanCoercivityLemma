import DM1a
import R7Fork.AdalyFormal.Balaban.RegularUGamma0

/-!
# DM1b -- the su(2) lift of the LOCAL Stokes comparison (coordinatewise, as `RegularUGamma0.ell_coarseCurlEnergy_le_plaqEnergy_trivialU`).
  ell * sum_{p in Y} || coarse curl (lineCoarseRestrictSuTwo ell A) (p) ||^2  <=  sum_{q in Pq} || flatCurlValue A q ||^2
whenever every fine plaquette in the windows of the coarse plaquettes of `Y` belongs to `Pq`.
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace AdalyFormal.DirichletMono

open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.AdmissibleSubspace
open AdalyFormal.Balaban.LatticeOperators (curlValue)
open AdalyFormal.Balaban.CoarseCurl
open AdalyFormal.Balaban.CoarseShiftCovariance
open AdalyFormal.Balaban.LineIntegralAveraging (lineCoarseRestrict)
open AdalyFormal.Balaban.LineIntegralCovariant (lineCoarseRestrictSuTwo)
open AdalyFormal.Balaban.CovariantOperators (SuTwo)
open AdalyFormal.Balaban.SuTwoGeomU1
open AdalyFormal.Balaban.SuTwoInner
open AdalyFormal.Balaban.CovU1Reduction (flatCurlValue)
open AdalyFormal.Balaban.ThirdLevelStokes (coarseCurlSuTwo)
open AdalyFormal.Balaban.RegularUGamma0 (suCoordLM_coarseCurlSuTwo)

variable {L : PeriodicLatticeExtent}

theorem norm_sq_suTwo_eq_sum (v : SuTwo) : ‖v‖ ^ 2 = ∑ i : Fin 3, (suCoordLM i v) ^ 2 := by
  have h := hsInner_eq_sum_coord v v
  rw [← inner_eq_hsInner, real_inner_self_eq_norm_sq] at h
  rw [h]
  exact Finset.sum_congr rfl (fun i _ => (sq _).symm)

/-- regroup a sum over a finset of pairs by the second component -/
theorem sum_by_second {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
    (S : Finset (α × β)) (g : α × β → ℝ) :
    ∑ p ∈ S, g p = ∑ b : β, ∑ a ∈ (Finset.univ : Finset α).filter (fun a => (a, b) ∈ S), g (a, b) := by
  classical
  have h1 : ∑ p ∈ S, g p = ∑ p : α × β, if p ∈ S then g p else 0 := by
    rw [← Finset.sum_filter]; congr 1; ext p; simp
  rw [h1, Fintype.sum_prod_type_right]
  refine Finset.sum_congr rfl (fun b _ => ?_)
  rw [Finset.sum_filter]

theorem local_stokes_suTwo {ell : ℕ} (hell : 0 < ell) (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1))
    (A : Bond L → SuTwo) (Y : Finset (CoarsePlaquette L ell)) (Pq : Finset (PeriodicLatticePlaquette L))
    (hY : ∀ p ∈ Y, ∀ x ∈ blockOf p.1.1 ell, ∀ i ∈ Finset.range ell, ∀ j ∈ Finset.range ell,
      (coarseShift (coarseShift x j p.2.1.2) i p.2.1.1, p.2) ∈ Pq) :
    (ell : ℝ) * ∑ p ∈ Y, ‖coarseCurlSuTwo hdvd (lineCoarseRestrictSuTwo ell A) p‖ ^ 2
      ≤ ∑ q ∈ Pq, ‖flatCurlValue A q‖ ^ 2 := by
  classical
  -- coordinates of both sides
  have hL : ∀ p : CoarsePlaquette L ell,
      ‖coarseCurlSuTwo hdvd (lineCoarseRestrictSuTwo ell A) p‖ ^ 2
        = ∑ i : Fin 3, (coarseCurlValue hdvd (lineCoarseRestrict ell (suComp i A)) p) ^ 2 := by
    intro p
    rw [norm_sq_suTwo_eq_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [suCoordLM_coarseCurlSuTwo]
    congr 2
    funext c
    exact suCoordLM_lineCoarseRestrictSuTwo i ell A c
  have hR : ∀ q : PeriodicLatticePlaquette L,
      ‖flatCurlValue A q‖ ^ 2 = ∑ i : Fin 3, (curlValue (suComp i A) q) ^ 2 := by
    intro q
    rw [norm_sq_suTwo_eq_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [suCoordLM_flatCurlValue]
  simp only [hL, hR]
  rw [Finset.sum_comm, Finset.mul_sum, Finset.sum_comm (s := Pq)]
  refine Finset.sum_le_sum (fun i _ => ?_)
  rw [sum_by_second Y, sum_by_second Pq, Finset.mul_sum]
  refine Finset.sum_le_sum (fun d _ => ?_)
  refine local_sum_sq_coarseCurl_le hell hdvd (suComp i A) d
    ((Finset.univ : Finset {y : PeriodicLatticeSite L // y ∈ CoarseLattice L ell}).filter (fun y => (y, d) ∈ Y))
    ((Finset.univ : Finset (PeriodicLatticeSite L)).filter (fun z => (z, d) ∈ Pq)) ?_
  intro y hy x hx i' hi' j hj
  have hyY : (y, d) ∈ Y := (Finset.mem_filter.mp hy).2
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hY (y, d) hyY x hx i' hi' j hj⟩

#print axioms local_stokes_suTwo

end AdalyFormal.DirichletMono
