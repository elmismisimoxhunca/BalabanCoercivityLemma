import NJ3Base
import NJ1Bridge
import AdalyFormal.Balaban.LineIntegralCovariant
import AdalyFormal.Balaban.StridedAveraging

/-!
# NJ15Cov -- BRIDGE to the earlier lanes' covariant carrier: the main term `T1 = unitToCoarseCov 1 ell V` of (124) (= (125))
IS `lineCoarseRestrictCov V ell` (the "linear covariant average" used by `RegU` / `nonflat_gram_floor` / `dyadic_gram_floor`).
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
namespace AdalyFormal.NonflatJet

open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.SuTwoLogExp (SU2 M2)
open AdalyFormal.Balaban.CovariantOperators (SuTwo RMap)
open AdalyFormal.Balaban.LatticeOperators (CoarseBond)
open AdalyFormal.Balaban.AdmissibleSubspace (CoarseLattice Bond blockOf)
open AdalyFormal.Balaban.StridedAveraging (mem_coarseLattice_one stepBondAvgAt stepBondAvgAt_one_eq coarseValAt)
open AdalyFormal.Balaban.ThirdLevelArrows (unitSitesOf)
open AdalyFormal.Balaban.QjComposite (stepBlockOf stepBlockOf_one)
open AdalyFormal.Balaban.TowerLawCov (unitToCoarseCov coarsePathHolonomy coarseTransportPath)
open AdalyFormal.Balaban.QOne (pathSite)
open AdalyFormal.Balaban.LineIntegralCovariant (lineCoarseRestrictCov)

variable {L : PeriodicLatticeExtent}

theorem sum_unitSites_eq (ell : ℕ) (y : PeriodicLatticeSite L) {β : Type*} [AddCommMonoid β]
    (F : PeriodicLatticeSite L → β) :
    ∑ u ∈ unitSitesOf 1 (1 * ell) y, F u.1 = ∑ x ∈ blockOf y ell, F x := by
  have h : (unitSitesOf 1 (1 * ell) y).map (Function.Embedding.subtype _) = blockOf y ell := by
    ext x
    simp only [Finset.mem_map, Function.Embedding.coe_subtype, unitSitesOf, Finset.mem_filter,
      Finset.mem_univ, true_and, Subtype.exists, exists_and_right, exists_eq_right, one_mul]
    constructor
    · rintro ⟨_, hx⟩; exact hx
    · intro hx; exact ⟨mem_coarseLattice_one x, hx⟩
  rw [← h, Finset.sum_map]
  rfl

theorem T1_eq_stepBondAvgAt (ell : ℕ) (V : PeriodicLinkConfiguration SU2 L) (B : CoarseBond L 1 → SuTwo)
    (c : CoarseBond L (1 * ell)) :
    unitToCoarseCov 1 ell V B c = stepBondAvgAt 1 V ell B c.1.1 c.2 := by
  unfold unitToCoarseCov stepBondAvgAt
  congr 1
  rw [stepBlockOf_one]
  have := sum_unitSites_eq (L := L) ell c.1.1 (fun x => ∑ i ∈ Finset.range ell,
    RMap (coarsePathHolonomy 1 V c.1.1 (coarseTransportPath 1 c.1.1 x c.2 i))
      (coarseValAt 1 B (AdalyFormal.Balaban.StridedAveraging.stepPathSite 1 x c.2 i) c.2))
  rw [← this]
  refine Finset.sum_congr rfl (fun u _ => Finset.sum_congr rfl (fun i _ => ?_))
  rw [dif_pos (mem_coarseLattice_one _), AdalyFormal.Balaban.StridedAveraging.coarseValAt_of_mem B
    (mem_coarseLattice_one _)]
  simp [AdalyFormal.Balaban.StridedAveraging.stepPathSite]

/-- **THE BRIDGE.** -/
theorem T1_eq_lineCoarseRestrictCov {ell : ℕ} (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1)) (hell : 0 < ell)
    (U : PeriodicLinkConfiguration SU2 L) (A : Bond L → SuTwo) (c : CoarseBond L ell) :
    unitToCoarseCov 1 ell U (bondToUnit A)
        (⟨⟨c.1.1, by rw [one_mul]; exact c.1.2⟩, c.2⟩ : CoarseBond L (1 * ell))
      = lineCoarseRestrictCov U ell A c := by
  rw [T1_eq_stepBondAvgAt]
  have hfit : ell ≤ L c.2 + 1 := Nat.le_of_dvd (Nat.succ_pos _) (hdvd c.2)
  exact stepBondAvgAt_one_eq U A c.1.1 c.2 hfit

#print axioms T1_eq_lineCoarseRestrictCov

end AdalyFormal.NonflatJet
