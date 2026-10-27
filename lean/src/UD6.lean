import UD5

/-!
# UD6 -- `genC_support`: `C B̃` is supported within `2ℓ` of `Λ` (lane m2_unitcharts_20261014)

`C = id - h Q` (`Cop`): off the dropped bonds `C B̃ = B̃`, supported on bonds touching `Λ` (`OnLambdaT`); on a dropped bond
`b = droppedBondLast ℓ c` with `c` touching `Λ'`, the base of `b` is within `ℓ - 1` of `c₋` and `c₋`, `c₊` are within `ℓ` of a point of `Λ`.
-/
set_option autoImplicit false
set_option maxHeartbeats 16000000
set_option maxRecDepth 8000
namespace AdalyFormal.M2UnitCharts

open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLane2 (OnLambdaT)
open AdalyFormal.StatementLaneR8 (Ball pdist_comm pdist_triangle pdist_coarseShift_le pdist_shift_le lamPrime_sub)
open AdalyFormal.Balaban.CovariantOperators (SuTwo)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.CoarseCurl (coarseShift)
open AdalyFormal.StatementLaneG (gparams)

theorem genC_support {ell k : ℕ} {Lu : PeriodicLatticeExtent} (hell : 0 < ell) (S : Tower (scaleUp ell k Lu))
    (U : AdalyFormal.Balaban.CoercUMainDesigned.LinkCfg (scaleUp ell k Lu)) (a : ℝ) (Lam : Set (PeriodicLatticeSite Lu))
    (Bt : Bond Lu → SuTwo) (hBT : OnLambdaT Lam Bt) (b : Bond Lu)
    (hb : AdalyFormal.StatementLaneG.GenP.genC (gparams ell k Lu hell S U a Lam) Bt b ≠ 0) :
    ∃ y0 ∈ Lam, pdist y0 b.1 ≤ 2 * ell := by
  by_cases hd : IsDroppedIn Lam ell b
  · obtain ⟨c, hc, rfl⟩ := hd
    have hpath : pdist c.1.1 (AdalyFormal.Balaban.ReparamCDisjoint.droppedBondLast ell c).1 ≤ ell - 1 :=
      pdist_coarseShift_le (L := Lu) c.1.1 (ell - 1) c.2
    rcases hc with h | h
    · exact ⟨c.1.1, lamPrime_sub hell h, by omega⟩
    · refine ⟨coarseShift c.1.1 ell c.2, lamPrime_sub hell h, ?_⟩
      have h1 : pdist (coarseShift c.1.1 ell c.2) c.1.1 ≤ ell := by
        rw [pdist_comm]; exact pdist_coarseShift_le _ _ _
      have h2 := pdist_triangle (coarseShift c.1.1 ell c.2) c.1.1
        (AdalyFormal.Balaban.ReparamCDisjoint.droppedBondLast ell c).1
      omega
  · have hid : AdalyFormal.StatementLaneG.GenP.genC (gparams ell k Lu hell S U a Lam) Bt b = Bt b :=
      AdalyFormal.IngredientFamilyR2.Cop_id _ _ Bt b hd
    rw [hid] at hb
    by_contra hno
    simp only [not_exists, not_and, not_le] at hno
    apply hb
    apply hBT
    rintro (h | h)
    · have := hno b.1 h
      rw [AdalyFormal.StatementLane.pdist_self] at this; omega
    · have := hno _ h
      have h3 := pdist_shift_le b.1 b.2
      rw [pdist_comm] at h3
      omega

end AdalyFormal.M2UnitCharts

#print axioms AdalyFormal.M2UnitCharts.genC_support
