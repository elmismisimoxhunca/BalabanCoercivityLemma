import ZGU1B
import ZXG3N
import AdalyFormal.Balaban.RegularUGamma0
import AdalyFormal.Balaban.CovU1Reduction

/-!
# GU1C -- fine/unit torus transport at ARBITRARY level `k` (ported from GenKGeometry's `sites`/`bonds`
with `embY` instead of `fineExtent`), and the flat Stokes comparison for the genuine `Q_k`:
  `ell^k * curlEnergy_unit(Q_k A) ≤ ‖curl A‖²`.
Standard axioms only (see the #print axioms lines).
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace AdalyFormal.GenuineU1

open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane (scaleUp)
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Balaban.CovariantOperators (SuTwo curlCovariantLM)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond blockOf CoarseLattice mem_CoarseLattice)
open AdalyFormal.Balaban.LatticeOperators (CoarseBond)
open AdalyFormal.Balaban.CoarseCurl (coarseShift coarseShift_mem_coarseLattice CoarsePlaquette)
open AdalyFormal.Balaban.ThirdLevelStokes (coarseCurlSuTwo)
open AdalyFormal.Balaban.RegularUGamma0 (coarseCurlEnergySuTwo ell_coarseCurlEnergy_le_plaqEnergy_trivialU)
open AdalyFormal.Balaban.SuTwoInner (inner_eq_hsInner)
open AdalyFormal.Balaban.CovU1Reduction (flatCurlValue curlCovariantLM_trivialU_eq_flatCurlLM)
open AdalyFormal.Balaban.LineIntegralCovariant (lineCoarseRestrictSuTwo lineCoarseRestrictCovLM
  lineCoarseRestrictCov_trivialU)
open AdalyFormal.Balaban.CovariantHjMinimizer (trivialU)

section
variable (ell k : ℕ) (Lu : PeriodicLatticeExtent) (hell : 0 < ell)

theorem embY_mem_CL (y : PeriodicLatticeSite Lu) :
    embY ell k Lu hell y ∈ CoarseLattice (scaleUp ell k Lu) (ell ^ k) := by
  rw [mem_CoarseLattice]
  intro μ
  rw [embY_val]
  exact Nat.mul_mod_right _ _

theorem scaleUp_tiling (hell : 0 < ell) : ∀ μ, ell ^ k ∣ scaleUp ell k Lu μ + 1 := fun μ => by
  rw [scaleUp_succ ell k Lu hell μ]; exact dvd_mul_left _ _

/-- the unit torus as the level-`k` coarse lattice of the fine torus -/
noncomputable def sitesE : PeriodicLatticeSite Lu ≃
    {x : PeriodicLatticeSite (scaleUp ell k Lu) // x ∈ CoarseLattice (scaleUp ell k Lu) (ell ^ k)} :=
  Equiv.ofBijective (fun y => ⟨embY ell k Lu hell y, embY_mem_CL ell k Lu hell y⟩)
    ⟨fun y y' h => embY_injective ell k Lu hell (congrArg Subtype.val h),
     fun x => by
       obtain ⟨y, hy⟩ := (coarse_k_iff_emb ell k Lu hell x.1).mp (fun μ =>
         Nat.dvd_of_mod_eq_zero ((mem_CoarseLattice.mp x.2) μ))
       exact ⟨y, Subtype.ext hy.symm⟩⟩

theorem sitesE_val (y : PeriodicLatticeSite Lu) : (sitesE ell k Lu hell y).1 = embY ell k Lu hell y := rfl

theorem sitesE_shift (hN : ∀ μ, 1 ≤ Lu μ) (y : PeriodicLatticeSite Lu) (μ : Fin 3) :
    (sitesE ell k Lu hell (periodicLatticeShift y μ)).1 = coarseShift (sitesE ell k Lu hell y).1 (ell ^ k) μ :=
  (AdalyFormal.StatementLaneG.coarseShift_embY ell k Lu hell hN y μ).symm

noncomputable def bondsE : Bond Lu ≃ CoarseBond (scaleUp ell k Lu) (ell ^ k) :=
  Equiv.prodCongr (sitesE ell k Lu hell) (Equiv.refl _)

noncomputable def plaqE : PeriodicLatticePlaquette Lu ≃ CoarsePlaquette (scaleUp ell k Lu) (ell ^ k) :=
  Equiv.prodCongr (sitesE ell k Lu hell) (Equiv.refl _)

/-- the unit-torus field carried by a coarse-bond field of the fine torus -/
noncomputable def unitField (A : CoarseBond (scaleUp ell k Lu) (ell ^ k) → SuTwo) : Bond Lu → SuTwo :=
  fun b => A (bondsE ell k Lu hell b)

theorem curl_reindex (hN : ∀ μ, 1 ≤ Lu μ)
    (A : CoarseBond (scaleUp ell k Lu) (ell ^ k) → SuTwo) (p : PeriodicLatticePlaquette Lu) :
    flatCurlValue (unitField ell k Lu hell A) p =
      coarseCurlSuTwo (scaleUp_tiling ell k Lu hell) A (plaqE ell k Lu hell p) := by
  unfold flatCurlValue coarseCurlSuTwo unitField
  have h0 : (sitesE ell k Lu hell (periodicLatticeShift p.1 p.2.1.1)) =
      ⟨coarseShift (sitesE ell k Lu hell p.1).1 (ell ^ k) p.2.1.1,
        coarseShift_mem_coarseLattice (scaleUp_tiling ell k Lu hell) (sitesE ell k Lu hell p.1).2 p.2.1.1⟩ :=
    Subtype.ext (sitesE_shift ell k Lu hell hN p.1 p.2.1.1)
  have h1 : (sitesE ell k Lu hell (periodicLatticeShift p.1 p.2.1.2)) =
      ⟨coarseShift (sitesE ell k Lu hell p.1).1 (ell ^ k) p.2.1.2,
        coarseShift_mem_coarseLattice (scaleUp_tiling ell k Lu hell) (sitesE ell k Lu hell p.1).2 p.2.1.2⟩ :=
    Subtype.ext (sitesE_shift ell k Lu hell hN p.1 p.2.1.2)
  change A (sitesE ell k Lu hell p.1, p.2.1.1) + A (sitesE ell k Lu hell (periodicLatticeShift p.1 p.2.1.1), p.2.1.2) -
    A (sitesE ell k Lu hell (periodicLatticeShift p.1 p.2.1.2), p.2.1.1) - A (sitesE ell k Lu hell p.1, p.2.1.2) = _
  rw [h0, h1]
  rfl

theorem curlEnergy_reindex (hN : ∀ μ, 1 ≤ Lu μ)
    (A : CoarseBond (scaleUp ell k Lu) (ell ^ k) → SuTwo) :
    ∑ p : PeriodicLatticePlaquette Lu, ‖flatCurlValue (unitField ell k Lu hell A) p‖ ^ 2 =
      coarseCurlEnergySuTwo (scaleUp_tiling ell k Lu hell) A := by
  unfold coarseCurlEnergySuTwo
  simp only [← inner_eq_hsInner, real_inner_self_eq_norm_sq, curl_reindex ell k Lu hell hN]
  exact Equiv.sum_comp (plaqE ell k Lu hell)
    (fun p => ‖coarseCurlSuTwo (scaleUp_tiling ell k Lu hell) A p‖ ^ 2)

/-- **FLAT STOKES COMPARISON for the level-`k` average**: for every fine su(2) bond field `A`,
`ell^k · ‖curl_unit (Q_k A)‖² ≤ ‖curl A‖²`. -/
theorem stokes_unit (hN : ∀ μ, 1 ≤ Lu μ) (A : Bond (scaleUp ell k Lu) → SuTwo) :
    ((ell ^ k : ℕ) : ℝ) * ∑ p : PeriodicLatticePlaquette Lu,
        ‖flatCurlValue (unitField ell k Lu hell (lineCoarseRestrictSuTwo (ell ^ k) A)) p‖ ^ 2
      ≤ ∑ p' : PeriodicLatticePlaquette (scaleUp ell k Lu), ‖flatCurlValue A p'‖ ^ 2 := by
  have hpos : 0 < ell ^ k := pow_pos hell k
  have h := ell_coarseCurlEnergy_le_plaqEnergy_trivialU hpos (scaleUp_tiling ell k Lu hell) A
  have hc : curlCovariantLM (trivialU (scaleUp ell k Lu)) A = flatCurlValue A := by
    rw [curlCovariantLM_trivialU_eq_flatCurlLM]; rfl
  have hq : lineCoarseRestrictCovLM (trivialU (scaleUp ell k Lu)) (ell ^ k) A
      = lineCoarseRestrictSuTwo (ell ^ k) A := by
    funext c
    exact lineCoarseRestrictCov_trivialU (ell ^ k) A c
  rw [hq, hc] at h
  rw [curlEnergy_reindex ell k Lu hell hN]
  exact h

end

#print axioms sitesE
#print axioms curl_reindex
#print axioms curlEnergy_reindex
#print axioms stokes_unit

end AdalyFormal.GenuineU1
