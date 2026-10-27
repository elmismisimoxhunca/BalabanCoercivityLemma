import NJ6Delta

/-!
# NJ6bSup -- `‖Δ_c A‖ ≤ 8 κ M` (stride 1, block `ell`), volume free.
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
namespace AdalyFormal.NonflatJet

open Matrix
open AdalyFormal.Target.ClayStatement
  (PeriodicLatticeExtent PeriodicLatticeSite PeriodicLinkConfiguration)
open AdalyFormal.Balaban.CovariantOperators (SuTwo RMap)
open AdalyFormal.Balaban.SuTwoInner
open AdalyFormal.Balaban.LatticeOperators (CoarseBond)
open AdalyFormal.Balaban.AdmissibleSubspace (CoarseLattice blockOf mem_blockOf)
open AdalyFormal.Balaban.StridedAveraging (mem_coarseLattice_one)
open AdalyFormal.Balaban.ThirdLevelArrows (unitSitesOf)
open AdalyFormal.Balaban.TowerLawCov (coarseGammaPath)
open SmallnessBridge.Assemble (coarseGammaPath_one_length_le coarseCoordSteps_one_lt_of_inBlock)
open OneStep124
local instance : NormedSpace ℝ SuTwo := instInnerProductSpaceSuTwo.toNormedSpace

variable {L : PeriodicLatticeExtent}

theorem inBlock_of_mem_unitSites {ell : ℕ} (y : PeriodicLatticeSite L)
    (u : {z : PeriodicLatticeSite L // z ∈ CoarseLattice L 1})
    (hu : u ∈ unitSitesOf 1 (1 * ell) y) : AdalyFormal.Balaban.AdmissibleSubspace.inBlock y ell u.1 := by
  have hb : u.1 ∈ blockOf y (1 * ell) := by simpa [unitSitesOf] using hu
  rw [one_mul] at hb
  exact mem_blockOf.mp hb

theorem near_len_le {ell : ℕ} (y : PeriodicLatticeSite L)
    (u : {z : PeriodicLatticeSite L // z ∈ CoarseLattice L 1})
    (hu : u ∈ unitSitesOf 1 (1 * ell) y) : (coarseGammaPath 1 y u.1).length ≤ 3 * ell :=
  le_trans (coarseGammaPath_one_length_le (inBlock_of_mem_unitSites y u hu)) (by omega)

theorem far_len_le {ell : ℕ} (c : CoarseBond L (1 * ell))
    (u : {z : PeriodicLatticeSite L // z ∈ CoarseLattice L 1})
    (hu : u ∈ unitSitesOf 1 (1 * ell) c.1.1) :
    (coarseGammaPath 1 (cPlus c) (partner c u.1)).length ≤ 3 * ell := by
  refine le_trans (coarseGammaPath_one_length_le_of_steps (cPlus c) (partner c u.1) (ell := ell) ?_)
    (by omega)
  intro ν
  show AdalyFormal.Balaban.TowerLawCov.coarseCoordSteps 1
    (AdalyFormal.Balaban.QOne.pathSite c.1.1 c.2 (ell * 1))
    (AdalyFormal.Balaban.QOne.pathSite u.1 c.2 (ell * 1)) ν < ell
  rw [coarseCoordSteps_shift]
  exact coarseCoordSteps_one_lt_of_inBlock (inBlock_of_mem_unitSites c.1.1 u hu) ν

#print axioms near_len_le
#print axioms far_len_le

end AdalyFormal.NonflatJet
