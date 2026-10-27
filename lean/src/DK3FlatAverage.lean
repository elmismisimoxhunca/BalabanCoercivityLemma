import DK3Crossing
import JointAverage
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
namespace HConstruction.DK3.GeneralAverage
open HConstruction.Carrier HConstruction.Covariance
open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.AdmissibleSubspace
open AdalyFormal.Balaban.CovariantOperators (SuTwo RMap_one)
open AdalyFormal.Balaban.CovariantHjMinimizer (trivialU)
open AdalyFormal.Balaban.LatticeOperators (CoarseBond)
open AdalyFormal.Balaban.ThirdLevelArrows (unitSitesOf)
open AdalyFormal.DeltaKR66
open AdalyFormal.DeltaKR85 (q124Principal Coeff124.ofPrincipalBackground)
open OneStep124
open HConstruction.NonzeroJet (ad_zero g_zero ginv_zero exp_zero)

variable {L : PeriodicLatticeExtent}
variable (hdvd : ∀ μ, 2 ∣ (L μ + 1))

lemma logs_zero (c : CoarseBond L (1 * 2)) (x : PeriodicLatticeSite L) :
    (sourcePrincipalLogData 1 2 (trivialU L)).Zx c x = 0 := by
  apply Subtype.ext
  change AdalyFormal.Balaban.SuTwoLogExp.su2Log
    (AdalyFormal.Balaban.UbarTowerCov.loopVar 1 2 (trivialU L) (c.1.1, c.2) x) = 0
  simp [AdalyFormal.Balaban.UbarTowerCov.loopVar,
    AdalyFormal.Balaban.UbarTowerCov.gammaVarStrided,
    AdalyFormal.Balaban.UbarTowerCov.coarseBondVar,
    AdalyFormal.Balaban.TowerLawCov.coarsePathHolonomy_trivialU]

lemma meanlog_zero (c : CoarseBond L (1 * 2)) :
    (sourcePrincipalLogData 1 2 (trivialU L)).Z c = 0 := by
  simp [LogData.Z, logs_zero]

lemma E1_flat (c : CoarseBond L (1 * 2)) (x : PeriodicLatticeSite L) :
    (Coeff124.ofPrincipalBackground 1 2 (trivialU L)).E1 c x = 0 := by
  simp [Coeff124.ofPrincipalBackground, Coeff124.ofBackground,
    meanlog_zero, logs_zero, ad_zero, g_zero, ginv_zero]

lemma E2_flat (c : CoarseBond L (1 * 2)) (x : PeriodicLatticeSite L) :
    (Coeff124.ofPrincipalBackground 1 2 (trivialU L)).E2 c x = 0 := by
  simp [Coeff124.ofPrincipalBackground, Coeff124.ofBackground,
    meanlog_zero, logs_zero, ad_zero, g_zero, ginv_zero, exp_zero]

include hdvd
lemma card_all (c : CoarseBond L (1*2)) : (unitSitesOf 1 2 c.1.1).card = 8 :=
  OneStep124.unitSitesOf_card_eq (L := L) (y := c.1.1) (ell := 1) (m := 2) Nat.one_pos c.1.2 hdvd

lemma E3_flat (c : CoarseBond L (1 * 2)) :
    (Coeff124.ofPrincipalBackground 1 2 (trivialU L)).E3 c = 0 := by
  simp [Coeff124.ofPrincipalBackground, Coeff124.ofBackground,
    meanlog_zero, logs_zero, ad_zero, g_zero, ginv_zero, exp_zero, card_all hdvd c]
  ext X i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Matrix.mul_apply, Fin.sum_univ_two, Matrix.ofNat_apply] <;> ring

/-- All five channels of the certified q124, on every field/output: the
flat background kills exactly the four correction channels. -/
theorem q124_flat (A : CoarseBond L 1 → SuTwo)
    (c : CoarseBond L (1 * 2)) :
    q124Principal 1 2 (trivialU L) A c =
      AdalyFormal.Balaban.TowerLawCov.unitToCoarseCov 1 2 (trivialU L) A c := by
  rw [AdalyFormal.DeltaKR85.q124Principal_eq_unitToCoarseCov_add_delta]
  have hd : delta124 1 2 (trivialU L)
      (Coeff124.ofPrincipalBackground 1 2 (trivialU L)) A c = 0 := by
    simp [delta124, term2, term3, term4, term5, E1_flat, E2_flat, E3_flat hdvd]
  rw [hd, add_zero]
end HConstruction.DK3.GeneralAverage

namespace HConstruction.DK3.GeneralSection
open HConstruction.Carrier HConstruction.Covariance
open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.AdmissibleSubspace
open AdalyFormal.Balaban.CovariantOperators (SuTwo RMap_one)
open AdalyFormal.Balaban.CovariantHjMinimizer (trivialU)
open AdalyFormal.Balaban.LatticeOperators (CoarseBond)
open AdalyFormal.Balaban.ThirdLevelArrows (unitSitesOf)
open AdalyFormal.Balaban.QOne (pathSite)
open AdalyFormal.Balaban.QcEquation (blockCorner)
open AdalyFormal.Balaban.StridedAveraging (mem_coarseLattice_one)
open HConstruction.DRepair.Reproduced (stepLift)
attribute [local irreducible] blockOf CoarseLattice

variable {L : PeriodicLatticeExtent}
variable (hdvd : ∀ μ, 2 ∣ (L μ + 1))
include hdvd
/-- Every length-two segment in an aligned block has exactly one last-layer
hit, and that hit belongs to this very block. Ordinary finite proof, no oracle. -/
lemma hit_geometry : ∀ (c : CoarseBond L (1 * 2))
    (u : {z : PeriodicLatticeSite L // z ∈ CoarseLattice L 1}),
    u ∈ unitSitesOf 1 2 c.1.1 →
    (((u.1 c.2).val % 2 = 1 ∧ blockCorner 2 u.1 = c.1.1 ∧
      ¬ ((pathSite u.1 c.2 1 c.2).val % 2 = 1)) ∨
     (¬ ((u.1 c.2).val % 2 = 1) ∧ (pathSite u.1 c.2 1 c.2).val % 2 = 1 ∧
      blockCorner 2 (pathSite u.1 c.2 1) = c.1.1)) := by
  intro c u hu
  have hx : u.1 ∈ blockOf c.1.1 2 := by
    exact (Finset.mem_filter.mp hu).2
  have hc := AdalyFormal.Balaban.QcEquation.blockCorner_of_mem_blockOf (L := L) c.1.2 hx
  have hs := AdalyFormal.Balaban.ReparamCDisjoint.pathSite_apply_self_val u.1 c.2 1
  have hlt : (u.1 c.2).val < L c.2 + 1 := (u.1 c.2).isLt
  have heven : (L c.2 + 1)%2 = 0 := Nat.mod_eq_zero_of_dvd (hdvd c.2)
  have hlast : (u.1 c.2).val + 1 < L c.2 + 1 ∨ (u.1 c.2).val + 1 = L c.2 + 1 := by omega
  have hstepParity : (pathSite u.1 c.2 1 c.2).val % 2 = ((u.1 c.2).val + 1)%2 := by
    rw [hs]
    rcases hlast with h | h
    · rw [Nat.mod_eq_of_lt h]
    · rw [h, Nat.mod_self, heven]
  by_cases h0 : (u.1 c.2).val % 2 = 1
  · exact Or.inl ⟨h0, hc, by omega⟩
  · refine Or.inr ⟨h0, by omega, ?_⟩
    apply AdalyFormal.Balaban.QcEquation.blockCorner_of_mem_blockOf (L := L) c.1.2
    apply mem_blockOf.mpr
    intro ν
    by_cases hν : ν = c.2
    · subst ν
      have hb := mem_blockOf.mp hx c.2
      have hy0 := mem_CoarseLattice.mp c.1.2 c.2
      change (c.1.1 c.2).val % 2 = 0 at hy0
      have hnowrap : (u.1 c.2).val + 1 < L c.2 + 1 := by omega
      rw [Nat.mod_eq_of_lt hnowrap] at hs
      constructor <;> omega
    · rw [AdalyFormal.Balaban.ReparamCDisjoint.pathSite_apply_ne _ _ _ _ hν]
      exact mem_blockOf.mp hx ν


end HConstruction.DK3.GeneralSection
