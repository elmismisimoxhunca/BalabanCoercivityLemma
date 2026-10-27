import DK3FineHodge
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
namespace HConstruction.DK3.FineScale.FlatQ
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
variable (s : ℕ) (hs : 0 < s) (hdvd : ∀ μ, s * 2 ∣ (L μ + 1))

lemma logs_zero (c : CoarseBond L (s * 2)) (x : PeriodicLatticeSite L) :
    (sourcePrincipalLogData s 2 (trivialU L)).Zx c x = 0 := by
  apply Subtype.ext
  change AdalyFormal.Balaban.SuTwoLogExp.su2Log
    (AdalyFormal.Balaban.UbarTowerCov.loopVar s 2 (trivialU L) (c.1.1, c.2) x) = 0
  simp [AdalyFormal.Balaban.UbarTowerCov.loopVar,
    AdalyFormal.Balaban.UbarTowerCov.gammaVarStrided,
    AdalyFormal.Balaban.UbarTowerCov.coarseBondVar,
    AdalyFormal.Balaban.TowerLawCov.coarsePathHolonomy_trivialU]

lemma meanlog_zero (c : CoarseBond L (s * 2)) :
    (sourcePrincipalLogData s 2 (trivialU L)).Z c = 0 := by
  simp [LogData.Z, logs_zero]

lemma E1_flat (c : CoarseBond L (s * 2)) (x : PeriodicLatticeSite L) :
    (Coeff124.ofPrincipalBackground s 2 (trivialU L)).E1 c x = 0 := by
  simp [Coeff124.ofPrincipalBackground, Coeff124.ofBackground,
    meanlog_zero, logs_zero, ad_zero, g_zero, ginv_zero]

lemma E2_flat (c : CoarseBond L (s * 2)) (x : PeriodicLatticeSite L) :
    (Coeff124.ofPrincipalBackground s 2 (trivialU L)).E2 c x = 0 := by
  simp [Coeff124.ofPrincipalBackground, Coeff124.ofBackground,
    meanlog_zero, logs_zero, ad_zero, g_zero, ginv_zero, exp_zero]

include hs hdvd
lemma card_all (c : CoarseBond L (s*2)) : (unitSitesOf s (s*2) c.1.1).card = 8 :=
  OneStep124.unitSitesOf_card_eq (L := L) (y := c.1.1) (ell := s) (m := 2) hs c.1.2 hdvd

lemma E3_flat (c : CoarseBond L (s * 2)) :
    (Coeff124.ofPrincipalBackground s 2 (trivialU L)).E3 c = 0 := by
  simp [Coeff124.ofPrincipalBackground, Coeff124.ofBackground,
    meanlog_zero, logs_zero, ad_zero, g_zero, ginv_zero, exp_zero, card_all s hs hdvd c]
  ext X i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Matrix.mul_apply, Fin.sum_univ_two, Matrix.ofNat_apply] <;> ring

/-- All five channels of the certified q124, on every field/output: the
flat background kills exactly the four correction channels. -/
theorem q124_flat (A : CoarseBond L s → SuTwo)
    (c : CoarseBond L (s * 2)) :
    q124Principal s 2 (trivialU L) A c =
      AdalyFormal.Balaban.TowerLawCov.unitToCoarseCov s 2 (trivialU L) A c := by
  rw [AdalyFormal.DeltaKR85.q124Principal_eq_unitToCoarseCov_add_delta]
  have hd : delta124 s 2 (trivialU L)
      (Coeff124.ofPrincipalBackground s 2 (trivialU L)) A c = 0 := by
    simp [delta124, term2, term3, term4, term5, E1_flat, E2_flat, E3_flat s hs hdvd]
  rw [hd, add_zero]
theorem q124_constant (v : Fin 3 → SuTwo) (c : CoarseBond L (s*2)) :
    q124Principal s 2 (trivialU L) (fun b => v b.2) c = v c.2 := by
  rw [q124_flat s hs hdvd]
  have hdvd0 : ∀ μ, s ∣ L μ + 1 := fun μ => dvd_trans (dvd_mul_right s 2) (hdvd μ)
  have hm (u : {z : PeriodicLatticeSite L // z ∈ CoarseLattice L s}) (i : ℕ) :
      AdalyFormal.Balaban.QOne.pathSite u.1 c.2 (i*s) ∈ CoarseLattice L s :=
    AdalyFormal.Balaban.ThirdLevelArrows.pathSite_mul_coarse s hdvd0 u.property c.2 i
  unfold AdalyFormal.Balaban.TowerLawCov.unitToCoarseCov
  simp only [hm, dif_pos, AdalyFormal.Balaban.TowerLawCov.coarsePathHolonomy_trivialU,
    RMap_one, LinearMap.id_apply, Finset.sum_const, Finset.card_range]
  rw [card_all s hs hdvd c]
  rw [← Nat.cast_smul_eq_nsmul ℝ, ← Nat.cast_smul_eq_nsmul ℝ, smul_smul, smul_smul]
  norm_num

end HConstruction.DK3.FineScale.FlatQ

namespace HConstruction.DK3.FineScale
open CovarianceScale (outputCoordinates incomingQ F)
open HConstruction.Carrier (fineCoordinates)
open AdalyFormal.Balaban.DeltaKUnified (bfl2Equiv)
open AdalyFormal.Balaban.CovariantOperators (SuTwo suTwoWitness suTwoWitness_ne_zero)
open AdalyFormal.Balaban.LatticeOperators (CoarseBond)

theorem incomingQ_constant (c : CoarseBond fineL 8) :
    outputCoordinates (incomingQ 0 constantField) c = suTwoWitness := by
  rw [CovarianceScale.incomingQ_order, tower_zero, U_zero,
    AdalyFormal.Balaban.BlockedBackground.ubarSU2_trivialU]
  have he : fineCoordinates constantField = fun _ => suTwoWitness := rfl
  rw [he]
  have hfirst : AdalyFormal.DeltaKR85.q124Principal 1 2
      (AdalyFormal.Balaban.CovariantHjMinimizer.trivialU fineL) (fun _ => suTwoWitness) =
      fun _ => suTwoWitness := by
    funext b
    exact FlatQ.q124_constant 1 (by norm_num) (by intro μ; norm_num) (fun _ => suTwoWitness) b
  rw [hfirst]
  have hsecond : AdalyFormal.DeltaKR85.q124Principal 2 2
      (AdalyFormal.Balaban.CovariantHjMinimizer.trivialU fineL) (fun _ => suTwoWitness) =
      fun _ => suTwoWitness := by
    funext b
    exact FlatQ.q124_constant 2 (by norm_num) (by intro μ; norm_num) (fun _ => suTwoWitness) b
  rw [hsecond]
  exact FlatQ.q124_constant 4 (by norm_num) (by intro μ; norm_num) (fun _ => suTwoWitness) c

theorem incomingQ_constant_nonzero : incomingQ 0 constantField ≠ 0 := by
  intro h
  have he := incomingQ_constant (CovarianceScale.outputBondEquiv ((fun _ => 0),0))
  rw [h,map_zero,Pi.zero_apply] at he
  exact suTwoWitness_ne_zero he.symm

/-- Positive control on precisely the fine harmonic witness that falsifies bare Delta.
Passing this test is NOT promoted to full invertibility. -/
theorem precision_constant_positive : (0 : ℝ) < inner ℝ constantField (precision 0 1 constantField) := by
  rw [precision_flat_energy, flatCurl_constant, norm_zero, zero_pow (by decide : 2 ≠ 0), zero_add]
  have hq : 0 < ‖incomingQ 0 constantField‖^2 :=
    sq_pos_of_pos (norm_pos_iff.mpr incomingQ_constant_nonzero)
  nlinarith [sq_nonneg ‖gaugeConstraintU 0 constantField‖]

#print axioms incomingQ_constant
#print axioms precision_constant_positive
end HConstruction.DK3.FineScale


