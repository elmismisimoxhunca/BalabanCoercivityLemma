import FlatSource
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
namespace HConstruction.DRepair
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
open HConstruction.NonzeroJet (logs_zero meanlog_zero ad_zero g_zero ginv_zero exp_zero)

lemma card_all : ∀ c : CoarseBond witnessL (1 * 2),
    (unitSitesOf 1 2 c.1.1).card = 8 := by decide

lemma E1_flat (c : CoarseBond witnessL (1 * 2)) (x : PeriodicLatticeSite witnessL) :
    (Coeff124.ofPrincipalBackground 1 2 (trivialU witnessL)).E1 c x = 0 := by
  simp [Coeff124.ofPrincipalBackground, Coeff124.ofBackground,
    meanlog_zero, logs_zero, ad_zero, g_zero, ginv_zero]

lemma E2_flat (c : CoarseBond witnessL (1 * 2)) (x : PeriodicLatticeSite witnessL) :
    (Coeff124.ofPrincipalBackground 1 2 (trivialU witnessL)).E2 c x = 0 := by
  simp [Coeff124.ofPrincipalBackground, Coeff124.ofBackground,
    meanlog_zero, logs_zero, ad_zero, g_zero, ginv_zero, exp_zero]

lemma E3_flat (c : CoarseBond witnessL (1 * 2)) :
    (Coeff124.ofPrincipalBackground 1 2 (trivialU witnessL)).E3 c = 0 := by
  simp [Coeff124.ofPrincipalBackground, Coeff124.ofBackground,
    meanlog_zero, logs_zero, ad_zero, g_zero, ginv_zero, exp_zero, card_all c]
  ext X i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Matrix.mul_apply, Fin.sum_univ_two, Matrix.ofNat_apply] <;> ring

/-- All five channels of the certified q124, on every field/output: the
flat background kills exactly the four correction channels. -/
theorem q124_flat (A : CoarseBond witnessL 1 → SuTwo)
    (c : CoarseBond witnessL (1 * 2)) :
    q124Principal 1 2 (trivialU witnessL) A c =
      AdalyFormal.Balaban.TowerLawCov.unitToCoarseCov 1 2 (trivialU witnessL) A c := by
  rw [AdalyFormal.DeltaKR85.q124Principal_eq_unitToCoarseCov_add_delta]
  have hd : delta124 1 2 (trivialU witnessL)
      (Coeff124.ofPrincipalBackground 1 2 (trivialU witnessL)) A c = 0 := by
    simp [delta124, term2, term3, term4, term5, E1_flat, E2_flat, E3_flat]
  rw [hd, add_zero]
end HConstruction.DRepair
