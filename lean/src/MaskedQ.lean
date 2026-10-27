import SourceRows
import SectorEnergy
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
set_option synthInstance.maxSize 10000
noncomputable section
namespace HConstruction.TransversePos
open HConstruction.Covariance HConstruction.SmallNF HConstruction.Carrier
open HConstruction.G0Final.Locality HConstruction.NfRepair.Reproduced
open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.AdmissibleSubspace (witnessL)
open AdalyFormal.Balaban.CovariantOperators (SuTwo RMap RMap_one)
open AdalyFormal.Balaban.CovariantHjMinimizer (trivialU)
open AdalyFormal.Balaban.LatticeOperators (CoarseBond)
open AdalyFormal.Balaban.ThirdLevelArrows (unitSitesOf)
open AdalyFormal.Balaban.QjComposite (stepBlockOf)
open AdalyFormal.Balaban.TowerLawCov
open AdalyFormal.DeltaKR66 AdalyFormal.DeltaKR85
open OneStep124
open HConstruction.NonzeroJet (ad_zero g_zero ginv_zero exp_zero)

/-- Only the transports used by T1: its last edge has no following input to transport.
Thus the sixth exceptional derivative row remains a flat T1 row. -/
theorem inactive_main_words : ∀ (a b d : Fin 2) (mu : Fin 3),
    coarseOutput a b d mu ∉ activeRows →
    ∀ u ∈ unitSitesOf 1 (1*2) (coarseOutput a b d mu).1.1,
    ∀ i ∈ Finset.range 2,
      wordCount (coarseOutput a b d mu).1.1
        (coarseTransportPath 1 (coarseOutput a b d mu).1.1 u.1 mu i) = 0 := by
  decide +kernel

theorem source_log_inactive (t : ℝ) (c : Output) (hc : c ∉ activeRows)
    (x : Site) (hx : x ∈ stepBlockOf c.1.1 1 2) :
    (sourcePrincipalLogData 1 2 (nonflatU t)).Zx c x = 0 := by
  change principalSuTwoLog _ = 0
  rw [loop_word, other_rows_zero c hc x hx, zpow_zero]
  exact Subtype.ext AdalyFormal.Balaban.SuTwoLogExp.su2Log_one

theorem source_mean_inactive (t : ℝ) (c : Output) (hc : c ∉ activeRows) :
    (sourcePrincipalLogData 1 2 (nonflatU t)).Z c = 0 := by
  unfold LogData.Z
  apply Finset.sum_eq_zero
  intro u hu
  rw [source_log_inactive t c hc u.1 (HConstruction.Coeff.unit_mem_step c u hu), smul_zero]

theorem coeff_inactive (t : ℝ) (c : Output) (hc : c ∉ activeRows) :
    (∀ u ∈ unitSitesOf 1 (1*2) c.1.1,
      (Coeff124.ofPrincipalBackground 1 2 (nonflatU t)).E1 c u.1 = 0 ∧
      (Coeff124.ofPrincipalBackground 1 2 (nonflatU t)).E2 c u.1 = 0) ∧
    (Coeff124.ofPrincipalBackground 1 2 (nonflatU t)).E3 c = 0 := by
  have hz := source_mean_inactive t c hc
  have hl (u : {x : Site // x ∈ AdalyFormal.Balaban.AdmissibleSubspace.CoarseLattice witnessL 1})
      (hu : u ∈ unitSitesOf 1 (1*2) c.1.1) :=
    source_log_inactive t c hc u.1 (HConstruction.Coeff.unit_mem_step c u hu)
  constructor
  · intro u hu
    simp [Coeff124.ofPrincipalBackground, Coeff124.ofBackground, hz, hl u hu,
      ad_zero, g_zero, ginv_zero, exp_zero]
  · change expOp _ - gOp _ * _ = 0
    rw [hz, ad_zero, exp_zero, neg_zero, g_zero]
    have hs : (∑ u ∈ unitSitesOf 1 (1*2) c.1.1,
        (1 / ((unitSitesOf 1 (1*2) c.1.1).card : ℝ)) •
          gInvOp (adOp ((sourcePrincipalLogData 1 2 (nonflatU t)).Zx c u.1))) = 1 := by
      have he : (∑ u ∈ unitSitesOf 1 (1*2) c.1.1,
        (1 / ((unitSitesOf 1 (1*2) c.1.1).card : ℝ)) •
          gInvOp (adOp ((sourcePrincipalLogData 1 2 (nonflatU t)).Zx c u.1))) =
        ∑ _u ∈ unitSitesOf 1 (1*2) c.1.1, (1/8 : ℝ) • (1 : SuTwo →L[ℝ] SuTwo) := by
        apply Finset.sum_congr rfl
        intro u hu
        rw [hl u hu, ad_zero, ginv_zero, unitSites_card]
        norm_num
      rw [he, Finset.sum_const, unitSites_card, ← Nat.cast_smul_eq_nsmul ℝ, smul_smul]
      norm_num
    rw [hs, one_mul, sub_self]

/-- Nineteen actual native-Q output rows are flat for EVERY t, including the
sixth path-exceptional row. No estimate of transcendental coefficients is used. -/
theorem q124_inactive_flat (t : ℝ) (A : CoarseBond witnessL 1 → SuTwo)
    (c : Output) (hc : c ∉ activeRows) :
    q124Principal 1 2 (nonflatU t) A c = q124Principal 1 2 (trivialU witnessL) A c := by
  obtain ⟨hh,he⟩ := coeff_inactive t c hc
  rw [q124Principal_eq_unitToCoarseCov_add_delta, HConstruction.DRepair.q124_flat]
  have hd : delta124 1 2 (nonflatU t)
      (Coeff124.ofPrincipalBackground 1 2 (nonflatU t)) A c = 0 := by
    have h1 (u) (hu : u ∈ unitSitesOf 1 (1*2) c.1.1) := (hh u hu).1
    have h2 (u) (hu : u ∈ unitSitesOf 1 (1*2) c.1.1) := (hh u hu).2
    have hz1 (f : {x : Site // x ∈ AdalyFormal.Balaban.AdmissibleSubspace.CoarseLattice witnessL 1} → SuTwo) :
        (∑ u ∈ unitSitesOf 1 (1*2) c.1.1,
          (Coeff124.ofPrincipalBackground 1 2 (nonflatU t)).E1 c u.1 (f u)) = 0 := by
      apply Finset.sum_eq_zero
      intro u hu
      rw [h1 u hu]; rfl
    have hz2 (f : {x : Site // x ∈ AdalyFormal.Balaban.AdmissibleSubspace.CoarseLattice witnessL 1} → SuTwo) :
        (∑ u ∈ unitSitesOf 1 (1*2) c.1.1,
          (Coeff124.ofPrincipalBackground 1 2 (nonflatU t)).E2 c u.1 (f u)) = 0 := by
      apply Finset.sum_eq_zero
      intro u hu
      rw [h2 u hu]; rfl
    simp only [delta124, term2, term3, term4, term5, he, hz1, hz2,
      ContinuousLinearMap.zero_apply, smul_zero, neg_zero, add_zero]
  rw [hd, add_zero]
  unfold unitToCoarseCov
  congr 1
  apply Finset.sum_congr rfl
  intro u hu
  apply Finset.sum_congr rfl
  intro i hi
  have hw : wordCount c.1.1 (coarseTransportPath 1 c.1.1 u.1 c.2 i) = 0 := by
    obtain ⟨a,b,d,mu,rfl⟩ := output_parametrization c
    exact inactive_main_words a b d mu hc u hu i hi
  rw [holonomy_eq_one_of_wordCount_zero t _ _ hw, coarsePathHolonomy_trivialU]

#print axioms inactive_main_words
#print axioms source_log_inactive
#print axioms coeff_inactive
#print axioms q124_inactive_flat
end HConstruction.TransversePos
