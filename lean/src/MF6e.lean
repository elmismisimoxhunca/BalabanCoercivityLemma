import MF6b
import AdalyFormal.Balaban.CStarReconciliation
import MF6c
import NJ20c
import NJ9cBase

/-!
# MF6e (TEXT COPY of nonflat_jet R5L2a, recompiled against the r7 fork) (r5 statement-lane carrier: `Dset` = coarse bonds TOUCHING `Λ'`; textual port of NJ21a,b,c)
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
namespace AdalyFormal.M0Finish.R7

open Matrix
open AdalyFormal.Target.ClayStatement
  (PeriodicLatticeExtent PeriodicLatticeSite PeriodicLatticeEdge PeriodicLinkConfiguration)
open AdalyFormal.Balaban.CovariantOperators (SuTwo)
open AdalyFormal.Balaban.SuTwoInner
open AdalyFormal.Balaban.SuTwoLogExp (SU2 M2)
open AdalyFormal.Balaban.LatticeOperators (CoarseBond)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.RMapLipschitz (frobNorm)
open AdalyFormal.Balaban.ReparamCDisjoint (droppedBondLast)
open AdalyFormal.Balaban.RegularUPerturbation (bondEnergy bondEnergy_nonneg)
open AdalyFormal.Balaban.CStarReconciliation (norm_le_sqrt_bondEnergy)
open AdalyFormal.Balaban.TowerLawCov (unitToCoarseCov)
open AdalyFormal.Balaban.CovariantHjMinimizer (trivialU)
open AdalyFormal.DeltaKR85 (q124Principal q124Principal_eq_unitToCoarseCov_add_delta)
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.NonflatJet
open EstimatesLayer.E1E3
open OneStep124 (delta124)
local instance : NormedSpace ℝ SuTwo := instInnerProductSpaceSuTwo.toNormedSpace

variable {L : PeriodicLatticeExtent}

theorem l1_gA_bondToUnit (B : Bond L → SuTwo) : l1 (gA (bondToUnit B)) = bondEnergy B := by
  unfold l1 gA fA bondToUnit bondEnergy
  rfl

/-- `ι_D` is an `L²` isometry. -/
theorem iotaD_energy {ell : ℕ} (hell : 0 < ell) (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1))
    (Lam : Set (PeriodicLatticeSite L)) (w : Dset L ell Lam → SuTwo) :
    bondEnergy (iotaD ell Lam w) = ∑ c : Dset L ell Lam, ‖w c‖ ^ 2 := by
  classical
  have hinj := AdalyFormal.Balaban.FullReparamC.droppedBondLast_injective (L := L) hell hdvd
  unfold bondEnergy
  have h0 : ∀ b ∈ (Finset.univ : Finset (Bond L)),
      b ∉ (Finset.univ : Finset (Dset L ell Lam)).image (fun c => droppedBondLast ell c.1) →
        ‖iotaD ell Lam w b‖ ^ 2 = 0 := by
    intro b _ hb
    have : ¬ AdalyFormal.StatementLane.IsDroppedIn Lam ell b := by
      rintro ⟨c, hc, rfl⟩
      exact hb (Finset.mem_image.mpr ⟨⟨c, hc⟩, Finset.mem_univ _, rfl⟩)
    rw [iotaD_apply_not_dropped Lam w b this]
    simp
  rw [← Finset.sum_subset (Finset.subset_univ _) h0, Finset.sum_image (fun c _ c' _ h => Subtype.ext (hinj h))]
  refine Finset.sum_congr rfl (fun c _ => ?_)
  rw [iotaD_apply_dropped Lam hinj w c]

/-- the flat `Δ` vanishes. -/
theorem delta_flat_zero {ell : ℕ} (hell : 0 < ell) (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1))
    (B : Bond L → SuTwo) (c : CoarseBond L (1 * ell)) :
    delta124 1 ell (trivialU L)
      (AdalyFormal.DeltaKR85.Coeff124.ofPrincipalBackground 1 ell (trivialU L)) (bondToUnit B) c = 0 := by
  have hflatV : ∀ e, frobNorm ((((trivialU L) e : SU2) : M2) - 1) ≤ 0 := by
    intro e
    show frobNorm (((1 : SU2) : M2) - 1) ≤ 0
    simp [AdalyFormal.Balaban.RMapLipschitz.frobNorm_zero]
  obtain ⟨hF1, hF2, hF3⟩ := E_bounds hell hdvd (trivialU L) 0 le_rfl hflatV
    (by rw [rhoOf_zero]; positivity) c
  rw [rhoOf_zero, e2Majorant_zero] at hF1 hF2 hF3
  have h := norm_delta124_le_sup hell (trivialU L) _ c 0 (Real.sqrt (bondEnergy B)) le_rfl (Real.sqrt_nonneg _)
    hF1 hF2 hF3 (bondToUnit B) (fun b => norm_le_sqrt_bondEnergy B _)
  have : ‖delta124 1 ell (trivialU L)
      (AdalyFormal.DeltaKR85.Coeff124.ofPrincipalBackground 1 ell (trivialU L)) (bondToUnit B) c‖ ≤ 0 := by
    simpa using h
  exact norm_le_zero_iff.mp this

#print axioms delta_flat_zero

theorem Q1jet_sub_flat_l2 {ell : ℕ} (hell : 0 < ell) (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1))
    (V : PeriodicLinkConfiguration SU2 L) (ε0 : ℝ) (hε0 : 0 ≤ ε0)
    (hV : ∀ e, frobNorm ((V e : M2) - 1) ≤ ε0) (hsmall : rhoOf ell ε0 < Real.pi / 2)
    (hreg : RegBg 1 ell V) (B : Bond L → SuTwo) :
    ∑ c : CoarseBond L ell, ‖Q1jet ell V B c - Q1jet ell flatCfg B c‖ ^ 2
      ≤ (384 * (ell * ε0) ^ 2 + 480 * (e2Majorant (rhoOf ell ε0)) ^ 2) * bondEnergy B := by
  have hk : 0 ≤ e2Majorant (rhoOf ell ε0) := e2Majorant_nonneg (by unfold rhoOf; positivity)
  have hE : ∀ c : CoarseBond L (1 * ell), _ := fun c => E_bounds hell hdvd V ε0 hε0 hV hsmall c
  have hL2 := delta124_l2 hell V (AdalyFormal.DeltaKR85.Coeff124.ofPrincipalBackground 1 ell V)
    (e2Majorant (rhoOf ell ε0)) hk (fun c => (hE c).1) (fun c => (hE c).2.1) (fun c => (hE c).2.2)
    (bondToUnit B)
  have hT := T1_drift_l2 hell V ε0 hε0 hV (bondToUnit B)
  rw [l1_gA_bondToUnit] at hL2 hT
  have hrow : ∀ c : CoarseBond L ell, ‖Q1jet ell V B c - Q1jet ell flatCfg B c‖ ^ 2
      ≤ 2 * ‖unitToCoarseCov 1 ell V (bondToUnit B) (cbEquiv ell c)
            - unitToCoarseCov 1 ell (trivialU L) (bondToUnit B) (cbEquiv ell c)‖ ^ 2
        + 2 * ‖delta124 1 ell V (AdalyFormal.DeltaKR85.Coeff124.ofPrincipalBackground 1 ell V)
            (bondToUnit B) (cbEquiv ell c)‖ ^ 2 := by
    intro c
    rw [Q1jet_eq_q124 V ell hell hdvd hreg (guard_of_small V ε0 hε0 hV hsmall) B c,
      Q1jet_eq_q124 (flatCfg : PeriodicLinkConfiguration SU2 L) ell hell hdvd (regBg_flat ell)
        (fun c x hx => flat_guard hell (c.1.1, c.2) x hx) B c, flatCfg_eq_trivialU]
    show ‖q124Principal 1 ell V (bondToUnit B) (cbEquiv ell c)
        - q124Principal 1 ell (trivialU L) (bondToUnit B) (cbEquiv ell c)‖ ^ 2 ≤ _
    rw [q124Principal_eq_unitToCoarseCov_add_delta, q124Principal_eq_unitToCoarseCov_add_delta,
      delta_flat_zero hell hdvd B (cbEquiv ell c), add_zero]
    have : unitToCoarseCov 1 ell V (bondToUnit B) (cbEquiv ell c)
          + delta124 1 ell V (AdalyFormal.DeltaKR85.Coeff124.ofPrincipalBackground 1 ell V)
              (bondToUnit B) (cbEquiv ell c)
          - unitToCoarseCov 1 ell (trivialU L) (bondToUnit B) (cbEquiv ell c)
        = (unitToCoarseCov 1 ell V (bondToUnit B) (cbEquiv ell c)
            - unitToCoarseCov 1 ell (trivialU L) (bondToUnit B) (cbEquiv ell c))
          + delta124 1 ell V (AdalyFormal.DeltaKR85.Coeff124.ofPrincipalBackground 1 ell V)
              (bondToUnit B) (cbEquiv ell c) := by abel
    rw [this]
    set a := ‖unitToCoarseCov 1 ell V (bondToUnit B) (cbEquiv ell c)
            - unitToCoarseCov 1 ell (trivialU L) (bondToUnit B) (cbEquiv ell c)‖
    set b := ‖delta124 1 ell V (AdalyFormal.DeltaKR85.Coeff124.ofPrincipalBackground 1 ell V)
              (bondToUnit B) (cbEquiv ell c)‖
    have h1 := norm_add_le (unitToCoarseCov 1 ell V (bondToUnit B) (cbEquiv ell c)
            - unitToCoarseCov 1 ell (trivialU L) (bondToUnit B) (cbEquiv ell c))
          (delta124 1 ell V (AdalyFormal.DeltaKR85.Coeff124.ofPrincipalBackground 1 ell V)
              (bondToUnit B) (cbEquiv ell c))
    have h2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
    nlinarith [sq_nonneg (a - b), norm_nonneg (unitToCoarseCov 1 ell V (bondToUnit B) (cbEquiv ell c)
            - unitToCoarseCov 1 ell (trivialU L) (bondToUnit B) (cbEquiv ell c))]
  refine le_trans (Finset.sum_le_sum (fun c _ => hrow c)) ?_
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  have e1 := Equiv.sum_comp (cbEquiv ell) (fun c' : CoarseBond L (1 * ell) =>
    ‖unitToCoarseCov 1 ell V (bondToUnit B) c' - unitToCoarseCov 1 ell (trivialU L) (bondToUnit B) c'‖ ^ 2)
  have e2 := Equiv.sum_comp (cbEquiv ell) (fun c' : CoarseBond L (1 * ell) =>
    ‖delta124 1 ell V (AdalyFormal.DeltaKR85.Coeff124.ofPrincipalBackground 1 ell V) (bondToUnit B) c'‖ ^ 2)
  rw [e1, e2]
  have hbe := bondEnergy_nonneg B
  nlinarith [hT, hL2]

#print axioms Q1jet_sub_flat_l2

end AdalyFormal.M0Finish.R7
