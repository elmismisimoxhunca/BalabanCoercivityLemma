import NJ7T1
import ProductAngle

/-!
# NJ8Eb -- from per-bond smallness `‖V e - 1‖_F ≤ ε₀` to the operator bounds `‖E_i‖ ≤ e2Majorant ρ`
(`ρ = n(ell) · (π/(2√2)) ε₀`, `n(ell) = 8 ell - 6`), by LoopHolonomySmall (`ν(log W_x) ≤ ρ`) and ESmall.
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
namespace AdalyFormal.NonflatJet

open Matrix
open AdalyFormal.Target.ClayStatement
  (PeriodicLatticeExtent PeriodicLatticeSite PeriodicLinkConfiguration)
open AdalyFormal.Balaban.CovariantOperators (SuTwo)
open AdalyFormal.Balaban.SuTwoInner
open AdalyFormal.Balaban.SuTwoLogExp (SU2 M2 su2Angle)
open AdalyFormal.Balaban.Bch2 (nu)
open AdalyFormal.Balaban.LatticeOperators (CoarseBond)
open AdalyFormal.Balaban.AdmissibleSubspace (CoarseLattice blockOf mem_blockOf)
open AdalyFormal.Balaban.ThirdLevelArrows (unitSitesOf)
open AdalyFormal.Balaban.QjComposite (stepBlockOf stepBlockOf_one)
open AdalyFormal.Balaban.RMapLipschitz (frobNorm)
open AdalyFormal.DeltaKR66 (principalSuTwoLog sourcePrincipalLogData)
open AdalyFormal.DeltaKR85 (Coeff124.ofPrincipalBackground)
open EstimatesLayer.E1E3
open OneStep124
local instance : NormedSpace ℝ SuTwo := instInnerProductSpaceSuTwo.toNormedSpace

variable {L : PeriodicLatticeExtent}

theorem mem_blockOf_of_mem_unitSites {ell : ℕ} (y : PeriodicLatticeSite L)
    (u : {z : PeriodicLatticeSite L // z ∈ CoarseLattice L 1})
    (hu : u ∈ unitSitesOf 1 (1 * ell) y) : u.1 ∈ blockOf y ell := by
  have hb : u.1 ∈ blockOf y (1 * ell) := by simpa [unitSitesOf] using hu
  rwa [one_mul] at hb

/-- the log radius `ρ(ell, ε₀)`. -/
def rhoOf (ell : ℕ) (ε0 : ℝ) : ℝ :=
  (SmallnessBridge.Assemble.loopFactorBound ell : ℝ) * ((Real.pi / (2 * Real.sqrt 2)) * ε0)

theorem e1Majorant_le_e2Majorant {ρ : ℝ} (hρ : 0 ≤ ρ) : e1Majorant ρ ≤ e2Majorant ρ := by
  unfold e2Majorant
  linarith [exp_two_rho_sub_one_nonneg hρ]

theorem E_bounds {ell : ℕ} (hell : 0 < ell) (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1))
    (V : PeriodicLinkConfiguration SU2 L) (ε0 : ℝ) (hε0 : 0 ≤ ε0)
    (hV : ∀ e, frobNorm ((V e : M2) - 1) ≤ ε0) (hsmall : rhoOf ell ε0 < Real.pi / 2)
    (c : CoarseBond L (1 * ell)) :
    (∀ u ∈ unitSitesOf 1 (1 * ell) c.1.1,
        ‖(Coeff124.ofPrincipalBackground 1 ell V).E1 c u.1‖ ≤ e2Majorant (rhoOf ell ε0)) ∧
    (∀ u ∈ unitSitesOf 1 (1 * ell) c.1.1,
        ‖(Coeff124.ofPrincipalBackground 1 ell V).E2 c u.1‖ ≤ e2Majorant (rhoOf ell ε0)) ∧
    ‖(Coeff124.ofPrincipalBackground 1 ell V).E3 c‖ ≤ e2Majorant (rhoOf ell ε0) := by
  set δ : ℝ := (Real.pi / (2 * Real.sqrt 2)) * ε0 with hδdef
  have hδ : 0 ≤ δ := by positivity
  have hang : ∀ e, su2Angle (V e) ≤ δ := fun e =>
    (SmallnessBridge.ProdBound.su2Angle_le_frobNorm (V e)).trans
      (mul_le_mul_of_nonneg_left (hV e) (by positivity))
  have hρ0 : 0 ≤ rhoOf ell ε0 := by unfold rhoOf; positivity
  have hρ : rhoOf ell ε0 ≤ Real.pi / 2 := hsmall.le
  set D := sourcePrincipalLogData 1 ell V with hD
  have hnu : ∀ u ∈ unitSitesOf 1 (1 * ell) c.1.1,
      nu ((D.Zx c u.1 : SuTwo) : M2) ≤ rhoOf ell ε0 := by
    intro u hu
    have hb : u.1 ∈ blockOf c.1.1 ell := mem_blockOf_of_mem_unitSites c.1.1 u hu
    have hx : u.1 ∈ stepBlockOf (c.1.1, c.2).1 1 ell := by
      show u.1 ∈ stepBlockOf c.1.1 1 ell
      rw [stepBlockOf_one]; exact hb
    exact (SmallnessBridge.Assemble.nu_loopVar_le_bound_mul V ell (c.1.1, c.2) u.1 δ hδ hang hx
      hsmall).1
  have hpos : 0 < (unitSitesOf 1 (1 * ell) c.1.1).card := by
    have hdvd1 : ∀ μ : Fin 3, (1 * ell) ∣ (L μ + 1) := by simpa using hdvd
    rw [OneStep124.unitSitesOf_card_eq (by norm_num : 0 < 1) c.1.2 hdvd1]
    positivity
  refine ⟨fun u hu => ?_, fun u hu => ?_, ?_⟩
  · exact (E1_norm_le_of_block V D c u.1 hρ0 hρ (hnu u hu) hnu).trans (e1Majorant_le_e2Majorant hρ0)
  · exact E2_norm_le_of_block V D c u.1 hρ0 hρ (hnu u hu) hnu
  · exact E3_norm_le V D c hρ0 hρ hnu hpos

#print axioms E_bounds

end AdalyFormal.NonflatJet
