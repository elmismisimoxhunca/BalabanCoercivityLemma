import MF6b
import ZXR2Wire4

/-!
# MF6c (TEXT COPY of nonflat_jet R5H0a, recompiled against the r7 fork) -- r5 carrier (`Dset` = coarse bonds TOUCHING `Λ'`): sup bound of `ι_D` and injectivity of `H₀ = ρ Q₁ ι_D`.
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
namespace AdalyFormal.M0Finish.R7

open Matrix
open AdalyFormal.Target.ClayStatement
  (PeriodicLatticeExtent PeriodicLatticeSite PeriodicLinkConfiguration)
open AdalyFormal.Balaban.CovariantOperators (SuTwo)
open AdalyFormal.Balaban.SuTwoInner
open AdalyFormal.Balaban.SuTwoLogExp (SU2 M2)
open AdalyFormal.Balaban.LatticeOperators (CoarseBond)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.RMapLipschitz (frobNorm)
open AdalyFormal.StatementLane (LamPrime IsDroppedIn)
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.NonflatJet (rhoOf)
open EstimatesLayer.E1E3
local instance : NormedSpace ℝ SuTwo := instInnerProductSpaceSuTwo.toNormedSpace

variable {L : PeriodicLatticeExtent}

theorem norm_iotaD_le {ell : ℕ} (hell : 0 < ell) (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1))
    (Lam : Set (PeriodicLatticeSite L)) (w : Dset L ell Lam → SuTwo) (M : ℝ) (hM : 0 ≤ M)
    (hw : ∀ c, ‖w c‖ ≤ M) (b : Bond L) : ‖iotaD ell Lam w b‖ ≤ M := by
  by_cases hb : IsDroppedIn Lam ell b
  · obtain ⟨c, hc, rfl⟩ := hb
    have hinj := AdalyFormal.Balaban.FullReparamC.droppedBondLast_injective (L := L) hell hdvd
    rw [iotaD_apply_dropped Lam hinj w ⟨c, hc⟩]
    exact hw _
  · rw [iotaD_apply_not_dropped Lam w b hb]
    simpa using hM

theorem H0_injective_of_small {ell : ℕ} (hell : 0 < ell) (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1))
    (Lam : Set (PeriodicLatticeSite L)) (V : PeriodicLinkConfiguration SU2 L) (ε0 : ℝ)
    (hε0 : 0 ≤ ε0) (hV : ∀ e, frobNorm ((V e : M2) - 1) ≤ ε0)
    (hsmall : rhoOf ell ε0 < Real.pi / 2) (hreg : RegBg 1 ell V)
    (hε : 8 * ell * ε0 + 8 * e2Majorant (rhoOf ell ε0) < 1 / (ell : ℝ) ^ 3) :
    Function.Injective (H0 Lam (Q1jet ell V)) := by
  have hellR : (0 : ℝ) < ell := by exact_mod_cast hell
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro w hw
  by_contra hne
  haveI : Nonempty (Dset L ell Lam) := by
    by_contra hE
    rw [not_nonempty_iff] at hE
    exact hne (funext fun c => (hE.false c).elim)
  obtain ⟨c0, hc0⟩ := Finite.exists_max (fun c : Dset L ell Lam => ‖w c‖)
  have hMpos : 0 < ‖w c0‖ := by
    by_contra h0
    push Not at h0
    apply hne
    funext c
    have := (hc0 c).trans h0
    exact norm_le_zero_iff.mp this
  set M := ‖w c0‖ with hM
  have hflat : H0 Lam (Q1jet ell (flatCfg : PeriodicLinkConfiguration SU2 L)) w c0
      = ((1 : ℝ) / (ell : ℝ) ^ 3) • w c0 := by
    rw [Q1_flat_eq ell hell hdvd]
    exact H0_q1SU2_apply hell hdvd Lam w c0
  have hdrift := Q1jet_sub_flat_le hell hdvd V ε0 hε0 hV hsmall hreg (iotaD ell Lam w) M
    hMpos.le (norm_iotaD_le hell hdvd Lam w M hMpos.le hc0) c0.1
  have hdiff : H0 Lam (Q1jet ell V) w c0 - H0 Lam (Q1jet ell flatCfg) w c0
      = Q1jet ell V (iotaD ell Lam w) c0.1 - Q1jet ell flatCfg (iotaD ell Lam w) c0.1 := rfl
  have hzero : H0 Lam (Q1jet ell V) w c0 = 0 := by rw [hw]; rfl
  rw [hzero, hflat] at hdiff
  have hn : ‖((1 : ℝ) / (ell : ℝ) ^ 3) • w c0‖ ≤ (8 * ell * ε0 + 8 * e2Majorant (rhoOf ell ε0)) * M := by
    have : ‖(0 : SuTwo) - ((1 : ℝ) / (ell : ℝ) ^ 3) • w c0‖ = ‖((1 : ℝ) / (ell : ℝ) ^ 3) • w c0‖ := by
      rw [zero_sub, norm_neg]
    rw [← this, hdiff]
    exact hdrift
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)] at hn
  nlinarith [hn, hε, hMpos]

#print axioms H0_injective_of_small

end AdalyFormal.M0Finish.R7
