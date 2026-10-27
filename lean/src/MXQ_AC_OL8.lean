import OL8
import MXQ_Base
import MXQ_AC_MZ3
import MXQ_AC_MZ4
import AC_OL8

/-! AC copy of OL8: affected declarations only (lane allc_20261016); 12 literal kept (control build). -/
set_option autoImplicit false
set_option maxHeartbeats 16000000
set_option maxRecDepth 8000

namespace MXQ.M2OpLayer
open MXQ.AllC (CF CubeFamOK)
open AdalyFormal.M2OpLayer

open AdalyFormal.AllC MXQ.AllC
variable {Fm : CF} [CubeFamOK Fm]

open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane AdalyFormal.StatementLane2 AdalyFormal.StatementLaneG AdalyFormal.IngredientFamilyR2
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.M1 (strat bstrat wnormSq)
open AdalyFormal.M1DStrat (omJ phiC wq delta2_conj eW)
open AdalyFormal.DLayer (psiD)
open AdalyFormal.M1IMS (sigG)
open AdalyFormal.M2DLayer (omS_nonneg omU Ageo su_le_sj)
open MXQ.M2DLayer (omSACΦ UncACΦ col_classACΦ Jf_splitACΦ)
open AdalyFormal.DLayer (bondWt)
open AdalyFormal.SiteCoercivity

section
variable {ell M R k : ℕ} {Lu : PeriodicLatticeExtent} {S : Tower (scaleUp ell k Lu)}

open Classical in
/-- the `ψ` bound at the printed class from the weighted columns -/
theorem psi_classACΦ (hell0 : 0 < ell) (hell2 : 2 ≤ ell) (hS : Admissible ell M R k S) (hR : 1 ≤ R) (hM : 1 ≤ M)
    (hRM : 4 ≤ R * M) {α₀ : ℝ} {U : LinkCfg (scaleUp ell k Lu)} (hU : ClassCoupledHQ ell M Fm 12 k S α₀ ((ell : ℝ) ^ k)⁻¹ U)
    (hα : 0 ≤ α₀) (hsm : 4 * ((12 : ℝ) * M * α₀) ≤ 1) {θ : ℝ} (hθ : 0 < θ)
    (hq : (ell : ℝ) ^ 3 * Real.exp (-(θ * (R * M))) ≤ 1 / 2) (a : ℝ) (Lam : Set (PeriodicLatticeSite Lu))
    (KH : ℝ) (hKH : 0 ≤ KH)
    (hHL2 : ∀ (p : BIdx (gparams ell k Lu hell0 S U a Lam).G) (v : SuTwo), ∃ c : PeriodicLatticeSite (scaleUp ell k Lu),
      ∑ b : Bond (scaleUp ell k Lu), ((((ell : ℝ) ^ strat S k b.1)⁻¹) * Real.exp (phiC S ell M R k θ c b.1)
        * ‖(iE (gparams ell k Lu hell0 S U a Lam).G ((gparams ell k Lu hell0 S U a Lam).data.H
            (WithLp.toLp 2 (Pi.single p v) : FSp (gparams ell k Lu hell0 S U a Lam).G))) b‖) ^ 2
        ≤ KH ^ 2 * (ell : ℝ) ^ strat S k c * ‖v‖ ^ 2)
    (p : BIdx (geomOf ell k S)) :
    ‖psiD (gparams ell k Lu hell0 S U a Lam) p‖
      ≤ (Real.sqrt (Ageo ell θ) * KH) * (400 * (ell : ℝ) ^ 3 * ((12 : ℝ) * M * α₀)) := by
  have hell1 : 1 ≤ ell := hell0
  have hβ0 : 0 ≤ (12 : ℝ) * M * α₀ := by positivity
  have hSJ0 : 0 ≤ 400 * (ell : ℝ) ^ 3 * ((12 : ℝ) * M * α₀) := by positivity
  have hcov : CoversOmQ ell M Fm k S := hU.1
  have hRM3 : 3 ≤ R * M := by omega
  have hJ : ∀ b, ‖(gparams ell k Lu hell0 S U a Lam).Jf b‖
      ≤ (400 * (ell : ℝ) ^ 3 * ((12 : ℝ) * M * α₀)) * omSACΦ Fm ell M k S b := by
    intro b
    have h := Jf_splitACΦ hell0 hS hRM hU hα hsm a Lam b
    have hsu := su_le_sj ell hell1 _ hβ0 hsm
    have hJ0 : 0 ≤ omJ S ell k b := by unfold omJ; positivity
    refine h.trans ?_
    unfold omSACΦ
    split_ifs with hu
    · have hU0 : 0 ≤ omU S ell k b := by unfold AdalyFormal.M2DLayer.omU; positivity
      have := mul_le_mul_of_nonneg_right hsu hU0
      nlinarith
    · linarith
  have hcol : ∀ (p : BIdx (gparams ell k Lu hell0 S U a Lam).G) (v : SuTwo),
      ∑ b, omSACΦ Fm ell M k S b * ‖(iE (gparams ell k Lu hell0 S U a Lam).G ((gparams ell k Lu hell0 S U a Lam).data.H
        (WithLp.toLp 2 (Pi.single p v) : FSp (gparams ell k Lu hell0 S U a Lam).G))) b‖
        ≤ (Real.sqrt (Ageo ell θ) * KH) * ‖v‖ := by
    intro p v
    obtain ⟨c, hc⟩ := hHL2 p v
    exact col_classACΦ hS hR hM hell2 hRM3 hcov hθ hq c _ (fun b => norm_nonneg _) KH ‖v‖ hKH (norm_nonneg _) hc
  exact AdalyFormal.M1DStrat.psi_le_of_wcol (gparams ell k Lu hell0 S U a Lam) (omSACΦ Fm ell M k S) _ _
    (mul_nonneg (Real.sqrt_nonneg _) hKH) hSJ0 hcol hJ p

/-- **the conjugated `Δ⁽²⁾` bound at the printed class** -/
theorem delta2_classACΦ (hell0 : 0 < ell) (hell2 : 2 ≤ ell) (hS : Admissible ell M R k S) (hR : 1 ≤ R) (hM : 1 ≤ M)
    (hroom : 18 * ell ≤ R * M) {α₀ : ℝ} {U : LinkCfg (scaleUp ell k Lu)}
    (hU : ClassCoupledHQ ell M Fm 12 k S α₀ ((ell : ℝ) ^ k)⁻¹ U)
    (hα : 0 ≤ α₀) (hsm : 4 * ((12 : ℝ) * M * α₀) ≤ 1) {θ : ℝ} (hθ : 0 < θ)
    (hq : (ell : ℝ) ^ 3 * Real.exp (-(θ * (R * M))) ≤ 1 / 2) (a : ℝ) (Lam : Set (PeriodicLatticeSite Lu))
    (KH : ℝ) (hKH : 0 ≤ KH)
    (hHL2 : ∀ (p : BIdx (gparams ell k Lu hell0 S U a Lam).G) (v : SuTwo), ∃ c : PeriodicLatticeSite (scaleUp ell k Lu),
      ∑ b : Bond (scaleUp ell k Lu), ((((ell : ℝ) ^ strat S k b.1)⁻¹) * Real.exp (phiC S ell M R k θ c b.1)
        * ‖(iE (gparams ell k Lu hell0 S U a Lam).G ((gparams ell k Lu hell0 S U a Lam).data.H
            (WithLp.toLp 2 (Pi.single p v) : FSp (gparams ell k Lu hell0 S U a Lam).G))) b‖) ^ 2
        ≤ KH ^ 2 * (ell : ℝ) ^ strat S k c * ‖v‖ ^ 2)
    (K2 : ℝ) (hK2 : 0 ≤ K2)
    (hC : ∀ z, ∑ q, ‖C2fullOf (geomOf ell k S) U z q‖ ≤ K2 * wnormSq S ell k z)
    (ξ : PeriodicLatticeSite (scaleUp ell k Lu) → ℝ) (kW : ℝ) (hkW : 0 ≤ kW)
    (hWp : ∀ z, ‖bondWt (-sigG (geomOf ell k S)) (bondWt (-ξ) (Wop (geomOf ell k S) U a (bondWt ξ z)))‖
      ≤ kW * ‖bondWt (-sigG (geomOf ell k S)) z‖)
    (hWm : ∀ z, ‖bondWt (-sigG (geomOf ell k S)) (bondWt ξ (Wop (geomOf ell k S) U a (bondWt (-ξ) z)))‖
      ≤ kW * ‖bondWt (-sigG (geomOf ell k S)) z‖)
    (Ω : ℝ) (hΩ : 0 ≤ Ω)
    (hosc : ∀ p : BIdx (geomOf ell k S), 1 ≤ (p.1 : ℕ) → ∀ e : Bond (scaleUp ell k Lu),
      e.1 ∈ AdalyFormal.StatementLaneR8.Ball p.2.1.1 (AdalyFormal.StatementLaneR8.rhoT ell p.1) → |ξ e.1 - ξ p.2.1.1| ≤ Ω)
    (A B : ↥(bondSupp (geomOf ell k S))) :
    |⟪eW (geomOf ell k S) ξ A, (gparams ell k Lu hell0 S U a Lam).data.Delta2 (gparams ell k Lu hell0 S U a Lam).data_laws
        (eW (geomOf ell k S) (-ξ) B)⟫|
      ≤ 2 * ((Real.sqrt (Ageo ell θ) * KH) * (400 * (ell : ℝ) ^ 3 * ((12 : ℝ) * M * α₀))) * K2 * Real.exp (2 * Ω)
          * 44217 * ((ell : ℝ) * kW) ^ 2
        * ‖wq S ell k (iE (geomOf ell k S) A)‖ * ‖wq S ell k (iE (geomOf ell k S) B)‖ := by
  have hRM : 4 ≤ R * M := by omega
  have hψ := psi_classACΦ hell0 hell2 hS hR hM hRM hU hα hsm hθ hq a Lam KH hKH hHL2
  have hSψ : 0 ≤ (Real.sqrt (Ageo ell θ) * KH) * (400 * (ell : ℝ) ^ 3 * ((12 : ℝ) * M * α₀)) := by positivity
  have hC' : ∀ z, ∑ q, ‖C2fullOf (geomOf ell k S) U z q‖ ≤ K2 * ‖wq S ell k z‖ ^ 2 := by
    intro z; rw [AdalyFormal.M1DStrat.wq_normSq]; exact hC z
  exact delta2_conj hS hell2 hroom hell0 U a Lam ξ kW hkW hWp hWm Ω hΩ hosc _ hSψ hψ K2 hK2 hC' hR hM A B

end

end MXQ.M2OpLayer

