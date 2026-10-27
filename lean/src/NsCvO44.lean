import NsCvO43

/-!
# CvO44 -- `Q*(zrow rho) = zfield (Wt rho)` (lane omega)
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace AdalyFormal.CoverOmega


set_option linter.unusedSectionVars false
variable [CfData]
open scoped Matrix RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.CoverJacobi
open AdalyFormal.CoverNested (cartan cartan_coe)
open AdalyFormal.Balaban.CovariantOperators
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.GaugeCov
open AdalyFormal.IngredientFamilyR2

variable {L : PeriodicLatticeExtent}

theorem Qfull_adBL (G : TowerGeom L) (c : ℕ) (t : ℝ) (w : BondFnL2 L) :
    QfullOf G (stagCfg c t) (adBL (hGauge L) w) = adFL (hGauge L) G (QfullOf G (stagCfg c t) w) := by
  have := QfullOf_gauge G (stagCfg c t : Cfg L) (hGauge L) w
  rwa [gaugeTransform_hGauge (stagCfg_cartan c t)] at this

/-- **`<Q w, zrow rho> = <w, zfield (Wt rho)>` for every `w`**. -/
theorem inner_Q_zrow {ell c : ℕ} {G : TowerGeom L} {isRow : ℕ → ℕ → Prop} (S : StagSetup L ell c G isRow) (t : ℝ) (htπ : |t| < tcap ell)
    (w : BondFnL2 L) (ρ : ℕ → ℕ → ℝ) :
    (inner ℝ (QfullOf G (stagCfg c t) w) (zrow G ρ) : ℝ) = inner ℝ w (zfield (Wt ell isRow ρ)) := by
  set A := adBL (hGauge L) with hA
  set AF := adFL (hGauge L) G with hAF
  set u := w + A w with hu
  have hAu : A u = u := by
    rw [hu, map_add, hA, adBL_hGauge_sq]; abel
  have hus : SigB (WithLp.ofLp u) := (adBL_hGauge_fixed_iff u).mp hAu
  -- left side
  have hl : (inner ℝ (QfullOf G (stagCfg c t) u) (zrow G ρ) : ℝ) = 2 * inner ℝ (QfullOf G (stagCfg c t) w) (zrow G ρ) := by
    rw [hu, map_add, Qfull_adBL, inner_add_left]
    have : (inner ℝ (AF (QfullOf G (stagCfg c t) w)) (zrow G ρ) : ℝ) = inner ℝ (QfullOf G (stagCfg c t) w) (zrow G ρ) := by
      conv_lhs => rw [← adFL_zrow G ρ]
      exact (adFL (hGauge L) G).inner_map_map _ _
    rw [this]; ring
  have hr : (inner ℝ u (zfield (Wt ell isRow ρ)) : ℝ) = 2 * inner ℝ w (zfield (Wt ell isRow ρ)) := by
    rw [hu, inner_add_left]
    have : (inner ℝ (A w) (zfield (Wt ell isRow ρ)) : ℝ) = inner ℝ w (zfield (Wt ell isRow ρ)) := by
      conv_lhs => rw [← adBL_zfield (L := L) (Wt ell isRow ρ)]
      exact (adBL (hGauge L)).inner_map_map _ _
    rw [this]; ring
  have key := pair_Q_zrow S t htπ u hus ρ
  rw [inner_sig_zfield u hus] at hr
  linarith

#print axioms inner_Q_zrow

end AdalyFormal.CoverOmega
