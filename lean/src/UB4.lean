import UB3
import GCz1

/-!
# UB4 -- the chart bond defect `D_q` is controlled by the row drift of `q`'s four rows (lane m2_unit_20261014)

* `row_identity` : for a unit bond `b` whose embedding is a top row and any `V` with `Q_V y = τ* B`:
  `‖q₁ⁿ y(b) − B b‖ = ‖Q_V y(row b) − Q_1 y(row b)‖`  (MA6's per-row identity).
* `Qgauge` : `Q_U y = τ* B ⟹ Q_{U^γ}(Ad_γ y) = τ*(Ad_u B)`, `u = γ ∘ embY` (GCz1 `bondEqv_gauge`, GCg4 `tauExt_adjoint_gauge`).
* `Dq_le` : `n³ D_q ≤ δ² Σ_{b∈∂q} ‖y|Foot(row b)‖²` with `δ = delLoc` of the regional class of `U^γ` on the cones of the four rows.
-/
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 8000
noncomputable section
namespace AdalyFormal.M2Unit

open Finset
open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2 RMap)
open AdalyFormal.Balaban.SuTwoLogExp (SU2 M2)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond CoarseLattice)
open AdalyFormal.Balaban.RMapLipschitz (frobNorm)
open AdalyFormal.Balaban.CovariantHjMinimizer (trivialU)
open AdalyFormal.Balaban.LineIntegralCovariant (lineCoarseRestrictSuTwo)
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
open AdalyFormal.Balaban.AlphaAnalyticity (GaugeFn gaugeActA)
open AdalyFormal.NonflatJet
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.StatementLane (Tower Admissible scaleUp)
open AdalyFormal.StatementLaneG (gparams pe tauAdj_apply)
open AdalyFormal.StatementLaneR8
open AdalyFormal.SliceCoerc (GF)
open AdalyFormal.DLayer (Foot bondRestr)
open AdalyFormal.GenuineU1 (bondsE unitField)
open SmallnessBridge.Assemble (loopFactorBound)
open AdalyFormal.TowerLoc (delLoc)
open AdalyFormal.GaugeCov (adBL adFL uOf)

theorem row_identity {ell k : ℕ} {Lu : PeriodicLatticeExtent} (hell : 0 < ell) (S : Tower (scaleUp ell k Lu))
    (V : LinkCfg (scaleUp ell k Lu)) (a : ℝ) (Lam : Set (PeriodicLatticeSite Lu))
    (y : BondFnL2 (scaleUp ell k Lu)) (B : BondFnL2 Lu)
    (hQ : (bondSectorOf (geomOf ell k S) V).Qfull y = ContinuousLinearMap.adjoint (gparams ell k Lu hell S V a Lam).tau B)
    (b : Bond Lu) (hb : unitBondEmb ell k Lu hell b ∈ bondsLam (geomOf ell k S) k) :
    ‖lineCoarseRestrictSuTwo (ell ^ k) (WithLp.ofLp y) (bondsE ell k Lu hell b) - (WithLp.ofLp B) b‖
      = ‖(WithLp.ofLp ((bondSectorOf (geomOf ell k S) V).Qfull y)) (pe (gparams ell k Lu hell S V a Lam) b hb)
          - (WithLp.ofLp ((bondSectorOf (geomOf ell k S) (trivialU _)).Qfull y)) (pe (gparams ell k Lu hell S V a Lam) b hb)‖ := by
  set P := gparams ell k Lu hell S V a Lam with hP
  set Pf : IngrBParams := { P with U := flatCfg } with hPf
  have h1 := AdalyFormal.FlatEllGeneral.Qfull_top_gen Pf rfl y b hb
  have h2 := tauAdj_apply P B b hb
  have h3 : (WithLp.ofLp ((bondSectorOf (geomOf ell k S) V).Qfull y)) (pe P b hb) = (WithLp.ofLp B) b := by
    rw [hQ]; exact h2
  have h4 : (WithLp.ofLp ((bondSectorOf (geomOf ell k S) (trivialU _)).Qfull y)) (pe P b hb)
      = lineCoarseRestrictSuTwo (ell ^ k) (WithLp.ofLp y) (bondsE ell k Lu hell b) := h1
  rw [h3, h4, norm_sub_rev]

theorem Qgauge {ell k : ℕ} {Lu : PeriodicLatticeExtent} (hell : 0 < ell) (S : Tower (scaleUp ell k Lu))
    (U : LinkCfg (scaleUp ell k Lu)) (a : ℝ) (Lam : Set (PeriodicLatticeSite Lu))
    (y : BondFnL2 (scaleUp ell k Lu)) (B : BondFnL2 Lu)
    (hQ : (bondSectorOf (geomOf ell k S) U).Qfull y = ContinuousLinearMap.adjoint (gparams ell k Lu hell S U a Lam).tau B)
    (γ : GaugeFn (scaleUp ell k Lu)) :
    (bondSectorOf (geomOf ell k S) (periodicGaugeTransform γ U)).Qfull (adBL γ y)
      = ContinuousLinearMap.adjoint (gparams ell k Lu hell S (periodicGaugeTransform γ U) a Lam).tau
          (adBL (uOf ell k Lu hell γ) B) := by
  set P := gparams ell k Lu hell S U a Lam with hP
  have h1 := (AdalyFormal.GaugeCov.bondEqv_gauge P γ).Q y
  have h2 := AdalyFormal.GaugeCov.tauExt_adjoint_gauge ell k Lu hell S γ B
  have h3 : (AdalyFormal.GaugeCov.gaugeP P γ).sector.Qfull (adBL γ y) = adFL γ P.G (P.sector.Qfull y) := h1
  show (AdalyFormal.GaugeCov.gaugeP P γ).sector.Qfull (adBL γ y) = _
  rw [h3]
  show adFL γ P.G ((bondSectorOf (geomOf ell k S) U).Qfull y) = _
  rw [hQ]
  exact h2.symm

theorem norm_bondRestr_adBL {L : PeriodicLatticeExtent} (P : PeriodicLatticeEdge L → Prop) (γ : GaugeFn L)
    (y : BondFnL2 L) : ‖bondRestr P (adBL γ y)‖ = ‖bondRestr P y‖ := by
  classical
  have h : ‖bondRestr P (adBL γ y)‖ ^ 2 = ‖bondRestr P y‖ ^ 2 := by
    rw [PiLp.norm_sq_eq_of_L2, PiLp.norm_sq_eq_of_L2]
    refine Finset.sum_congr rfl (fun e _ => ?_)
    simp only [bondRestr, PiLp.toLp_apply]
    split_ifs
    · show ‖RMap (γ e.1) (y e)‖ ^ 2 = ‖y e‖ ^ 2
      rw [AdalyFormal.Balaban.AlphaAnalyticity.norm_RMap]
    · rfl
  exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp h

/-- one chart bond: `n³ ‖q₁ⁿ(γ·y)(b) − (u·B)(b)‖² ≤ δ² ‖y|Foot(row b)‖²`. -/
theorem chart_bond_le {ell k : ℕ} {Lu : PeriodicLatticeExtent} (hell : 0 < ell) (S : Tower (scaleUp ell k Lu))
    (U : LinkCfg (scaleUp ell k Lu)) (a : ℝ) (Lam : Set (PeriodicLatticeSite Lu))
    (y : BondFnL2 (scaleUp ell k Lu)) (B : BondFnL2 Lu)
    (hQ : (bondSectorOf (geomOf ell k S) U).Qfull y = ContinuousLinearMap.adjoint (gparams ell k Lu hell S U a Lam).tau B)
    (γ : GaugeFn (scaleUp ell k Lu)) (ε : ℕ → ℝ) (W : ℕ → Set (PeriodicLatticeSite (scaleUp ell k Lu)))
    (hcl : ∀ l, l < k → ∀ z ∈ W l, z ∈ CoarseLattice (scaleUp ell k Lu) (ell ^ l) → ∀ μ : Fin 3,
      frobNorm (((bgTower (GF ell k Lu) (periodicGaugeTransform γ U) l (z, μ) : SU2) : M2) - 1) ≤ ε l)
    (hε0 : ∀ j, j < k → 0 ≤ ε j) (hsm : ∀ j, j < k → rhoOf ell (ε j) < Real.pi / 2)
    (hr : ∀ j, j < k → Real.pi / 2 * ((loopFactorBound ell : ℝ) * ε j) < r0)
    (b : Bond Lu) (hb : unitBondEmb ell k Lu hell b ∈ bondsLam (geomOf ell k S) k)
    (hW : ∀ l, l < k → Ball (embY ell k Lu hell b.1) (rhoT ell k - rhoT ell l) ⊆ W l) :
    ((ell : ℝ) ^ k) ^ 3 * ‖lineCoarseRestrictSuTwo (ell ^ k) (gaugeActA γ (WithLp.ofLp y)) (bondsE ell k Lu hell b)
        - gaugeActA (uOf ell k Lu hell γ) (WithLp.ofLp B) b‖ ^ 2
      ≤ delLoc ell ε (Fin.last k) ^ 2 * ‖bondRestr (Foot ell k (unitBondEmb ell k Lu hell b)) y‖ ^ 2 := by
  classical
  set V := periodicGaugeTransform γ U with hV
  set P' := gparams ell k Lu hell S V a Lam with hP'
  have hQ' := Qgauge hell S U a Lam y B hQ γ
  have hid := row_identity hell S V a Lam (adBL γ y) (adBL (uOf ell k Lu hell γ) B) hQ' b hb
  have e1 : gaugeActA γ (WithLp.ofLp y) = WithLp.ofLp (adBL γ y) := rfl
  have e2 : gaugeActA (uOf ell k Lu hell γ) (WithLp.ofLp B) = WithLp.ofLp (adBL (uOf ell k Lu hell γ) B) := rfl
  rw [e1, e2, hid]
  set r : {e : Bond (scaleUp ell k Lu) // e ∈ bondsLam (geomOf ell k S) (Fin.last k)} := ⟨unitBondEmb ell k Lu hell b, hb⟩
    with hr_def
  have hsub := rows_drift_sub hell V ε W hcl hε0 hsm hr (Fin.last k) {r}
    (fun r' hr' l hl => by rw [Finset.mem_singleton] at hr'; rw [hr']; exact hW l hl) (adBL γ y)
  rw [Finset.sum_singleton] at hsub
  have hpe : pe P' b hb = ⟨Fin.last k, r⟩ := rfl
  have hfoot : (fun e => ∃ r' ∈ ({r} : Finset _), Foot ell ((Fin.last k : Fin (k + 1)) : ℕ) r'.1 e)
      = Foot ell k (unitBondEmb ell k Lu hell b) := by
    funext e
    apply propext
    constructor
    · rintro ⟨r', hr', hf⟩
      rw [Finset.mem_singleton] at hr'
      rw [hr', hr_def] at hf
      simpa [Fin.val_last] using hf
    · intro hf
      refine ⟨r, Finset.mem_singleton_self _, ?_⟩
      rw [hr_def]
      simpa [Fin.val_last] using hf
  rw [hfoot, norm_bondRestr_adBL] at hsub
  rw [hpe]
  have hk : ((Fin.last k : Fin (k + 1)) : ℕ) = k := Fin.val_last k
  rw [hk] at hsub
  exact hsub

end AdalyFormal.M2Unit

#print axioms AdalyFormal.M2Unit.row_identity
#print axioms AdalyFormal.M2Unit.Qgauge
#print axioms AdalyFormal.M2Unit.norm_bondRestr_adBL
#print axioms AdalyFormal.M2Unit.chart_bond_le
