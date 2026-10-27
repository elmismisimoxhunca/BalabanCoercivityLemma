import UB4

/-!
# UB5 -- U1 at one unit plaquette, chart data bundled (lane m2_unit_20261014)

`ChartOK` : the per-plaquette chart conditions (ONE fine gauge `γ` per unit plaquette `q`):
 * window base links of `U^γ` `≤ s/n`;
 * the two base links of `W^u` (`u = γ ∘ embY`) `≤ κ`;
 * the four bonds of `q` embed into top rows, and the regional class of `U^γ` holds (constants `ε l`, sets `Wr l`) on the cones
   of those four rows.
`stokes_q` : under `ChartOK`,
  `n‖curl_W B q‖² ≤ (1+ε') n⁻² winSum G(q) + (1+1/ε')(16κ² n(‖B b₂‖² + ‖B b₃‖²) + 8 n⁻² δ² Σ_{b∈∂q} ‖y|Foot(row b)‖²)`,
  `δ = delLoc ℓ ε k`.  Every term but the chart conditions is gauge invariant.
-/
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 8000
noncomputable section
namespace AdalyFormal.M2Unit

open Finset
open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2 RMap curlValueCovariant)
open AdalyFormal.Balaban.SuTwoLogExp (SU2 M2)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond CoarseLattice blockOf)
open AdalyFormal.Balaban.RMapLipschitz (frobNorm)
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
open AdalyFormal.GenuineU1 (bondsE unitField plaqE)
open SmallnessBridge.Assemble (loopFactorBound)
open AdalyFormal.TowerLoc (delLoc)
open AdalyFormal.GaugeCov (adBL adFL uOf)

/-- the four bonds of a plaquette, as a list of positions. -/
def qb1 {L : PeriodicLatticeExtent} (q : PeriodicLatticePlaquette L) : Bond L := (q.1, q.2.1.1)
def qb2 {L : PeriodicLatticeExtent} (q : PeriodicLatticePlaquette L) : Bond L := (periodicLatticeShift q.1 q.2.1.1, q.2.1.2)
def qb3 {L : PeriodicLatticeExtent} (q : PeriodicLatticePlaquette L) : Bond L := (periodicLatticeShift q.1 q.2.1.2, q.2.1.1)
def qb4 {L : PeriodicLatticeExtent} (q : PeriodicLatticePlaquette L) : Bond L := (q.1, q.2.1.2)

/-- the per-plaquette chart conditions. -/
structure ChartOK {ell k : ℕ} {Lu : PeriodicLatticeExtent} (hell : 0 < ell) (S : Tower (scaleUp ell k Lu))
    (U : LinkCfg (scaleUp ell k Lu)) (W : PeriodicLinkConfiguration SU2 Lu) (q : PeriodicLatticePlaquette Lu)
    (γ : GaugeFn (scaleUp ell k Lu)) (s κ : ℝ) (ε : ℕ → ℝ) (Wr : ℕ → Set (PeriodicLatticeSite (scaleUp ell k Lu))) :
    Prop where
  win : ∀ x ∈ blockOf (embY ell k Lu hell q.1) (ell ^ k), ∀ i ∈ Finset.range (ell ^ k), ∀ j ∈ Finset.range (ell ^ k),
      frobNorm (((periodicGaugeTransform γ U ((winPl q.2 x i j).1, q.2.1.1) : SU2) : M2) - 1) ≤ s / (ell : ℝ) ^ k ∧
      frobNorm (((periodicGaugeTransform γ U ((winPl q.2 x i j).1, q.2.1.2) : SU2) : M2) - 1) ≤ s / (ell : ℝ) ^ k
  W1 : frobNorm (((periodicGaugeTransform (fun w => γ (embY ell k Lu hell w)) W (q.1, q.2.1.1) : SU2) : M2) - 1) ≤ κ
  W2 : frobNorm (((periodicGaugeTransform (fun w => γ (embY ell k Lu hell w)) W (q.1, q.2.1.2) : SU2) : M2) - 1) ≤ κ
  rows : ∀ b ∈ ({qb1 q, qb2 q, qb3 q, qb4 q} : Finset (Bond Lu)), unitBondEmb ell k Lu hell b ∈ bondsLam (geomOf ell k S) k
  hcl : ∀ l, l < k → ∀ z ∈ Wr l, z ∈ CoarseLattice (scaleUp ell k Lu) (ell ^ l) → ∀ μ : Fin 3,
      frobNorm (((bgTower (GF ell k Lu) (periodicGaugeTransform γ U) l (z, μ) : SU2) : M2) - 1) ≤ ε l
  hW : ∀ b ∈ ({qb1 q, qb2 q, qb3 q, qb4 q} : Finset (Bond Lu)), ∀ l, l < k →
      Ball (embY ell k Lu hell b.1) (rhoT ell k - rhoT ell l) ⊆ Wr l

/-- the foot term of a unit bond. -/
noncomputable def footT {ell k : ℕ} {Lu : PeriodicLatticeExtent} (hell : 0 < ell) (y : BondFnL2 (scaleUp ell k Lu))
    (b : Bond Lu) : ℝ :=
  ‖bondRestr (Foot ell k (unitBondEmb ell k Lu hell b)) y‖ ^ 2

theorem stokes_q {ell k : ℕ} {Lu : PeriodicLatticeExtent} (hell : 0 < ell) (hu : ∀ μ, 1 ≤ Lu μ)
    (S : Tower (scaleUp ell k Lu)) (U : LinkCfg (scaleUp ell k Lu)) (a : ℝ) (Lam : Set (PeriodicLatticeSite Lu))
    (W : PeriodicLinkConfiguration SU2 Lu)
    (y : BondFnL2 (scaleUp ell k Lu)) (B : BondFnL2 Lu)
    (hQ : (bondSectorOf (geomOf ell k S) U).Qfull y = ContinuousLinearMap.adjoint (gparams ell k Lu hell S U a Lam).tau B)
    (q : PeriodicLatticePlaquette Lu) (γ : GaugeFn (scaleUp ell k Lu)) (s κ ε' : ℝ) (ε : ℕ → ℝ)
    (Wr : ℕ → Set (PeriodicLatticeSite (scaleUp ell k Lu)))
    (hs : 0 ≤ s) (hκ : 0 ≤ κ) (hε' : 0 < ε')
    (hε0 : ∀ j, j < k → 0 ≤ ε j) (hsm : ∀ j, j < k → rhoOf ell (ε j) < Real.pi / 2)
    (hr : ∀ j, j < k → Real.pi / 2 * ((loopFactorBound ell : ℝ) * ε j) < r0)
    (hC : ChartOK hell S U W q γ s κ ε Wr) :
    (ell : ℝ) ^ k * ‖curlValueCovariant W (WithLp.ofLp B) q‖ ^ 2
      ≤ (1 + ε') * ((1 / ((ell : ℝ) ^ k) ^ 2) *
            winSum (ell ^ k) (Gwin U (WithLp.ofLp y) (s / (ell : ℝ) ^ k)) (plaqE ell k Lu hell q))
        + (1 + 1 / ε') * (16 * κ ^ 2 * (ell : ℝ) ^ k * (‖(WithLp.ofLp B) (qb2 q)‖ ^ 2 + ‖(WithLp.ofLp B) (qb3 q)‖ ^ 2)
          + 8 * (1 / ((ell : ℝ) ^ k) ^ 2) * delLoc ell ε (Fin.last k) ^ 2 *
            (footT hell y (qb1 q) + footT hell y (qb2 q) + footT hell y (qb3 q) + footT hell y (qb4 q))) := by
  have hnR0 : (0 : ℝ) < (ell : ℝ) ^ k := pow_pos (by exact_mod_cast hell) k
  have hcore := stokes_chart hell hu U W (WithLp.ofLp y) (WithLp.ofLp B) q γ s κ ε' hs hκ hε' hC.win hC.W1 hC.W2
  have hbond : ∀ b ∈ ({qb1 q, qb2 q, qb3 q, qb4 q} : Finset (Bond Lu)),
      ((ell : ℝ) ^ k) ^ 3 * ‖lineCoarseRestrictSuTwo (ell ^ k) (gaugeActA γ (WithLp.ofLp y)) (bondsE ell k Lu hell b)
        - gaugeActA (uOf ell k Lu hell γ) (WithLp.ofLp B) b‖ ^ 2 ≤ delLoc ell ε (Fin.last k) ^ 2 * footT hell y b :=
    fun b hb => chart_bond_le hell S U a Lam y B hQ γ ε Wr hC.hcl hε0 hsm hr b (hC.rows b hb) (hC.hW b hb)
  have m1 : qb1 q ∈ ({qb1 q, qb2 q, qb3 q, qb4 q} : Finset (Bond Lu)) := by simp
  have m2 : qb2 q ∈ ({qb1 q, qb2 q, qb3 q, qb4 q} : Finset (Bond Lu)) := by simp
  have m3 : qb3 q ∈ ({qb1 q, qb2 q, qb3 q, qb4 q} : Finset (Bond Lu)) := by simp
  have m4 : qb4 q ∈ ({qb1 q, qb2 q, qb3 q, qb4 q} : Finset (Bond Lu)) := by simp
  have hD : ((ell : ℝ) ^ k) ^ 3 * Dq hell γ (WithLp.ofLp y) (WithLp.ofLp B) q
      ≤ delLoc ell ε (Fin.last k) ^ 2 *
        (footT hell y (qb1 q) + footT hell y (qb2 q) + footT hell y (qb3 q) + footT hell y (qb4 q)) := by
    have h1 := hbond _ m1
    have h2 := hbond _ m2
    have h3 := hbond _ m3
    have h4 := hbond _ m4
    have hDq : Dq hell γ (WithLp.ofLp y) (WithLp.ofLp B) q
        = ‖lineCoarseRestrictSuTwo (ell ^ k) (gaugeActA γ (WithLp.ofLp y)) (bondsE ell k Lu hell (qb1 q))
            - gaugeActA (uOf ell k Lu hell γ) (WithLp.ofLp B) (qb1 q)‖ ^ 2
          + ‖lineCoarseRestrictSuTwo (ell ^ k) (gaugeActA γ (WithLp.ofLp y)) (bondsE ell k Lu hell (qb2 q))
            - gaugeActA (uOf ell k Lu hell γ) (WithLp.ofLp B) (qb2 q)‖ ^ 2
          + ‖lineCoarseRestrictSuTwo (ell ^ k) (gaugeActA γ (WithLp.ofLp y)) (bondsE ell k Lu hell (qb3 q))
            - gaugeActA (uOf ell k Lu hell γ) (WithLp.ofLp B) (qb3 q)‖ ^ 2
          + ‖lineCoarseRestrictSuTwo (ell ^ k) (gaugeActA γ (WithLp.ofLp y)) (bondsE ell k Lu hell (qb4 q))
            - gaugeActA (uOf ell k Lu hell γ) (WithLp.ofLp B) (qb4 q)‖ ^ 2 := rfl
    rw [hDq]
    linarith
  have hD' : (ell : ℝ) ^ k * (8 * Dq hell γ (WithLp.ofLp y) (WithLp.ofLp B) q)
      ≤ 8 * (1 / ((ell : ℝ) ^ k) ^ 2) * delLoc ell ε (Fin.last k) ^ 2 *
        (footT hell y (qb1 q) + footT hell y (qb2 q) + footT hell y (qb3 q) + footT hell y (qb4 q)) := by
    have e : (ell : ℝ) ^ k * (8 * Dq hell γ (WithLp.ofLp y) (WithLp.ofLp B) q)
        = 8 * (1 / ((ell : ℝ) ^ k) ^ 2) * (((ell : ℝ) ^ k) ^ 3 * Dq hell γ (WithLp.ofLp y) (WithLp.ofLp B) q) := by
      field_simp
    rw [e]
    have : 0 ≤ 8 * (1 / ((ell : ℝ) ^ k) ^ 2) := by positivity
    have := mul_le_mul_of_nonneg_left hD this
    linarith
  have hε1 : 0 ≤ 1 + 1 / ε' := by positivity
  have e2 : (ell : ℝ) ^ k * (16 * κ ^ 2 * (‖(WithLp.ofLp B) (periodicLatticeShift q.1 q.2.1.1, q.2.1.2)‖ ^ 2
        + ‖(WithLp.ofLp B) (periodicLatticeShift q.1 q.2.1.2, q.2.1.1)‖ ^ 2) + 8 * Dq hell γ (WithLp.ofLp y) (WithLp.ofLp B) q)
      = 16 * κ ^ 2 * (ell : ℝ) ^ k * (‖(WithLp.ofLp B) (qb2 q)‖ ^ 2 + ‖(WithLp.ofLp B) (qb3 q)‖ ^ 2)
        + (ell : ℝ) ^ k * (8 * Dq hell γ (WithLp.ofLp y) (WithLp.ofLp B) q) := by
    simp only [qb2, qb3]; ring
  rw [e2] at hcore
  have := mul_le_mul_of_nonneg_left hD' hε1
  nlinarith

end AdalyFormal.M2Unit

#print axioms AdalyFormal.M2Unit.stokes_q
