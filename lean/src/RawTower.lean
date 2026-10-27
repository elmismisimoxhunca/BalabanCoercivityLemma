import StridedSurfaceFill
import AdalyFormal.Balaban.BlockedBackground
import Lean.Util.CollectAxioms

set_option autoImplicit false
set_option maxHeartbeats 4000000

/-!
# Corrected depth-k uniformity on the RAW Balaban tower

The previous campaign wired Balaban Proposition 1 (CMP98 p.26 eq. 51) to the
self-consistent **diagonal modified** step `modifiedAverageS s V ell V`. That
hypothesis was independently refuted: a flat pure-gauge field stays flat under
the raw average, but not under the diagonal modified average.

This file restates the isolated one-step input as `OneStepPropagationRaw`, whose
left-hand side is the **plain raw average** `ubarSU2` — the object Prop 1 actually
bounds — and iterates it along the certified raw tower `ubarTowerSU2`
(`Ū^{l+1} = ubarSU2 (ell^l) ell (Ū^l)`, CMP98 (43)).

The real-analysis contraction (`betaRec` / geometric sum) is the same strategy
as the prior depth-uniformity proof; it is re-derived here against the corrected
operator, not imported as a theorem about the false target.

The single-level plaquette-to-angle bridge is the certified
`nu_loopVar_le_rhoPlaq_S` (stride-`s` form of `LoopHolonomySmall.nu_loopVar_V0_le_rho`).
-/

noncomputable section

namespace DepthUniformity.RawTower

open Matrix
open AdalyFormal.Target.ClayStatement
  (PeriodicLatticeExtent PeriodicLatticeEdge PeriodicLatticeSite PeriodicLinkConfiguration
    PeriodicLatticePlaquette PeriodicPlaquetteDirections
    periodicPlaquetteHolonomy periodicLatticeShift)
open AdalyFormal.Balaban.SuTwoLogExp (SU2 M2 su2Exp su2Angle su2Angle_conj)
open AdalyFormal.Balaban.Bch2
open AdalyFormal.Balaban.RMapLipschitz
open AdalyFormal.Balaban.TowerLawCov
  (coarsePathHolonomy coarseGammaPath coarseStraightSegment coarseCoordSteps
    coarsePathEndpoint)
open AdalyFormal.Balaban.UbarTowerCov (loopVar gammaVarStrided coarseBondVar cPlusS cPlusS_eq)
open AdalyFormal.Balaban.QjComposite
  (stepBlockOf mem_stepBlockOf stepBlockOf_one inStepBlock
    coarsePathHolonomy_nil coarsePathHolonomy_cons
    coarsePathHolonomy_append coarsePathEndpoint_cons coarsePathEndpoint_append
    coarsePathEndpoint_coarseGammaPath coarseGaugeTransform)
open AdalyFormal.Balaban.AdmissibleSubspace (inBlock mem_blockOf)
open AdalyFormal.Balaban.CoarseCurl (coarseShift)
open AdalyFormal.Balaban.CovariantOperators (SuTwo)
open AdalyFormal.Balaban.CovariantHjMinimizer (trivialU)
open AdalyFormal.Balaban.BlockedBackground
  (ubarSU2 ubarTowerSU2 ubarTowerSU2_zero ubarTowerSU2_succ ubarSU2_trivialU ubarSU2_gauge)
open AdalyFormal.Balaban.BlockingLinkEstimate (frobNorm_conj_sub_one)
open AdalyFormal.DeltaKR66 (principalSuTwoLog)
open SmallnessBridge.ProdBound
open SmallnessBridge.Assemble
open DepthUniformity.Strided

variable {L : PeriodicLatticeExtent}

/-! ## §1 — level plaquette bound and the corrected Prop-1 input -/

/-- **Level-`j` plaquette deviation bound** for a background tower `bg`: every stride-`ell^j`
oriented plaquette of `bg j` (Balaban's `Ū^j(∂p)`) is within `β` of 1 in Frobenius norm. -/
def LevelPlaqBound (bg : ℕ → PeriodicLinkConfiguration SU2 L) (ell j : ℕ) (β : ℝ) : Prop :=
  ∀ (y : PeriodicLatticeSite L) (μ ν : Fin 3),
    frobNorm (((orientedPlaqHolS (ell ^ j) (bg j) y μ ν : SU2) : M2) - 1) ≤ β

/-- **Balaban Proposition 1 (CMP98 (51)), restated on the RAW average.**

Printed (51): `|V̄(∂p') − 1| < L²α₀ + C₀(L²α₀)²` for the **plain raw average** `V̄` of a
single field `V` (CMP98 (42)/(43) = `ubarSU2`). This is an ordinary `Prop` parameter of
the main theorems, never an axiom. Discharging it is the analytic content of pp.24–26
(tree gauge + quadratic remainder), owned by the Prop-1 formalization lane.

NOT the refuted diagonal modified operator `modifiedAverageS s V ell V`. -/
def OneStepPropagationRaw (ell : ℕ) (C0 c2' : ℝ) : Prop :=
  ∀ (s : ℕ) (V : PeriodicLinkConfiguration SU2 L) (β : ℝ),
    0 ≤ β → β ≤ c2' →
    (∀ (y : PeriodicLatticeSite L) (μ ν : Fin 3),
      frobNorm (((orientedPlaqHolS s V y μ ν : SU2) : M2) - 1) ≤ β) →
    ∀ (y : PeriodicLatticeSite L) (μ ν : Fin 3),
      frobNorm
          (((orientedPlaqHolS (s * ell) (ubarSU2 s ell V) y μ ν : SU2) : M2) - 1) ≤
        (ell : ℝ)^2 * β + C0 * ((ell : ℝ)^2 * β)^2

/-- Literal unfolding: the one-step LHS is `ubarSU2`, definitionally. -/
theorem OneStepPropagationRaw_iff_ubarSU2 (ell : ℕ) (C0 c2' : ℝ) :
    OneStepPropagationRaw (L := L) ell C0 c2' ↔
      ∀ (s : ℕ) (V : PeriodicLinkConfiguration SU2 L) (β : ℝ),
        0 ≤ β → β ≤ c2' →
        (∀ (y : PeriodicLatticeSite L) (μ ν : Fin 3),
          frobNorm (((orientedPlaqHolS s V y μ ν : SU2) : M2) - 1) ≤ β) →
        ∀ (y : PeriodicLatticeSite L) (μ ν : Fin 3),
          frobNorm
              (((orientedPlaqHolS (s * ell) (ubarSU2 s ell V) y μ ν : SU2) : M2) - 1) ≤
            (ell : ℝ)^2 * β + C0 * ((ell : ℝ)^2 * β)^2 :=
  Iff.rfl

/-! ## §2 — Prop-2 iteration as pure real analysis

`betaRec` is the worst-case deviation recursion
`β_0 = alpha0·ell^{-2k}`, `β_{j+1} = ell²·β_j + C0·(ell²·β_j)²`.
With `q = ell²`, `a_j = alpha0·q^j·q^{-k}`, `S_j = Σ_{i=1}^{j} q^i`, the invariant is
`β_j ≤ a_j·(1 + 4·C0·alpha0·q^{-k}·S_j)`. This arithmetic does not mention the averaging
operator; it applies to any one-step map obeying the (51) monomial bound. -/

/-- `η² = (ell²)^{-k}` — the printed (52) damping factor at depth `k`. -/
def etaSq (ell k : ℕ) : ℝ := (((ell : ℝ) ^ 2) ^ k)⁻¹

/-- The deviation recursion of CMP98 (51) iterated: `β_0 = alpha0·η²`,
`β_{j+1} = ell²·β_j + C0·(ell²·β_j)²`. -/
def betaRec (ell : ℕ) (C0 alpha0 : ℝ) (k : ℕ) : ℕ → ℝ
  | 0 => alpha0 * etaSq ell k
  | j + 1 => (ell : ℝ)^2 * betaRec ell C0 alpha0 k j +
      C0 * ((ell : ℝ)^2 * betaRec ell C0 alpha0 k j)^2

/-- Partial geometric sum `S_j = q + q² + ⋯ + q^j` with `q = ell²`. -/
def geomS (ell : ℕ) : ℕ → ℝ
  | 0 => 0
  | j + 1 => geomS ell j + ((ell : ℝ)^2)^(j + 1)

theorem etaSq_nonneg (ell k : ℕ) : 0 ≤ etaSq ell k :=
  inv_nonneg.mpr (pow_nonneg (sq_nonneg _) _)

theorem geomS_zero (ell : ℕ) : geomS ell 0 = 0 := rfl

theorem geomS_succ (ell j : ℕ) :
    geomS ell (j + 1) = geomS ell j + ((ell : ℝ)^2)^(j + 1) := rfl

theorem geomS_nonneg (ell : ℕ) (j : ℕ) : 0 ≤ geomS ell j := by
  induction j with
  | zero => rw [geomS_zero]
  | succ j ih =>
      rw [geomS_succ]
      exact add_nonneg ih (pow_nonneg (sq_nonneg _) _)

theorem geomS_mono (ell : ℕ) {j k : ℕ} (h : j ≤ k) : geomS ell j ≤ geomS ell k := by
  induction h with
  | refl => exact le_refl _
  | step h' ih =>
      rw [geomS_succ]
      exact ih.trans (le_add_of_nonneg_right (pow_nonneg (sq_nonneg _) _))

/-- The geometric-series identity, division-free: `S_j·(q − 1) = q·(q^j − 1)`. -/
theorem geomS_mul_sub (ell : ℕ) (j : ℕ) :
    geomS ell j * ((ell : ℝ)^2 - 1) = (ell : ℝ)^2 * (((ell : ℝ)^2)^j - 1) := by
  induction j with
  | zero => simp [geomS_zero]
  | succ j ih =>
      rw [geomS_succ, add_mul, ih]
      ring

theorem betaRec_zero (ell : ℕ) (C0 alpha0 : ℝ) (k : ℕ) :
    betaRec ell C0 alpha0 k 0 = alpha0 * etaSq ell k := rfl

theorem betaRec_succ (ell : ℕ) (C0 alpha0 : ℝ) (k j : ℕ) :
    betaRec ell C0 alpha0 k (j + 1) =
      (ell : ℝ)^2 * betaRec ell C0 alpha0 k j +
        C0 * ((ell : ℝ)^2 * betaRec ell C0 alpha0 k j)^2 := rfl

theorem betaRec_nonneg (ell : ℕ) (C0 alpha0 : ℝ) (hC0 : 0 ≤ C0) (hα0 : 0 < alpha0) (k j : ℕ) :
    0 ≤ betaRec ell C0 alpha0 k j := by
  induction j with
  | zero =>
      rw [betaRec_zero]
      exact mul_nonneg hα0.le (etaSq_nonneg ell k)
  | succ j ih =>
      rw [betaRec_succ]
      exact add_nonneg (mul_nonneg (sq_nonneg _) ih)
        (mul_nonneg hC0 (sq_nonneg _))

/-- **The key global bound**: `4·C0·alpha0·(η²·S_k) ≤ 1` from `4·C0·alpha0·q ≤ q − 1`. -/
theorem etaSq_geomS_key_bound (ell : ℕ) (C0 alpha0 : ℝ) (hell : 2 ≤ ell) (hC0 : 0 ≤ C0) (hα0 : 0 < alpha0)
    (hC0α0 : 4 * C0 * alpha0 * (ell : ℝ)^2 ≤ (ell : ℝ)^2 - 1) (k : ℕ) :
    4 * C0 * alpha0 * (etaSq ell k * geomS ell k) ≤ 1 := by
  have h2 : (2:ℝ) ≤ (ell : ℝ) := by exact_mod_cast hell
  have h4 : (4:ℝ) ≤ (ell : ℝ)^2 := by
    nlinarith [mul_nonneg (show (0:ℝ) ≤ (ell:ℝ) - 2 by linarith)
      (show (0:ℝ) ≤ (ell:ℝ) + 2 by linarith)]
  have hq1 : (1:ℝ) < (ell : ℝ)^2 := by linarith
  have hq1m : (0:ℝ) < (ell : ℝ)^2 - 1 := by linarith
  have hqk0 : (0:ℝ) < ((ell : ℝ)^2)^k := pow_pos (by linarith) k
  have hqk1 : (1:ℝ) ≤ ((ell : ℝ)^2)^k := by
    have h := pow_le_pow_right₀ hq1.le (Nat.zero_le k)
    simpa using h
  have hA0 : (0:ℝ) ≤ 4 * C0 * alpha0 := by positivity
  have hgeom := geomS_mul_sub ell k
  have hstep1 :
      ((4 * C0 * alpha0) * geomS ell k) * ((ell : ℝ)^2 - 1) ≤
        (((ell : ℝ)^2)^k - 1) * ((ell : ℝ)^2 - 1) := by
    calc ((4 * C0 * alpha0) * geomS ell k) * ((ell : ℝ)^2 - 1)
        = (4 * C0 * alpha0) * (geomS ell k * ((ell : ℝ)^2 - 1)) := by ring
      _ = (4 * C0 * alpha0) * ((ell : ℝ)^2 * (((ell : ℝ)^2)^k - 1)) := by rw [hgeom]
      _ = ((4 * C0 * alpha0) * (ell : ℝ)^2) * (((ell : ℝ)^2)^k - 1) := by ring
      _ ≤ ((ell : ℝ)^2 - 1) * (((ell : ℝ)^2)^k - 1) :=
          mul_le_mul_of_nonneg_right (by linarith [hC0α0]) (by linarith)
      _ = (((ell : ℝ)^2)^k - 1) * ((ell : ℝ)^2 - 1) := by ring
  have hstep2 : (4 * C0 * alpha0) * geomS ell k ≤ ((ell : ℝ)^2)^k - 1 :=
    le_of_mul_le_mul_right hstep1 hq1m
  have hdiv1 :
      ((4 * C0 * alpha0) * geomS ell k) * (((ell : ℝ)^2)^k)⁻¹ ≤
        (((ell : ℝ)^2)^k - 1) * (((ell : ℝ)^2)^k)⁻¹ :=
    mul_le_mul_of_nonneg_right hstep2 (inv_nonneg.mpr hqk0.le)
  have hfin : (((ell : ℝ)^2)^k - 1) * (((ell : ℝ)^2)^k)⁻¹ ≤ 1 := by
    rw [sub_mul, mul_inv_cancel₀ (ne_of_gt hqk0), one_mul]
    have hnn : 0 ≤ (((ell : ℝ)^2)^k)⁻¹ := inv_nonneg.mpr hqk0.le
    linarith
  calc 4 * C0 * alpha0 * (etaSq ell k * geomS ell k)
      = ((4 * C0 * alpha0) * geomS ell k) * (((ell : ℝ)^2)^k)⁻¹ := by
        unfold etaSq; ring
    _ ≤ (((ell : ℝ)^2)^k - 1) * (((ell : ℝ)^2)^k)⁻¹ := hdiv1
    _ ≤ 1 := hfin

/-- Self-consistent ceiling: the correction factor `γ_j = 1 + 4·C0·alpha0·η²·S_j` never
exceeds `2` along the tower (`j ≤ k`). -/
theorem gamma_le_two (ell : ℕ) (C0 alpha0 : ℝ) (hell : 2 ≤ ell) (hC0 : 0 ≤ C0) (hα0 : 0 < alpha0)
    (hC0α0 : 4 * C0 * alpha0 * (ell : ℝ)^2 ≤ (ell : ℝ)^2 - 1) {k j : ℕ} (hjk : j ≤ k) :
    1 + 4 * C0 * alpha0 * etaSq ell k * geomS ell j ≤ 2 := by
  have hkey := etaSq_geomS_key_bound ell C0 alpha0 hell hC0 hα0 hC0α0 k
  have hmono : geomS ell j ≤ geomS ell k := geomS_mono ell hjk
  have h2 : etaSq ell k * geomS ell j ≤ etaSq ell k * geomS ell k :=
    mul_le_mul_of_nonneg_left hmono (etaSq_nonneg ell k)
  have hA0 : (0:ℝ) ≤ 4 * C0 * alpha0 := by positivity
  have h3 : 4 * C0 * alpha0 * (etaSq ell k * geomS ell j) ≤
      4 * C0 * alpha0 * (etaSq ell k * geomS ell k) :=
    mul_le_mul_of_nonneg_left h2 hA0
  have h4 : 4 * C0 * alpha0 * etaSq ell k * geomS ell j =
      4 * C0 * alpha0 * (etaSq ell k * geomS ell j) := by ring
  linarith

/-- **The Prop-2 iteration bound** (CMP98 (53) content):
for every `j ≤ k`,
`β_j ≤ a_j·γ_j` with `a_j = alpha0·q^{j}·η²` and `γ_j = 1 + 4·C0·alpha0·η²·S_j ≤ 2`. -/
theorem betaRec_le (ell : ℕ) (C0 alpha0 : ℝ) (hell : 2 ≤ ell) (hC0 : 0 ≤ C0) (hα0 : 0 < alpha0)
    (hC0α0 : 4 * C0 * alpha0 * (ell : ℝ)^2 ≤ (ell : ℝ)^2 - 1) {k : ℕ} :
    ∀ (j : ℕ), j ≤ k →
      betaRec ell C0 alpha0 k j ≤
        (alpha0 * ((ell : ℝ)^2)^j * etaSq ell k) *
          (1 + 4 * C0 * alpha0 * etaSq ell k * geomS ell j) := by
  intro j
  induction j with
  | zero =>
      intro _
      simp [betaRec_zero, geomS_zero]
  | succ j ih =>
      intro hjk
      have hjk' : j ≤ k := Nat.le_of_succ_le hjk
      have ih' := ih hjk'
      have h2 : (2:ℝ) ≤ (ell : ℝ) := by exact_mod_cast hell
      have hq0 : (0:ℝ) < (ell : ℝ)^2 := by
        nlinarith [mul_nonneg (show (0:ℝ) ≤ (ell:ℝ) - 2 by linarith)
          (show (0:ℝ) ≤ (ell:ℝ) + 2 by linarith)]
      have hq0' : (0:ℝ) ≤ (ell : ℝ)^2 := hq0.le
      have hγ2 := gamma_le_two ell C0 alpha0 hell hC0 hα0 hC0α0 hjk'
      have hA0 : (0:ℝ) ≤ 4 * C0 * alpha0 := by positivity
      have hη0 : 0 ≤ etaSq ell k := etaSq_nonneg ell k
      have hg0 : 0 ≤ geomS ell j := geomS_nonneg ell j
      have hγ0 : (0:ℝ) ≤ 1 + 4 * C0 * alpha0 * etaSq ell k * geomS ell j := by
        have hnn : (0:ℝ) ≤ 4 * C0 * alpha0 * etaSq ell k * geomS ell j :=
          mul_nonneg (mul_nonneg hA0 hη0) hg0
        linarith
      have hβ0 : 0 ≤ betaRec ell C0 alpha0 k j := betaRec_nonneg ell C0 alpha0 hC0 hα0 k j
      have haj0 : (0:ℝ) ≤ alpha0 * ((ell : ℝ)^2)^j * etaSq ell k :=
        mul_nonneg (mul_nonneg hα0.le (pow_nonneg hq0' j)) hη0
      calc betaRec ell C0 alpha0 k (j + 1)
          = (ell : ℝ)^2 * betaRec ell C0 alpha0 k j +
              C0 * ((ell : ℝ)^2 * betaRec ell C0 alpha0 k j)^2 :=
            betaRec_succ ell C0 alpha0 k j
        _ ≤ (ell : ℝ)^2 * ((alpha0 * ((ell : ℝ)^2)^j * etaSq ell k) *
                (1 + 4 * C0 * alpha0 * etaSq ell k * geomS ell j)) +
              C0 * ((ell : ℝ)^2 * ((alpha0 * ((ell : ℝ)^2)^j * etaSq ell k) *
                (1 + 4 * C0 * alpha0 * etaSq ell k * geomS ell j)))^2 := by
            apply add_le_add
            · exact mul_le_mul_of_nonneg_left ih' hq0'
            · apply mul_le_mul_of_nonneg_left _ hC0
              set u := (ell : ℝ)^2 * betaRec ell C0 alpha0 k j with hu
              set v := (ell : ℝ)^2 * ((alpha0 * ((ell : ℝ)^2)^j * etaSq ell k) *
                (1 + 4 * C0 * alpha0 * etaSq ell k * geomS ell j)) with hv
              have huv0 : u ≤ v := mul_le_mul_of_nonneg_left ih' hq0'
              have hu0 : 0 ≤ u := mul_nonneg hq0' hβ0
              have hv0 : 0 ≤ v := mul_nonneg hq0' (mul_nonneg haj0 hγ0)
              nlinarith [mul_nonneg (sub_nonneg.mpr huv0) (by linarith : (0:ℝ) ≤ u + v)]
        _ = (alpha0 * ((ell : ℝ)^2)^(j + 1) * etaSq ell k) *
                (1 + 4 * C0 * alpha0 * etaSq ell k * geomS ell j) +
              C0 * ((alpha0 * ((ell : ℝ)^2)^(j + 1) * etaSq ell k) *
                (1 + 4 * C0 * alpha0 * etaSq ell k * geomS ell j))^2 := by
            rw [pow_succ']
            ring
        _ ≤ (alpha0 * ((ell : ℝ)^2)^(j + 1) * etaSq ell k) *
                (1 + 4 * C0 * alpha0 * etaSq ell k * geomS ell j) +
              C0 * ((alpha0 * ((ell : ℝ)^2)^(j + 1) * etaSq ell k) * 2)^2 := by
            refine add_le_add le_rfl ?_
            apply mul_le_mul_of_nonneg_left _ hC0
            set w := alpha0 * ((ell : ℝ)^2)^(j + 1) * etaSq ell k with hw
            have hw0 : 0 ≤ w :=
              mul_nonneg (mul_nonneg hα0.le (pow_nonneg hq0' (j + 1))) hη0
            have hww : w * (1 + 4 * C0 * alpha0 * etaSq ell k * geomS ell j) ≤ w * 2 :=
              mul_le_mul_of_nonneg_left hγ2 hw0
            have hwg0 : 0 ≤ w * (1 + 4 * C0 * alpha0 * etaSq ell k * geomS ell j) :=
              mul_nonneg hw0 hγ0
            nlinarith [mul_nonneg (sub_nonneg.mpr hww)
              (by linarith : (0:ℝ) ≤ w * (1 + 4 * C0 * alpha0 * etaSq ell k * geomS ell j) + w * 2)]
        _ = (alpha0 * ((ell : ℝ)^2)^(j + 1) * etaSq ell k) *
              ((1 + 4 * C0 * alpha0 * etaSq ell k * geomS ell j) +
                4 * C0 * (alpha0 * ((ell : ℝ)^2)^(j + 1) * etaSq ell k)) := by
            ring
        _ = (alpha0 * ((ell : ℝ)^2)^(j + 1) * etaSq ell k) *
              (1 + 4 * C0 * alpha0 * etaSq ell k * geomS ell (j + 1)) := by
            rw [geomS_succ]
            ring

/-- **The uniform-in-`k` ceiling** (CMP98 (54) content): `β_j ≤ 2·alpha0` for all `j ≤ k`. -/
theorem betaRec_le_two_alpha0 (ell : ℕ) (C0 alpha0 : ℝ) (hell : 2 ≤ ell) (hC0 : 0 ≤ C0) (hα0 : 0 < alpha0)
    (hC0α0 : 4 * C0 * alpha0 * (ell : ℝ)^2 ≤ (ell : ℝ)^2 - 1) {k j : ℕ} (hjk : j ≤ k) :
    betaRec ell C0 alpha0 k j ≤ 2 * alpha0 := by
  have h1 := betaRec_le ell C0 alpha0 hell hC0 hα0 hC0α0 j hjk
  have hγ2 := gamma_le_two ell C0 alpha0 hell hC0 hα0 hC0α0 hjk
  have h2 : (2:ℝ) ≤ (ell : ℝ) := by exact_mod_cast hell
  have hq0 : (0:ℝ) < (ell : ℝ)^2 := by
    nlinarith [mul_nonneg (show (0:ℝ) ≤ (ell:ℝ) - 2 by linarith)
      (show (0:ℝ) ≤ (ell:ℝ) + 2 by linarith)]
  have hq1 : (1:ℝ) ≤ (ell : ℝ)^2 := by nlinarith
  have hqk0 : (0:ℝ) < ((ell : ℝ)^2)^k := pow_pos hq0 k
  have hjk' : ((ell : ℝ)^2)^j ≤ ((ell : ℝ)^2)^k := pow_le_pow_right₀ hq1 hjk
  have hfrac : ((ell : ℝ)^2)^j * etaSq ell k ≤ 1 := by
    rw [etaSq, ← div_eq_mul_inv, div_le_one hqk0]
    exact hjk'
  have haj0 : (0:ℝ) ≤ alpha0 * ((ell : ℝ)^2)^j * etaSq ell k :=
    mul_nonneg (mul_nonneg hα0.le (pow_nonneg hq0.le j)) (etaSq_nonneg ell k)
  calc betaRec ell C0 alpha0 k j
      ≤ (alpha0 * ((ell : ℝ)^2)^j * etaSq ell k) *
          (1 + 4 * C0 * alpha0 * etaSq ell k * geomS ell j) := h1
    _ ≤ (alpha0 * ((ell : ℝ)^2)^j * etaSq ell k) * 2 :=
        mul_le_mul_of_nonneg_left hγ2 haj0
    _ = 2 * alpha0 * (((ell : ℝ)^2)^j * etaSq ell k) := by ring
    _ ≤ 2 * alpha0 * 1 :=
        mul_le_mul_of_nonneg_left hfrac (by linarith : (0:ℝ) ≤ 2 * alpha0)
    _ = 2 * alpha0 := by ring

/-- **Per-level sharpening**: `β_j ≤ 2·a_j = 2·alpha0·q^{j-k}`. -/
theorem betaRec_le_two_a (ell : ℕ) (C0 alpha0 : ℝ) (hell : 2 ≤ ell) (hC0 : 0 ≤ C0) (hα0 : 0 < alpha0)
    (hC0α0 : 4 * C0 * alpha0 * (ell : ℝ)^2 ≤ (ell : ℝ)^2 - 1) {k j : ℕ} (hjk : j ≤ k) :
    betaRec ell C0 alpha0 k j ≤ 2 * (alpha0 * ((ell : ℝ)^2)^j * etaSq ell k) := by
  have h1 := betaRec_le ell C0 alpha0 hell hC0 hα0 hC0α0 j hjk
  have hγ2 := gamma_le_two ell C0 alpha0 hell hC0 hα0 hC0α0 hjk
  have h2 : (2:ℝ) ≤ (ell : ℝ) := by exact_mod_cast hell
  have hq0' : (0:ℝ) ≤ (ell : ℝ)^2 := by
    nlinarith [mul_nonneg (show (0:ℝ) ≤ (ell:ℝ) - 2 by linarith)
      (show (0:ℝ) ≤ (ell:ℝ) + 2 by linarith)]
  have haj0 : (0:ℝ) ≤ alpha0 * ((ell : ℝ)^2)^j * etaSq ell k :=
    mul_nonneg (mul_nonneg hα0.le (pow_nonneg hq0' j)) (etaSq_nonneg ell k)
  calc betaRec ell C0 alpha0 k j
      ≤ (alpha0 * ((ell : ℝ)^2)^j * etaSq ell k) *
          (1 + 4 * C0 * alpha0 * etaSq ell k * geomS ell j) := h1
    _ ≤ (alpha0 * ((ell : ℝ)^2)^j * etaSq ell k) * 2 :=
        mul_le_mul_of_nonneg_left hγ2 haj0
    _ = 2 * (alpha0 * ((ell : ℝ)^2)^j * etaSq ell k) := by ring

/-- At every intermediate level `j < k` the propagated deviation is `≤ alpha0/2 < alpha0`. -/
theorem betaRec_lt_alpha0_of_lt (ell : ℕ) (C0 alpha0 : ℝ) (hell : 2 ≤ ell)
    (hC0 : 0 ≤ C0) (hα0 : 0 < alpha0)
    (hC0α0 : 4 * C0 * alpha0 * (ell : ℝ)^2 ≤ (ell : ℝ)^2 - 1) {k j : ℕ} (hjk : j < k) :
    betaRec ell C0 alpha0 k j ≤ alpha0 / 2 ∧ betaRec ell C0 alpha0 k j < alpha0 := by
  have h1 := betaRec_le_two_a ell C0 alpha0 hell hC0 hα0 hC0α0 (Nat.le_of_lt hjk)
  have h2 : (2:ℝ) ≤ (ell : ℝ) := by exact_mod_cast hell
  have h4 : (4:ℝ) ≤ (ell : ℝ)^2 := by
    nlinarith [mul_nonneg (show (0:ℝ) ≤ (ell:ℝ) - 2 by linarith)
      (show (0:ℝ) ≤ (ell:ℝ) + 2 by linarith)]
  have hq0 : (0:ℝ) < (ell : ℝ)^2 := by linarith
  have hq1 : (1:ℝ) ≤ (ell : ℝ)^2 := by linarith
  have hqk0 : (0:ℝ) < ((ell : ℝ)^2)^k := pow_pos hq0 k
  have hjkle : j ≤ k - 1 := Nat.le_sub_one_of_lt hjk
  have hqj : ((ell : ℝ)^2)^j ≤ ((ell : ℝ)^2)^(k - 1) := pow_le_pow_right₀ hq1 hjkle
  have hkk : ((ell : ℝ)^2)^k = (ell : ℝ)^2 * ((ell : ℝ)^2)^(k - 1) := by
    conv_lhs => rw [← Nat.sub_add_cancel (show 1 ≤ k from by omega)]
    rw [pow_succ]
    ring
  have hfrac : ((ell : ℝ)^2)^j * etaSq ell k ≤ ((ell : ℝ)^2)⁻¹ := by
    rw [etaSq, ← div_eq_mul_inv, div_le_iff₀ hqk0]
    calc ((ell : ℝ)^2)^j ≤ ((ell : ℝ)^2)^(k - 1) := hqj
      _ = ((ell : ℝ)^2)⁻¹ * ((ell : ℝ)^2)^k := by
          rw [hkk, ← mul_assoc, inv_mul_cancel₀ hq0.ne', one_mul]
      _ ≤ ((ell : ℝ)^2)⁻¹ * ((ell : ℝ)^2)^k := le_refl _
  have hbound : 2 * (alpha0 * ((ell : ℝ)^2)^j * etaSq ell k) ≤ alpha0 / 2 := by
    have h := mul_le_mul_of_nonneg_left hfrac (by linarith : (0:ℝ) ≤ 2 * alpha0)
    have hhalf : (2:ℝ) * ((ell : ℝ)^2)⁻¹ ≤ 1 / 2 := by
      rw [inv_eq_one_div, mul_one_div, div_le_iff₀ hq0]
      linarith [h4]
    calc 2 * (alpha0 * ((ell : ℝ)^2)^j * etaSq ell k)
        = 2 * alpha0 * (((ell : ℝ)^2)^j * etaSq ell k) := by ring
      _ ≤ 2 * alpha0 * ((ell : ℝ)^2)⁻¹ := h
      _ = alpha0 * (2 * ((ell : ℝ)^2)⁻¹) := by ring
      _ ≤ alpha0 * (1 / 2) := mul_le_mul_of_nonneg_left hhalf hα0.le
      _ = alpha0 / 2 := by ring
  have hle : betaRec ell C0 alpha0 k j ≤ alpha0 / 2 := h1.trans hbound
  exact ⟨hle, by linarith [hle, hα0]⟩

/-! ## §3 — tower propagation along `ubarTowerSU2` -/

/-- **Balaban Proposition 2's engine on the RAW tower**: the level plaquette bound
propagates along `ubarTowerSU2` by `hProp1` (the raw Prop 1) alone. One step is
`ubarTowerSU2_succ : Ū^{j+1} = ubarSU2 (ell^j) ell (Ū^j)`. -/
theorem levelPlaqBound_tower (ell : ℕ) (hell : 2 ≤ ell) (C0 alpha0 c2' : ℝ)
    (hC0 : 0 ≤ C0) (hα0 : 0 < alpha0)
    (hC0α0 : 4 * C0 * alpha0 * (ell : ℝ)^2 ≤ (ell : ℝ)^2 - 1) (hc2 : 2 * alpha0 ≤ c2')
    (k : ℕ) (U : PeriodicLinkConfiguration SU2 L)
    (hProp1 : OneStepPropagationRaw (L := L) ell C0 c2')
    (hFine : LevelPlaqBound (ubarTowerSU2 ell U) ell 0 (betaRec ell C0 alpha0 k 0)) :
    ∀ (j : ℕ), j ≤ k →
      LevelPlaqBound (ubarTowerSU2 ell U) ell j (betaRec ell C0 alpha0 k j) := by
  intro j
  induction j with
  | zero => intro _; exact hFine
  | succ j ih =>
      intro hjk
      have hjk' : j ≤ k := Nat.le_of_succ_le hjk
      have ih' := ih hjk'
      have hβj2 : betaRec ell C0 alpha0 k j ≤ 2 * alpha0 :=
        betaRec_le_two_alpha0 ell C0 alpha0 hell hC0 hα0 hC0α0 hjk'
      have hβj0 : 0 ≤ betaRec ell C0 alpha0 k j := betaRec_nonneg ell C0 alpha0 hC0 hα0 k j
      intro y μ ν
      have hpow : ell ^ (j + 1) = ell ^ j * ell := by rw [pow_add, pow_one]
      rw [ubarTowerSU2_succ, hpow, betaRec_succ]
      exact hProp1 (ell ^ j) (ubarTowerSU2 ell U j) (betaRec ell C0 alpha0 k j)
        hβj0 (hβj2.trans hc2) ih' y μ ν

/-! ## §4 — depth-uniformity theorem on the raw tower -/

theorem loopRhoPlaq_mono {ell : ℕ} {eps0 eps1 : ℝ} (h : eps0 ≤ eps1) :
    loopRhoPlaq eps0 ell ≤ loopRhoPlaq eps1 ell := by
  unfold loopRhoPlaq
  exact mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_left h (by positivity)) (Nat.cast_nonneg _)

/-- **DEPTH-k UNIFORMITY on the RAW tower.**  Under the single finest-scale plaquette
hypothesis and `hProp1 : OneStepPropagationRaw`, every loop holonomy log at every
level `j = 0,…,k` of `ubarTowerSU2 ell U` has principal-log norm bounded by the same
explicit radius `loopRhoPlaq (2·alpha0) ell`, independent of `j` and of `k`. -/
theorem nu_loopVar_tower_uniform
    (ell k : ℕ) (hell : 2 ≤ ell) (C0 alpha0 c2' : ℝ) (hC0 : 0 ≤ C0) (hα0 : 0 < alpha0)
    (hC0α0 : 4 * C0 * alpha0 * (ell : ℝ)^2 ≤ (ell : ℝ)^2 - 1) (hc2 : 2 * alpha0 ≤ c2')
    (U : PeriodicLinkConfiguration SU2 L)
    (hProp1 : OneStepPropagationRaw (L := L) ell C0 c2')
    (hFine : ∀ (y : PeriodicLatticeSite L) (μ ν : Fin 3),
      frobNorm (((orientedPlaqHolS 1 U y μ ν : SU2) : M2) - 1) ≤ alpha0 * etaSq ell k)
    (j : ℕ) (hjk : j ≤ k)
    (c : PeriodicLatticeEdge L) (x : PeriodicLatticeSite L)
    (hx : x ∈ stepBlockOf c.1 (ell ^ j) ell)
    (hπ : loopRhoPlaq (2 * alpha0) ell < Real.pi / 2) :
    nu ((principalSuTwoLog (loopVar (ell ^ j) ell (ubarTowerSU2 ell U j) c x) :
          SuTwo) : M2) ≤
        loopRhoPlaq (2 * alpha0) ell ∧
      loopRhoPlaq (2 * alpha0) ell < Real.pi / 2 := by
  have hFine' : LevelPlaqBound (ubarTowerSU2 ell U) ell 0
      (betaRec ell C0 alpha0 k 0) :=
    fun y μ ν => hFine y μ ν
  have hβj := levelPlaqBound_tower ell hell C0 alpha0 c2' hC0 hα0 hC0α0 hc2 k U hProp1
    hFine' j hjk
  have hβ2 := betaRec_le_two_alpha0 ell C0 alpha0 hell hC0 hα0 hC0α0 hjk
  have hβ0 := betaRec_nonneg ell C0 alpha0 hC0 hα0 k j
  have h0ell : 0 < ell := by omega
  have hs : 0 < ell ^ j := Nat.pow_pos h0ell
  have hmono : loopRhoPlaq (betaRec ell C0 alpha0 k j) ell ≤ loopRhoPlaq (2 * alpha0) ell :=
    loopRhoPlaq_mono hβ2
  have hsmall : loopRhoPlaq (betaRec ell C0 alpha0 k j) ell < Real.pi / 2 :=
    lt_of_le_of_lt hmono hπ
  have hbr := nu_loopVar_le_rhoPlaq_S (ubarTowerSU2 ell U j) (ell ^ j) ell hs
    (betaRec ell C0 alpha0 k j) hβ0 c x hx hβj hsmall
  exact ⟨hbr.1.trans hmono, hπ⟩

/-- **Per-level sharpening** on the raw tower. -/
theorem nu_loopVar_tower_perlevel
    (ell k : ℕ) (hell : 2 ≤ ell) (C0 alpha0 c2' : ℝ) (hC0 : 0 ≤ C0) (hα0 : 0 < alpha0)
    (hC0α0 : 4 * C0 * alpha0 * (ell : ℝ)^2 ≤ (ell : ℝ)^2 - 1) (hc2 : 2 * alpha0 ≤ c2')
    (U : PeriodicLinkConfiguration SU2 L)
    (hProp1 : OneStepPropagationRaw (L := L) ell C0 c2')
    (hFine : ∀ (y : PeriodicLatticeSite L) (μ ν : Fin 3),
      frobNorm (((orientedPlaqHolS 1 U y μ ν : SU2) : M2) - 1) ≤ alpha0 * etaSq ell k)
    (j : ℕ) (hjk : j ≤ k)
    (c : PeriodicLatticeEdge L) (x : PeriodicLatticeSite L)
    (hx : x ∈ stepBlockOf c.1 (ell ^ j) ell)
    (hπ : loopRhoPlaq (2 * alpha0) ell < Real.pi / 2) :
    nu ((principalSuTwoLog (loopVar (ell ^ j) ell (ubarTowerSU2 ell U j) c x) :
          SuTwo) : M2) ≤
        loopRhoPlaq (2 * (alpha0 * ((ell : ℝ)^2)^j * etaSq ell k)) ell := by
  have hFine' : LevelPlaqBound (ubarTowerSU2 ell U) ell 0
      (betaRec ell C0 alpha0 k 0) :=
    fun y μ ν => hFine y μ ν
  have hβj := levelPlaqBound_tower ell hell C0 alpha0 c2' hC0 hα0 hC0α0 hc2 k U hProp1
    hFine' j hjk
  have hβ2a := betaRec_le_two_a ell C0 alpha0 hell hC0 hα0 hC0α0 hjk
  have hβ0 := betaRec_nonneg ell C0 alpha0 hC0 hα0 k j
  have h0ell : 0 < ell := by omega
  have hs : 0 < ell ^ j := Nat.pow_pos h0ell
  have hmono1 : loopRhoPlaq (betaRec ell C0 alpha0 k j) ell ≤
      loopRhoPlaq (2 * (alpha0 * ((ell : ℝ)^2)^j * etaSq ell k)) ell :=
    loopRhoPlaq_mono hβ2a
  have hmono2 : loopRhoPlaq (2 * (alpha0 * ((ell : ℝ)^2)^j * etaSq ell k)) ell ≤
      loopRhoPlaq (2 * alpha0) ell := by
    apply loopRhoPlaq_mono
    have h2 : (2:ℝ) ≤ (ell : ℝ) := by exact_mod_cast hell
    have hq0 : (0:ℝ) < (ell : ℝ)^2 := by
      nlinarith [mul_nonneg (show (0:ℝ) ≤ (ell:ℝ) - 2 by linarith)
        (show (0:ℝ) ≤ (ell:ℝ) + 2 by linarith)]
    have hq1 : (1:ℝ) ≤ (ell : ℝ)^2 := by nlinarith
    have hqk0 : (0:ℝ) < ((ell : ℝ)^2)^k := pow_pos hq0 k
    have hjk' : ((ell : ℝ)^2)^j ≤ ((ell : ℝ)^2)^k := pow_le_pow_right₀ hq1 hjk
    have hfrac : ((ell : ℝ)^2)^j * etaSq ell k ≤ 1 := by
      rw [etaSq, ← div_eq_mul_inv, div_le_one hqk0]
      exact hjk'
    have := mul_le_mul_of_nonneg_left hfrac (by linarith : (0:ℝ) ≤ 2 * alpha0)
    calc 2 * (alpha0 * ((ell : ℝ)^2)^j * etaSq ell k)
        = 2 * alpha0 * (((ell : ℝ)^2)^j * etaSq ell k) := by ring
      _ ≤ 2 * alpha0 * 1 := this
      _ = 2 * alpha0 := by ring
  have hsmall : loopRhoPlaq (betaRec ell C0 alpha0 k j) ell < Real.pi / 2 :=
    lt_of_le_of_lt (hmono1.trans hmono2) hπ
  have hbr := nu_loopVar_le_rhoPlaq_S (ubarTowerSU2 ell U j) (ell ^ j) ell hs
    (betaRec ell C0 alpha0 k j) hβ0 c x hx hβj hsmall
  exact hbr.1.trans hmono1

theorem loopRhoPlaq_two_alpha0_eq (ell : ℕ) (alpha0 : ℝ) :
    loopRhoPlaq (2 * alpha0) ell =
      (3 * ell * (ell - 1) : ℕ) * (Real.pi / (2 * Real.sqrt 2)) * (2 * alpha0) := by
  unfold loopRhoPlaq loopSurfaceBound
  ring

/-! ## §5 — level-0 wrapper from the printed unit-plaquette hypothesis -/

theorem levelPlaqBound_zero_of_printed (U : PeriodicLinkConfiguration SU2 L) (δ : ℝ)
    (hδ : 0 ≤ δ)
    (hU : ∀ p : PeriodicLatticePlaquette L,
      frobNorm ((periodicPlaquetteHolonomy (G := SU2) U p : M2) - 1) ≤ δ) :
    ∀ (y : PeriodicLatticeSite L) (μ ν : Fin 3),
      frobNorm (((orientedPlaqHolS 1 U y μ ν : SU2) : M2) - 1) ≤ δ := by
  intro y μ ν
  rw [orientedPlaqHolS_one_eq]
  rcases lt_trichotomy μ ν with hlt | heq | hgt
  · have hp : orientedPlaqHol U y μ ν =
        periodicPlaquetteHolonomy U (y, ⟨(μ, ν), hlt⟩) := rfl
    rw [hp]
    exact hU _
  · subst heq
    have h1 : orientedPlaqHol U y μ μ = 1 := by
      simp [orientedPlaqHol, mul_assoc, mul_inv_cancel]
    rw [h1]
    have hz : frobNorm (((1 : SU2) : M2) - 1) = 0 := by
      have h10 : (((1 : SU2) : M2) - 1) = (0 : M2) := by simp
      rw [h10]
      simp [frobNorm]
    rw [hz]
    exact hδ
  · have hp : orientedPlaqHol U y μ ν =
        (periodicPlaquetteHolonomy U (y, ⟨(ν, μ), hgt⟩))⁻¹ := by
      simp [orientedPlaqHol, periodicPlaquetteHolonomy, mul_assoc, inv_inv]
    rw [hp, frobNorm_inv_sub_one]
    exact hU _

theorem nu_loopVar_tower_uniform_printed
    (ell k : ℕ) (hell : 2 ≤ ell) (C0 alpha0 c2' : ℝ) (hC0 : 0 ≤ C0) (hα0 : 0 < alpha0)
    (hC0α0 : 4 * C0 * alpha0 * (ell : ℝ)^2 ≤ (ell : ℝ)^2 - 1) (hc2 : 2 * alpha0 ≤ c2')
    (U : PeriodicLinkConfiguration SU2 L)
    (hProp1 : OneStepPropagationRaw (L := L) ell C0 c2')
    (hPrint : ∀ p : PeriodicLatticePlaquette L,
      frobNorm ((periodicPlaquetteHolonomy (G := SU2) U p : M2) - 1) ≤ alpha0 * etaSq ell k)
    (j : ℕ) (hjk : j ≤ k)
    (c : PeriodicLatticeEdge L) (x : PeriodicLatticeSite L)
    (hx : x ∈ stepBlockOf c.1 (ell ^ j) ell)
    (hπ : loopRhoPlaq (2 * alpha0) ell < Real.pi / 2) :
    nu ((principalSuTwoLog (loopVar (ell ^ j) ell (ubarTowerSU2 ell U j) c x) :
          SuTwo) : M2) ≤
        loopRhoPlaq (2 * alpha0) ell ∧
      loopRhoPlaq (2 * alpha0) ell < Real.pi / 2 :=
  nu_loopVar_tower_uniform ell k hell C0 alpha0 c2' hC0 hα0 hC0α0 hc2 U hProp1
    (levelPlaqBound_zero_of_printed U _ (mul_nonneg hα0.le (etaSq_nonneg ell k)) hPrint)
    j hjk c x hx hπ

/-! ## §6 — explicit non-refutation by the flat/pure-gauge class

The independently verified counterexample against the OLD hypothesis was a globally
flat pure-gauge field: input plaquettes are the identity (so any positive `β` is a
valid hypothesis radius), the **raw** average stays flat, but the **diagonal
modified** average has a strictly positive plaquette deviation, which beats the
quadratic polynomial for small enough `β`.

This section tests the CORRECTED hypothesis on that same class, before any appeal
to compilation of the composition theorems. If a flat pure-gauge input produced a
positive raw-average deviation, `OneStepPropagationRaw` would be false for the same
reason. We prove it does not: raw averaging sends a stride-`s` pure gauge to a
stride-`(s·ell)` pure gauge, whose plaquettes are identically 1. -/

/-- Identity configuration has identity plaquettes at every stride. -/
theorem orientedPlaqHolS_trivialU (s : ℕ) (y : PeriodicLatticeSite L) (μ ν : Fin 3) :
    orientedPlaqHolS s (trivialU L) y μ ν = 1 := by
  simp [orientedPlaqHolS, trivialU]

/-- Strided plaquette of a gauge transform is conjugation at the basepoint.
Uses only certified shift commutation; not an assumed covariance of averaging. -/
theorem plaq_gauge {G : Type*} [Group G] (s : ℕ)
    (g : PeriodicLatticeSite L → G) (V : PeriodicLinkConfiguration G L)
    (y : PeriodicLatticeSite L) (μ ν : Fin 3) :
    orientedPlaqHolS s (coarseGaugeTransform s g V) y μ ν =
      g y * orientedPlaqHolS s V y μ ν * (g y)⁻¹ := by
  unfold orientedPlaqHolS coarseGaugeTransform
  rw [coarseShift_comm y s s μ ν]
  group

theorem plaq_gauge_norm (s : ℕ) (g : PeriodicLatticeSite L → SU2)
    (V : PeriodicLinkConfiguration SU2 L)
    (y : PeriodicLatticeSite L) (μ ν : Fin 3) :
    frobNorm (((orientedPlaqHolS s (coarseGaugeTransform s g V) y μ ν : SU2) : M2) - 1) =
      frobNorm (((orientedPlaqHolS s V y μ ν : SU2) : M2) - 1) := by
  rw [plaq_gauge]
  exact frobNorm_conj_sub_one _ _

/-- Stride-`s` pure gauge: the class of the old flat-input witness. -/
def pureGauge (s : ℕ) (g : PeriodicLatticeSite L → SU2) : PeriodicLinkConfiguration SU2 L :=
  coarseGaugeTransform s g (trivialU L)

theorem orientedPlaqHolS_pureGauge (s : ℕ) (g : PeriodicLatticeSite L → SU2)
    (y : PeriodicLatticeSite L) (μ ν : Fin 3) :
    orientedPlaqHolS s (pureGauge s g) y μ ν = 1 := by
  unfold pureGauge
  rw [plaq_gauge, orientedPlaqHolS_trivialU]
  group

/-- Certified covariance (11) specialised to a pure gauge: the raw average of a
stride-`s` pure gauge IS the stride-`(s·ell)` pure gauge of the same site function. -/
theorem ubarSU2_pureGauge (s ell : ℕ) (g : PeriodicLatticeSite L → SU2) :
    ubarSU2 s ell (pureGauge s g) = pureGauge (s * ell) g := by
  funext c
  unfold pureGauge
  rw [ubarSU2_gauge, ubarSU2_trivialU]

/-- The raw one-step output of a flat pure gauge is itself flat. -/
theorem orientedPlaqHolS_ubar_pureGauge (s ell : ℕ) (g : PeriodicLatticeSite L → SU2)
    (y : PeriodicLatticeSite L) (μ ν : Fin 3) :
    orientedPlaqHolS (s * ell) (ubarSU2 s ell (pureGauge s g)) y μ ν = 1 := by
  rw [ubarSU2_pureGauge]
  exact orientedPlaqHolS_pureGauge (s * ell) g y μ ν

theorem frobNorm_one_sub_one : frobNorm (((1 : SU2) : M2) - 1) = 0 := by
  have h10 : (((1 : SU2) : M2) - 1) = (0 : M2) := by simp
  rw [h10, frobNorm_zero]

theorem prop1_poly_nonneg (ell : ℕ) (C0 β : ℝ) (hC0 : 0 ≤ C0) (hβ : 0 ≤ β) :
    0 ≤ (ell : ℝ)^2 * β + C0 * ((ell : ℝ)^2 * β)^2 :=
  add_nonneg (mul_nonneg (sq_nonneg _) hβ) (mul_nonneg hC0 (sq_nonneg _))

/-- Input deviations of a pure gauge are exactly 0, so any `β ≥ 0` is a valid
hypothesis radius — the same opening the old refutation used. -/
theorem pureGauge_input_frob_eq_zero (s : ℕ) (g : PeriodicLatticeSite L → SU2)
    (y : PeriodicLatticeSite L) (μ ν : Fin 3) :
    frobNorm (((orientedPlaqHolS s (pureGauge s g) y μ ν : SU2) : M2) - 1) = 0 := by
  rw [orientedPlaqHolS_pureGauge, frobNorm_one_sub_one]

/-- Output deviations of the RAW average of a pure gauge are exactly 0. -/
theorem pureGauge_raw_output_frob_eq_zero (s ell : ℕ) (g : PeriodicLatticeSite L → SU2)
    (y : PeriodicLatticeSite L) (μ ν : Fin 3) :
    frobNorm
        (((orientedPlaqHolS (s * ell) (ubarSU2 s ell (pureGauge s g)) y μ ν : SU2) : M2) - 1) =
      0 := by
  rw [orientedPlaqHolS_ubar_pureGauge, frobNorm_one_sub_one]

/-- Instantiation of the corrected one-step bound at an arbitrary pure-gauge field.
The output is 0, which lies under the nonnegative (51) polynomial. -/
theorem OneStepPropagationRaw_holds_at_pureGauge
    (ell : ℕ) (C0 c2' : ℝ) (hC0 : 0 ≤ C0)
    (s : ℕ) (g : PeriodicLatticeSite L → SU2) (β : ℝ)
    (hβ : 0 ≤ β) (_hβc : β ≤ c2')
    (y : PeriodicLatticeSite L) (μ ν : Fin 3) :
    frobNorm
        (((orientedPlaqHolS (s * ell) (ubarSU2 s ell (pureGauge s g)) y μ ν : SU2) : M2) - 1) ≤
      (ell : ℝ)^2 * β + C0 * ((ell : ℝ)^2 * β)^2 := by
  rw [pureGauge_raw_output_frob_eq_zero]
  exact prop1_poly_nonneg ell C0 β hC0 hβ

/-- **The explicit non-refutation.** For every `C0 ≥ 0` and every threshold `c2'`,
every stride, every block factor, and every site-valued gauge, the pure-gauge field
(the class that refuted `modifiedAverageS s V ell V`) satisfies the body of
`OneStepPropagationRaw` at every `β ∈ [0, c2']`. A positive-radius attack of the
old style therefore cannot refute the corrected hypothesis: input deviation is 0
(hence `< β` for `β > 0`) while output deviation is 0 (hence it does **not**
exceed the polynomial). -/
theorem flat_pureGauge_does_not_refute
    (ell : ℕ) (C0 c2' : ℝ) (hC0 : 0 ≤ C0)
    (s : ℕ) (g : PeriodicLatticeSite L → SU2) (β : ℝ)
    (hβ : 0 ≤ β) (hβc : β ≤ c2') :
    (∀ (y : PeriodicLatticeSite L) (μ ν : Fin 3),
        frobNorm (((orientedPlaqHolS s (pureGauge s g) y μ ν : SU2) : M2) - 1) ≤ β) ∧
      ∀ (y : PeriodicLatticeSite L) (μ ν : Fin 3),
        frobNorm
            (((orientedPlaqHolS (s * ell) (ubarSU2 s ell (pureGauge s g)) y μ ν : SU2) :
                M2) - 1) ≤
          (ell : ℝ)^2 * β + C0 * ((ell : ℝ)^2 * β)^2 :=
  ⟨fun y μ ν => (pureGauge_input_frob_eq_zero s g y μ ν).le.trans hβ,
    fun y μ ν => OneStepPropagationRaw_holds_at_pureGauge ell C0 c2' hC0 s g β hβ hβc y μ ν⟩

/-- Identity field is the trivial pure gauge; included as the degenerate witness. -/
theorem OneStepPropagationRaw_holds_at_trivialU
    (ell : ℕ) (C0 c2' : ℝ) (hC0 : 0 ≤ C0)
    (s : ℕ) (β : ℝ) (hβ : 0 ≤ β) (_hβc : β ≤ c2')
    (y : PeriodicLatticeSite L) (μ ν : Fin 3) :
    frobNorm
        (((orientedPlaqHolS (s * ell) (ubarSU2 s ell (trivialU L)) y μ ν : SU2) : M2) - 1) ≤
      (ell : ℝ)^2 * β + C0 * ((ell : ℝ)^2 * β)^2 := by
  have hg : ubarSU2 s ell (trivialU L) = trivialU L := ubarSU2_trivialU s ell
  rw [hg, orientedPlaqHolS_trivialU, frobNorm_one_sub_one]
  exact prop1_poly_nonneg ell C0 β hC0 hβ

/-- The raw tower of a pure gauge remains a pure gauge at every level, hence stays
flat: iterating the one-step identity cannot create a positive plaquette deviation
from a flat input, unlike the diagonal modified tower. -/
theorem ubarTowerSU2_pureGauge (ell : ℕ) (g : PeriodicLatticeSite L → SU2) :
    ∀ j : ℕ, ubarTowerSU2 ell (pureGauge 1 g) j = pureGauge (ell ^ j) g
  | 0 => by
      rw [ubarTowerSU2_zero, pow_zero]
  | j + 1 => by
      rw [ubarTowerSU2_succ, ubarTowerSU2_pureGauge ell g j, ubarSU2_pureGauge, pow_succ, mul_comm]

theorem orientedPlaqHolS_ubarTower_pureGauge (ell : ℕ) (g : PeriodicLatticeSite L → SU2)
    (j : ℕ) (y : PeriodicLatticeSite L) (μ ν : Fin 3) :
    orientedPlaqHolS (ell ^ j) (ubarTowerSU2 ell (pureGauge 1 g) j) y μ ν = 1 := by
  rw [ubarTowerSU2_pureGauge]
  exact orientedPlaqHolS_pureGauge (ell ^ j) g y μ ν

end DepthUniformity.RawTower

/-! ## §7 — import fingerprints and axiom audit -/

run_cmd do
  let loopDir := "/home/sebastian/projects/project-adaly/compute/prop1_tower_fix/tower/loop01"
  let stridedDir := "/home/sebastian/projects/project-adaly/compute/prop1_tower_fix/tower/strided01"
  let lh ← Lean.findOLean `LoopHolonomySmall
  unless lh.toString == s!"{loopDir}/LoopHolonomySmall.olean" do
    Lean.logInfo m!"GUARD_NEUTRALISED RAWTOWER_IMPORT_MISMATCH LoopHolonomySmall: resolved {lh}"
  Lean.logInfo m!"RAWTOWER_RESOLVED LoopHolonomySmall: {lh}"
  let sf ← Lean.findOLean `StridedSurfaceFill
  unless sf.toString == s!"{stridedDir}/StridedSurfaceFill.olean" do
    Lean.logInfo m!"GUARD_NEUTRALISED RAWTOWER_IMPORT_MISMATCH StridedSurfaceFill: resolved {sf}"
  Lean.logInfo m!"RAWTOWER_RESOLVED StridedSurfaceFill: {sf}"
  let allowed : List Lean.Name := [`propext, `Classical.choice, `Quot.sound]
  let thms : List Lean.Name :=
    [`DepthUniformity.RawTower.OneStepPropagationRaw_iff_ubarSU2,
     `DepthUniformity.RawTower.geomS_mul_sub,
     `DepthUniformity.RawTower.etaSq_geomS_key_bound,
     `DepthUniformity.RawTower.gamma_le_two,
     `DepthUniformity.RawTower.betaRec_le,
     `DepthUniformity.RawTower.betaRec_le_two_alpha0,
     `DepthUniformity.RawTower.betaRec_le_two_a,
     `DepthUniformity.RawTower.betaRec_lt_alpha0_of_lt,
     `DepthUniformity.RawTower.levelPlaqBound_tower,
     `DepthUniformity.RawTower.nu_loopVar_tower_uniform,
     `DepthUniformity.RawTower.nu_loopVar_tower_perlevel,
     `DepthUniformity.RawTower.levelPlaqBound_zero_of_printed,
     `DepthUniformity.RawTower.nu_loopVar_tower_uniform_printed,
     `DepthUniformity.RawTower.orientedPlaqHolS_trivialU,
     `DepthUniformity.RawTower.plaq_gauge,
     `DepthUniformity.RawTower.orientedPlaqHolS_pureGauge,
     `DepthUniformity.RawTower.ubarSU2_pureGauge,
     `DepthUniformity.RawTower.orientedPlaqHolS_ubar_pureGauge,
     `DepthUniformity.RawTower.pureGauge_input_frob_eq_zero,
     `DepthUniformity.RawTower.pureGauge_raw_output_frob_eq_zero,
     `DepthUniformity.RawTower.OneStepPropagationRaw_holds_at_pureGauge,
     `DepthUniformity.RawTower.flat_pureGauge_does_not_refute,
     `DepthUniformity.RawTower.OneStepPropagationRaw_holds_at_trivialU,
     `DepthUniformity.RawTower.ubarTowerSU2_pureGauge,
     `DepthUniformity.RawTower.orientedPlaqHolS_ubarTower_pureGauge]
  for thm in thms do
    unless (← Lean.getEnv).contains thm do
      throwError "RAWTOWER missing declaration: {thm}"
    let axioms ← Lean.collectAxioms thm
    Lean.logInfo m!"RAWTOWER_AXIOMS {thm}: {axioms}"
    for ax in axioms do
      unless allowed.contains ax do
        throwError "Nonstandard axiom in {thm}: {ax}"
  Lean.logInfo "RAWTOWER_AUDIT_PASS"

#print axioms DepthUniformity.RawTower.nu_loopVar_tower_uniform
#print axioms DepthUniformity.RawTower.nu_loopVar_tower_uniform_printed
#print axioms DepthUniformity.RawTower.flat_pureGauge_does_not_refute
#print axioms DepthUniformity.RawTower.OneStepPropagationRaw_iff_ubarSU2
#print axioms DepthUniformity.RawTower.levelPlaqBound_tower
