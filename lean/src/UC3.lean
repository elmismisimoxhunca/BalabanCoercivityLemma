import UC2

/-!
# UC3 -- consumer forms and witnesses for Layer U (lane m2_unit_20261014)

* `kapQ_le`  : `κ' = kapQ ℓ κ ≤ 930 ℓ κ` once `ρ(κ) ≤ 1/10` (NJ11Num `e2Majorant_le_twelve`, NJ11bNum `rhoOf_le`).
* `Eims_le`  : explicit k-free bound `Eims ℓ (π/2Mc) (4ℓπ/2Mc) κ ε ≤ 384·930² ℓ³ κ² + (8 + 4(1+1/ε)) π²/Mc² + 64(1+1/ε) κ²`.
* `unit_chain_closed` : the chain with `‖C B̃‖²` collected on the left (coefficient `cU`) and `‖y‖² ≤ n² xx`, the shape MA8's
  `assemble_real` consumes:  `cU · bondEnergy B̃ ≤ (2(1+ε)(1+ε')/n) Xbox + (1+ε)/n ((1+ε')64 s² + (1+1/ε')62208 δ²) xx`.
* `agree_one` : the trivial chart (`γ = 1`, `V = U`) — when `U` itself is `M1Regular`, every chart hypothesis of
  `unit_chain_M1charts` that concerns `(γ, V)` is met with these choices (non-vacuity of the chart interface).
-/
set_option autoImplicit false
set_option maxHeartbeats 16000000
set_option maxRecDepth 8000
noncomputable section
namespace AdalyFormal.M2Unit

open Finset
open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2 curlValueCovariant)
open AdalyFormal.Balaban.SuTwoLogExp (SU2 M2)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.RegularUPerturbation (bondEnergy)
open AdalyFormal.NonflatJet
open AdalyFormal.StatementLaneR8 (AgreeAt)
open EstimatesLayer.E1E3 (e2Majorant)

theorem kapQ_le {ell : ℕ} (hell : 1 ≤ ell) {κ : ℝ} (hκ : 0 ≤ κ) (hρ : rhoOf ell κ ≤ 1 / 10) :
    kapQ ell κ ≤ 930 * ell * κ := by
  unfold kapQ
  have h0 : 0 ≤ rhoOf ell κ := by unfold rhoOf; positivity
  have h1 := AdalyFormal.NonflatJet.e2Majorant_le_twelve h0 hρ
  have h2 := rhoOf_le (ell := ell) κ hκ
  have hellR : (1 : ℝ) ≤ ell := by exact_mod_cast hell
  nlinarith

theorem Eims_le {ell Mc : ℕ} (hell : 1 ≤ ell) (hMc : 0 < Mc) {κ ε : ℝ} (hκ : 0 ≤ κ) (hε : 0 < ε)
    (hρ : rhoOf ell κ ≤ 1 / 10) :
    Eims ell (Real.pi / (2 * Mc)) ((4 * ell : ℕ) * (Real.pi / (2 * Mc))) κ ε
      ≤ 384 * 930 ^ 2 * (ell : ℝ) ^ 3 * κ ^ 2 + (8 + 4 * (1 + 1 / ε)) * Real.pi ^ 2 / (Mc : ℝ) ^ 2
        + 64 * (1 + 1 / ε) * κ ^ 2 := by
  have hk := kapQ_le hell hκ hρ
  have hk0 : 0 ≤ kapQ ell κ := by
    unfold kapQ
    have : 0 ≤ e2Majorant (rhoOf ell κ) := EstimatesLayer.E1E3.e2Majorant_nonneg (by unfold rhoOf; positivity)
    positivity
  have hellR : (1 : ℝ) ≤ ell := by exact_mod_cast hell
  have hMR : (0 : ℝ) < Mc := by exact_mod_cast hMc
  have hk2 : kapQ ell κ ^ 2 ≤ (930 * ell * κ) ^ 2 := pow_le_pow_left₀ hk0 hk 2
  unfold Eims
  have e1 : (ell : ℝ) * (2 * (((4 * ell : ℕ) : ℝ) * (Real.pi / (2 * Mc))) ^ 2 / (ell : ℝ) ^ 3)
      = 8 * Real.pi ^ 2 / (Mc : ℝ) ^ 2 := by
    push_cast; field_simp; ring
  have e2 : 4 * (1 + 1 / ε) * (4 * (Real.pi / (2 * Mc)) ^ 2 + 16 * κ ^ 2)
      = 4 * (1 + 1 / ε) * Real.pi ^ 2 / (Mc : ℝ) ^ 2 + 64 * (1 + 1 / ε) * κ ^ 2 := by
    field_simp; ring
  have e3 : (ell : ℝ) * (384 * kapQ ell κ ^ 2 + 2 * (((4 * ell : ℕ) : ℝ) * (Real.pi / (2 * Mc))) ^ 2 / (ell : ℝ) ^ 3)
      = 384 * (ell : ℝ) * kapQ ell κ ^ 2
        + (ell : ℝ) * (2 * (((4 * ell : ℕ) : ℝ) * (Real.pi / (2 * Mc))) ^ 2 / (ell : ℝ) ^ 3) := by ring
  rw [e3, e1, e2]
  have h3 : 384 * (ell : ℝ) * kapQ ell κ ^ 2 ≤ 384 * 930 ^ 2 * (ell : ℝ) ^ 3 * κ ^ 2 := by
    have := mul_le_mul_of_nonneg_left hk2 (by positivity : (0 : ℝ) ≤ 384 * (ell : ℝ))
    nlinarith
  have e4 : (8 + 4 * (1 + 1 / ε)) * Real.pi ^ 2 / (Mc : ℝ) ^ 2
      = 8 * Real.pi ^ 2 / (Mc : ℝ) ^ 2 + 4 * (1 + 1 / ε) * Real.pi ^ 2 / (Mc : ℝ) ^ 2 := by ring
  rw [e4]
  linarith

/-- the chain with `‖C B̃‖²` collected (pure arithmetic on UC1/UC2's conclusion), then `bt ≤ ‖C B̃‖²`. -/
theorem unit_chain_closed {c0 BE bt Xb Y xx n ε ε' s κ₁ δ E : ℝ} (hn : 0 < n) (hε : 0 < ε) (hε' : 0 < ε')
    (hY : Y ≤ n ^ 2 * xx) (hxx : 0 ≤ xx) (hbt : bt ≤ BE)
    (hcoef : 0 ≤ c0 - E - (1 + ε) * (1 + 1 / ε') * 64 * κ₁ ^ 2)
    (hchain : c0 * BE ≤ (1 + ε) * (1 / n) * ((1 + ε') * (2 * Xb + 64 * (s / n) ^ 2 * Y)
        + (1 + 1 / ε') * (64 * κ₁ ^ 2 * n * BE + 8 * 7776 * (1 / n ^ 2) * δ ^ 2 * Y)) + E * BE) :
    (c0 - E - (1 + ε) * (1 + 1 / ε') * 64 * κ₁ ^ 2) * bt
      ≤ 2 * (1 + ε) * (1 + ε') / n * Xb
        + (1 + ε) / n * ((1 + ε') * 64 * s ^ 2 + (1 + 1 / ε') * 62208 * δ ^ 2) * xx := by
  have hε1 : 0 < 1 + 1 / ε' := by positivity
  have e1 : (1 + ε) * (1 / n) * ((1 + 1 / ε') * (64 * κ₁ ^ 2 * n * BE))
      = (1 + ε) * (1 + 1 / ε') * 64 * κ₁ ^ 2 * BE := by field_simp
  have t1 : (1 + ε) * (1 / n) * ((1 + ε') * (64 * (s / n) ^ 2 * Y))
      ≤ (1 + ε) / n * ((1 + ε') * 64 * s ^ 2) * xx := by
    have h1 : 64 * (s / n) ^ 2 * Y ≤ 64 * s ^ 2 * xx := by
      have hs2 : 0 ≤ 64 * (s / n) ^ 2 := by positivity
      have := mul_le_mul_of_nonneg_left hY hs2
      have e : 64 * (s / n) ^ 2 * (n ^ 2 * xx) = 64 * s ^ 2 * xx := by field_simp
      linarith
    have h2 := mul_le_mul_of_nonneg_left h1 (by positivity : (0 : ℝ) ≤ (1 + ε) * (1 / n) * (1 + ε'))
    have e : (1 + ε) * (1 / n) * (1 + ε') * (64 * s ^ 2 * xx) = (1 + ε) / n * ((1 + ε') * 64 * s ^ 2) * xx := by ring
    nlinarith
  have t2 : (1 + ε) * (1 / n) * ((1 + 1 / ε') * (8 * 7776 * (1 / n ^ 2) * δ ^ 2 * Y))
      ≤ (1 + ε) / n * ((1 + 1 / ε') * 62208 * δ ^ 2) * xx := by
    have h1 : 8 * 7776 * (1 / n ^ 2) * δ ^ 2 * Y ≤ 62208 * δ ^ 2 * xx := by
      have hc : 0 ≤ 8 * 7776 * (1 / n ^ 2) * δ ^ 2 := by positivity
      have := mul_le_mul_of_nonneg_left hY hc
      have e : 8 * 7776 * (1 / n ^ 2) * δ ^ 2 * (n ^ 2 * xx) = 62208 * δ ^ 2 * xx := by field_simp; ring
      linarith
    have h2 := mul_le_mul_of_nonneg_left h1 (by positivity : (0 : ℝ) ≤ (1 + ε) * (1 / n) * (1 + 1 / ε'))
    have e : (1 + ε) * (1 / n) * (1 + 1 / ε') * (62208 * δ ^ 2 * xx)
        = (1 + ε) / n * ((1 + 1 / ε') * 62208 * δ ^ 2) * xx := by ring
    nlinarith
  have e2 : (1 + ε) * (1 / n) * ((1 + ε') * (2 * Xb)) = 2 * (1 + ε) * (1 + ε') / n * Xb := by ring
  have hexp : (1 + ε) * (1 / n) * ((1 + ε') * (2 * Xb + 64 * (s / n) ^ 2 * Y)
        + (1 + 1 / ε') * (64 * κ₁ ^ 2 * n * BE + 8 * 7776 * (1 / n ^ 2) * δ ^ 2 * Y))
      = (1 + ε) * (1 / n) * ((1 + ε') * (2 * Xb)) + (1 + ε) * (1 / n) * ((1 + ε') * (64 * (s / n) ^ 2 * Y))
        + (1 + ε) * (1 / n) * ((1 + 1 / ε') * (64 * κ₁ ^ 2 * n * BE))
        + (1 + ε) * (1 / n) * ((1 + 1 / ε') * (8 * 7776 * (1 / n ^ 2) * δ ^ 2 * Y)) := by ring
  rw [hexp, e1, e2] at hchain
  have hmono := mul_le_mul_of_nonneg_left hbt hcoef
  nlinarith

/-- the trivial chart: `γ = 1` makes `U^γ = U`, so `V = U` agrees everywhere. -/
theorem agree_one {L : PeriodicLatticeExtent} (W : Set (PeriodicLatticeSite L)) (U : PeriodicLinkConfiguration SU2 L) :
    AgreeAt W (periodicGaugeTransform (fun _ => (1 : SU2)) U) U := by
  intro z _ μ
  show (1 : SU2) * U (z, μ) * (1 : SU2)⁻¹ = U (z, μ)
  simp

end AdalyFormal.M2Unit

#print axioms AdalyFormal.M2Unit.kapQ_le
#print axioms AdalyFormal.M2Unit.Eims_le
#print axioms AdalyFormal.M2Unit.unit_chain_closed
#print axioms AdalyFormal.M2Unit.agree_one
