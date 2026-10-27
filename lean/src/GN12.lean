import GN7
import SL5

/-!
# GN12 -- the `Φ` drift input of GN7/GN8/GN10 decomposed into three local/named pieces (genuine objects, full tower)

`phi_drift_decomp`: for `t > 0`, `a ≥ 0`, with `P = plaqIn Ω₀`,
* `hc` : `‖χ_P curl_1 x - χ_P curl_U x‖ ≤ δc ‖x‖`   (local curl drift),
* `hdp`: `|Δ'_U(x,x)| ≤ θ ‖x‖²`                      (curvature term; NF4-type plaquette bound),
* `hm` : `Σ_p a ℓ^{j(p)} ‖(Q(1)x)_p - (Q(U)x)_p‖² ≤ δm² ‖x‖²` (weighted bond-composite drift = plan node C1),
gives `Φ_1(x) ≤ (1+t) Φ_U(x) + ((1+t)θ + (1+1/t)(δc² + δm²)) ‖x‖²`  (uses `Δ'_1 = 0`, r7 `deltaPrimeBilNormLoc_trivialU`).
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace AdalyFormal.SliceCoerc

open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.Balaban.CovariantHjMinimizer (trivialU)
open AdalyFormal.Balaban.DeltaKFull (curlCovariantLM_L2)
open AdalyFormal.StatementLane (scaleUp)

theorem phi_drift_decomp (ell k : ℕ) (Lu : PeriodicLatticeExtent) (U : Cfg (scaleUp ell k Lu)) (a : ℝ)
    (ha : 0 ≤ a) (t : ℝ) (ht : 0 < t) (δc θ δm : ℝ)
    (hc : ∀ x : BondFnL2 (scaleUp ell k Lu),
      ‖AdalyFormal.StatementLaneR6.plaqMask (plaqIn (GF ell k Lu).Om0) (curlCovariantLM_L2 (trivialU _) x)
        - AdalyFormal.StatementLaneR6.plaqMask (plaqIn (GF ell k Lu).Om0) (curlCovariantLM_L2 U x)‖ ≤ δc * ‖x‖)
    (hdp : ∀ x : BondFnL2 (scaleUp ell k Lu),
      |AdalyFormal.StatementLaneR6.deltaPrimeBilL2NormLoc U (plaqIn (GF ell k Lu).Om0) x x| ≤ θ * ‖x‖ ^ 2)
    (hm : ∀ x : BondFnL2 (scaleUp ell k Lu),
      ∑ p : BIdx (GF ell k Lu), a * ((GF ell k Lu).ell : ℝ) ^ (p.1 : ℕ) *
        ‖(bondSectorOf (GF ell k Lu) (trivialU _)).Qfull x p - (bondSectorOf (GF ell k Lu) U).Qfull x p‖ ^ 2
        ≤ δm ^ 2 * ‖x‖ ^ 2)
    (x : BondFnL2 (scaleUp ell k Lu)) :
    PhiF ell k Lu a (trivialU _) x
      ≤ (1 + t) * PhiF ell k Lu a U x + ((1 + t) * θ + (1 + 1 / t) * (δc ^ 2 + δm ^ 2)) * ‖x‖ ^ 2 := by
  unfold PhiF Delta
  rw [AdalyFormal.StatementLaneR6.inner_deltaKLocCLM, AdalyFormal.StatementLaneR6.inner_deltaKLocCLM,
    inner_MassFull, inner_MassFull]
  have h0 : AdalyFormal.StatementLaneR6.deltaPrimeBilL2NormLoc (trivialU (scaleUp ell k Lu))
      (plaqIn (GF ell k Lu).Om0) x x = 0 :=
    AdalyFormal.StatementLaneR6.deltaPrimeBilNormLoc_trivialU _ _ _
  rw [h0, add_zero, real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq]
  set c1 := AdalyFormal.StatementLaneR6.plaqMask (plaqIn (GF ell k Lu).Om0) (curlCovariantLM_L2 (trivialU _) x)
  set cU := AdalyFormal.StatementLaneR6.plaqMask (plaqIn (GF ell k Lu).Om0) (curlCovariantLM_L2 U x)
  have hy := young_sq c1 cU t ht
  have hcx := hc x
  have hc2 : ‖c1 - cU‖ ^ 2 ≤ δc ^ 2 * ‖x‖ ^ 2 := by
    rw [← mul_pow]; exact pow_le_pow_left₀ (norm_nonneg _) hcx 2
  have hmw := young_wsum Finset.univ (fun p : BIdx (GF ell k Lu) => a * ((GF ell k Lu).ell : ℝ) ^ (p.1 : ℕ))
    (fun p _ => by positivity) (fun p => (bondSectorOf (GF ell k Lu) (trivialU _)).Qfull x p)
    (fun p => (bondSectorOf (GF ell k Lu) U).Qfull x p) t ht
  have hmx := hm x
  have hdx := hdp x
  have hd' := neg_abs_le (AdalyFormal.StatementLaneR6.deltaPrimeBilL2NormLoc U (plaqIn (GF ell k Lu).Om0) x x)
  have h1t : 0 ≤ 1 + 1 / t := by positivity
  have hA : (1 + 1 / t) * ‖c1 - cU‖ ^ 2 ≤ (1 + 1 / t) * (δc ^ 2 * ‖x‖ ^ 2) :=
    mul_le_mul_of_nonneg_left hc2 h1t
  have hB : (1 + 1 / t) * ∑ p : BIdx (GF ell k Lu), a * ((GF ell k Lu).ell : ℝ) ^ (p.1 : ℕ) *
        ‖(bondSectorOf (GF ell k Lu) (trivialU _)).Qfull x p - (bondSectorOf (GF ell k Lu) U).Qfull x p‖ ^ 2
      ≤ (1 + 1 / t) * (δm ^ 2 * ‖x‖ ^ 2) := mul_le_mul_of_nonneg_left hmx h1t
  have hC : -(1 + t) * AdalyFormal.StatementLaneR6.deltaPrimeBilL2NormLoc U (plaqIn (GF ell k Lu).Om0) x x
      ≤ (1 + t) * (θ * ‖x‖ ^ 2) := by nlinarith
  linarith [hy, hmw, hA, hB, hC]

#print axioms phi_drift_decomp

end AdalyFormal.SliceCoerc
