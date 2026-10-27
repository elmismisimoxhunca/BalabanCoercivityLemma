import AU_CUT
import UD2
import UD5
import OG1

/-!
# AU_UD4 -- `chart_of_ballU`: the c-FREE replacement of `chart_of_class` (lane allc_20261016, uniform-in-c route)

`chart_of_class(AC)` took a TOP-LEVEL class cube (side `fc B`, needs `3 fc M <= R M`).  Here the global clause-3-free configuration `V` (`M1RegularU`) agreeing with `U^g` on `Ball (embY q) r`
comes from a `BallChartsAt` region chart at `j = k` on `Ball (embY q) rho`, `rho = 6 B - 1` (`B = M ell^k`): `embY q in Omega_k` (`pdist y0 q <= R M`), the ball lies in `Omega_{k-1}`
because `R b_{k-1} >= 6 B` (`6 ell <= R`), `Omega_{k+1} = emptyset`; no wrap `2 rho + 2 = 12 B <= N`.  Cutoff width `W = 64 ell^k`: `r + 64 ell^k + 5 <= rho`.
-/
set_option autoImplicit false
set_option maxHeartbeats 16000000
set_option maxRecDepth 8000
namespace AdalyFormal.M2UnitCharts

open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
open AdalyFormal.Balaban.AlphaAnalyticity (GaugeFn)
open AdalyFormal.StatementLaneR8 (Ball AgreeAt pdist_shift_le pdist_triangle pdist_comm)
open AdalyFormal.IngredientFamilyR2 (embY embY_val)
open AdalyFormal.AllU (M1RegularU regime_of_region)

theorem chart_of_ballU {ell M R k : ℕ} {Lu : PeriodicLatticeExtent} (hell : 0 < ell) (hM : 0 < M) (hk : 1 ≤ k)
    {S : Tower (scaleUp ell k Lu)} (hS : Admissible ell M R k S) {Lam : Set (PeriodicLatticeSite Lu)}
    (hL : AdalyFormal.StatementLane.LambdaOK ell M R k S Lam)
    (hthick : ∀ σ : Fin 3, 12 * (M * ell ^ k) ≤ scaleUp ell k Lu σ + 1)
    (hR6 : 6 * ell ≤ R)
    {y0 : PeriodicLatticeSite Lu} (hy0 : y0 ∈ Lam) (q : PeriodicLatticeSite Lu) (hD : pdist y0 q ≤ R * M)
    (r : ℕ) (hr : r + 64 * ell ^ k + 5 ≤ 6 * (M * ell ^ k) - 1)
    {C α₀ : ℝ} (hC : 1 ≤ C) (hα : 0 < α₀) {U : LinkCfg (scaleUp ell k Lu)}
    (hBall : AdalyFormal.OneGap.BallChartsAt ell M k S U C α₀ ((ell : ℝ) ^ k)⁻¹) :
    ∃ (g : GaugeFn (scaleUp ell k Lu)) (V : LinkCfg (scaleUp ell k Lu)),
      M1RegularU ell M 12 k S ((ell : ℝ) ^ 3 * (2 * (C * α₀))) ((ell : ℝ) ^ k)⁻¹ V ∧
      AgreeAt (Ball (embY ell k Lu hell q) r) (periodicGaugeTransform g U) V := by
  set n := ell ^ k with hn0
  have hnpos : 0 < n := pow_pos hell k
  have hB : 0 < M * n := Nat.mul_pos hM hnpos
  set w := embY ell k Lu hell q with hw
  have hwOm : w ∈ S.Om k := embY_mem_Om hell hL hy0 hD
  set ρ := 6 * (M * n) - 1 with hρ
  have hη : (0 : ℝ) < ((ell : ℝ) ^ k)⁻¹ := by positivity
  -- the ball lies in Omega_{k-1}
  have hbs : bigSide M ell k = ell * bigSide M ell (k - 1) := by
    unfold bigSide
    have : ell ^ k = ell * ell ^ (k - 1) := by rw [← pow_succ']; congr 1; omega
    rw [this]; ring
  have hin : ∀ x ∈ Ball w ρ, x ∈ S.Om (k - 1) := by
    intro x hx
    by_contra hc
    have hw1 : w ∈ S.Om (k - 1 + 1) := by rw [Nat.sub_add_cancel hk]; exact hwOm
    have h5 := hS.2.2.2.2.1 (k - 1) (by omega) x hc w hw1
    have hx' : pdist w x ≤ ρ := hx
    rw [pdist_comm] at hx'
    have h6 : 6 * (ell * bigSide M ell (k - 1)) ≤ R * bigSide M ell (k - 1) := by
      rw [← Nat.mul_assoc]; exact Nat.mul_le_mul_right _ hR6
    have h7 : 6 * (ell * bigSide M ell (k - 1)) = 6 * (M * n) := by
      rw [← hbs]; rfl
    omega
  have hOm1 : S.Om (k + 1) = ∅ := hS.2.1 (k + 1) (by omega)
  have hOm2 : S.Om (k + 2) = ∅ := hS.2.1 (k + 2) (by omega)
  have hnw : ∀ σ : Fin 3, 2 * ρ + 2 ≤ scaleUp ell k Lu σ + 1 := by
    intro σ
    have := hthick σ
    have e : M * ell ^ k = M * n := rfl
    omega
  have hrc := hBall k le_rfl w ⟨w, hwOm, by rw [AdalyFormal.StatementLaneR8.pdist_self]; exact Nat.zero_le _⟩ ρ
    (by have : ρ ≤ 6 * (M * n) := by omega
        calc ρ ≤ 6 * (M * n) := this
          _ ≤ 7 * M * ell ^ k := by
            have : 6 * (M * n) ≤ 7 * (M * n) := by omega
            calc 6 * (M * n) ≤ 7 * (M * n) := this
              _ = 7 * M * ell ^ k := by rw [hn0]; ring)
    hnw hin (fun x _ h => by rw [hOm2] at h; exact h)
    (Or.inr (fun x _ h => by rw [hOm1] at h; exact h))
  have hik : k ≤ (k - 1) + 1 := by omega
  obtain ⟨g, V, hV, hag⟩ := regime_of_region (R := R) (ell := ell) (M := M) (f := 12) (k := k) (i := k - 1) hS hell (by norm_num) hM
    (by positivity : 0 < C * α₀) hη hik hrc (W := 64 * n) (r := r) (by omega)
    (by
      have : ell ^ (k - 1) ≤ ell ^ k := Nat.pow_le_pow_right hell (by omega)
      omega) (by omega)
  exact ⟨g, V, hV, fun x hx μ => (hag x hx μ).symm⟩

end AdalyFormal.M2UnitCharts

#print axioms AdalyFormal.M2UnitCharts.chart_of_ballU
