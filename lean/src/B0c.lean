import B0b
import SmoothLog

/-!
# B0c -- first-order jet of one level of the pure-gauge propagation (`t ↦ nextG s ell V (γ t) y` at `t = 0`)

For a gauge curve `γ : ℝ → sites → SU(2)` with `γ 0 = 1` near `y` and derivatives `ν x` (anti-Hermitian) at the
sites of the strided block `B = stepBlockOf y s ell` and at `y`:
* `rProd_pgV`: `rProd s V (pgV s V γ) y Γ_{y,x} = γ(y) H γ(x)⁻¹ H⁻¹`, `H = V(Γ_{y,x})`, for `x ∈ B` (exact).
* `hasDerivAt_logLoop`: `d/dt su2Log(rProd …)|₀ = ν y - H (ν x) Hᴴ`.
* `hasDerivAt_nextG`: `d/dt (nextG s ell V (γ t) y : M2)|₀ = (Σ_{x∈B} ℓ⁻³ (ν y - H ν x Hᴴ))ᴴ + ν y`.
Also `antiHerm_of_hasDerivAt`: the velocity at `1` of an `SU(2)`-valued curve is anti-Hermitian.
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace AdalyFormal.SliceCoerc

open scoped Matrix Matrix.Norms.Frobenius
open AdalyFormal.Target.ClayStatement
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Balaban.SuTwoLogExp (su2LogExp su2Log su2Exp M2 SU2 su2Log_one su2Exp_zero
  su2Log_antiHermitian su2Log_traceless mul_star_self star_mul_self)
open AdalyFormal.Balaban.CovariantOperators (suTwo mem_suTwo_iff)
open AdalyFormal.Balaban.SmoothLog (Lg Lg_hasStrictFDerivAt su2Log_comp_eventuallyEq
  exp_hasFDerivAt_zero su2Exp_coe_of_mem_suTwo)
open AdalyFormal.Balaban.QjComposite (stepBlockOf mem_stepBlockOf coarsePathHolonomy_coarseGaugeTransform
  coarsePathEndpoint_coarseGammaPath)
open AdalyFormal.Balaban.TowerLawCov (coarsePathHolonomy coarseGammaPath)
open Filter Topology

variable {L : PeriodicLatticeExtent}

theorem hasDerivAt_su2Log_comp (G : ℝ → SU2) (v : M2)
    (hG : HasDerivAt (fun t => (G t : M2)) v 0) (hG0 : G 0 = 1) :
    HasDerivAt (fun t => su2Log (G t)) v 0 := by
  have hL : HasFDerivAt Lg (ContinuousLinearMap.id ℝ M2) ((G 0 : SU2) : M2) := by
    rw [hG0]; exact Lg_hasStrictFDerivAt.hasFDerivAt
  have h := hL.comp_hasDerivAt (0 : ℝ) hG
  exact h.congr_of_eventuallyEq (su2Log_comp_eventuallyEq G hG.continuousAt hG0)

/-- velocity at `1` of an `SU(2)`-curve is anti-Hermitian. -/
theorem antiHerm_of_hasDerivAt (G : ℝ → SU2) (v : M2)
    (hG : HasDerivAt (fun t => (G t : M2)) v 0) (hG0 : G 0 = 1) : vᴴ = -v := by
  have hs : HasDerivAt (fun t => ((G t : SU2) : M2)ᴴ) vᴴ 0 := by
    have := hG.star; exact this
  have hp := hs.fun_mul hG
  have hc : (fun t => ((G t : SU2) : M2)ᴴ * ((G t : SU2) : M2)) = fun _ => (1 : M2) := by
    funext t; exact star_mul_self (G t)
  rw [hc] at hp
  have h0 := hp.unique (hasDerivAt_const (0 : ℝ) (1 : M2))
  rw [hG0] at h0
  simp only [OneMemClass.coe_one, Matrix.conjTranspose_one, Matrix.one_mul, Matrix.mul_one] at h0
  exact eq_neg_of_add_eq_zero_left h0

theorem rProd_pgV (s ell : ℕ) (V : PeriodicLinkConfiguration SU2 L) (γ : PeriodicLatticeSite L → SU2)
    (y x : PeriodicLatticeSite L) (hx : x ∈ stepBlockOf y s ell) :
    rProd s V (pgV s V γ) y (coarseGammaPath s y x)
      = γ y * coarsePathHolonomy s V y (coarseGammaPath s y x) * (γ x)⁻¹
        * (coarsePathHolonomy s V y (coarseGammaPath s y x))⁻¹ := by
  have hx' := mem_stepBlockOf.mp hx
  have hend := coarsePathEndpoint_coarseGammaPath (s := s) (y := y) (x := x)
    (fun μ => ⟨(hx' μ).1, (hx' μ).2.2⟩)
  rw [rProd_eq, pgV_mul, coarsePathHolonomy_coarseGaugeTransform, hend]

theorem hasDerivAt_logLoop (s ell : ℕ) (V : PeriodicLinkConfiguration SU2 L)
    (γ : ℝ → PeriodicLatticeSite L → SU2) (ν : PeriodicLatticeSite L → M2)
    (y x : PeriodicLatticeSite L) (hx : x ∈ stepBlockOf y s ell)
    (h0y : γ 0 y = 1) (h0x : γ 0 x = 1)
    (hdy : HasDerivAt (fun t => (γ t y : M2)) (ν y) 0) (hdx : HasDerivAt (fun t => (γ t x : M2)) (ν x) 0)
    (hah : (ν x)ᴴ = -ν x) :
    HasDerivAt (fun t => su2Log (rProd s V (pgV s V (γ t)) y (coarseGammaPath s y x)))
      (ν y - ((coarsePathHolonomy s V y (coarseGammaPath s y x) : SU2) : M2) * ν x
        * ((coarsePathHolonomy s V y (coarseGammaPath s y x) : SU2) : M2)ᴴ) 0 := by
  set H := coarsePathHolonomy s V y (coarseGammaPath s y x) with hH
  have hfun : (fun t => su2Log (rProd s V (pgV s V (γ t)) y (coarseGammaPath s y x)))
      = fun t => su2Log (γ t y * H * (γ t x)⁻¹ * H⁻¹) := by
    funext t; rw [rProd_pgV s ell V (γ t) y x hx]
  rw [hfun]
  apply hasDerivAt_su2Log_comp (fun t => γ t y * H * (γ t x)⁻¹ * H⁻¹)
  · have hxs : HasDerivAt (fun t => ((γ t x : SU2) : M2)ᴴ) (ν x)ᴴ 0 := by
      have := hdx.star; exact this
    have h1 := ((hdy.fun_mul (hasDerivAt_const (0 : ℝ) (H : M2))).fun_mul hxs).fun_mul
      (hasDerivAt_const (0 : ℝ) ((H : M2)ᴴ))
    have hHH : (H : M2) * (H : M2)ᴴ = 1 := mul_star_self H
    refine h1.congr_deriv ?_
    rw [h0y, h0x, hah]
    simp only [OneMemClass.coe_one, Matrix.conjTranspose_one, Matrix.one_mul, Matrix.mul_one, mul_zero,
      add_zero, zero_mul]
    rw [add_mul, Matrix.mul_assoc (ν y), hHH, Matrix.mul_one]
    noncomm_ring
  · rw [h0y, h0x]; group

#print axioms hasDerivAt_su2Log_comp
#print axioms antiHerm_of_hasDerivAt
#print axioms rProd_pgV
#print axioms hasDerivAt_logLoop

end AdalyFormal.SliceCoerc
