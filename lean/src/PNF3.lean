import AdalyFormal.Balaban.DeltaPrime
import AdalyFormal.Balaban.RMapLipschitz
import AdalyFormal.Balaban.DeltaPrimeBound

/-!
# NF3 -- the EXACT curvature action `curl_U (D_U ν) = (R(h₁) - R(h₂)) ν(far corner)` made quantitative:
with `ζ` a bound on the plaquette defects `‖U(∂p) - 1‖_F`,  `Σ_p ‖curl_U D_U ν‖² ≤ 12 ζ² Σ_x ‖ν(x)‖²`.
(`curlValueCovariant_gradValueCovariant` is the tree's identity; the bound and the aggregation are new here.)
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace AdalyFormal.NonflatHunit

open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.CovariantOperators
open AdalyFormal.Balaban.DeltaPrime (holonomyElem)
open AdalyFormal.Balaban.RMapLipschitz (frobNorm)
open AdalyFormal.Balaban.CovariantHjMinimizer (periodicLatticeShiftEquiv)

variable {L : PeriodicLatticeExtent}

/-- far corner `x + e_μ + e_ν` of a plaquette -/
def farCorner (p : PeriodicLatticePlaquette L) : PeriodicLatticeSite L :=
  periodicLatticeShift (periodicLatticeShift p.1 p.2.1.1) p.2.1.2

theorem norm_curl_grad_le (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (lam : PeriodicLatticeSite L → SuTwo) (p : PeriodicLatticePlaquette L) :
    ‖curlValueCovariant U (gradValueCovariant U lam) p‖
      ≤ 2 * frobNorm ((holonomyElem U p : Matrix (Fin 2) (Fin 2) ℂ) - 1) * ‖lam (farCorner p)‖ := by
  rw [curlValueCovariant_gradValueCovariant]
  have e : U (p.1, p.2.1.1) * U (periodicLatticeShift p.1 p.2.1.1, p.2.1.2)
      = holonomyElem U p * (U (p.1, p.2.1.2) * U (periodicLatticeShift p.1 p.2.1.2, p.2.1.1)) := by
    unfold holonomyElem AdalyFormal.Target.ClayStatement.periodicPlaquetteHolonomy
    group
  rw [e, ← RMap_mul_apply]
  have h := AdalyFormal.Balaban.RMapLipschitz.norm_RMap_sub_self_le (holonomyElem U p)
    (RMap (U (p.1, p.2.1.2) * U (periodicLatticeShift p.1 p.2.1.2, p.2.1.1)) (lam (farCorner p)))
  rw [AdalyFormal.Balaban.AlphaAnalyticity.norm_RMap] at h
  exact h

#print axioms norm_curl_grad_le

theorem card_dirs : Fintype.card PeriodicPlaquetteDirections = 3 := by decide

/-- `Σ_p ‖ν(far corner of p)‖² = 3 Σ_x ‖ν x‖²` (each direction pair: the double shift is a bijection). -/
theorem sum_farCorner_sq (lam : PeriodicLatticeSite L → SuTwo) :
    ∑ p : PeriodicLatticePlaquette L, ‖lam (farCorner p)‖ ^ 2 = 3 * ∑ x : PeriodicLatticeSite L, ‖lam x‖ ^ 2 := by
  rw [Fintype.sum_prod_type_right]
  have h : ∀ d : PeriodicPlaquetteDirections,
      ∑ x : PeriodicLatticeSite L, ‖lam (farCorner (x, d))‖ ^ 2 = ∑ x : PeriodicLatticeSite L, ‖lam x‖ ^ 2 := by
    intro d
    exact Equiv.sum_comp ((periodicLatticeShiftEquiv (L := L) d.1.1).trans
      (periodicLatticeShiftEquiv (L := L) d.1.2)) (fun y => ‖lam y‖ ^ 2)
  rw [Finset.sum_congr rfl (fun d _ => h d), Finset.sum_const, Finset.card_univ, card_dirs]
  simp

theorem sum_norm_sq_curl_grad_le (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (lam : PeriodicLatticeSite L → SuTwo) {ζ : ℝ} (hζ0 : 0 ≤ ζ)
    (hζ : ∀ p : PeriodicLatticePlaquette L, frobNorm ((holonomyElem U p : Matrix (Fin 2) (Fin 2) ℂ) - 1) ≤ ζ) :
    ∑ p : PeriodicLatticePlaquette L, ‖curlValueCovariant U (gradValueCovariant U lam) p‖ ^ 2
      ≤ 12 * ζ ^ 2 * ∑ x : PeriodicLatticeSite L, ‖lam x‖ ^ 2 := by
  have hpt : ∀ p : PeriodicLatticePlaquette L,
      ‖curlValueCovariant U (gradValueCovariant U lam) p‖ ^ 2 ≤ 4 * ζ ^ 2 * ‖lam (farCorner p)‖ ^ 2 := by
    intro p
    have h1 := norm_curl_grad_le U lam p
    have h2 : 2 * frobNorm ((holonomyElem U p : Matrix (Fin 2) (Fin 2) ℂ) - 1) ≤ 2 * ζ :=
      by linarith [hζ p]
    have h3 : 2 * frobNorm ((holonomyElem U p : Matrix (Fin 2) (Fin 2) ℂ) - 1) * ‖lam (farCorner p)‖
        ≤ 2 * ζ * ‖lam (farCorner p)‖ := mul_le_mul_of_nonneg_right h2 (norm_nonneg _)
    have h4 := h1.trans h3
    have h5 := pow_le_pow_left₀ (norm_nonneg _) h4 2
    calc _ ≤ (2 * ζ * ‖lam (farCorner p)‖) ^ 2 := h5
      _ = 4 * ζ ^ 2 * ‖lam (farCorner p)‖ ^ 2 := by ring
  calc _ ≤ ∑ p : PeriodicLatticePlaquette L, 4 * ζ ^ 2 * ‖lam (farCorner p)‖ ^ 2 :=
        Finset.sum_le_sum (fun p _ => hpt p)
    _ = 4 * ζ ^ 2 * (3 * ∑ x : PeriodicLatticeSite L, ‖lam x‖ ^ 2) := by
        rw [← Finset.mul_sum, sum_farCorner_sq]
    _ = 12 * ζ ^ 2 * ∑ x : PeriodicLatticeSite L, ‖lam x‖ ^ 2 := by ring

#print axioms sum_farCorner_sq
#print axioms sum_norm_sq_curl_grad_le

end AdalyFormal.NonflatHunit
