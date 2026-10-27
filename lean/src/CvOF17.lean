import CvOF16

/-!
# CvOF17 -- core: `genForm < 0` along the staggered path near the crossing, given the two units (lane omega)
-/
set_option autoImplicit false
set_option maxHeartbeats 8000000

namespace AdalyFormal.CoverOmega

open scoped Matrix RealInnerProductSpace
open Finset
open AdalyFormal.Target.ClayStatement
open AdalyFormal.CoverNested
open AdalyFormal.CoverJacobi
open AdalyFormal.StatementLane (scaleUp)
open AdalyFormal.StatementLane
open AdalyFormal.StatementLane2
open AdalyFormal.StatementLaneG
open AdalyFormal.IngredientFamilyR2

variable {ell M R : ℕ}

theorem nested_genForm_neg (hell3 : 3 ≤ ell) (hE : 2 ∣ ell) (hdvd : ell ∣ M) (hMe : ell ≤ M) (hM : 0 < M) (hR : 1 ≤ R) (a : ℝ) :
    ∃ cs : ℝ, -1 < cs ∧ cs < 1 ∧ IsCrossingN ell M R cs ∧ ∃ p : ℕ, p ≤ 1 ∧ ∃ ε : ℝ, 0 < ε ∧ ∀ t : ℝ, |t| < Real.pi → cs < Real.cos t → Real.cos t < cs + ε →
      IsUnit (GenP.Nmat (Pn ell M R (by omega) a t)) → IsUnit (Pn ell M R (by omega) a t).G1inv →
      GenP.genForm (Pn ell M R (by omega) a t) (WithLp.toLp 2 (GenP.genC (Pn ell M R (by omega) a t) (zfun (gU M R p)))) < 0 := by
  have hg := nGeo hell3 hdvd hM hR
  obtain ⟨cs, h1, h2, hcr, i1, p, hp, hp1, hi1, hst, hln, hex⟩ := nested_Zchain hg hell3 hMe
  have hell : 0 < ell := by omega
  have hη : 0 < (((ell : ℝ) ^ 2)⁻¹) := by positivity
  set T1 : ℝ := ((((scaleUp ell 2 (neLu M R)) 1 + 1) * ((scaleUp ell 2 (neLu M R)) 2 + 1) : ℕ) : ℝ) with hT1
  set T2 : ℝ := (((neLu M R 1 + 1) * (neLu M R 2 + 1) : ℕ) : ℝ) with hT2
  have hT1p : 0 < T1 := by rw [hT1]; positivity
  have hAp : 0 < (((ell : ℝ) ^ 2)⁻¹) * (c0 * T1) := mul_pos hη (mul_pos c0_pos hT1p)
  set Kc' : ℝ := (((ell : ℝ) ^ 2)⁻¹) * Kc ell M R a (gU M R p) - a * (c0 * T2 * ∑ v ∈ range (neLu M R 0 + 1), gU M R p v * gU M R p v) with hKc'
  obtain ⟨ε, hε, hbl⟩ := hex ((-1 - Kc') / ((((ell : ℝ) ^ 2)⁻¹) * (c0 * T1)))
  refine ⟨cs, h1, h2, hcr, p, hp1, ε, hε, fun t htπ hc1 hc2 hN hG1 => ?_⟩
  obtain ⟨e, hrad, hS, hq⟩ := hbl (Real.cos t) hc1 hc2 (Real.cos_le_one t)
  have hgf := nested_genForm hell3 hE hdvd hM hR a t htπ hN hG1 (gU M R p) (gU_block hE hell3 hdvd hp1) e hrad hS
  rw [hgf]
  have hη' : (Pn ell M R (by omega) a t).eta = (((ell : ℝ) ^ 2)⁻¹) := rfl
  rw [hη']
  have := (lt_div_iff₀ hAp).mp hq
  nlinarith

#print axioms nested_genForm_neg

end AdalyFormal.CoverOmega
