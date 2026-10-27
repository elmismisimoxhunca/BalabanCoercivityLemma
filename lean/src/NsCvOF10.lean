import NsCvOF9

/-!
# CvOF10 -- `genForm` of the Z-profile at a chain saddle (lane omega)
`genForm = eta*(c0*T1*qF_c(e) + Kc) - a*c0*T1*sum g^2` : the only `t`-dependence is `qF_c(e)`.
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace AdalyFormal.CoverOmega


set_option linter.unusedSectionVars false
variable [CfData]
open scoped Matrix RealInnerProductSpace
open Finset
open AdalyFormal.Target.ClayStatement
open AdalyFormal.CoverNested
open AdalyFormal.CoverJacobi
open AdalyFormal.Balaban.CovariantOperators (BondFnL2 SuTwo)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.StatementLane (scaleUp)
open AdalyFormal.StatementLaneG

variable {ell M R : ℕ}

theorem nested_genForm (hell3 : 3 ≤ ell) (hE : StagOK ell) (hdvd : ell ∣ M) (hM : 0 < M) (hR : 1 ≤ R) (a t : ℝ) (htπ : |t| < tcap ell)
    (hN : IsUnit (GenP.Nmat (Pn ell M R (by omega) a t))) (hG1 : IsUnit (Pn ell M R (by omega) a t).G1inv)
    (g : ℕ → ℝ) (hblk : ∀ q : ℕ, ∑ n ∈ Finset.range ell, g (ell * q + n) = 0) (e : Fin (nN ell M R) → ℝ)
    (hrad : ∀ d : Fin (nN ell M R) → ℝ, d ∈ Vsub (rowOfN ell M R) → BF (neC ell M R - neP0 ell M R) (Real.cos t) e d = 0)
    (hS : ∀ j, j ≤ 2 → ∀ r, isRowN ell M R j r → fSum ell j (fe (neP0 ell M R) e) r = (ell : ℝ) ^ j * rhoY ell g j r) :
    GenP.genForm (Pn ell M R (by omega) a t) (WithLp.toLp 2 (GenP.genC (Pn ell M R (by omega) a t) (zfun g))) =
      (Pn ell M R (by omega) a t).eta *
        (c0 * ((((scaleUp ell 2 (neLu M R)) 1 + 1) * ((scaleUp ell 2 (neLu M R)) 2 + 1) : ℕ) : ℝ) *
          qF (neC ell M R - neP0 ell M R) (Real.cos t) e + Kc ell M R a g) -
      a * (c0 * (((neLu M R 1 + 1) * (neLu M R 2 + 1) : ℕ) : ℝ) *
        ∑ v ∈ range (neLu M R 0 + 1), g v * g v) := by
  rw [Pn_genC hell3 hE hdvd hM hR a t htπ g hblk]
  have hz : GenP.genForm (Pn ell M R (by omega) a t) (WithLp.toLp 2 (zfun g)) =
      GenP.genForm (Pn ell M R (by omega) a t) (zfield g) := rfl
  rw [hz]
  unfold GenP.genForm
  rw [Pn_D2in hell3 hE hdvd hM hR a t htπ g, map_zero, inner_zero_left, mul_zero, sub_zero,
    nested_firstTerm hell3 hE hdvd hM hR a t htπ hN hG1 g e hrad hS, inner_zfield_zfield]


#print axioms nested_genForm

end AdalyFormal.CoverOmega
