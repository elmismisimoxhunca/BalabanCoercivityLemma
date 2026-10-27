import MA5
import TL6b
import MI20

/-!
# MA6 -- weighted-norm bookkeeping and the top-row drift (lane m1_assembly_20261014)
-/
set_option autoImplicit false
set_option maxRecDepth 8000
set_option maxHeartbeats 8000000
set_option synthInstance.maxHeartbeats 400000
namespace AdalyFormal.M1Assembly

open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane (Tower scaleUp)
open AdalyFormal.StatementLaneG (gparams pe tauAdj_apply pe_injective)
open AdalyFormal.GenuineU1 (bondsE)
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.CovariantHjMinimizer (trivialU)
open AdalyFormal.Balaban.LineIntegralCovariant (lineCoarseRestrictSuTwo)
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)

/-- `||y||^2 <= (ell^k)^2 wnormSq y`: every weight is at least `ell^{-2k}`. -/
theorem normSq_le_wnorm {ell k : ℕ} (hell : 1 ≤ ell) {L : PeriodicLatticeExtent} (S : Tower L) (y : BondFnL2 L) :
    ‖y‖ ^ 2 ≤ ((ell : ℝ) ^ k) ^ 2 * AdalyFormal.M1.wnormSq S ell k y := by
  rw [PiLp.norm_sq_eq_of_L2]
  unfold AdalyFormal.M1.wnormSq
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum (fun b _ => ?_)
  have hr : (1 : ℝ) ≤ ell := by exact_mod_cast hell
  have h1 : (ell : ℝ) ^ AdalyFormal.M1.bstrat S k b ≤ (ell : ℝ) ^ k :=
    pow_le_pow_right₀ hr (AdalyFormal.M1.bstrat_le S k b)
  have hp : (0 : ℝ) < (ell : ℝ) ^ AdalyFormal.M1.bstrat S k b := by positivity
  have h2 : (((ell : ℝ) ^ k) ^ 2) * (((ell : ℝ) ^ AdalyFormal.M1.bstrat S k b)⁻¹) ^ 2 ≥ 1 := by
    rw [← mul_pow]
    have : 1 ≤ (ell : ℝ) ^ k * ((ell : ℝ) ^ AdalyFormal.M1.bstrat S k b)⁻¹ := by
      rw [← div_eq_mul_inv, le_div_iff₀ hp]; linarith
    nlinarith
  have h3 : 0 ≤ ‖(WithLp.ofLp y) b‖ ^ 2 := sq_nonneg _
  nlinarith

open Classical in
/-- the top-level rows of the unit bonds in `E` carry the drift: `n^3 sum_{b in E} |Bf b - B b|^2 <= sum_p wF p |Q^U y p - Q^1 y p|^2`. -/
theorem rows_drift {ell k : ℕ} {Lu : PeriodicLatticeExtent} (hell : 0 < ell) (S : Tower (scaleUp ell k Lu))
    (V : LinkCfg (scaleUp ell k Lu)) (a : ℝ) (Lam : Set (PeriodicLatticeSite Lu))
    (y : BondFnL2 (scaleUp ell k Lu)) (B : BondFnL2 Lu)
    (hQ : (bondSectorOf (geomOf ell k S) V).Qfull y = ContinuousLinearMap.adjoint (gparams ell k Lu hell S V a Lam).tau B)
    (E : Finset (Bond Lu)) (hE : ∀ b ∈ E, unitBondEmb ell k Lu hell b ∈ bondsLam (geomOf ell k S) k) :
    ((ell : ℝ) ^ k) ^ 3 * ∑ b ∈ E, ‖lineCoarseRestrictSuTwo (ell ^ k) (WithLp.ofLp y) (bondsE ell k Lu hell b)
          - (WithLp.ofLp B) b‖ ^ 2
      ≤ ∑ p, AdalyFormal.W6.wF p * ‖(WithLp.ofLp ((bondSectorOf (geomOf ell k S) V).Qfull y)) p
          - (WithLp.ofLp ((bondSectorOf (geomOf ell k S) (trivialU _)).Qfull y)) p‖ ^ 2 := by
  set P := gparams ell k Lu hell S V a Lam with hP
  set Pf : IngrBParams := { P with U := flatCfg } with hPf
  set g : BIdx (geomOf ell k S) → ℝ := fun p => AdalyFormal.W6.wF p *
      ‖(WithLp.ofLp ((bondSectorOf (geomOf ell k S) V).Qfull y)) p
          - (WithLp.ofLp ((bondSectorOf (geomOf ell k S) (trivialU _)).Qfull y)) p‖ ^ 2 with hg
  have hnn : ∀ p, 0 ≤ g p := fun p => by
    have : 0 ≤ AdalyFormal.W6.wF p := by unfold AdalyFormal.W6.wF; positivity
    exact mul_nonneg this (sq_nonneg _)
  set f : E → BIdx (geomOf ell k S) := fun b => pe P b.1 (hE b.1 b.2) with hf
  have hfinj : Function.Injective f := fun b b' h =>
    Subtype.ext (pe_injective P b.1 b'.1 (hE b.1 b.2) (hE b'.1 b'.2) h)
  have hterm : ∀ b : E, ((ell : ℝ) ^ k) ^ 3 * ‖lineCoarseRestrictSuTwo (ell ^ k) (WithLp.ofLp y) (bondsE ell k Lu hell b.1)
          - (WithLp.ofLp B) b.1‖ ^ 2 = g (f b) := by
    intro b
    have h1 := AdalyFormal.FlatEllGeneral.Qfull_top_gen Pf rfl y b.1 (hE b.1 b.2)
    have h2 := tauAdj_apply P B b.1 (hE b.1 b.2)
    have h3 : (WithLp.ofLp ((bondSectorOf (geomOf ell k S) V).Qfull y)) (pe P b.1 (hE b.1 b.2)) = (WithLp.ofLp B) b.1 := by
      rw [hQ]; exact h2
    have h4 : (WithLp.ofLp ((bondSectorOf (geomOf ell k S) (trivialU _)).Qfull y)) (pe P b.1 (hE b.1 b.2))
        = lineCoarseRestrictSuTwo (ell ^ k) (WithLp.ofLp y) (bondsE ell k Lu hell b.1) := h1
    show _ = AdalyFormal.W6.wF (pe P b.1 (hE b.1 b.2)) * ‖_ - _‖ ^ 2
    rw [h3, h4]
    have hw : AdalyFormal.W6.wF (pe P b.1 (hE b.1 b.2)) = ((ell : ℝ) ^ k) ^ 3 := by
      unfold AdalyFormal.W6.wF pe
      simp
      rfl
    rw [hw, norm_sub_rev]
  have hs1 : ∑ b : E, g (f b) ≤ ∑ p, g p := by
    have himg : (∑ p ∈ (Finset.univ : Finset E).image f, g p) = ∑ b : E, g (f b) :=
      Finset.sum_image (fun a _ b _ h => hfinj h)
    rw [← himg]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun p _ _ => hnn p)
  have hs2 : ((ell : ℝ) ^ k) ^ 3 * ∑ b ∈ E, ‖lineCoarseRestrictSuTwo (ell ^ k) (WithLp.ofLp y) (bondsE ell k Lu hell b)
          - (WithLp.ofLp B) b‖ ^ 2 = ∑ b : E, g (f b) := by
    rw [Finset.mul_sum, ← Finset.sum_coe_sort E]
    exact Finset.sum_congr rfl (fun b _ => hterm b)
  rw [hs2]
  exact hs1

end AdalyFormal.M1Assembly

#print axioms AdalyFormal.M1Assembly.normSq_le_wnorm
#print axioms AdalyFormal.M1Assembly.rows_drift
