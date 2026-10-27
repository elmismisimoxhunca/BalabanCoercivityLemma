import NJE7
import NJL2m

/-!
# NJE8 -- THE LEVEL JET, VOLUME-FREE `L²` FORM: for the genuine composite `Q_{j+1}(U) = Q(Ū^j) Q_j(U)` (3.15),
`Σ_{c} ‖ ell⁻¹ D(qCompX_{j+1})(0) a (embE c) - T1(V)(Y|_sublattice)(c) ‖² ≤ 240 κ² Σ_e ‖Y(embE e)‖²`.
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
namespace AdalyFormal.NonflatJet

open Matrix
open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.SuTwoLogExp (SU2 M2 su2NegOne)
open AdalyFormal.Balaban.CovariantOperators (SuTwo)
open AdalyFormal.Balaban.SuTwoInner
open AdalyFormal.Balaban.LatticeOperators (CoarseBond)
open AdalyFormal.Balaban.TowerLawCov (unitToCoarseCov)
open AdalyFormal.Balaban.RMapLipschitz (frobNorm)
open AdalyFormal.DeltaKR85 (q124Principal q124Principal_eq_unitToCoarseCov_add_delta)
open AdalyFormal.IngredientFamilyR2
open EstimatesLayer.E1E3
open OneStep124 (delta124)
local instance : NormedSpace ℝ SuTwo := instInnerProductSpaceSuTwo.toNormedSpace

variable {L Lq : PeriodicLatticeExtent}

theorem level_jet_sub_T1_l2 (ell : ℕ) (bg : ℕ → PeriodicLinkConfiguration SU2 L) (J : ℕ)
    (hreg : RegTower ell bg J) (j : ℕ) (hj : j < J)
    (hs : ∀ μ, L μ + 1 = ell ^ j * (Lq μ + 1)) (hell : 0 < ell)
    (hdvd : ∀ μ : Fin 3, ell ∣ (Lq μ + 1)) (ε0 : ℝ) (hε0 : 0 ≤ ε0)
    (hV : ∀ e, frobNorm (((resV hs (bg j)) e : M2) - 1) ≤ ε0) (hsmall : rhoOf ell ε0 < Real.pi / 2)
    (a : XS L) :
    ∑ c : CoarseBond Lq ell,
        ‖suOf ((ell : ℝ)⁻¹ • QlinCompX ell bg (j + 1) a (embE hs (c.1.1, c.2)))
          - unitToCoarseCov 1 ell (resV hs (bg j))
              (fun b : CoarseBond Lq 1 => suOf (resA hs (QlinCompX ell bg j a) (b.1.1, b.2)))
              (cbEquiv ell c)‖ ^ 2
      ≤ 240 * (e2Majorant (rhoOf ell ε0)) ^ 2 *
          ∑ e : PeriodicLatticeEdge Lq, ‖suOf (resA hs (QlinCompX ell bg j a) e)‖ ^ 2 := by
  set Y := resA hs (QlinCompX ell bg j a) with hYdef
  set A : CoarseBond Lq 1 → SuTwo := fun b => suOf (Y (b.1.1, b.2)) with hAdef
  have hk : 0 ≤ e2Majorant (rhoOf ell ε0) := e2Majorant_nonneg (by unfold rhoOf; positivity)
  have hE : ∀ c : CoarseBond Lq (1 * ell), _ := fun c => E_bounds hell hdvd (resV hs (bg j)) ε0 hε0 hV hsmall c
  have hL2 := delta124_l2 hell (resV hs (bg j))
    (AdalyFormal.DeltaKR85.Coeff124.ofPrincipalBackground 1 ell (resV hs (bg j)))
    (e2Majorant (rhoOf ell ε0)) hk (fun c => (hE c).1) (fun c => (hE c).2.1) (fun c => (hE c).2.2) A
  have hEq := Equiv.sum_comp (cbEquiv ell) (fun c' : CoarseBond Lq (1 * ell) =>
    ‖delta124 1 ell (resV hs (bg j))
      (AdalyFormal.DeltaKR85.Coeff124.ofPrincipalBackground 1 ell (resV hs (bg j))) A c'‖ ^ 2)
  rw [← hEq] at hL2
  have hl1 : l1 (gA A) = ∑ e : PeriodicLatticeEdge Lq, ‖suOf (Y e)‖ ^ 2 := rfl
  rw [hl1] at hL2
  refine le_trans (le_of_eq ?_) hL2
  refine Finset.sum_congr rfl (fun c _ => ?_)
  congr 1
  have hjet := QlinCompX_succ_apply_emb ell bg J hreg j hj hs hell hdvd (c.1.1, c.2) c.1.2
    (fun x hx => guard_of_small (resV hs (bg j)) ε0 hε0 hV hsmall c x hx) a
  have hX : suOf ((ell : ℝ)⁻¹ • QlinCompX ell bg (j + 1) a (embE hs (c.1.1, c.2)))
      = q124Principal 1 ell (resV hs (bg j)) A (cbEquiv ell c) := by
    apply Subtype.ext
    show toM2 _ = _
    rw [hjet, map_smul, map_smul, smul_smul, inv_mul_cancel₀ (by exact_mod_cast hell.ne'), one_smul]
    exact toM2_fromM2 (q124Principal 1 ell (resV hs (bg j)) A (cbEquiv ell c)).2
  rw [hX, q124Principal_eq_unitToCoarseCov_add_delta, add_sub_cancel_left]

#print axioms level_jet_sub_T1_l2

end AdalyFormal.NonflatJet
