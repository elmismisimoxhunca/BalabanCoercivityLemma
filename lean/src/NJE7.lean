import NJE6
import NJ9dQ124
import NJ9cBase

/-!
# NJE7 -- THE LEVEL JET = COVARIANT MAIN TERM + REMAINDER, for the genuine composite `Q_{j+1}(U) = Q(Ū^j) Q_j(U)` (3.15):
with `Y = D(qCompX_j)(0) a` (level-`j` output), `V = (Ū^j)|_{stride-ell^j sublattice}`,
`‖ ell⁻¹ D(qCompX_{j+1})(0) a (embE c) - T1(V)(Y|_sublattice)(c) ‖ ≤ 8 κ M`, `κ = e2Majorant ρ(ell, ε_j)`.
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
open AdalyFormal.Balaban.AdmissibleSubspace (CoarseLattice)
open AdalyFormal.Balaban.QjComposite (stepBlockOf)
open AdalyFormal.Balaban.TowerLawCov (unitToCoarseCov)
open AdalyFormal.Balaban.RMapLipschitz (frobNorm)
open AdalyFormal.DeltaKR85 (q124Principal)
open AdalyFormal.IngredientFamilyR2
open EstimatesLayer.E1E3
local instance : NormedSpace ℝ SuTwo := instInnerProductSpaceSuTwo.toNormedSpace

variable {L Lq : PeriodicLatticeExtent}

/-- the su(2)-element of a coordinate vector. -/
def suOf (v : Fin 3 → ℝ) : SuTwo := ⟨toM2 v, toM2_mem v⟩

theorem level_jet_sub_T1_le (ell : ℕ) (bg : ℕ → PeriodicLinkConfiguration SU2 L) (J : ℕ)
    (hreg : RegTower ell bg J) (j : ℕ) (hj : j < J)
    (hs : ∀ μ, L μ + 1 = ell ^ j * (Lq μ + 1)) (hell : 0 < ell)
    (hdvd : ∀ μ : Fin 3, ell ∣ (Lq μ + 1)) (ε0 : ℝ) (hε0 : 0 ≤ ε0)
    (hV : ∀ e, frobNorm (((resV hs (bg j)) e : M2) - 1) ≤ ε0) (hsmall : rhoOf ell ε0 < Real.pi / 2)
    (a : XS L) (M : ℝ) (hM : 0 ≤ M)
    (hY : ∀ e, ‖suOf (resA hs (QlinCompX ell bg j a) e)‖ ≤ M) (c : CoarseBond Lq ell) :
    ‖suOf ((ell : ℝ)⁻¹ • QlinCompX ell bg (j + 1) a (embE hs (c.1.1, c.2)))
        - unitToCoarseCov 1 ell (resV hs (bg j))
            (fun b : CoarseBond Lq 1 => suOf (resA hs (QlinCompX ell bg j a) (b.1.1, b.2)))
            (⟨⟨c.1.1, by rw [one_mul]; exact c.1.2⟩, c.2⟩ : CoarseBond Lq (1 * ell))‖
      ≤ 8 * e2Majorant (rhoOf ell ε0) * M := by
  set Y := resA hs (QlinCompX ell bg j a) with hYdef
  have hjet := QlinCompX_succ_apply_emb ell bg J hreg j hj hs hell hdvd (c.1.1, c.2) c.1.2
    (fun x hx => guard_of_small (resV hs (bg j)) ε0 hε0 hV hsmall c x hx) a
  have hq := q124_sub_T1_le hell hdvd (resV hs (bg j)) ε0 hε0 hV hsmall
    (fun b : CoarseBond Lq 1 => suOf (Y (b.1.1, b.2))) M hM (fun b => hY _)
    (⟨⟨c.1.1, by rw [one_mul]; exact c.1.2⟩, c.2⟩ : CoarseBond Lq (1 * ell))
  have hA : fineDirToUnitBond (fun e => toM2 (Y e)) (fun e => (toM2_mem (Y e)).1)
      (fun e => (toM2_mem (Y e)).2) = fun b : CoarseBond Lq 1 => suOf (Y (b.1.1, b.2)) := rfl
  rw [hA] at hjet
  have hX : suOf ((ell : ℝ)⁻¹ • QlinCompX ell bg (j + 1) a (embE hs (c.1.1, c.2)))
      = q124Principal 1 ell (resV hs (bg j)) (fun b : CoarseBond Lq 1 => suOf (Y (b.1.1, b.2)))
          (⟨⟨c.1.1, by rw [one_mul]; exact c.1.2⟩, c.2⟩ : CoarseBond Lq (1 * ell)) := by
    apply Subtype.ext
    show toM2 _ = _
    rw [hjet, map_smul, map_smul, smul_smul, inv_mul_cancel₀ (by exact_mod_cast hell.ne'), one_smul]
    exact toM2_fromM2 (q124Principal 1 ell (resV hs (bg j)) (fun b : CoarseBond Lq 1 => suOf (Y (b.1.1, b.2)))
          (⟨⟨c.1.1, by rw [one_mul]; exact c.1.2⟩, c.2⟩ : CoarseBond Lq (1 * ell))).2
  rw [hX]
  exact hq

#print axioms level_jet_sub_T1_le

end AdalyFormal.NonflatJet
