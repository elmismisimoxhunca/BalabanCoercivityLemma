import CvOF5

/-!
# CvOF6 -- `Q x = y`, `N v = y`, `N⁻¹ y = v` for the chain saddle (lane omega)
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace AdalyFormal.CoverOmega

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

/-- the row field of the unit field `zfield g` at the top level. -/
def rhoY (ell : ℕ) (g : ℕ → ℝ) : ℕ → ℕ → ℝ := fun j r => if j = 2 then g (r / ell ^ 2) else 0

variable {ell M R : ℕ}

theorem Pn_tau_adjoint (hell3 : 3 ≤ ell) (hdvd : ell ∣ M) (hM : 0 < M) (hR : 1 ≤ R) (a t : ℝ) (g : ℕ → ℝ) :
    ContinuousLinearMap.adjoint (Pn ell M R (by omega) a t).tau (zfield g) = zrow (Pn ell M R (by omega) a t).G (rhoY ell g) := by
  have hg := nGeo hell3 hdvd hM hR
  have := tau_adjoint_zfield ell 2 (neLu M R) (by omega) (neS ell M R)
    (fun b hb => crs_of_bondsLam hg hM (by norm_num) b hb) g
  exact this

/-- `Q x = y`. -/
theorem nested_Q_eq (hell3 : 3 ≤ ell) (hE : 2 ∣ ell) (hdvd : ell ∣ M) (hM : 0 < M) (hR : 1 ≤ R) (a t : ℝ) (htπ : |t| < Real.pi)
    (g : ℕ → ℝ) (e : Fin (nN ell M R) → ℝ)
    (hS : ∀ j, j ≤ 2 → ∀ r, isRowN ell M R j r → fSum ell j (fe (neP0 ell M R) e) r = (ell : ℝ) ^ j * rhoY ell g j r) :
    QfullOf (Pn ell M R (by omega) a t).G (stagCfg (neC ell M R) t) (zfield (fe (neP0 ell M R) e)) =
      zrow (Pn ell M R (by omega) a t).G (rhoY ell g) := by
  have hg := nGeo hell3 hdvd hM hR
  have hell : 0 < ell := by omega
  have S := nested_stagSetup hell3 hE hdvd hM hR
  rw [Qfull_zfield_eq_zrow S t htπ]
  refine PiLp.ext (fun p => ?_)
  show (if p.2.1.2 = 1 then dgS (((ell : ℝ) ^ (p.1 : ℕ))⁻¹ * fSum ell (p.1 : ℕ) (fe (neP0 ell M R) e) (p.2.1.1 0).val) else 0) =
    (if p.2.1.2 = 1 then dgS (rhoY ell g (p.1 : ℕ) (p.2.1.1 0).val) else 0)
  by_cases h1 : p.2.1.2 = 1
  · rw [if_pos h1, if_pos h1]
    congr 1
    have hj : (p.1 : ℕ) ≤ 2 := by have := p.1.2; simp [geomOf] at this ⊢; omega
    have hmem : (p.2.1.1, (1 : Fin 3)) ∈ bondsLam (geomOf ell 2 (neS ell M R)) (p.1 : ℕ) := by
      have := p.2.2
      have hq : ((p.2.1.1, (1 : Fin 3))) = p.2.1 := Prod.ext rfl h1.symm
      rw [hq]
      exact this
    have hrow := ((bondsLam_one_iff hg hM hj p.2.1.1).mp hmem).2
    rw [hS _ hj _ hrow]
    have : (ell : ℝ) ^ (p.1 : ℕ) ≠ 0 := pow_ne_zero _ (by exact_mod_cast hell.ne')
    field_simp
  · rw [if_neg h1, if_neg h1]

#print axioms nested_Q_eq

end AdalyFormal.CoverOmega
