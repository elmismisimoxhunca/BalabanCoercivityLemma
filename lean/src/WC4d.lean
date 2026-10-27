import WC4c

/-!
# WC4d -- `T = Q_U ∘ EU = I + N + S` (M2 W6 lane)
`Tlin = Q_U ∘ EU`, `Sfun y p' = Σ_p Ad(γ_p z_p')⁻¹ ( (Q_{V_p} - Q₁) ψ_p (Ad(γ_p z_p) y_p) ) p'`, `Slin = Tlin - id - Nlin`, `Slin y = Sfun y`.
No sorry / native_decide / axiom.
-/
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 8000

namespace AdalyFormal.M2W6

open Finset
open AdalyFormal.Target.ClayStatement
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2 RMap RMap_mul_apply RMap_one)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.CovariantHjMinimizer (trivialU)
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
open AdalyFormal.Balaban.AlphaAnalyticity (GaugeFn)
open AdalyFormal.StatementLane (Tower Admissible scaleUp)
open AdalyFormal.W6

section alg3
variable {ell M R k : ℕ} {Lu : PeriodicLatticeExtent} {S : Tower (scaleUp ell k Lu)}

/-- `T = Q_U ∘ EU` -/
noncomputable def Tlin (hell : 0 < ell) (U : LinkCfg (scaleUp ell k Lu))
    (γ : BIdx (geomOf ell k S) → GaugeFn (scaleUp ell k Lu)) :
    FSp (geomOf ell k S) →ₗ[ℝ] FSp (geomOf ell k S) :=
  (((bondSectorOf (geomOf ell k S) U).Qfull : BondFnL2 (scaleUp ell k Lu) →L[ℝ] FSp (geomOf ell k S)) :
    BondFnL2 (scaleUp ell k Lu) →ₗ[ℝ] FSp (geomOf ell k S)).comp (EU hell γ)

theorem Tlin_apply (hell : 0 < ell) (U : LinkCfg (scaleUp ell k Lu))
    (γ : BIdx (geomOf ell k S) → GaugeFn (scaleUp ell k Lu)) (y : FSp (geomOf ell k S)) :
    Tlin hell U γ y = (bondSectorOf (geomOf ell k S) U).Qfull (EU hell γ y) := rfl

/-- the defect part of `T` -/
noncomputable def Sfun (hell : 0 < ell) (U : LinkCfg (scaleUp ell k Lu))
    (γ : BIdx (geomOf ell k S) → GaugeFn (scaleUp ell k Lu)) (y : FSp (geomOf ell k S)) : FSp (geomOf ell k S) :=
  WithLp.toLp 2 (fun p' => ∑ p, RMap ((((γ p) p'.2.1.1)⁻¹))
    ((Dfun hell U γ p (RMap ((γ p) p.2.1.1) (y p))) p'))

/-- the flat part: `Σ_p kap p' p • rot(y p) = y p' + (N y) p'` -/
theorem kap_rot_sum (hell : 0 < ell) (hell2 : 2 ≤ ell) (hS : Admissible ell M R k S) (hM : 1 ≤ M) (hR : 8 * ell ≤ R)
    (γ : BIdx (geomOf ell k S) → GaugeFn (scaleUp ell k Lu)) (y : FSp (geomOf ell k S))
    (p' : BIdx (geomOf ell k S)) :
    ∑ p, kap hell p' p • rotL γ p' p (y p) = y p' + (Nlin hell γ y) p' := by
  classical
  have hR4 : 4 * ell ≤ R := by omega
  have pt : ∀ p : BIdx (geomOf ell k S), kap hell p' p • rotL γ p' p (y p)
      = (if p = p' then y p' else 0) + NtermL hell γ p' p (y p) := by
    intro p
    by_cases hp : p = p'
    · subst hp
      have h1 := kap_same hell hell2 p p rfl
      rw [if_pos rfl] at h1
      rw [h1, one_smul, rotL_self, if_pos rfl]
      show _ = _ + Nterm hell γ p p (y p)
      unfold Nterm
      rw [if_neg (by omega), add_zero]
    · rw [if_neg hp, zero_add]
      show _ = Nterm hell γ p' p (y p)
      unfold Nterm
      by_cases hl : (p.1 : ℕ) + 1 = (p'.1 : ℕ)
      · rw [if_pos hl]
      · rw [if_neg hl]
        have hk : kap hell p' p = 0 := by
          rcases lt_trichotomy (p.1 : ℕ) (p'.1 : ℕ) with h | h | h
          · exact kap_far hell hS hM hR4 p' p (by omega)
          · rw [kap_same hell hell2 p' p h, if_neg hp]
          · exact kap_low hell hS p' p h
        rw [hk, zero_smul]
  rw [Finset.sum_congr rfl (fun p _ => pt p), Finset.sum_add_distrib, Nlin_apply]
  simp

/-- the exact decomposition -/
theorem Tlin_row (hell : 0 < ell) (hell2 : 2 ≤ ell) (hS : Admissible ell M R k S) (hM : 1 ≤ M) (hR : 8 * ell ≤ R)
    (U : LinkCfg (scaleUp ell k Lu)) (γ : BIdx (geomOf ell k S) → GaugeFn (scaleUp ell k Lu))
    (y : FSp (geomOf ell k S)) :
    Tlin hell U γ y = y + Nlin hell γ y + Sfun hell U γ y := by
  refine PiLp.ext (fun p' => ?_)
  rw [Tlin_apply, EU_apply, map_sum]
  simp only [PiLp.add_apply, Sfun]
  simp only [WithLp.ofLp_sum, Finset.sum_apply]
  rw [Finset.sum_congr rfl (fun p _ => Q_src_row hell U γ p p' (y p)), Finset.sum_add_distrib,
    kap_rot_sum hell hell2 hS hM hR γ y p', add_assoc]

end alg3

end AdalyFormal.M2W6

#print axioms AdalyFormal.M2W6.Tlin_row
