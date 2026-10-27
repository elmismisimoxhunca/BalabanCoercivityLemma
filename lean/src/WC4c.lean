import WC4b

/-!
# WC4c -- the exact decomposition `T = I + N + S` and `N ∘ N = 0` (M2 W6 lane)
(continues WC4b; split off because the first version of `Q_src_row` used a `show` with a heavy unification.)
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
open AdalyFormal.GaugeCov (adBL adFL adGen_symm_apply adGen_apply)

section alg2
variable {ell M R k : ℕ} {Lu : PeriodicLatticeExtent} {S : Tower (scaleUp ell k Lu)}

/-- row `p'` of `Q_U (srcL γ p w)`: the flat part (`kap`) plus the chart defect, in the frame of `p'` -/
theorem Q_src_row (hell : 0 < ell) (U : LinkCfg (scaleUp ell k Lu))
    (γ : BIdx (geomOf ell k S) → GaugeFn (scaleUp ell k Lu)) (p p' : BIdx (geomOf ell k S)) (w : SuTwo) :
    ((bondSectorOf (geomOf ell k S) U).Qfull (srcL hell γ p w)) p'
      = kap hell p' p • rotL γ p' p w
        + RMap ((((γ p) p'.2.1.1)⁻¹)) ((Dfun hell U γ p (RMap ((γ p) p.2.1.1) w)) p') := by
  have hsym : ∀ f : FSp (geomOf ell k S), ((adFL (γ p) (geomOf ell k S)).symm f) p'
      = RMap (((γ p) p'.2.1.1)⁻¹) (f p') :=
    fun f => adGen_symm_apply (fun q : BIdx (geomOf ell k S) => (γ p) q.2.1.1) f p'
  rw [Q_src, hsym]
  have hsplit : (bondSectorOf (geomOf ell k S) (periodicGaugeTransform (γ p) U)).Qfull
        (psiL hell p (RMap ((γ p) p.2.1.1) w))
      = (bondSectorOf (geomOf ell k S) (trivialU _)).Qfull (psiL hell p (RMap ((γ p) p.2.1.1) w))
        + Dfun hell U γ p (RMap ((γ p) p.2.1.1) w) :=
    (add_sub_cancel _ _).symm
  have hflat : ((bondSectorOf (geomOf ell k S) (trivialU _)).Qfull (psiL hell p (RMap ((γ p) p.2.1.1) w))) p'
      = kap hell p' p • RMap ((γ p) p.2.1.1) w := by
    have h1 := Qflat_E hell (sglL p (RMap ((γ p) p.2.1.1) w)) p'
    have h2 : (EflatL hell) (sglL p (RMap ((γ p) p.2.1.1) w)) = psiL hell p (RMap ((γ p) p.2.1.1) w) := rfl
    rw [h2] at h1
    rw [h1]
    simp only [sglL_apply, smul_ite, smul_zero]
    rw [Finset.sum_ite_eq' Finset.univ p]
    simp
  rw [hsplit, PiLp.add_apply, hflat, map_add, map_smul, RMap_mul_apply]
  rfl

open Classical in
/-- one summand of `N`. -/
noncomputable def Nterm (hell : 0 < ell) (γ : BIdx (geomOf ell k S) → GaugeFn (scaleUp ell k Lu))
    (p' p : BIdx (geomOf ell k S)) (w : SuTwo) : SuTwo :=
  if (p.1 : ℕ) + 1 = (p'.1 : ℕ) then kap hell p' p • rotL γ p' p w else 0

theorem Nterm_add (hell : 0 < ell) (γ : BIdx (geomOf ell k S) → GaugeFn (scaleUp ell k Lu))
    (p' p : BIdx (geomOf ell k S)) (w w' : SuTwo) :
    Nterm hell γ p' p (w + w') = Nterm hell γ p' p w + Nterm hell γ p' p w' := by
  unfold Nterm; split_ifs <;> simp [map_add, smul_add]

theorem Nterm_smul (hell : 0 < ell) (γ : BIdx (geomOf ell k S) → GaugeFn (scaleUp ell k Lu))
    (p' p : BIdx (geomOf ell k S)) (c : ℝ) (w : SuTwo) :
    Nterm hell γ p' p (c • w) = c • Nterm hell γ p' p w := by
  unfold Nterm
  split_ifs
  · rw [map_smul, smul_comm]
  · simp

/-- `Nterm` as a linear map -/
noncomputable def NtermL (hell : 0 < ell) (γ : BIdx (geomOf ell k S) → GaugeFn (scaleUp ell k Lu))
    (p' p : BIdx (geomOf ell k S)) : SuTwo →ₗ[ℝ] SuTwo where
  toFun := Nterm hell γ p' p
  map_add' := Nterm_add hell γ p' p
  map_smul' := Nterm_smul hell γ p' p

/-- the cross-level part `N` -/
noncomputable def Nlin (hell : 0 < ell) (γ : BIdx (geomOf ell k S) → GaugeFn (scaleUp ell k Lu)) :
    FSp (geomOf ell k S) →ₗ[ℝ] FSp (geomOf ell k S) where
  toFun y := WithLp.toLp 2 (fun p' => ∑ p, NtermL hell γ p' p (y p))
  map_add' y y' := by
    refine PiLp.ext (fun p' => ?_)
    simp only [PiLp.add_apply, map_add, Finset.sum_add_distrib]
  map_smul' c y := by
    refine PiLp.ext (fun p' => ?_)
    simp only [PiLp.smul_apply, map_smul, RingHom.id_apply, Finset.smul_sum]

theorem Nlin_apply (hell : 0 < ell) (γ : BIdx (geomOf ell k S) → GaugeFn (scaleUp ell k Lu))
    (y : FSp (geomOf ell k S)) (p' : BIdx (geomOf ell k S)) :
    (Nlin hell γ y) p' = ∑ p, NtermL hell γ p' p (y p) := rfl

theorem Nterm_Nterm (hell : 0 < ell) (hell2 : 2 ≤ ell) (hS : Admissible ell M R k S) (hM : 1 ≤ M) (hR : 8 * ell ≤ R)
    (γ : BIdx (geomOf ell k S) → GaugeFn (scaleUp ell k Lu)) (p'' p' p : BIdx (geomOf ell k S)) (w : SuTwo) :
    NtermL hell γ p'' p' (NtermL hell γ p' p w) = 0 := by
  show Nterm hell γ p'' p' (Nterm hell γ p' p w) = 0
  unfold Nterm
  by_cases h1 : (p'.1 : ℕ) + 1 = (p''.1 : ℕ)
  · by_cases h2 : (p.1 : ℕ) + 1 = (p'.1 : ℕ)
    · rw [if_pos h1, if_pos h2]
      rcases kap_N2 hell hell2 hS hM hR p'' p' p h1 h2 with h | h
      · rw [h]; simp
      · rw [h]; simp
    · rw [if_pos h1, if_neg h2]; simp
  · rw [if_neg h1]

/-- **`N ∘ N = 0`, termwise** (`kap_N2`). -/
theorem Nlin_Nlin (hell : 0 < ell) (hell2 : 2 ≤ ell) (hS : Admissible ell M R k S) (hM : 1 ≤ M) (hR : 8 * ell ≤ R)
    (γ : BIdx (geomOf ell k S) → GaugeFn (scaleUp ell k Lu)) (y : FSp (geomOf ell k S)) :
    Nlin hell γ (Nlin hell γ y) = 0 := by
  refine PiLp.ext (fun p'' => ?_)
  rw [Nlin_apply, PiLp.zero_apply]
  refine Finset.sum_eq_zero (fun p' _ => ?_)
  rw [Nlin_apply, map_sum]
  exact Finset.sum_eq_zero (fun p _ => Nterm_Nterm hell hell2 hS hM hR γ p'' p' p (y p))

end alg2

end AdalyFormal.M2W6

#print axioms AdalyFormal.M2W6.Q_src_row
