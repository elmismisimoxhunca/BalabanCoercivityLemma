import MI2

/-!
# MI21 -- W5 `units_strat`: `IsUnit G₁⁻¹` and `IsUnit (Q G₁ Q*)` on proper towers from W4 (M1 lane E, 2026-10-13)

Inputs, all at one point `P = gparams ell k Lu hell S U a Lam` of a (proper) tower:
* `hcoer` (W4 output form): `c_w · wnormSq A ≤ ⟪A, Ginv A⟫`;
* `hD2` (the stratified D-layer form bound of lane B's `DLayerStrat`, first clause): `|⟪A, Δ⁽²⁾ A⟫| ≤ ε₂ · wnormSq A`;
* `hQs` : `Q*` injective (plan node W6, lane D);  `ε₂ < c_w`.
Outputs: `G1inv_coercive_strat` (`(c_w − ε₂) wnormSq ≤ ⟪A, G₁⁻¹ A⟫`, every `A`), `G1inv_coercive_plain`
(`(c_w − ε₂) ℓ^{−2k} ‖A‖² ≤ ⟪A, G₁⁻¹ A⟫`), **`units_strat`** (`IsUnit (gparams ell k Lu hell S U a Lam).G1inv ∧ IsUnit (Nmat P)`).
`hb` (bijectivity of `H₀`) is not part of this module; `WellDef` (with `hb`) is assembled in MI33 `wellDef_strat`.
No sorry / native_decide / axiom.
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace AdalyFormal.M1IMS

open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane AdalyFormal.StatementLaneG AdalyFormal.IngredientFamilyR2
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.M1

section
variable {L : PeriodicLatticeExtent}

/-- `wnormSq ≥ ℓ^{−2k} ‖A‖²`. -/
theorem wnormSq_ge (S : Tower L) {ell : ℕ} (hell : 1 ≤ ell) (k : ℕ) (A : BondFnL2 L) :
    ((ell : ℝ) ^ k)⁻¹ ^ 2 * ‖A‖ ^ 2 ≤ wnormSq S ell k A := by
  unfold wnormSq
  rw [PiLp.norm_sq_eq_of_L2, Finset.mul_sum]
  refine Finset.sum_le_sum (fun b _ => mul_le_mul_of_nonneg_right ?_ (sq_nonneg _))
  have hb := bstrat_le S k b
  have h1 : (1 : ℝ) ≤ ell := by exact_mod_cast hell
  have h2 : (0 : ℝ) < (ell : ℝ) ^ bstrat S k b := by positivity
  have h3 : (ell : ℝ) ^ bstrat S k b ≤ (ell : ℝ) ^ k := pow_le_pow_right₀ h1 hb
  have h4 : ((ell : ℝ) ^ k)⁻¹ ≤ ((ell : ℝ) ^ bstrat S k b)⁻¹ := inv_anti₀ h2 h3
  exact pow_le_pow_left₀ (by positivity) h4 2

end

section
variable (ell k : ℕ) (Lu : PeriodicLatticeExtent) (hell : 0 < ell) (S : Tower (scaleUp ell k Lu))
  (U : LinkCfg (scaleUp ell k Lu)) (a : ℝ) (Lam : Set (PeriodicLatticeSite Lu))

/-- `G₁⁻¹ = Ginv − Δ⁽²⁾` is coercive in the weighted norm. -/
theorem G1inv_coercive_strat (cw ε2 : ℝ)
    (hcoer : ∀ A : ↥(bondSupp (gparams ell k Lu hell S U a Lam).G),
      cw * wnormSq S ell k (A : BondFnL2 (scaleUp ell k Lu)) ≤ ⟪A, (gparams ell k Lu hell S U a Lam).data.Ginv A⟫)
    (hD2 : ∀ A : ↥(bondSupp (gparams ell k Lu hell S U a Lam).G),
      |⟪A, (gparams ell k Lu hell S U a Lam).data.Delta2 (gparams ell k Lu hell S U a Lam).data_laws A⟫|
        ≤ ε2 * wnormSq S ell k (A : BondFnL2 (scaleUp ell k Lu)))
    (A : ↥(bondSupp (gparams ell k Lu hell S U a Lam).G)) :
    (cw - ε2) * wnormSq S ell k (A : BondFnL2 (scaleUp ell k Lu))
      ≤ ⟪A, (gparams ell k Lu hell S U a Lam).G1inv A⟫ := by
  have hEq : (gparams ell k Lu hell S U a Lam).G1inv = (gparams ell k Lu hell S U a Lam).data.Ginv - (gparams ell k Lu hell S U a Lam).data.Delta2 (gparams ell k Lu hell S U a Lam).data_laws :=
    (gparams ell k Lu hell S U a Lam).data.G1inv_unique (gparams ell k Lu hell S U a Lam).G1inv_spec ((gparams ell k Lu hell S U a Lam).data.isG1inv_sub (gparams ell k Lu hell S U a Lam).data_laws)
  rw [hEq, ContinuousLinearMap.sub_apply, inner_sub_right]
  have h1 := hcoer A
  have h2 := (abs_le.mp (hD2 A)).2
  linarith

/-- plain coercivity with constant `(c_w − ε₂) ℓ^{−2k}`. -/
theorem G1inv_coercive_plain (cw ε2 : ℝ) (hε : ε2 ≤ cw)
    (hcoer : ∀ A : ↥(bondSupp (gparams ell k Lu hell S U a Lam).G),
      cw * wnormSq S ell k (A : BondFnL2 (scaleUp ell k Lu)) ≤ ⟪A, (gparams ell k Lu hell S U a Lam).data.Ginv A⟫)
    (hD2 : ∀ A : ↥(bondSupp (gparams ell k Lu hell S U a Lam).G),
      |⟪A, (gparams ell k Lu hell S U a Lam).data.Delta2 (gparams ell k Lu hell S U a Lam).data_laws A⟫|
        ≤ ε2 * wnormSq S ell k (A : BondFnL2 (scaleUp ell k Lu)))
    (A : ↥(bondSupp (gparams ell k Lu hell S U a Lam).G)) :
    ((cw - ε2) * ((ell : ℝ) ^ k)⁻¹ ^ 2) * ‖A‖ ^ 2 ≤ ⟪A, (gparams ell k Lu hell S U a Lam).G1inv A⟫ := by
  have h1 := G1inv_coercive_strat ell k Lu hell S U a Lam cw ε2 hcoer hD2 A
  have h2 := wnormSq_ge S (show 1 ≤ ell by omega) k (A : BondFnL2 (scaleUp ell k Lu))
  have hn : ‖A‖ = ‖(A : BondFnL2 (scaleUp ell k Lu))‖ := rfl
  rw [hn]
  have h3 : (cw - ε2) * (((ell : ℝ) ^ k)⁻¹ ^ 2 * ‖(A : BondFnL2 (scaleUp ell k Lu))‖ ^ 2)
      ≤ (cw - ε2) * wnormSq S ell k (A : BondFnL2 (scaleUp ell k Lu)) :=
    mul_le_mul_of_nonneg_left h2 (by linarith)
  nlinarith

/-- **W5 `units_strat`**: `IsUnit G₁⁻¹` and `IsUnit (Q G₁ Q*)`. -/
theorem units_strat (cw ε2 : ℝ) (hε : ε2 < cw)
    (hcoer : ∀ A : ↥(bondSupp (gparams ell k Lu hell S U a Lam).G),
      cw * wnormSq S ell k (A : BondFnL2 (scaleUp ell k Lu)) ≤ ⟪A, (gparams ell k Lu hell S U a Lam).data.Ginv A⟫)
    (hD2 : ∀ A : ↥(bondSupp (gparams ell k Lu hell S U a Lam).G),
      |⟪A, (gparams ell k Lu hell S U a Lam).data.Delta2 (gparams ell k Lu hell S U a Lam).data_laws A⟫|
        ≤ ε2 * wnormSq S ell k (A : BondFnL2 (scaleUp ell k Lu)))
    (hQs : Function.Injective (gparams ell k Lu hell S U a Lam).data.Qs) :
    IsUnit (gparams ell k Lu hell S U a Lam).G1inv ∧ IsUnit (GenP.Nmat (gparams ell k Lu hell S U a Lam)) := by
  set c := (cw - ε2) * ((ell : ℝ) ^ k)⁻¹ ^ 2
  have hc : 0 < c := by
    have : (0 : ℝ) < ((ell : ℝ) ^ k)⁻¹ := by have : (0:ℝ) < ell := (by exact_mod_cast hell); positivity
    exact mul_pos (by linarith) (by positivity)
  have hco := G1inv_coercive_plain ell k Lu hell S U a Lam cw ε2 hε.le hcoer hD2
  have hGu : IsUnit (gparams ell k Lu hell S U a Lam).G1inv := by
    have hinj : Function.Injective (gparams ell k Lu hell S U a Lam).G1inv := by
      rw [injective_iff_map_eq_zero]
      intro x hx
      have h := hco x
      rw [hx, inner_zero_right] at h
      have : ‖x‖ ^ 2 ≤ 0 := by
        by_contra hh; push Not at hh; nlinarith
      exact norm_eq_zero.mp (by nlinarith [norm_nonneg x])
    exact (ContinuousLinearMap.isUnit_iff_bijective).mpr
      ⟨hinj, (LinearMap.injective_iff_surjective (f := ((gparams ell k Lu hell S U a Lam).G1inv : ↥(bondSupp (gparams ell k Lu hell S U a Lam).G) →ₗ[ℝ] ↥(bondSupp (gparams ell k Lu hell S U a Lam).G)))).mp hinj⟩
  exact ⟨hGu, (gparams ell k Lu hell S U a Lam).data.QG1Qs_isUnit (gparams ell k Lu hell S U a Lam).G1inv_spec hc hco hQs⟩

end

end AdalyFormal.M1IMS

#print axioms AdalyFormal.M1IMS.wnormSq_ge
#print axioms AdalyFormal.M1IMS.G1inv_coercive_strat
#print axioms AdalyFormal.M1IMS.G1inv_coercive_plain
#print axioms AdalyFormal.M1IMS.units_strat
