import W6H
import M1Cov

/-!
# W6I -- the abstract drift form of W6, and the flat proper-tower witness (W6 lane, 2026-10-13)

* **`qs_injective_of_drift`** : the injectivity of `Q_U*` needs ONLY a row-normalised drift bound
  `‖(Q_U − Q₁) x‖_F² ≤ D ‖x‖²` with `D · CEp < 1` (any discharge of the drift plugs in here; `qs_injective_strat` is the
  discharge through the global tower class, W6E `drift_F`).
* `qs_injective_flat` : at `U = 1` (`D = 0`) on every admissible tower with `M ≥ 1`, `8ℓ ≤ R`, `ℓ ≥ 2`.
* `bond_rightinv_slab` (L7 witness for W6H's existential): at the same slab tower and flat `U`, every `u ∈ L²(𝔅)` has a
  preimage in `E₀` with the weighted-energy bounds (the hypotheses of `bond_rightinv_strat` hold with `ε = 0`, `δ = 0`).
* `qs_injective_slab` (L7 witness): the hypotheses are jointly satisfiable at a PROPER two-stratum tower: lane B's slab tower
  `TS 24` (`ℓ = 3`, `M = 3`, `R = 24 = 8ℓ`, `k = 1`, `Ω₀ ≠` torus, M1Cov `TS_admissible`), flat `U`.
No sorry / native_decide / axiom.
-/
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 8000

namespace AdalyFormal.W6

open Finset
open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.Balaban.CovariantHjMinimizer (trivialU)
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
open AdalyFormal.StatementLane (Tower Admissible scaleUp)
open AdalyFormal.StatementLaneG (gparams)

section abs
variable {ell M R k : ℕ} {Lu : PeriodicLatticeExtent} {S : Tower (scaleUp ell k Lu)}

/-- **abstract W6**: drift `≤ D` in the row-normalised norm and `D · CEp < 1` ⇒ `Q_U*` injective. -/
theorem qs_injective_of_drift (hell : 0 < ell) (hell2 : 2 ≤ ell) (hS : Admissible ell M R k S) (hM : 0 < M)
    (hR : 8 * ell ≤ R) (U : LinkCfg (scaleUp ell k Lu)) (a : ℝ) (Lam : Set (PeriodicLatticeSite Lu)) (D : ℝ)
    (hD : ∀ x : BondFnL2 (scaleUp ell k Lu),
      ∑ p, wF p * ‖(bondSectorOf (geomOf ell k S) U).Qfull x p - (bondSectorOf (geomOf ell k S) (trivialU _)).Qfull x p‖ ^ 2
        ≤ D * ‖x‖ ^ 2)
    (hsmall : D * CEp < 1) :
    Function.Injective (gparams ell k Lu hell S U a Lam).data.Qs := by
  set G := geomOf ell k S with hGdef
  set A : ↥(bondSupp G) →L[ℝ] FSp G := ((bondSectorOf G U).Qfull).comp (iE G) with hA
  set E2 : FSp G →ₗ[ℝ] ↥(bondSupp G) := LinearMap.codRestrict (bondSupp G) (ErightL hell)
    (fun y => Eright_mem hell hS y) with hE2
  set T : FSp G →ₗ[ℝ] FSp G := (A : ↥(bondSupp G) →ₗ[ℝ] FSp G).comp E2 with hT
  have hTapp : ∀ y, T y = (bondSectorOf G U).Qfull (ErightL hell y) := fun y => rfl
  have hTinj : Function.Injective T := by
    rw [injective_iff_map_eq_zero]
    intro y hy0
    have hd : ∀ p, y p = (bondSectorOf G (trivialU _)).Qfull (ErightL hell y) p
        - (bondSectorOf G U).Qfull (ErightL hell y) p := by
      intro p
      have h1 := congrArg (fun w : FSp G => w p) (Eright_rightInv hell hell2 hS hM hR y)
      have h2 : (bondSectorOf G U).Qfull (ErightL hell y) p = 0 := by
        rw [← hTapp, hy0]; rfl
      simp only at h1
      rw [h2, sub_zero, h1]
    have hny : nF y ≤ D * ‖ErightL hell y‖ ^ 2 := by
      unfold nF
      refine le_trans (le_of_eq ?_) (hD (ErightL hell y))
      refine Finset.sum_congr rfl (fun p _ => ?_)
      rw [hd p, norm_sub_rev]
    have hEn := Eright_norm_sq hell hell2 hS hM hR y
    have hy0' := nF_nonneg hell y
    by_cases hD0 : 0 ≤ D
    · have : nF y ≤ (D * CEp) * nF y := by
        calc nF y ≤ D * ‖ErightL hell y‖ ^ 2 := hny
          _ ≤ D * (CEp * nF y) := mul_le_mul_of_nonneg_left hEn hD0
          _ = (D * CEp) * nF y := by ring
      have hle : nF y ≤ 0 := by nlinarith
      exact eq_zero_of_nF hell y hle
    · push Not at hD0
      have hle : nF y ≤ 0 := le_trans hny (mul_nonpos_of_nonpos_of_nonneg hD0.le (sq_nonneg _))
      exact eq_zero_of_nF hell y hle
  have hTsurj : Function.Surjective T := LinearMap.injective_iff_surjective.mp hTinj
  show Function.Injective (ContinuousLinearMap.adjoint A)
  rw [injective_iff_map_eq_zero]
  intro z hz
  obtain ⟨y, hy⟩ := hTsurj z
  have h1 : ⟪z, z⟫ = 0 := by
    calc ⟪z, z⟫ = ⟪A (E2 y), z⟫ := by rw [← hy]; rfl
      _ = ⟪E2 y, ContinuousLinearMap.adjoint A z⟫ := by rw [ContinuousLinearMap.adjoint_inner_right]
      _ = 0 := by rw [hz, inner_zero_right]
  exact inner_self_eq_zero.mp h1

/-- the flat case (`D = 0`) -/
theorem qs_injective_flat (hell : 0 < ell) (hell2 : 2 ≤ ell) (hS : Admissible ell M R k S) (hM : 0 < M)
    (hR : 8 * ell ≤ R) (a : ℝ) (Lam : Set (PeriodicLatticeSite Lu)) :
    Function.Injective (gparams ell k Lu hell S (trivialU _) a Lam).data.Qs :=
  qs_injective_of_drift hell hell2 hS hM hR (trivialU _) a Lam 0
    (fun x => by simp) (by rw [zero_mul]; norm_num)

end abs

/-- the unit torus of the slab witness -/
def LuSlab : PeriodicLatticeExtent := fun _ => 215

theorem slab_side : ∀ μ, scaleUp 3 1 LuSlab μ + 1 = 18 * 24 + 216 := by
  intro μ; simp [scaleUp, LuSlab]

/-- **L7 witness at a proper two-stratum tower**: lane B's slab tower `TS 24` (`ℓ = 3`, `M = 3`, `R = 24`, `k = 1`). -/
theorem qs_injective_slab :
    Admissible 3 3 24 1 (AdalyFormal.M1.TS 24 (scaleUp 3 1 LuSlab)) ∧
    (∃ x, x ∉ (AdalyFormal.M1.TS 24 (scaleUp 3 1 LuSlab)).Om 0) ∧
    (∃ x, x ∈ (AdalyFormal.M1.TS 24 (scaleUp 3 1 LuSlab)).Om 1) ∧
    ∀ (a : ℝ) (Lam : Set (PeriodicLatticeSite LuSlab)),
      Function.Injective
        (gparams 3 1 LuSlab (by norm_num) (AdalyFormal.M1.TS 24 (scaleUp 3 1 LuSlab)) (trivialU _) a Lam).data.Qs := by
  have hS := AdalyFormal.M1.TS_admissible 24 slab_side
  refine ⟨hS, ?_, ?_, fun a Lam => qs_injective_flat (ell := 3) (M := 3) (R := 24) (k := 1) (by norm_num) (by norm_num) hS
    (by norm_num) (by norm_num) a Lam⟩
  · refine ⟨fun μ => ⟨0, by have := slab_side μ; omega⟩, ?_⟩
    rw [AdalyFormal.M1.TS_om0]; simp
  · refine ⟨fun μ => ⟨9 * 24 + 18, by have := slab_side μ; omega⟩, ?_⟩
    rw [AdalyFormal.M1.TS_om1]; simp

theorem delW_zero {ell' k' : ℕ} (hell : 0 < ell') : delW ell' k' (fun _ => 0) = 0 := by
  unfold delW SS
  simp [AdalyFormal.BondComposite.thetaOf_zero ell' hell]

/-- **L7 witness for `bond_rightinv_strat`** at the slab tower, flat `U`. -/
theorem bond_rightinv_slab (a : ℝ) (Lam : Set (PeriodicLatticeSite LuSlab))
    (u : FSp (geomOf 3 1 (AdalyFormal.M1.TS 24 (scaleUp 3 1 LuSlab)))) :
    ∃ x : ↥(bondSupp (geomOf 3 1 (AdalyFormal.M1.TS 24 (scaleUp 3 1 LuSlab)))),
      (gparams 3 1 LuSlab (by norm_num) (AdalyFormal.M1.TS 24 (scaleUp 3 1 LuSlab)) (trivialU _) a Lam).data.Q x = u ∧
      AdalyFormal.M1.wnormSq (AdalyFormal.M1.TS 24 (scaleUp 3 1 LuSlab)) 3 1 (x : BondFnL2 (scaleUp 3 1 LuSlab))
        ≤ 4 * CwE 3 * nD u ∧
      ∀ ν0 : Fin 3, gradW (x : BondFnL2 (scaleUp 3 1 LuSlab)) ν0 ≤ 4 * CgE 3 * nD u := by
  have hS := AdalyFormal.M1.TS_admissible 24 slab_side
  refine bond_rightinv_strat (ell := 3) (M := 3) (R := 24) (k := 1) (by norm_num) (by norm_num) hS (by norm_num)
    (by norm_num) (trivialU _) a Lam (fun _ => 0) (regTower_triv (by norm_num)) (towerClass_triv (by norm_num))
    (fun _ _ => le_rfl) (fun _ _ => rhoOf_zero_lt 3) ?_ u
  rw [delW_zero (by norm_num)]
  norm_num

end AdalyFormal.W6

#print axioms AdalyFormal.W6.qs_injective_of_drift
#print axioms AdalyFormal.W6.qs_injective_flat
#print axioms AdalyFormal.W6.qs_injective_slab
#print axioms AdalyFormal.W6.delW_zero
#print axioms AdalyFormal.W6.bond_rightinv_slab
