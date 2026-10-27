import MF4
import MF5d

/-!
# MF5e -- `WellDef` pieces at NON-FLAT `U` on the full tower (M0): `Q*` injective, `IsUnit G₁⁻¹`, `IsUnit N`.

* `qs_injective_PU` : `Q_U*` is injective, from the flat bond right inverse `bondE` (MF5c/MF5d: `Q₁ E = id`, `‖E‖² ≤ 16 n³`)
  and the bond drift `Σ_p a ℓ^{j(p)} ‖(Q₁ − Q_U) x‖² ≤ δm² ‖x‖²`, provided `16 n² δm² < a` (in the class: `16 φ² < 1`).
* `units_PU`        : `IsUnit G₁⁻¹ ∧ IsUnit N` from `G⁻¹` coercivity (`‖x‖² ≤ C0 ⟨x,G⁻¹x⟩`), `‖Δ⁽²⁾‖ ≤ ε2`, `ε2 C0 < 1`, and `Q*` injective.
-/
set_option autoImplicit false
set_option maxHeartbeats 16000000
set_option maxRecDepth 8000

namespace AdalyFormal.M0Finish

open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane (scaleUp)
open AdalyFormal.StatementLaneG (GenP.Nmat pe)
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.LatticeOperators (CoarseBond)
open AdalyFormal.Balaban.LineIntegralCovariant (lineCoarseRestrictSuTwo)
open AdalyFormal.Balaban.CovariantHjMinimizer (trivialU)
open AdalyFormal.SliceCoerc (GF)

theorem qs_injective_PU (ell k : ℕ) (Lu : PeriodicLatticeExtent) (hell : 0 < ell) (U : Cfg (scaleUp ell k Lu))
    (a : ℝ) (ha : 0 < a) (Lam : Set (PeriodicLatticeSite Lu)) (δm : ℝ)
    (hC1 : ∀ x : BondFnL2 (scaleUp ell k Lu),
      ∑ p : BIdx (GF ell k Lu), a * ((GF ell k Lu).ell : ℝ) ^ (p.1 : ℕ) *
        ‖(bondSectorOf (GF ell k Lu) (trivialU _)).Qfull x p - (bondSectorOf (GF ell k Lu) U).Qfull x p‖ ^ 2
        ≤ δm ^ 2 * ‖x‖ ^ 2)
    (hsm : 16 * ((ell : ℝ) ^ k) ^ 2 * δm ^ 2 < a) :
    Function.Injective (PU ell k Lu hell U a Lam).data.Qs := by
  classical
  set P := PU ell k Lu hell U a Lam with hP
  have hFS : P.FullSupp := fullTower_fullSupp ell k Lu hell U a Lam
  set n : ℝ := (ell : ℝ) ^ k with hn
  have hnpos : 0 < n := pow_pos (by exact_mod_cast hell) k
  have hdvdf : ∀ ν, ell ^ k ∣ scaleUp ell k Lu ν + 1 := AdalyFormal.GenuineU1.scaleUp_tiling ell k Lu hell
  rw [injective_iff_map_eq_zero]
  intro y hy
  set W : CoarseBond (scaleUp ell k Lu) (ell ^ k) → SuTwo :=
    fun c => (WithLp.ofLp y) (P.eqv hFS ((AdalyFormal.GenuineU1.bondsE ell k Lu hell).symm c)) with hW
  set x0 : BondFnL2 (scaleUp ell k Lu) := WithLp.toLp 2 (bondE (ell ^ k) W) with hx0
  -- flat Q of x0 is y
  have hQ1 : (bondSectorOf (GF ell k Lu) (trivialU _)).Qfull x0 = y := by
    refine PiLp.ext (fun p => ?_)
    obtain ⟨e', rfl⟩ := (P.eqv hFS).surjective p
    have h1 := AdalyFormal.FlatEllGeneral.Qfull_top_gen (PU ell k Lu hell flatCfg a Lam) rfl x0 e'
      (IngrBParams.mem_of_fullSupp P hFS e')
    have h2 := bondE_rightInv (ell ^ k) (pow_pos hell k) hdvdf W (AdalyFormal.GenuineU1.bondsE ell k Lu hell e')
    show (bondSectorOf (GF ell k Lu) (trivialU _)).Qfull x0 (pe P e' (IngrBParams.mem_of_fullSupp P hFS e')) = _
    rw [show (bondSectorOf (GF ell k Lu) (trivialU _)).Qfull x0 (pe P e' (IngrBParams.mem_of_fullSupp P hFS e'))
        = ((PU ell k Lu hell flatCfg a Lam).sector.Qfull x0)
            (pe (PU ell k Lu hell flatCfg a Lam) e' (IngrBParams.mem_of_fullSupp P hFS e')) from rfl, h1]
    show lineCoarseRestrictSuTwo (ell ^ k) (bondE (ell ^ k) W) (AdalyFormal.GenuineU1.bondsE ell k Lu hell e') = _
    rw [h2, hW]
    simp only [Equiv.symm_apply_apply]
  -- the norm of x0
  have hWsum : ∑ c : CoarseBond (scaleUp ell k Lu) (ell ^ k), ‖W c‖ ^ 2 = ‖y‖ ^ 2 := by
    rw [PiLp.norm_sq_eq_of_L2]
    have e1 : ∑ c : CoarseBond (scaleUp ell k Lu) (ell ^ k), ‖W c‖ ^ 2
        = ∑ e' : Bond Lu, ‖(WithLp.ofLp y) (P.eqv hFS e')‖ ^ 2 := by
      refine Fintype.sum_equiv (AdalyFormal.GenuineU1.bondsE ell k Lu hell).symm _ _ (fun c => ?_)
      rfl
    rw [e1]
    exact Fintype.sum_equiv (P.eqv hFS) _ _ (fun e' => rfl)
  have hx0 : ‖x0‖ ^ 2 ≤ 16 * n ^ 3 * ‖y‖ ^ 2 := by
    have h := bondE_norm_sq (ell ^ k) (pow_pos hell k) hdvdf W
    rw [hWsum] at h
    rw [hx0, PiLp.norm_sq_eq_of_L2]
    have e2 : ((ell ^ k : ℕ) : ℝ) = n := by rw [hn, Nat.cast_pow]
    rw [e2] at h
    exact h
  -- the drift of x0
  have hlev : ∀ p : BIdx (GF ell k Lu), a * ((GF ell k Lu).ell : ℝ) ^ (p.1 : ℕ) = a * n := by
    intro p
    have := AdalyFormal.GenuineU1.Gen.level_eq P hFS p
    show a * (ell : ℝ) ^ (p.1 : ℕ) = a * n
    rw [this]
  have hd := hC1 x0
  simp only [hlev] at hd
  rw [← Finset.mul_sum] at hd
  set d : FSp P.G := (bondSectorOf (GF ell k Lu) (trivialU _)).Qfull x0 - (bondSectorOf (GF ell k Lu) U).Qfull x0
    with hddef
  have hdn : ‖d‖ ^ 2 = ∑ p : BIdx (GF ell k Lu),
      ‖(bondSectorOf (GF ell k Lu) (trivialU _)).Qfull x0 p - (bondSectorOf (GF ell k Lu) U).Qfull x0 p‖ ^ 2 := by
    rw [hddef, PiLp.norm_sq_eq_of_L2]; rfl
  have han : 0 < a * n := by positivity
  have hd2 : ‖d‖ ^ 2 ≤ 16 * n ^ 2 * δm ^ 2 / a * ‖y‖ ^ 2 := by
    rw [hdn]
    have h3 : a * n * ∑ p : BIdx (GF ell k Lu),
        ‖(bondSectorOf (GF ell k Lu) (trivialU _)).Qfull x0 p - (bondSectorOf (GF ell k Lu) U).Qfull x0 p‖ ^ 2
        ≤ δm ^ 2 * (16 * n ^ 3 * ‖y‖ ^ 2) :=
      hd.trans (mul_le_mul_of_nonneg_left hx0 (sq_nonneg _))
    rw [div_mul_eq_mul_div, le_div_iff₀ ha]
    have e3 : δm ^ 2 * (16 * n ^ 3 * ‖y‖ ^ 2) = n * (16 * n ^ 2 * δm ^ 2 * ‖y‖ ^ 2) := by ring
    rw [e3] at h3
    have h4 : n * (a * ∑ p : BIdx (GF ell k Lu),
        ‖(bondSectorOf (GF ell k Lu) (trivialU _)).Qfull x0 p - (bondSectorOf (GF ell k Lu) U).Qfull x0 p‖ ^ 2)
        ≤ n * (16 * n ^ 2 * δm ^ 2 * ‖y‖ ^ 2) := by linarith
    have := le_of_mul_le_mul_left h4 hnpos
    linarith
  -- ⟨y, Q_U x0⟩ = ⟨Q_U* y, x0⟩ = 0
  set x0' : ↥(bondSupp P.G) := ⟨x0, mem_bondSupp_PU ell k Lu hell U a Lam x0⟩ with hx0'
  have hQU : P.data.Q x0' = (bondSectorOf (GF ell k Lu) U).Qfull x0 := rfl
  have hzero : ⟪y, (bondSectorOf (GF ell k Lu) U).Qfull x0⟫ = 0 := by
    rw [← hQU, real_inner_comm, P.data.Q_adj, hy, inner_zero_right]
  have hyy : ‖y‖ ^ 2 = ⟪y, d⟫ := by
    rw [hddef, inner_sub_right, hQ1, hzero, sub_zero, real_inner_self_eq_norm_sq]
  have hcs : ⟪y, d⟫ ≤ ‖y‖ * ‖d‖ := real_inner_le_norm y d
  have hκ : 16 * n ^ 2 * δm ^ 2 / a < 1 := by rw [div_lt_one ha]; exact hsm
  have hκ0 : 0 ≤ 16 * n ^ 2 * δm ^ 2 / a := by positivity
  -- ‖d‖ ≤ √κ ‖y‖
  have hdle : ‖d‖ ≤ Real.sqrt (16 * n ^ 2 * δm ^ 2 / a) * ‖y‖ := by
    rw [← Real.sqrt_sq (norm_nonneg d), ← Real.sqrt_sq (norm_nonneg y), ← Real.sqrt_mul hκ0]
    exact Real.sqrt_le_sqrt hd2
  have hs1 : Real.sqrt (16 * n ^ 2 * δm ^ 2 / a) < 1 := by
    rw [Real.sqrt_lt' one_pos]; simpa using hκ
  have hy0 : ‖y‖ = 0 := by
    have hny := norm_nonneg y
    by_contra hne
    have hpos : 0 < ‖y‖ := lt_of_le_of_ne hny (Ne.symm hne)
    have : ‖y‖ ^ 2 ≤ ‖y‖ * (Real.sqrt (16 * n ^ 2 * δm ^ 2 / a) * ‖y‖) := by
      rw [hyy]; exact hcs.trans (mul_le_mul_of_nonneg_left hdle hny)
    have hy2 : 0 < ‖y‖ ^ 2 := by positivity
    have e : ‖y‖ * (Real.sqrt (16 * n ^ 2 * δm ^ 2 / a) * ‖y‖) = Real.sqrt (16 * n ^ 2 * δm ^ 2 / a) * ‖y‖ ^ 2 := by
      ring
    rw [e] at this
    have h5 := mul_lt_mul_of_pos_right hs1 hy2
    linarith
  exact norm_eq_zero.mp hy0

theorem units_PU (ell k : ℕ) (Lu : PeriodicLatticeExtent) (hell : 0 < ell) (U : Cfg (scaleUp ell k Lu))
    (a : ℝ) (Lam : Set (PeriodicLatticeSite Lu)) (C0 ε2 : ℝ) (hC0 : 0 < C0) (hε2C : ε2 * C0 < 1)
    (hcoer : ∀ y : ↥(bondSupp (PU ell k Lu hell U a Lam).G),
      ‖y‖ ^ 2 ≤ C0 * ⟪y, (PU ell k Lu hell U a Lam).data.Ginv y⟫)
    (hD2 : ‖(PU ell k Lu hell U a Lam).data.Delta2 (PU ell k Lu hell U a Lam).data_laws‖ ≤ ε2)
    (hQs : Function.Injective (PU ell k Lu hell U a Lam).data.Qs) :
    IsUnit (PU ell k Lu hell U a Lam).G1inv ∧ IsUnit (GenP.Nmat (PU ell k Lu hell U a Lam)) := by
  set P := PU ell k Lu hell U a Lam with hP
  have hc : ∀ x, (1 / C0) * ‖x‖ ^ 2 ≤ ⟪x, P.data.Ginv x⟫ := by
    intro x
    have := hcoer x
    rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ hC0]; linarith
  have hco := P.data.G1inv_coercive P.data_laws P.G1inv_spec hc hD2
  have hpos : 0 < 1 / C0 - ε2 := by
    rw [sub_pos, lt_div_iff₀ hC0]; linarith
  have hGu : IsUnit P.G1inv := by
    have hinj : Function.Injective P.G1inv := by
      rw [injective_iff_map_eq_zero]
      intro x hx
      have h := hco x
      rw [hx, inner_zero_right] at h
      have : ‖x‖ ^ 2 ≤ 0 := by
        by_contra hh; push_neg at hh; nlinarith
      exact norm_eq_zero.mp (by nlinarith [norm_nonneg x])
    exact (ContinuousLinearMap.isUnit_iff_bijective).mpr
      ⟨hinj, (LinearMap.injective_iff_surjective (f := (P.G1inv : ↥(bondSupp P.G) →ₗ[ℝ] ↥(bondSupp P.G)))).mp hinj⟩
  exact ⟨hGu, P.data.QG1Qs_isUnit P.G1inv_spec hpos hco hQs⟩

#print axioms qs_injective_PU
#print axioms units_PU

end AdalyFormal.M0Finish
