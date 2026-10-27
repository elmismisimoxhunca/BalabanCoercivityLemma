import W6E

/-!
# W6F -- `qs_injective_strat`: `Q_U*` is injective at non-flat `U` on proper towers (W6 lane, 2026-10-13)

* `Kop` : the matrix `kap` as an operator on `L²(𝔅)` (`Kop y = Q₁(E y)`, `Kop_eq`).
* `ErightL y = E (2y − K y)` : **`Eright_rightInv`** `Q₁ (E' y) = y` (from `kap_sq`, `(K − I)² = 0`), **`Eright_mem`** `E' y ∈ E₀`,
  **`Eright_norm_sq`** `‖E' y‖² ≤ CEp · ‖y‖_F²`, `CEp = CE (8 + 6 CE)`: a multi-level bond right inverse of the flat `Q` with a
  `k`-, volume- and tower-free bound in the row-normalised norm.
* **`gram_lower`** : `Σ_p (ℓ^{3 lev p})⁻¹ ‖z_p‖² ≤ CEp ‖Q₁* z‖²` for every `z ∈ L²(𝔅)`: the row-normalised Gram of the flat `Q`
  (restricted to `E₀`) is bounded below by `1/CEp`, uniformly in `k`, the volume and the tower.
* **`qs_injective_strat`** : `Function.Injective (gparams ℓ k Lu hell S U a Λ).data.Qs` — the exact hypothesis `hQs` of lane E's
  `wellDef_strat` (MI33) — for every admissible `S` (`M ≥ 1`, `8ℓ ≤ R`, `ℓ ≥ 2`), every `Λ`, `a`, and every `U` in the M0-chain tower
  class (`RegTower`, `TowerClass ε`, `ε ≥ 0`, `ρ(ε) < π/2`: the hypotheses W4/W5 already carry) with `3 δ(ε)² CEp < 1`.
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
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.CovariantHjMinimizer (trivialU)
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
open AdalyFormal.StatementLane (Tower Admissible scaleUp)
open AdalyFormal.StatementLaneG (gparams)
open AdalyFormal.SliceCoerc (GF)
open AdalyFormal.NonflatJet (rhoOf)
open AdalyFormal.BondComposite (TowerClass)

section rinv
variable {ell M R k : ℕ} {Lu : PeriodicLatticeExtent} {S : Tower (scaleUp ell k Lu)}

/-- the matrix `kap` acting on `L²(𝔅)` -/
noncomputable def Kop (hell : 0 < ell) : FSp (geomOf ell k S) →ₗ[ℝ] FSp (geomOf ell k S) where
  toFun y := WithLp.toLp 2 (fun p' => ∑ p, kap hell p' p • (WithLp.ofLp y) p)
  map_add' y y' := by
    refine PiLp.ext (fun p => ?_)
    simp [smul_add, Finset.sum_add_distrib]
  map_smul' c y := by
    refine PiLp.ext (fun p => ?_)
    simp [Finset.smul_sum, smul_smul, mul_comm]

theorem Kop_apply (hell : 0 < ell) (y : FSp (geomOf ell k S)) (p' : BIdx (geomOf ell k S)) :
    (Kop hell y) p' = ∑ p, kap hell p' p • y p := rfl

theorem Kop_eq (hell : 0 < ell) (y : FSp (geomOf ell k S)) :
    Kop hell y = (bondSectorOf (geomOf ell k S) (trivialU _)).Qfull (EflatL hell y) := by
  refine PiLp.ext (fun p' => ?_)
  rw [Qflat_E hell y p']
  rfl

/-- `E' y = E (2y − K y)` -/
noncomputable def ErightL (hell : 0 < ell) : FSp (geomOf ell k S) →ₗ[ℝ] BondFnL2 (scaleUp ell k Lu) :=
  (EflatL hell).comp ((2 : ℝ) • LinearMap.id - Kop hell)

theorem ErightL_apply (hell : 0 < ell) (y : FSp (geomOf ell k S)) :
    ErightL hell y = EflatL hell ((2 : ℝ) • y - Kop hell y) := rfl

/-- **`Q₁ E' = id`** -/
theorem Eright_rightInv (hell : 0 < ell) (hell2 : 2 ≤ ell) (hS : Admissible ell M R k S) (hM : 1 ≤ M)
    (hR : 8 * ell ≤ R) (y : FSp (geomOf ell k S)) :
    (bondSectorOf (geomOf ell k S) (trivialU _)).Qfull (ErightL hell y) = y := by
  refine PiLp.ext (fun p'' => ?_)
  rw [ErightL_apply, Qflat_E hell _ p'']
  have hz : ∀ p, ((2 : ℝ) • y - Kop hell y) p = (2 : ℝ) • y p - ∑ q, kap hell p q • y q := fun p => rfl
  simp only [hz, smul_sub, Finset.smul_sum, smul_smul, Finset.sum_sub_distrib]
  rw [Finset.sum_comm (f := fun p q => (kap hell p'' p * kap hell p q) • y q)]
  simp only [← Finset.sum_smul, kap_sq hell hell2 hS hM hR p'']
  simp only [sub_smul, Finset.sum_sub_distrib, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq, mem_univ, if_true]
  have e : ∑ x, (kap hell p'' x * 2) • y x = ∑ x, (2 * kap hell p'' x) • y x :=
    Finset.sum_congr rfl (fun x _ => by rw [mul_comm])
  rw [e]
  abel

theorem Eright_mem (hell : 0 < ell) (hS : Admissible ell M R k S) (y : FSp (geomOf ell k S)) :
    ErightL hell y ∈ bondSupp (geomOf ell k S) := EflatL_mem hell hS _

/-- `‖a − b‖² ≤ 2‖a‖² + 2‖b‖²` in the row-normalised norm -/
theorem nF_sub_le (hell : 0 < ell) (y z : FSp (geomOf ell k S)) : nF (y - z) ≤ 2 * nF y + 2 * nF z := by
  unfold nF
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum (fun p _ => ?_)
  have hw := (wF_pos hell p).le
  have h1 : ‖(y - z) p‖ ≤ ‖y p‖ + ‖z p‖ := by
    rw [show (y - z) p = y p - z p from rfl]; exact norm_sub_le _ _
  have h2 : ‖(y - z) p‖ ^ 2 ≤ 2 * ‖y p‖ ^ 2 + 2 * ‖z p‖ ^ 2 := by
    nlinarith [norm_nonneg ((y - z) p), norm_nonneg (y p), norm_nonneg (z p), sq_nonneg (‖y p‖ - ‖z p‖)]
  nlinarith [mul_le_mul_of_nonneg_left h2 hw]

theorem nF_smul (c : ℝ) (y : FSp (geomOf ell k S)) : nF (c • y) = c ^ 2 * nF y := by
  unfold nF
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun p _ => ?_)
  rw [show (c • y) p = c • y p from rfl, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  ring

/-- the norm constant of `E'` -/
noncomputable def CEp : ℝ := CE * (8 + 6 * CE)

theorem CE_pos : 0 < CE := by unfold CE; norm_num

theorem CEp_pos : 0 < CEp := by unfold CEp; have := CE_pos; positivity

/-- **`‖E' y‖² ≤ CEp ‖y‖_F²`** -/
theorem Eright_norm_sq (hell : 0 < ell) (hell2 : 2 ≤ ell) (hS : Admissible ell M R k S) (hM : 0 < M)
    (hR : 8 * ell ≤ R) (y : FSp (geomOf ell k S)) :
    ‖ErightL hell y‖ ^ 2 ≤ CEp * nF y := by
  rw [ErightL_apply]
  have h1 := EflatL_norm_sq hell hell2 hS ((2 : ℝ) • y - Kop hell y)
  have hK : nF (Kop hell y) ≤ 3 * (CE * nF y) := by
    rw [Kop_eq]
    have h3 : nF ((bondSectorOf (geomOf ell k S) (trivialU _)).Qfull (EflatL hell y)) ≤ 3 * ‖EflatL hell y‖ ^ 2 :=
      flat_F hell2 hS hM hR (EflatL hell y)
    have h2 := EflatL_norm_sq hell hell2 hS y
    linarith
  have h3 := nF_sub_le hell ((2 : ℝ) • y) (Kop hell y)
  rw [nF_smul] at h3
  have hCE := CE_pos
  have hy := nF_nonneg hell y
  unfold CEp
  calc ‖EflatL hell ((2 : ℝ) • y - Kop hell y)‖ ^ 2 ≤ CE * nF ((2 : ℝ) • y - Kop hell y) := h1
    _ ≤ CE * (2 * (2 ^ 2 * nF y) + 2 * (3 * (CE * nF y))) := by
        apply mul_le_mul_of_nonneg_left _ hCE.le; linarith
    _ = CE * (8 + 6 * CE) * nF y := by ring

/-- `nF y = 0 ⇒ y = 0` -/
theorem eq_zero_of_nF (hell : 0 < ell) (y : FSp (geomOf ell k S)) (h : nF y ≤ 0) : y = 0 := by
  have hterm : ∀ p, wF p * ‖y p‖ ^ 2 = 0 := by
    intro p
    have hall := (Finset.sum_eq_zero_iff_of_nonneg (fun p _ => mul_nonneg (wF_pos hell p).le (sq_nonneg ‖y p‖))).mp
      (le_antisymm h (nF_nonneg hell y))
    exact hall p (mem_univ p)
  refine PiLp.ext (fun p => ?_)
  have h1 := hterm p
  have hw := wF_pos hell p
  have h2 : ‖y p‖ ^ 2 = 0 := by
    rcases mul_eq_zero.mp h1 with h | h
    · exact absurd h hw.ne'
    · exact h
  have : ‖y p‖ = 0 := by simpa using h2
  simpa using this

/-- **the row-normalised Gram of the flat `Q` is bounded below uniformly** -/
theorem gram_lower (hell : 0 < ell) (hell2 : 2 ≤ ell) (hS : Admissible ell M R k S) (hM : 0 < M)
    (hR : 8 * ell ≤ R) (a : ℝ) (Lam : Set (PeriodicLatticeSite Lu)) (z : FSp (geomOf ell k S)) :
    ∑ p, (wF p)⁻¹ * ‖z p‖ ^ 2
      ≤ CEp * ‖(gparams ell k Lu hell S (trivialU _) a Lam).data.Qs z‖ ^ 2 := by
  set y : FSp (geomOf ell k S) := WithLp.toLp 2 (fun p => (wF p)⁻¹ • z p) with hy
  set x : ↥(bondSupp (geomOf ell k S)) := ⟨ErightL hell y, Eright_mem hell hS y⟩ with hx
  have hQx : (gparams ell k Lu hell S (trivialU _) a Lam).data.Q x = y :=
    Eright_rightInv hell hell2 hS hM hR y
  set G := ∑ p, (wF p)⁻¹ * ‖z p‖ ^ 2 with hG
  have hG0 : 0 ≤ G := Finset.sum_nonneg (fun p _ => mul_nonneg (inv_nonneg.mpr (wF_pos hell p).le) (sq_nonneg _))
  have hzy : ⟪z, y⟫ = G := by
    rw [PiLp.inner_apply, hG]
    refine Finset.sum_congr rfl (fun p _ => ?_)
    show ⟪z p, (wF p)⁻¹ • z p⟫ = _
    rw [real_inner_smul_right, real_inner_self_eq_norm_sq]
  have hnF : nF y = G := by
    unfold nF
    refine Finset.sum_congr rfl (fun p _ => ?_)
    show wF p * ‖(wF p)⁻¹ • z p‖ ^ 2 = _
    have hw := wF_pos hell p
    rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hw, mul_pow]
    field_simp
  have hadj : ⟪z, y⟫ = ⟪(gparams ell k Lu hell S (trivialU _) a Lam).data.Qs z, x⟫ := by
    rw [← hQx]
    show ⟪z, ((bondSectorOf (geomOf ell k S) (trivialU _)).Qfull.comp (iE (geomOf ell k S))) x⟫
      = ⟪ContinuousLinearMap.adjoint ((bondSectorOf (geomOf ell k S) (trivialU _)).Qfull.comp (iE (geomOf ell k S))) z, x⟫
    rw [ContinuousLinearMap.adjoint_inner_left, real_inner_comm]
  have hxn : ‖x‖ ^ 2 ≤ CEp * G := by
    rw [← hnF]
    have : ‖x‖ = ‖ErightL hell y‖ := rfl
    rw [this]
    exact Eright_norm_sq hell hell2 hS hM hR y
  set q := ‖(gparams ell k Lu hell S (trivialU _) a Lam).data.Qs z‖ with hq
  have hcs : G ≤ q * ‖x‖ := by
    rw [← hzy, hadj]
    exact real_inner_le_norm _ _
  have hq0 : 0 ≤ q := norm_nonneg _
  have hx0 : 0 ≤ ‖x‖ := norm_nonneg _
  have hC := CEp_pos
  -- G² ≤ q² ‖x‖² ≤ q² CEp G
  have h2 : G ^ 2 ≤ q ^ 2 * (CEp * G) := by
    have := mul_le_mul hcs hcs hG0 (mul_nonneg hq0 hx0)
    calc G ^ 2 = G * G := by ring
      _ ≤ q * ‖x‖ * (q * ‖x‖) := this
      _ = q ^ 2 * ‖x‖ ^ 2 := by ring
      _ ≤ q ^ 2 * (CEp * G) := mul_le_mul_of_nonneg_left hxn (sq_nonneg q)
  by_cases hG' : G = 0
  · rw [hG']; positivity
  · have hGp : 0 < G := lt_of_le_of_ne hG0 (Ne.symm hG')
    have : G * G ≤ (CEp * q ^ 2) * G := by nlinarith
    exact le_of_mul_le_mul_right this hGp

/-- **W6: `Q_U*` injective at non-flat `U` on proper admissible towers** (the exact form consumed by `wellDef_strat`). -/
theorem qs_injective_strat (hell : 0 < ell) (hell2 : 2 ≤ ell) (hS : Admissible ell M R k S) (hM : 0 < M)
    (hR : 8 * ell ≤ R) (U : LinkCfg (scaleUp ell k Lu)) (a : ℝ) (Lam : Set (PeriodicLatticeSite Lu))
    (ε : ℕ → ℝ) (hreg : RegTower ell (bgTower (GF ell k Lu) U) k) (hcl : TowerClass ell k Lu U ε)
    (hε0 : ∀ j, j < k → 0 ≤ ε j) (hsm : ∀ j, j < k → rhoOf ell (ε j) < Real.pi / 2)
    (hsmall : 3 * delW ell k ε ^ 2 * CEp < 1) :
    Function.Injective (gparams ell k Lu hell S U a Lam).data.Qs := by
  set G := geomOf ell k S with hGdef
  set A : ↥(bondSupp G) →L[ℝ] FSp G := ((bondSectorOf G U).Qfull).comp (iE G) with hA
  -- the right inverse into `E₀`
  set E2 : FSp G →ₗ[ℝ] ↥(bondSupp G) := LinearMap.codRestrict (bondSupp G) (ErightL hell)
    (fun y => Eright_mem hell hS y) with hE2
  set T : FSp G →ₗ[ℝ] FSp G := (A : ↥(bondSupp G) →ₗ[ℝ] FSp G).comp E2 with hT
  have hTapp : ∀ y, T y = (bondSectorOf G U).Qfull (ErightL hell y) := fun y => rfl
  -- T y = y − d, d the drift of E' y
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
    have hdr := drift_F hell2 hS hM hR U ε hreg hcl hε0 hsm (ErightL hell y)
    have hny : nF y ≤ 3 * delW ell k ε ^ 2 * ‖ErightL hell y‖ ^ 2 := by
      unfold nF
      refine le_trans (le_of_eq ?_) hdr
      refine Finset.sum_congr rfl (fun p _ => ?_)
      rw [hd p, norm_sub_rev]
    have hEn := Eright_norm_sq hell hell2 hS hM hR y
    have hδ0 : 0 ≤ 3 * delW ell k ε ^ 2 := by positivity
    have hy0' := nF_nonneg hell y
    have : nF y ≤ (3 * delW ell k ε ^ 2 * CEp) * nF y := by
      calc nF y ≤ 3 * delW ell k ε ^ 2 * ‖ErightL hell y‖ ^ 2 := hny
        _ ≤ 3 * delW ell k ε ^ 2 * (CEp * nF y) := mul_le_mul_of_nonneg_left hEn hδ0
        _ = (3 * delW ell k ε ^ 2 * CEp) * nF y := by ring
    have hle : nF y ≤ 0 := by nlinarith
    exact eq_zero_of_nF hell y hle
  have hTsurj : Function.Surjective T := LinearMap.injective_iff_surjective.mp hTinj
  -- Q* injective
  show Function.Injective (ContinuousLinearMap.adjoint A)
  rw [injective_iff_map_eq_zero]
  intro z hz
  obtain ⟨y, hy⟩ := hTsurj z
  have h1 : ⟪z, z⟫ = 0 := by
    calc ⟪z, z⟫ = ⟪A (E2 y), z⟫ := by rw [← hy]; rfl
      _ = ⟪E2 y, ContinuousLinearMap.adjoint A z⟫ := by rw [ContinuousLinearMap.adjoint_inner_right]
      _ = 0 := by rw [hz, inner_zero_right]
  exact inner_self_eq_zero.mp h1

end rinv

end AdalyFormal.W6

#print axioms AdalyFormal.W6.Kop
#print axioms AdalyFormal.W6.Kop_apply
#print axioms AdalyFormal.W6.Kop_eq
#print axioms AdalyFormal.W6.ErightL
#print axioms AdalyFormal.W6.ErightL_apply
#print axioms AdalyFormal.W6.Eright_rightInv
#print axioms AdalyFormal.W6.Eright_mem
#print axioms AdalyFormal.W6.nF_sub_le
#print axioms AdalyFormal.W6.nF_smul
#print axioms AdalyFormal.W6.CEp
#print axioms AdalyFormal.W6.CE_pos
#print axioms AdalyFormal.W6.CEp_pos
#print axioms AdalyFormal.W6.Eright_norm_sq
#print axioms AdalyFormal.W6.eq_zero_of_nF
#print axioms AdalyFormal.W6.gram_lower
#print axioms AdalyFormal.W6.qs_injective_strat
