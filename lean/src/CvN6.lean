import CvN5c
import GenCl4

/-!
# CvN6 -- COVERAGE IS NECESSARY: the coverage-free headlines are FALSE (lane cover_necessary_20261016)

Instance: the isolated-block tower `gcS ell M R` of lane general_class_20261015 (GenCl2), with NC4's `Λ`, and its tip site
`x_t` (GenCl4), which lies in no class cube (r8's factor-12 cubes, and general cubes of every factor `f ≥ 10`) when `3 ≤ ell ≤ 7`.
The free bond is `b_t = (x_t, 1)`; the plaquette `p_t = (x_t; 0, 1)` lies in `plaqIn Ω₀`.

* `tip_dist`: every site of `Ω₁` is at `ℓ¹`-distance at least `RM - M + 1` from `x_t`.
* **`exists_singular_tip`**: for `3 ≤ ell ≤ 7`, `M ≥ 2`, `R ≥ 9 ell + 1`, `0 < a < 1` and any `Λ`, there is `v ∈ SU(2)` with
  `Ginv` (3.122) NOT invertible at `1[b_t ↦ v]` (continuity of `θ ↦ Ginv(1[b_t ↦ vPath θ])` on `[0, π]`, PSD at `θ = 0`, a negative
  direction at `θ = π`, CvN1 `exists_not_isUnit`).
* **`tip_counterexample`**: on these instances (headline regime: `TorusOK`, `Admissible`, `LambdaOK2`), for every `γ₀ ≥ 0` the
  printed inequality `InstIneq` FAILS at a configuration that is in r8's class `PerCubeRegular2 .. 12 ..` and in the general class
  `PerCubeRegularG .. F ..` for every `F` and every `α₀ > 0`.
* **`not_P428Target8G`**: `¬ P428Target8G F` for EVERY `F` (general per-cube class, no coverage).
* **`not_P428Target8NC`**: `¬ P428Target8NC` (the r8 headline with `CoversOm0p` removed).
-/
set_option autoImplicit false
set_option maxRecDepth 8000
set_option maxHeartbeats 2000000

namespace AdalyFormal.CoverNec

open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLane2
open AdalyFormal.StatementLaneG
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.NoCover
open AdalyFormal.GeneralClass
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2 suTwoWitness suTwoWitness_ne_zero)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
open AdalyFormal.NonVac (pcd_self')

theorem tip_dist {ell M R : ℕ} (hell : 2 ≤ ell) (hell0 : 0 < ell) (hM : 0 < M) (hR : 1 ≤ R) (y : GSite ell M R)
    (hy : y ∈ gcOm1 ell M R) : R * M - M + 1 ≤ pdist y (xtG ell M R hell0 hM) := by
  have hN := nc_scaleUp (ell := ell) (R := R) hell0 hM
  obtain ⟨e1, e2, e3, -, e5⟩ := nc_expand ell M R
  have hme : M * ell = ell * M := Nat.mul_comm _ _
  have hRM : M ≤ R * M := Nat.le_mul_of_pos_left M (by omega)
  have hRMl : R * M ≤ ell * (R * M) := Nat.le_mul_of_pos_left _ hell0
  have hMl : 2 * M ≤ M * ell := by rw [mul_comm 2 M]; exact Nat.mul_le_mul_left M hell
  have hlt : ∀ w : GSite ell M R, ∀ ν, (w ν).val < ncN ell M R := fun w ν => by
    have := (w ν).isLt; have := hN ν; omega
  obtain ⟨hx0, -, -⟩ := xtG_val (R := R) hell0 hM
  have hx0N := hlt (xtG ell M R hell0 hM) 0
  have hy0N := hlt y 0
  have hc : R * M - M + 1 ≤ pcd (ncN ell M R) ((xtG ell M R hell0 hM) 0).val (y 0).val := by
    rw [hx0] at hx0N ⊢
    rcases hy with hy | ⟨hy0, -, -⟩
    · rw [e1, e2] at hy
      apply pcd_ge <;> split_ifs <;> rw [e3, e5] at * <;> omega
    · apply pcd_ge <;> split_ifs <;> rw [e3, e5] at * <;> omega
  have h3 := pdist_three y (xtG ell M R hell0 hM)
  simp only [hN] at h3
  have h4 : pcd (ncN ell M R) (y 0).val ((xtG ell M R hell0 hM) 0).val =
      pcd (ncN ell M R) ((xtG ell M R hell0 hM) 0).val (y 0).val := AdalyFormal.StatementLaneR8.pcd_comm _ _ _
  omega

/-- the hypotheses of the analytic step, on the tip instance. -/
theorem tip_far9 {ell M R : ℕ} (hell : 3 ≤ ell) (hell0 : 0 < ell) (hM : 0 < M) (hR : 9 * ell + 1 ≤ R) :
    ∀ y ∈ (gcS ell M R).Om 1, 9 * ell < pdist y (xtG ell M R hell0 hM) := by
  intro y hy
  rw [gcS_om1] at hy
  have h1 := tip_dist (by omega) hell0 hM (by omega) y hy
  have h2 : R ≤ R * M - M + 1 := by
    have : R * M - M = (R - 1) * M := by rw [Nat.sub_mul, one_mul]
    rw [this]
    have : R - 1 ≤ (R - 1) * M := Nat.le_mul_of_pos_right _ hM
    omega
  omega

theorem tip_outside {ell M R : ℕ} (hell : 3 ≤ ell) (hell0 : 0 < ell) (hM : 0 < M) (hR : 1 ≤ R) :
    ∃ w, w ∉ (gcS ell M R).Om 0 := by
  have hN := nc_scaleUp (ell := ell) (R := R) hell0 hM
  obtain ⟨-, -, -, -, e5⟩ := nc_expand ell M R
  have hv : 2 * (M * ell) + M < scaleUp ell 1 (ncLu M R) 1 + 1 := by
    rw [hN 1, e5]
    have hme : M * ell = ell * M := Nat.mul_comm _ _
    have hRM : 0 < ell * (R * M) := Nat.mul_pos hell0 (Nat.mul_pos (by omega) hM)
    have h3M : 3 * M ≤ M * ell := by rw [mul_comm 3 M]; exact Nat.mul_le_mul_left M hell
    omega
  refine ⟨Function.update (xtG ell M R hell0 hM) 1 ⟨2 * (M * ell) + M, hv⟩,
    tip_far (by omega) hM hR _ ?_ (Or.inl ?_)⟩
  · obtain ⟨h0, -, -⟩ := xtG_val (R := R) hell0 hM
    rw [Function.update_of_ne (by decide : (0 : Fin 3) ≠ 1)]
    exact h0
  · rw [Function.update_self]

theorem tip_side {ell M R : ℕ} (hell0 : 0 < ell) (hM : 0 < M) : ∀ μ, 1 ≤ scaleUp ell 1 (ncLu M R) μ := fun μ => by
  have hN := nc_scaleUp (ell := ell) (R := R) hell0 hM
  obtain ⟨-, -, -, -, e5⟩ := nc_expand ell M R
  have h := hN μ
  have : 1 < ncN ell M R := by
    rw [e5]; have : 0 < ell * M := Nat.mul_pos hell0 hM; omega
  omega

theorem exists_singular_GinvAt {ell M R : ℕ} (hell : 3 ≤ ell) (hell7 : ell ≤ 7) (hell0 : 0 < ell) (hM2 : 2 ≤ M)
    (hM : 0 < M) (hR : 9 * ell + 1 ≤ R) {a : ℝ} (ha : 0 < a) (ha1 : a < 1) (Lam : Set (PeriodicLatticeSite (ncLu M R))) :
    ∃ t : ℝ, ¬ IsUnit (GinvAt ell hell0 (ncLu M R) (gcS ell M R) a Lam (Upath (xtG ell M R hell0 hM, 1) t)) := by
  have hfar : ∀ y ∈ (gcS ell M R).Om 1, 9 * ell < pdist y ((xtG ell M R hell0 hM, 1) : Bond _).1 :=
    tip_far9 hell hell0 hM hR
  have hne := tip_outside hell hell0 hM (by omega) (R := R)
  have hL := tip_side (R := R) hell0 hM
  have hb0 : ((xtG ell M R hell0 hM, 1) : Bond (scaleUp ell 1 (ncLu M R))).1 ∈ (gcS ell M R).Om 0 :=
    xtG_om0 (by omega) hM (by omega)
  have hp0 : pStar (xtG ell M R hell0 hM) ∈ plaqIn ((gcS ell M R).Om 0) := pStar_plaqIn_tip (by omega) hM2 (by omega)
  have hA := Ginv_path_continuous hell0 (gcS ell M R) ha Lam ((xtG ell M R hell0 hM, 1) : Bond _) hfar hne
  have hs : ∀ t (u w : ↥(bondSupp (geomOf ell 1 (gcS ell M R)))),
      ⟪GinvAt ell hell0 (ncLu M R) (gcS ell M R) a Lam (Upath (xtG ell M R hell0 hM, 1) t) u, w⟫ =
        ⟪u, GinvAt ell hell0 (ncLu M R) (gcS ell M R) a Lam (Upath (xtG ell M R hell0 hM, 1) t) w⟫ :=
    fun t u w => BaseDataS.Ginv_symm
      (gparams ell 1 (ncLu M R) hell0 (gcS ell M R) (Upath (xtG ell M R hell0 hM, 1) t) a Lam).data
      (IngrBParams.data_laws _) u w
  have h0 : ∀ u, 0 ≤ ⟪u, GinvAt ell hell0 (ncLu M R) (gcS ell M R) a Lam (Upath (xtG ell M R hell0 hM, 1) 0) u⟫ :=
    fun u => Ginv_psd_one (gparams ell 1 (ncLu M R) hell0 (gcS ell M R) (Upath (xtG ell M R hell0 hM, 1) 0) a Lam)
      (Upath_zero _) ha.le u
  obtain ⟨Y, hY⟩ := Ginv_neg_flip hell0 (gcS ell M R) hL ha.le Lam ((xtG ell M R hell0 hM, 1) : Bond _) hfar hb0
    (pStar (xtG ell M R hell0 hM)) hp0 (bStar_mem _) suTwoWitness
  have hX : 0 < ‖suTwoWitness‖ ^ 2 := by
    have := norm_pos_iff.2 suTwoWitness_ne_zero; positivity
  have hneg : ⟪Y, GinvAt ell hell0 (ncLu M R) (gcS ell M R) a Lam (Upath (xtG ell M R hell0 hM, 1) Real.pi) Y⟫ < 0 := by
    rw [Upath_pi]
    have hY' : ⟪Y, GinvAt ell hell0 (ncLu M R) (gcS ell M R) a Lam (Upi (xtG ell M R hell0 hM, 1)) Y⟫ ≤
        (a - 1) * ‖suTwoWitness‖ ^ 2 := hY
    have : (a - 1) * ‖suTwoWitness‖ ^ 2 < 0 := mul_neg_of_neg_of_pos (by linarith) hX
    exact lt_of_le_of_lt hY' this
  obtain ⟨t, -, ht⟩ := exists_not_isUnit _ hA hs Real.pi_pos.le h0 hneg
  exact ⟨t, ht⟩

theorem exists_singular_tip {ell M R : ℕ} (hell : 3 ≤ ell) (hell7 : ell ≤ 7) (hM2 : 2 ≤ M) (hR : 9 * ell + 1 ≤ R)
    {a : ℝ} (ha : 0 < a) (ha1 : a < 1) (Lam : Set (PeriodicLatticeSite (ncLu M R))) :
    ∃ v : Matrix.specialUnitaryGroup (Fin 2) ℂ, ¬ IsUnit (gparams ell 1 (ncLu M R) (by omega) (gcS ell M R)
      (Function.update (fun _ => 1) ((xtG ell M R (by omega) (by omega), 1) : Bond _) v) a Lam).data.Ginv := by
  obtain ⟨t, ht⟩ := exists_singular_GinvAt hell hell7 (by omega) hM2 (by omega) hR ha ha1 Lam
  exact ⟨vPath t, ht⟩

/-- **the counterexample instance, stated with every hypothesis of the headline's inner claim.** -/
theorem tip_counterexample {m R : ℕ} (hm : 1 ≤ m) (hR : 28 ≤ R) {a : ℝ} (ha : 0 < a) (ha1 : a < 1) :
    ∃ v : Matrix.specialUnitaryGroup (Fin 2) ℂ,
      TorusOK 3 (3 ^ m) (ncLu (3 ^ m) R) ∧ Admissible 3 (3 ^ m) R 1 (gcS 3 (3 ^ m) R) ∧
      LambdaOK2 3 (3 ^ m) R 1 (gcS 3 (3 ^ m) R) (ncLam (3 ^ m) R) ∧ (ncLam (3 ^ m) R).Nonempty ∧
      (∀ α₀ : ℝ, 0 < α₀ → PerCubeRegular2 3 (3 ^ m) 12 1 (gcS 3 (3 ^ m) R) α₀ ((3 : ℝ) ^ 1)⁻¹
        (Function.update (fun _ => 1) ((xtG 3 (3 ^ m) R (by norm_num) (by positivity), 1) : Bond _) v)) ∧
      (∀ (F : ℕ) (α₀ : ℝ), 0 < α₀ → PerCubeRegularG 3 (3 ^ m) F 1 (gcS 3 (3 ^ m) R) α₀ ((3 : ℝ) ^ 1)⁻¹
        (Function.update (fun _ => 1) ((xtG 3 (3 ^ m) R (by norm_num) (by positivity), 1) : Bond _) v)) ∧
      ∀ γ₀ : ℝ, 0 ≤ γ₀ → ¬ InstIneq 3 1 (by norm_num) a (ncLu (3 ^ m) R) γ₀ (gcS 3 (3 ^ m) R) (ncLam (3 ^ m) R)
        (Function.update (fun _ => 1) ((xtG 3 (3 ^ m) R (by norm_num) (by positivity), 1) : Bond _) v) := by
  have hM : 0 < 3 ^ m := by positivity
  have hM2 : 2 ≤ 3 ^ m := le_trans (by norm_num) (Nat.le_self_pow (by omega) 3)
  have hdvd : 3 ∣ 3 ^ m := dvd_pow_self 3 (by omega)
  obtain ⟨v, hv⟩ := exists_singular_tip (ell := 3) (M := 3 ^ m) (R := R) le_rfl (by norm_num) hM2 (by omega) ha ha1
    (ncLam (3 ^ m) R)
  have hunc := gc_tip_uncovered (ell := 3) (R := R) (by norm_num) (by norm_num) hM (by omega)
  have hη : (0 : ℝ) < ((3 : ℝ) ^ 1)⁻¹ := by norm_num
  refine ⟨v, torusOK_nc le_rfl hdvd hM, gc_admissible (by norm_num) hM, lambdaOK2_gc le_rfl hdvd hM (by omega),
    ncLam_nonempty hM, ?_, ?_, ?_⟩
  · intro α₀ hα
    exact perCube_update (perCube_one (by norm_num) hM (by norm_num) hα hη) _
      (fun sites j hq => hunc 12 sites j (isClassCube_toG (gc_admissible (R := R) (by norm_num) hM).1 (by norm_num) hq)) v
  · intro F α₀ hα
    exact perCubeG_update (perCubeG_one (by norm_num) hM hα hη) _ (fun f sites j _ hq => hunc f sites j hq) v
  · intro γ₀ hγ
    exact instIneq_fails_of_not_unit_gc le_rfl hdvd hM ha hγ _ hv

/-- **`¬ P428Target8G F` for every `F`**: the general-class headline without coverage is false. -/
theorem not_P428Target8G (F : ℕ) : ¬ P428Target8G F := by
  intro h
  have h1 : P428Target8G (max F 1) := P428Target8G.mono (le_max_left F 1) h
  obtain ⟨m₀, hm₀, hm⟩ := gc_tip_forces_unit (le_max_right F 1) h1 3 le_rfl (by norm_num) (1 / 2) (by norm_num)
  obtain ⟨R₀, hR⟩ := hm m₀ le_rfl
  have hM2 : 2 ≤ 3 ^ m₀ := le_trans (by norm_num) (Nat.le_self_pow (by omega) 3)
  obtain ⟨v, hv⟩ := exists_singular_tip (ell := 3) (M := 3 ^ m₀) (R := max R₀ 28) le_rfl (by norm_num) hM2
    (le_max_right _ _) (a := 1 / 2) (by norm_num) (by norm_num) (ncLam (3 ^ m₀) (max R₀ 28))
  exact hv (hR (max R₀ 28) (le_max_left _ _) (by omega) v)

/-- **`¬ P428Target8NC`**: the r8 headline with the coverage hypothesis `CoversOm0p` removed is false. -/
theorem not_P428Target8NC : ¬ AdalyFormal.NoCover.P428Target8NC := fun h =>
  not_P428Target8G 12 (AdalyFormal.GeneralClass.P428Target8NC.toG le_rfl h)

#print axioms tip_dist
#print axioms tip_far9
#print axioms tip_outside
#print axioms tip_side
#print axioms exists_singular_GinvAt
#print axioms exists_singular_tip
#print axioms tip_counterexample
#print axioms not_P428Target8G
#print axioms not_P428Target8NC

end AdalyFormal.CoverNec
