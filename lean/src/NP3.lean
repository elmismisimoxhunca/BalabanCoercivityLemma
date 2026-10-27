import NP2

/-!
# NP3 -- the covariant bump bound: a row-represented `Δ_U h` on a cube is controlled by `h` on the cube (m1_patch_nonflat, 2026-10-14)

Setting (one constraint cube `C = blockOf y n`, `n ≥ 24`, fitting in the torus): a linear row `ℓ : SiteL2 → su(2)` with
* `hnorm`  : `‖ℓ f‖ ≤ n⁻³ Σ_C ‖f‖`   (the composite average is an average of isometries: BondComposite `norm_Qcomposite_le`);
* `hdrift` : `‖ℓ f − n⁻³ Σ_C f‖ ≤ D n⁻³ Σ_C ‖f‖`, `D ≤ 1/2`   (BondComposite `Qcomposite_drift_pointwise`);
* `hrep`   : `⟪Δ_U h, f⟫ = ⟪c, ℓ f⟫` for every `f` supported in `C`   (the K-orthogonality, NP4);
* link bounds on the cube in the M1 gauge: `frobNorm(U b − 1) ≤ θ/n` and `frobNorm(U(x−e_μ,μ) − U(x,μ)) ≤ θ/n²`.
**`bump_cov`** : `Σ_C ‖Δ_U h‖² ≤ Kq θ ² · n⁻⁴ · Σ_C ‖h‖²`, `Kq θ = 2·72³·(13824 + 12 θ² + 582 θ)`.
No derivative of the field beyond the FIRST-difference clause enters: the zeroth-order coefficient of `Δ_U − Δ` is bounded
by the exact identity `R_W c + R_W⁻¹ c − 2c = −(R_W⁻¹ Y − Y)`, `Y = R_W c − c` (`two_sided_bound`), and the neighbour
difference `‖R_{W'}⁻¹ c − R_W⁻¹ c‖ ≤ 2 frobNorm(W − W') ‖c‖` (`inv_diff_bound`).
No sorry / axiom.
-/
set_option autoImplicit false
set_option maxHeartbeats 8000000

namespace AdalyFormal.M1NonFlat

open scoped RealInnerProductSpace Matrix
open AdalyFormal.Target.ClayStatement
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.StatementLane (pdist)
open AdalyFormal.StatementLaneR8 (Ball pdist_comm pdist_triangle pdist_shift_le pdist_self)
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2 RMap RMap_mul)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond blockOf mem_blockOf)
open AdalyFormal.Balaban.CovariantHjMinimizer (periodicLatticeShiftBack periodicLatticeShift_shiftBack)
open AdalyFormal.Balaban.RMapLipschitz (frobNorm frobSq frobNorm_nonneg frobNorm_sq norm_RMap_sub_self_le
  frobSq_mul_right_isometry)
open AdalyFormal.M1Decay (mulR mulR_apply lapR normSq_site LipP bump bump_supp bump_mem bump_nonneg bump_lapR
  sum_bump_ge mem_cube_of_near r_pos cen pdist_back_le smoothCut sc_lip sc_le_one)

variable {L : PeriodicLatticeExtent}

abbrev SU2 : Type := Matrix.specialUnitaryGroup (Fin 2) ℂ

theorem coe_inv_su2 (W : SU2) : ((W⁻¹ : SU2) : Matrix (Fin 2) (Fin 2) ℂ) = (W : Matrix (Fin 2) (Fin 2) ℂ)ᴴ := rfl

theorem su2_mul_conj (W : SU2) : (W : Matrix (Fin 2) (Fin 2) ℂ) * (W : Matrix (Fin 2) (Fin 2) ℂ)ᴴ = 1 := by
  have h := Matrix.mem_unitaryGroup_iff.mp W.2.1
  rwa [Matrix.star_eq_conjTranspose] at h

theorem su2_conj_mul (W : SU2) : (W : Matrix (Fin 2) (Fin 2) ℂ)ᴴ * (W : Matrix (Fin 2) (Fin 2) ℂ) = 1 := by
  have h := Matrix.mem_unitaryGroup_iff'.mp W.2.1
  rwa [Matrix.star_eq_conjTranspose] at h

theorem frobSq_neg (M : Matrix (Fin 2) (Fin 2) ℂ) : frobSq (-M) = frobSq M := by
  unfold frobSq; simp [Complex.normSq_neg]

theorem frobNorm_inv_sub_one (W : SU2) :
    frobNorm (((W⁻¹ : SU2) : Matrix (Fin 2) (Fin 2) ℂ) - 1) = frobNorm ((W : Matrix (Fin 2) (Fin 2) ℂ) - 1) := by
  unfold frobNorm
  congr 1
  rw [coe_inv_su2]
  have e : (W : Matrix (Fin 2) (Fin 2) ℂ)ᴴ - 1 = (-((W : Matrix (Fin 2) (Fin 2) ℂ) - 1)) * (W : Matrix (Fin 2) (Fin 2) ℂ)ᴴ := by
    rw [neg_sub, Matrix.sub_mul, Matrix.one_mul, su2_mul_conj]
  rw [e, frobSq_mul_right_isometry _ _ (by rw [Matrix.conjTranspose_conjTranspose]; exact su2_conj_mul W), frobSq_neg]

theorem frobNorm_mul_inv_sub_one (W W' : SU2) :
    frobNorm (((W * W'⁻¹ : SU2) : Matrix (Fin 2) (Fin 2) ℂ) - 1)
      = frobNorm ((W : Matrix (Fin 2) (Fin 2) ℂ) - (W' : Matrix (Fin 2) (Fin 2) ℂ)) := by
  unfold frobNorm
  congr 1
  have e : ((W * W'⁻¹ : SU2) : Matrix (Fin 2) (Fin 2) ℂ) - 1
      = ((W : Matrix (Fin 2) (Fin 2) ℂ) - (W' : Matrix (Fin 2) (Fin 2) ℂ)) * (W' : Matrix (Fin 2) (Fin 2) ℂ)ᴴ := by
    rw [Submonoid.coe_mul, coe_inv_su2, Matrix.sub_mul, su2_mul_conj]
  rw [e, frobSq_mul_right_isometry _ _ (by rw [Matrix.conjTranspose_conjTranspose]; exact su2_conj_mul W')]

/-- `‖R_W c + R_W⁻¹ c − 2c‖ ≤ 4 frobNorm(W − 1)² ‖c‖` (exact identity, then the RMap Lipschitz bound twice). -/
theorem two_sided_bound (W : SU2) (c : SuTwo) :
    ‖RMap W c + RMap W⁻¹ c - (2 : ℝ) • c‖ ≤ 4 * frobNorm ((W : Matrix (Fin 2) (Fin 2) ℂ) - 1) ^ 2 * ‖c‖ := by
  set Y := RMap W c - c with hY
  have e : RMap W c + RMap W⁻¹ c - (2 : ℝ) • c = -(RMap W⁻¹ Y - Y) := by
    rw [hY, map_sub, RMap_inv_cancel, two_smul]; abel
  rw [e, norm_neg]
  have h1 := norm_RMap_sub_self_le W⁻¹ Y
  rw [frobNorm_inv_sub_one] at h1
  have h2 := norm_RMap_sub_self_le W c
  have hf := frobNorm_nonneg ((W : Matrix (Fin 2) (Fin 2) ℂ) - 1)
  calc ‖RMap W⁻¹ Y - Y‖ ≤ 2 * frobNorm ((W : Matrix (Fin 2) (Fin 2) ℂ) - 1) * ‖Y‖ := h1
    _ ≤ 2 * frobNorm ((W : Matrix (Fin 2) (Fin 2) ℂ) - 1) * (2 * frobNorm ((W : Matrix (Fin 2) (Fin 2) ℂ) - 1) * ‖c‖) :=
        mul_le_mul_of_nonneg_left h2 (by positivity)
    _ = 4 * frobNorm ((W : Matrix (Fin 2) (Fin 2) ℂ) - 1) ^ 2 * ‖c‖ := by ring

/-- `‖R_{W'}⁻¹ c − R_W⁻¹ c‖ ≤ 2 frobNorm(W − W') ‖c‖`. -/
theorem inv_diff_bound (W W' : SU2) (c : SuTwo) :
    ‖RMap W'⁻¹ c - RMap W⁻¹ c‖ ≤ 2 * frobNorm ((W : Matrix (Fin 2) (Fin 2) ℂ) - (W' : Matrix (Fin 2) (Fin 2) ℂ)) * ‖c‖ := by
  have e : RMap W'⁻¹ c - RMap W⁻¹ c = RMap W⁻¹ (RMap (W * W'⁻¹) c - c) := by
    rw [map_sub, RMap_mul]
    simp only [LinearMap.comp_apply, RMap_inv_cancel]
  rw [e, norm_RMap']
  have := norm_RMap_sub_self_le (W * W'⁻¹) c
  rwa [frobNorm_mul_inv_sub_one] at this

/-- `‖R_W⁻¹ c − c‖ ≤ 2 frobNorm(W − 1) ‖c‖`. -/
theorem inv_sub_bound (W : SU2) (c : SuTwo) :
    ‖RMap W⁻¹ c - c‖ ≤ 2 * frobNorm ((W : Matrix (Fin 2) (Fin 2) ℂ) - 1) * ‖c‖ := by
  have := norm_RMap_sub_self_le W⁻¹ c
  rwa [frobNorm_inv_sub_one] at this

/-- the pointwise deviation of `Δ_U(ψ c)` from `(lapR ψ) c`. -/
theorem lap_cov_const_dev (U : Cfg L) (ψ : PeriodicLatticeSite L → ℝ) (c : SuTwo) (x : PeriodicLatticeSite L)
    (a1 a2 lip : ℝ) (hψ0 : 0 ≤ ψ x) (hψ1 : ψ x ≤ 1)
    (hlipF : ∀ μ : Fin 3, |ψ (periodicLatticeShift x μ) - ψ x| ≤ lip)
    (hlipB : ∀ μ : Fin 3, |ψ (periodicLatticeShiftBack x μ) - ψ x| ≤ lip)
    (h1 : ∀ μ : Fin 3, frobNorm (((U (x, μ) : SU2) : Matrix (Fin 2) (Fin 2) ℂ) - 1) ≤ a1)
    (h1b : ∀ μ : Fin 3, frobNorm (((U (periodicLatticeShiftBack x μ, μ) : SU2) : Matrix (Fin 2) (Fin 2) ℂ) - 1) ≤ a1)
    (h2 : ∀ μ : Fin 3, frobNorm (((U (x, μ) : SU2) : Matrix (Fin 2) (Fin 2) ℂ)
      - ((U (periodicLatticeShiftBack x μ, μ) : SU2) : Matrix (Fin 2) (Fin 2) ℂ)) ≤ a2)
    (ha1 : 0 ≤ a1) (hlip : 0 ≤ lip) :
    ‖(lapFull U (WithLp.toLp 2 (fun z => ψ z • c))) x - lapR ψ x • c‖
      ≤ 3 * (4 * a1 ^ 2 + 2 * a2 + 4 * lip * a1) * ‖c‖ := by
  rw [lap_cov]
  unfold lapR
  rw [Finset.sum_smul, ← Finset.sum_sub_distrib]
  have hpt : ∀ μ : Fin 3, ‖((2 : ℝ) • (ψ x • c) - RMap (U (x, μ)) (ψ (periodicLatticeShift x μ) • c)
        - RMap (U (periodicLatticeShiftBack x μ, μ))⁻¹ (ψ (periodicLatticeShiftBack x μ) • c))
        - (2 * ψ x - ψ (periodicLatticeShift x μ) - ψ (periodicLatticeShiftBack x μ)) • c‖
      ≤ (4 * a1 ^ 2 + 2 * a2 + 4 * lip * a1) * ‖c‖ := by
    intro μ
    set W := U (x, μ)
    set W' := U (periodicLatticeShiftBack x μ, μ)
    set p := ψ (periodicLatticeShift x μ)
    set q := ψ (periodicLatticeShiftBack x μ)
    have e : ((2 : ℝ) • (ψ x • c) - RMap W (p • c) - RMap W'⁻¹ (q • c)) - (2 * ψ x - p - q) • c
        = -(ψ x • (RMap W c + RMap W⁻¹ c - (2 : ℝ) • c) + ψ x • (RMap W'⁻¹ c - RMap W⁻¹ c)
          + (p - ψ x) • (RMap W c - c) + (q - ψ x) • (RMap W'⁻¹ c - c)) := by
      rw [map_smul, map_smul]; module
    rw [e, norm_neg]
    have t1 := two_sided_bound W c
    have t2 := inv_diff_bound W W' c
    have t3 := norm_RMap_sub_self_le W c
    have t4 := inv_sub_bound W' c
    have hc := norm_nonneg c
    have hfW := frobNorm_nonneg ((W : Matrix (Fin 2) (Fin 2) ℂ) - 1)
    have hfW' := frobNorm_nonneg ((W' : Matrix (Fin 2) (Fin 2) ℂ) - 1)
    have hfWW := frobNorm_nonneg ((W : Matrix (Fin 2) (Fin 2) ℂ) - (W' : Matrix (Fin 2) (Fin 2) ℂ))
    have b1 : ‖ψ x • (RMap W c + RMap W⁻¹ c - (2 : ℝ) • c)‖ ≤ 4 * a1 ^ 2 * ‖c‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hψ0]
      have ha := h1 μ
      have : frobNorm ((W : Matrix (Fin 2) (Fin 2) ℂ) - 1) ^ 2 ≤ a1 ^ 2 := pow_le_pow_left₀ hfW ha 2
      calc ψ x * ‖RMap W c + RMap W⁻¹ c - (2 : ℝ) • c‖ ≤ 1 * (4 * a1 ^ 2 * ‖c‖) := by
            apply mul_le_mul hψ1 (t1.trans ?_) (norm_nonneg _) zero_le_one
            exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left this (by norm_num)) hc
        _ = 4 * a1 ^ 2 * ‖c‖ := one_mul _
    have b2 : ‖ψ x • (RMap W'⁻¹ c - RMap W⁻¹ c)‖ ≤ 2 * a2 * ‖c‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hψ0]
      calc ψ x * ‖RMap W'⁻¹ c - RMap W⁻¹ c‖ ≤ 1 * (2 * a2 * ‖c‖) := by
            apply mul_le_mul hψ1 (t2.trans ?_) (norm_nonneg _) zero_le_one
            exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (h2 μ) (by norm_num)) hc
        _ = 2 * a2 * ‖c‖ := one_mul _
    have b3 : ‖(p - ψ x) • (RMap W c - c)‖ ≤ 2 * lip * a1 * ‖c‖ := by
      rw [norm_smul, Real.norm_eq_abs]
      calc |p - ψ x| * ‖RMap W c - c‖ ≤ lip * (2 * a1 * ‖c‖) := by
            apply mul_le_mul (hlipF μ) (t3.trans ?_) (norm_nonneg _) hlip
            exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (h1 μ) (by norm_num)) hc
        _ = 2 * lip * a1 * ‖c‖ := by ring
    have b4 : ‖(q - ψ x) • (RMap W'⁻¹ c - c)‖ ≤ 2 * lip * a1 * ‖c‖ := by
      rw [norm_smul, Real.norm_eq_abs]
      calc |q - ψ x| * ‖RMap W'⁻¹ c - c‖ ≤ lip * (2 * a1 * ‖c‖) := by
            apply mul_le_mul (hlipB μ) (t4.trans ?_) (norm_nonneg _) hlip
            exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (h1b μ) (by norm_num)) hc
        _ = 2 * lip * a1 * ‖c‖ := by ring
    calc _ ≤ ‖ψ x • (RMap W c + RMap W⁻¹ c - (2 : ℝ) • c) + ψ x • (RMap W'⁻¹ c - RMap W⁻¹ c)
            + (p - ψ x) • (RMap W c - c)‖ + ‖(q - ψ x) • (RMap W'⁻¹ c - c)‖ := norm_add_le _ _
      _ ≤ ‖ψ x • (RMap W c + RMap W⁻¹ c - (2 : ℝ) • c) + ψ x • (RMap W'⁻¹ c - RMap W⁻¹ c)‖
            + ‖(p - ψ x) • (RMap W c - c)‖ + ‖(q - ψ x) • (RMap W'⁻¹ c - c)‖ := by
          gcongr; exact norm_add_le _ _
      _ ≤ ‖ψ x • (RMap W c + RMap W⁻¹ c - (2 : ℝ) • c)‖ + ‖ψ x • (RMap W'⁻¹ c - RMap W⁻¹ c)‖
            + ‖(p - ψ x) • (RMap W c - c)‖ + ‖(q - ψ x) • (RMap W'⁻¹ c - c)‖ := by
          gcongr; exact norm_add_le _ _
      _ ≤ 4 * a1 ^ 2 * ‖c‖ + 2 * a2 * ‖c‖ + 2 * lip * a1 * ‖c‖ + 2 * lip * a1 * ‖c‖ := by
          linarith
      _ = (4 * a1 ^ 2 + 2 * a2 + 4 * lip * a1) * ‖c‖ := by ring
  calc ‖∑ μ : Fin 3, (((2 : ℝ) • (ψ x • c) - RMap (U (x, μ)) (ψ (periodicLatticeShift x μ) • c)
        - RMap (U (periodicLatticeShiftBack x μ, μ))⁻¹ (ψ (periodicLatticeShiftBack x μ) • c))
        - (2 * ψ x - ψ (periodicLatticeShift x μ) - ψ (periodicLatticeShiftBack x μ)) • c)‖
      ≤ ∑ μ : Fin 3, (4 * a1 ^ 2 + 2 * a2 + 4 * lip * a1) * ‖c‖ :=
        (norm_sum_le _ _).trans (Finset.sum_le_sum (fun μ _ => hpt μ))
    _ = 3 * (4 * a1 ^ 2 + 2 * a2 + 4 * lip * a1) * ‖c‖ := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]; simp; ring

/-- the bump constant at link size `θ`. -/
noncomputable def Kq (θ : ℝ) : ℝ := 2 * 72 ^ 3 * (13824 + 12 * θ ^ 2 + 582 * θ)

theorem Kq_nonneg {θ : ℝ} (hθ : 0 ≤ θ) : 0 ≤ Kq θ := by unfold Kq; positivity

section cube
variable (y : PeriodicLatticeSite L) (n : ℕ) (hn : 24 ≤ n) (hfit : ∀ μ, (y μ).val + n ≤ L μ + 1)
include hn hfit

theorem n24_ge : (n : ℝ) / 48 ≤ ((n / 24 : ℕ) : ℝ) := by
  have h1 : 24 * (n / 24) + n % 24 = n := Nat.div_add_mod n 24
  have h2 : n % 24 < 24 := Nat.mod_lt _ (by norm_num)
  have h3 : 1 ≤ n / 24 := by omega
  have : (n : ℝ) ≤ 48 * ((n / 24 : ℕ) : ℝ) := by
    have : n ≤ 48 * (n / 24) := by omega
    exact_mod_cast this
  linarith

theorem n72_le : (n : ℝ) / 72 ≤ ((n / 24 / 3 + 1 : ℕ) : ℝ) := by
  have h1 : 72 * (n / 24 / 3) + 72 > n := by omega
  have : (n : ℝ) ≤ 72 * ((n / 24 / 3 + 1 : ℕ) : ℝ) := by
    have : n ≤ 72 * (n / 24 / 3 + 1) := by omega
    exact_mod_cast this
  linarith

/-- the covariant Laplacian of a bump times a constant is supported in the cube. -/
theorem lap_bump_mem (U : Cfg L) (c : SuTwo) (z : PeriodicLatticeSite L)
    (hz : (lapFull U (WithLp.toLp 2 (fun u => bump y n hn hfit u • c))) z ≠ 0) : z ∈ blockOf y n := by
  by_contra hc
  apply hz
  have h0 : ∀ u, pdist z u ≤ 1 → bump y n hn hfit u = 0 := by
    intro u hu
    by_contra hu0
    apply hc
    have h1 := bump_supp y n hn hfit u hu0
    have h2 := pdist_triangle (cen y n hfit) u z
    rw [pdist_comm u z] at h2
    exact mem_cube_of_near y n hn hfit z (by omega)
  rw [lap_cov]
  refine Finset.sum_eq_zero (fun μ _ => ?_)
  show (2 : ℝ) • (bump y n hn hfit z • c) - RMap (U (z, μ)) (bump y n hn hfit (periodicLatticeShift z μ) • c)
    - RMap (U (periodicLatticeShiftBack z μ, μ))⁻¹ (bump y n hn hfit (periodicLatticeShiftBack z μ) • c) = 0
  rw [h0 z (by rw [pdist_self]; omega), h0 _ (pdist_shift_le z μ), h0 _ (pdist_back_le z μ)]
  simp

open Classical in
/-- **the covariant bump bound**. -/
theorem bump_cov (U : Cfg L) (h : SiteL2 L) (ℓ : SiteL2 L →ₗ[ℝ] SuTwo) (c : SuTwo)
    (hrep : ∀ f : SiteL2 L, (∀ z, z ∉ blockOf y n → f z = 0) → ⟪lapFull U h, f⟫ = ⟪c, ℓ f⟫)
    (hnorm : ∀ f : SiteL2 L, ‖ℓ f‖ ≤ ((n : ℝ) ^ 3)⁻¹ * ∑ z ∈ blockOf y n, ‖f z‖)
    (D : ℝ) (hD : D ≤ 1 / 2)
    (hdrift : ∀ f : SiteL2 L, ‖ℓ f - ((n : ℝ) ^ 3)⁻¹ • ∑ z ∈ blockOf y n, f z‖
      ≤ D * (((n : ℝ) ^ 3)⁻¹ * ∑ z ∈ blockOf y n, ‖f z‖))
    (θ : ℝ) (hθ : 0 ≤ θ)
    (hV1 : ∀ z ∈ blockOf y n, ∀ μ : Fin 3,
      frobNorm (((U (z, μ) : SU2) : Matrix (Fin 2) (Fin 2) ℂ) - 1) ≤ θ / n ∧
      frobNorm (((U (periodicLatticeShiftBack z μ, μ) : SU2) : Matrix (Fin 2) (Fin 2) ℂ) - 1) ≤ θ / n)
    (hV2 : ∀ z ∈ blockOf y n, ∀ μ : Fin 3,
      frobNorm (((U (z, μ) : SU2) : Matrix (Fin 2) (Fin 2) ℂ)
        - ((U (periodicLatticeShiftBack z μ, μ) : SU2) : Matrix (Fin 2) (Fin 2) ℂ)) ≤ θ / (n : ℝ) ^ 2) :
    ∑ z ∈ blockOf y n, ‖lapFull U h z‖ ^ 2 ≤ Kq θ ^ 2 * (((n : ℝ) ^ 4)⁻¹ * ∑ z ∈ blockOf y n, ‖h z‖ ^ 2) := by
  set C := blockOf y n with hC
  set k := lapFull U h with hk
  have hn24 : (24 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hn3 : (0 : ℝ) < (n : ℝ) ^ 3 := by positivity
  have hcard : ((C.card : ℕ) : ℝ) = (n : ℝ) ^ 3 := by
    rw [hC, AdalyFormal.M1Site.card_blockOf y n hfit]; push_cast; ring
  set K2 := ∑ z ∈ C, ‖k z‖ ^ 2 with hK2
  set S2 := ∑ z ∈ C, ‖h z‖ ^ 2 with hS2
  have hK20 : 0 ≤ K2 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hS20 : 0 ≤ S2 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  -- (1) K2 ≤ n⁻³ ‖c‖²
  set kC : SiteL2 L := WithLp.toLp 2 (fun z => if z ∈ C then k z else 0) with hkC
  have hkCsupp : ∀ z, z ∉ C → kC z = 0 := fun z hz => by
    show (if z ∈ C then k z else 0) = 0; rw [if_neg hz]
  have hkCinner : ⟪k, kC⟫ = K2 := by
    rw [hK2, PiLp.inner_apply, ← Finset.sum_subset (Finset.subset_univ C)]
    · refine Finset.sum_congr rfl (fun z hz => ?_)
      show ⟪k z, (if z ∈ C then k z else 0)⟫ = _; rw [if_pos hz, real_inner_self_eq_norm_sq]
    · intro z _ hz; show ⟪k z, (if z ∈ C then k z else 0)⟫ = 0; rw [if_neg hz, inner_zero_right]
  have hkCsum : ∑ z ∈ C, ‖kC z‖ = ∑ z ∈ C, ‖k z‖ := by
    refine Finset.sum_congr rfl (fun z hz => ?_)
    show ‖(if z ∈ C then k z else 0)‖ = _; rw [if_pos hz]
  set S1k := ∑ z ∈ C, ‖k z‖ with hS1k
  have hS1k0 : 0 ≤ S1k := Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  have hA : K2 ≤ ‖c‖ * (((n : ℝ) ^ 3)⁻¹ * S1k) := by
    rw [← hkCinner, hrep kC hkCsupp, ← hkCsum]
    exact (real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_left (hnorm kC) (norm_nonneg _))
  have hB : S1k ^ 2 ≤ (n : ℝ) ^ 3 * K2 := by
    have hcs := sq_sum_le_card_mul_sum_sq (s := C) (f := fun z => ‖k z‖)
    rw [hcard] at hcs; exact hcs
  have hK2c : K2 ≤ ((n : ℝ) ^ 3)⁻¹ * ‖c‖ ^ 2 := by
    rcases hK20.eq_or_lt with h0 | hpos
    · rw [← h0]; positivity
    · have h1 : K2 ^ 2 ≤ (‖c‖ * (((n : ℝ) ^ 3)⁻¹ * S1k)) ^ 2 := pow_le_pow_left₀ hK20 hA 2
      have h2 : (‖c‖ * (((n : ℝ) ^ 3)⁻¹ * S1k)) ^ 2 = ‖c‖ ^ 2 * ((n : ℝ) ^ 3)⁻¹ ^ 2 * S1k ^ 2 := by ring
      have h3 : ‖c‖ ^ 2 * ((n : ℝ) ^ 3)⁻¹ ^ 2 * S1k ^ 2 ≤ ‖c‖ ^ 2 * ((n : ℝ) ^ 3)⁻¹ ^ 2 * ((n : ℝ) ^ 3 * K2) :=
        mul_le_mul_of_nonneg_left hB (by positivity)
      have h4 : ‖c‖ ^ 2 * ((n : ℝ) ^ 3)⁻¹ ^ 2 * ((n : ℝ) ^ 3 * K2) = (((n : ℝ) ^ 3)⁻¹ * ‖c‖ ^ 2) * K2 := by
        field_simp
      have h5 : K2 * K2 ≤ (((n : ℝ) ^ 3)⁻¹ * ‖c‖ ^ 2) * K2 := by nlinarith
      exact le_of_mul_le_mul_right h5 hpos
  -- (2) the bump test
  set ψ := bump y n hn hfit with hψ
  set r : ℕ := n / 24 with hr
  have hr0 : 0 < r := r_pos n hn hfit
  have hrR : (n : ℝ) / 48 ≤ (r : ℝ) := n24_ge y n hn hfit
  have hr0' : (0 : ℝ) < r := by exact_mod_cast hr0
  have hψ0 : ∀ z, 0 ≤ ψ z := bump_nonneg y n hn hfit
  have hψ1 : ∀ z, ψ z ≤ 1 := fun z => sc_le_one (cen y n hfit) (4 * (n / 24)) (n / 24) (n / 24) hr0 z
  have hψlip : LipP ψ (1 / (r : ℝ)) := sc_lip (cen y n hfit) (4 * (n / 24)) (n / 24) (n / 24) hr0 hr0
  have hlip48 : 1 / (r : ℝ) ≤ 48 / n := by
    rw [div_le_div_iff₀ hr0' hn0]; linarith
  have hlipF : ∀ z (μ : Fin 3), |ψ (periodicLatticeShift z μ) - ψ z| ≤ 48 / n := by
    intro z μ
    have h1 := hψlip (periodicLatticeShift z μ) z
    have hp : (pdist (periodicLatticeShift z μ) z : ℝ) ≤ 1 := by
      rw [pdist_comm]; exact_mod_cast pdist_shift_le z μ
    calc |ψ (periodicLatticeShift z μ) - ψ z| ≤ 1 / r * (pdist (periodicLatticeShift z μ) z : ℝ) := h1
      _ ≤ 1 / r * 1 := mul_le_mul_of_nonneg_left hp (by positivity)
      _ ≤ 48 / n := by rw [mul_one]; exact hlip48
  have hlipB : ∀ z (μ : Fin 3), |ψ (periodicLatticeShiftBack z μ) - ψ z| ≤ 48 / n := by
    intro z μ
    have h1 := hψlip (periodicLatticeShiftBack z μ) z
    have hp : (pdist (periodicLatticeShiftBack z μ) z : ℝ) ≤ 1 := by
      rw [pdist_comm]; exact_mod_cast pdist_back_le z μ
    calc |ψ (periodicLatticeShiftBack z μ) - ψ z| ≤ 1 / r * (pdist (periodicLatticeShiftBack z μ) z : ℝ) := h1
      _ ≤ 1 / r * 1 := mul_le_mul_of_nonneg_left hp (by positivity)
      _ ≤ 48 / n := by rw [mul_one]; exact hlip48
  set φ : SiteL2 L := WithLp.toLp 2 (fun z => ψ z • c) with hφ
  have hφsupp : ∀ z, z ∉ C → φ z = 0 := by
    intro z hz
    show ψ z • c = 0
    have : ψ z = 0 := by by_contra h0; exact hz (bump_mem y n hn hfit z h0)
    rw [this, zero_smul]
  set Spsi := ∑ z ∈ C, ψ z with hSpsi
  have hSpsi0 : 0 ≤ Spsi := Finset.sum_nonneg (fun z _ => hψ0 z)
  have hSpsige : ((n : ℝ) / 72) ^ 3 ≤ Spsi := by
    have h1 := sum_bump_ge y n hn hfit
    have h2 := n72_le y n hn hfit
    exact (pow_le_pow_left₀ (by positivity) h2 3).trans h1
  -- lower bound: ⟪k, φ⟫ ≥ ½ n⁻³ Spsi ‖c‖²
  have hlow : 1 / 2 * (((n : ℝ) ^ 3)⁻¹ * Spsi) * ‖c‖ ^ 2 ≤ ⟪k, φ⟫ := by
    rw [hrep φ hφsupp]
    have hsumφ : ∑ z ∈ C, φ z = Spsi • c := by
      rw [hSpsi, Finset.sum_smul]
    have hsumφn : ∑ z ∈ C, ‖φ z‖ = Spsi * ‖c‖ := by
      rw [hSpsi, Finset.sum_mul]
      refine Finset.sum_congr rfl (fun z _ => ?_)
      show ‖ψ z • c‖ = _
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (hψ0 z)]
    have hd := hdrift φ
    rw [hsumφ, hsumφn] at hd
    set e := ℓ φ - ((n : ℝ) ^ 3)⁻¹ • (Spsi • c) with he
    have hℓ : ℓ φ = (((n : ℝ) ^ 3)⁻¹ * Spsi) • c + e := by rw [he, smul_smul]; abel
    rw [hℓ, inner_add_right, real_inner_smul_right, real_inner_self_eq_norm_sq]
    have hce : -(‖c‖ * (D * (((n : ℝ) ^ 3)⁻¹ * (Spsi * ‖c‖)))) ≤ ⟪c, e⟫ := by
      have := neg_abs_le ⟪c, e⟫
      have h2 := abs_real_inner_le_norm c e
      have h3 : ‖c‖ * ‖e‖ ≤ ‖c‖ * (D * (((n : ℝ) ^ 3)⁻¹ * (Spsi * ‖c‖))) := mul_le_mul_of_nonneg_left hd (norm_nonneg _)
      linarith
    have hD0 : D * (((n : ℝ) ^ 3)⁻¹ * Spsi) * ‖c‖ ^ 2 ≤ 1 / 2 * (((n : ℝ) ^ 3)⁻¹ * Spsi) * ‖c‖ ^ 2 := by
      have : 0 ≤ (((n : ℝ) ^ 3)⁻¹ * Spsi) * ‖c‖ ^ 2 := by positivity
      nlinarith
    nlinarith
  -- upper bound: ⟪k, φ⟫ ≤ M ‖c‖ Σ_C ‖h‖
  set M : ℝ := (13824 + 12 * θ ^ 2 + 582 * θ) / (n : ℝ) ^ 2 with hM
  have hlapφ : ∀ z ∈ C, ‖lapFull U φ z‖ ≤ M * ‖c‖ := by
    intro z hz
    have hdev := lap_cov_const_dev U ψ c z (θ / n) (θ / (n : ℝ) ^ 2) (48 / n) (hψ0 z) (hψ1 z)
      (hlipF z) (hlipB z) (fun μ => (hV1 z hz μ).1) (fun μ => (hV1 z hz μ).2) (hV2 z hz) (by positivity)
      (by positivity)
    have hlr : |lapR ψ z| ≤ 13824 / (n : ℝ) ^ 2 := by
      have h1 := bump_lapR y n hn hfit z
      have h2 : 6 / ((r : ℝ) * r) ≤ 13824 / (n : ℝ) ^ 2 := by
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        have : ((n : ℝ) / 48) ^ 2 ≤ (r : ℝ) ^ 2 := pow_le_pow_left₀ (by positivity) hrR 2
        nlinarith
      exact h1.trans h2
    have e1 : ‖lapFull U φ z‖ ≤ ‖lapFull U φ z - lapR ψ z • c‖ + ‖lapR ψ z • c‖ := by
      have := norm_add_le (lapFull U φ z - lapR ψ z • c) (lapR ψ z • c)
      rwa [sub_add_cancel] at this
    rw [norm_smul, Real.norm_eq_abs] at e1
    have e2 : 3 * (4 * (θ / n) ^ 2 + 2 * (θ / (n : ℝ) ^ 2) + 4 * (48 / n) * (θ / n)) = (12 * θ ^ 2 + 582 * θ) / (n : ℝ) ^ 2 := by
      field_simp; ring
    rw [e2] at hdev
    have : |lapR ψ z| * ‖c‖ ≤ 13824 / (n : ℝ) ^ 2 * ‖c‖ := mul_le_mul_of_nonneg_right hlr (norm_nonneg _)
    calc ‖lapFull U φ z‖ ≤ (12 * θ ^ 2 + 582 * θ) / (n : ℝ) ^ 2 * ‖c‖ + 13824 / (n : ℝ) ^ 2 * ‖c‖ := by linarith
      _ = M * ‖c‖ := by rw [hM]; ring
  set S1h := ∑ z ∈ C, ‖h z‖ with hS1h
  have hS1h0 : 0 ≤ S1h := Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  have hup : ⟪k, φ⟫ ≤ M * ‖c‖ * S1h := by
    rw [hk, lapFull_symm, PiLp.inner_apply, ← Finset.sum_subset (Finset.subset_univ C)]
    · rw [hS1h, Finset.mul_sum]
      refine Finset.sum_le_sum (fun z hz => ?_)
      calc ⟪h z, lapFull U φ z⟫ ≤ ‖h z‖ * ‖lapFull U φ z‖ := real_inner_le_norm _ _
        _ ≤ ‖h z‖ * (M * ‖c‖) := mul_le_mul_of_nonneg_left (hlapφ z hz) (norm_nonneg _)
        _ = M * ‖c‖ * ‖h z‖ := by ring
    · intro z _ hz
      have : lapFull U φ z = 0 := by
        by_contra h0; exact hz (lap_bump_mem y n hn hfit U c z h0)
      show ⟪h z, lapFull U φ z⟫ = 0
      rw [this, inner_zero_right]
  -- combine: ‖c‖ ≤ 2·72³ · n² M · n⁻³ ... in squared form
  have hM0 : 0 ≤ M := by rw [hM]; positivity
  have hS1hsq : S1h ^ 2 ≤ (n : ℝ) ^ 3 * S2 := by
    have hcs := sq_sum_le_card_mul_sum_sq (s := C) (f := fun z => ‖h z‖)
    rw [hcard] at hcs; exact hcs
  have hc1 : ‖c‖ ^ 2 / (2 * 72 ^ 3) ≤ M * ‖c‖ * S1h := by
    have h1 : 1 / 2 * (((n : ℝ) ^ 3)⁻¹ * ((n : ℝ) / 72) ^ 3) * ‖c‖ ^ 2
        ≤ 1 / 2 * (((n : ℝ) ^ 3)⁻¹ * Spsi) * ‖c‖ ^ 2 := by
      have : ((n : ℝ) ^ 3)⁻¹ * ((n : ℝ) / 72) ^ 3 ≤ ((n : ℝ) ^ 3)⁻¹ * Spsi :=
        mul_le_mul_of_nonneg_left hSpsige (by positivity)
      nlinarith [sq_nonneg ‖c‖]
    have e : 1 / 2 * (((n : ℝ) ^ 3)⁻¹ * ((n : ℝ) / 72) ^ 3) * ‖c‖ ^ 2 = ‖c‖ ^ 2 / (2 * 72 ^ 3) := by
      field_simp
    linarith [hlow, hup]
  have hcc : ‖c‖ ≤ 2 * 72 ^ 3 * M * S1h := by
    rcases (norm_nonneg c).eq_or_lt with h0 | hpos
    · rw [← h0]; positivity
    · have : ‖c‖ * ‖c‖ ≤ ‖c‖ * (2 * 72 ^ 3 * M * S1h) := by
        have := hc1
        rw [div_le_iff₀ (by norm_num)] at this
        nlinarith
      exact le_of_mul_le_mul_left this hpos
  have hcsq : ‖c‖ ^ 2 ≤ (2 * 72 ^ 3 * M) ^ 2 * ((n : ℝ) ^ 3 * S2) := by
    have h1 := pow_le_pow_left₀ (norm_nonneg c) hcc 2
    calc ‖c‖ ^ 2 ≤ (2 * 72 ^ 3 * M * S1h) ^ 2 := h1
      _ = (2 * 72 ^ 3 * M) ^ 2 * S1h ^ 2 := by ring
      _ ≤ (2 * 72 ^ 3 * M) ^ 2 * ((n : ℝ) ^ 3 * S2) := mul_le_mul_of_nonneg_left hS1hsq (sq_nonneg _)
  calc K2 ≤ ((n : ℝ) ^ 3)⁻¹ * ‖c‖ ^ 2 := hK2c
    _ ≤ ((n : ℝ) ^ 3)⁻¹ * ((2 * 72 ^ 3 * M) ^ 2 * ((n : ℝ) ^ 3 * S2)) :=
        mul_le_mul_of_nonneg_left hcsq (by positivity)
    _ = Kq θ ^ 2 * (((n : ℝ) ^ 4)⁻¹ * S2) := by
        rw [hM]; unfold Kq; field_simp

end cube

end AdalyFormal.M1NonFlat

#print axioms AdalyFormal.M1NonFlat.frobNorm_inv_sub_one
#print axioms AdalyFormal.M1NonFlat.frobNorm_mul_inv_sub_one
#print axioms AdalyFormal.M1NonFlat.two_sided_bound
#print axioms AdalyFormal.M1NonFlat.inv_diff_bound
#print axioms AdalyFormal.M1NonFlat.lap_cov_const_dev
#print axioms AdalyFormal.M1NonFlat.lap_bump_mem
#print axioms AdalyFormal.M1NonFlat.bump_cov
