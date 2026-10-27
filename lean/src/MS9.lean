import MS8

/-!
# MS9 -- discharge of S1's tower hypothesis `hT` from stratified fine-link and fine-plaquette bounds (one gauge)

Admissible tower `S` (`Admissible ℓ M R k S`), geometry `G = geomOf ℓ k S`.  Hypotheses (stated on the tower sets; equivalent to
the PLAN §1.1 `M1Regime` clauses `hlinks`/`hplaq` read through `bstrat`/`pstrat` = both-endpoint strata):
* `hlink` : a fine link with both endpoints in `Ω_{j0}` has `dv ≤ ρ/ℓ^{j0}`;
* `hplaq` : a fine plaquette word `pw 1 U y ν μ` whose four corners lie in `Ω_{j0}` has `dv ≤ ρ/ℓ^{2 j0}`;
* collar `18 ≤ R·M`, no wrap `4ℓ^k < L_σ + 1`, smallness `4·10⁶ ℓ² ρ ≤ 1` (all k-free).
Conclusion **`hT_of_regime`**: S1/S3's tower hypothesis (MSal form) with `ρ_T = (ℓ + 3πℓ²)ρ`:
for `i < j`, `z` an `ℓ^i`-aligned site of a level-`j` block, `‖Ū^{(i)}(z,μ) − 1‖_F ≤ ρ_T ℓ^i/ℓ^j`.
Route: `link_tower_na_loc` (curvature_blocking NB25) at level `i` with `e = ρ/ℓ^{j−1}`, `q0 = ρ/ℓ^{2(j−1)}`, the cones
contained in the box `off ≤ 4ℓ^i` (MS8), which lies in `Ω_{j−1}` by admissibility clause 5 at level `j − 1`.
**`site_coercive_M1`** : S1 for such `U` (no `hT` hypothesis), constant `(1 − 216ρ_T²)/max(6, 16/(3a))`.
-/
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 8000

namespace AdalyFormal.M1Site

open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.SiteCoercivity
open AdalyFormal.StatementLane (Tower Admissible bigSide BlockClosed pdist pcd)
open AdalyFormal.Balaban.AdmissibleSubspace (blockOf mem_blockOf CoarseLattice mem_CoarseLattice Bond)
open AdalyFormal.Balaban.CoarseCurl (coarseShift coarseShift_apply_ne coarseShift_val_eq)
open AdalyFormal.Balaban.RMapLipschitz (frobNorm)
open AdalyFormal.Balaban.SuTwoLogExp (SU2)
open AdalyFormal.CurvBlock (off dv pw off_shift_self off_shift_ne link_tower_na_loc)

variable {Lf : PeriodicLatticeExtent}

theorem pcd_le_off (z v : PeriodicLatticeSite Lf) (σ : Fin 3) :
    pcd (Lf σ + 1) (v σ).val (z σ).val ≤ off z v σ := by
  unfold pcd off
  have hv := (v σ).isLt
  have hz := (z σ).isLt
  by_cases hle : z σ ≤ v σ
  · rw [Fin.sub_val_of_le hle]
    have : ¬ ((v σ).val ≤ (z σ).val) ∨ (v σ).val = (z σ).val := by
      rw [Fin.le_def] at hle; omega
    split_ifs with h
    · rw [Fin.le_def] at hle; omega
    · exact min_le_left _ _
  · push Not at hle
    have hval : (v σ - z σ).val = (Lf σ + 1) - ((z σ).val - (v σ).val) := by
      rw [Fin.sub_def]
      simp only
      rw [Fin.lt_def] at hle
      rw [Nat.mod_eq_of_lt (by omega)]
      omega
    rw [hval]
    rw [Fin.lt_def] at hle
    rw [if_pos (by omega)]
    exact min_le_right _ _

theorem pdist_le_off (z v : PeriodicLatticeSite Lf) : pdist v z ≤ ∑ σ : Fin 3, off z v σ := by
  unfold pdist
  exact Finset.sum_le_sum (fun σ _ => pcd_le_off z v σ)

theorem off_shift_one_le (z w : PeriodicLatticeSite Lf) (ν σ : Fin 3) :
    off z (coarseShift w 1 ν) σ ≤ off z w σ + 1 := by
  by_cases hσ : σ = ν
  · subst hσ; rw [off_shift_self]; exact Nat.mod_le _ _
  · rw [off_shift_ne _ _ _ hσ]; omega

/-- sites of a level-`j` block lie in `Ω_j` -/
theorem block_sub_Om {ell M R k : ℕ} (hell : 0 < ell) {S : Tower Lf} (hS : Admissible ell M R k S)
    {j : ℕ} (hj : j ≤ k) {y : PeriodicLatticeSite Lf} (hy : y ∈ (geomOf ell k S).Lam j)
    {x : PeriodicLatticeSite Lf} (hx : x ∈ blockOf y (ell ^ j)) : x ∈ S.Om j := by
  obtain ⟨-, -, -, hblk, -, -⟩ := hS
  obtain ⟨hydiv, hyOm, -⟩ := hy
  rw [mem_blockOf] at hx
  refine hblk j hj y hyOm x (fun μ => ?_)
  obtain ⟨h1, h2⟩ := hx μ
  have := blk_div (ell ^ j) M (y μ).val (x μ).val (pow_pos hell j) (hydiv μ) h1 h2
  show (x μ).val / (M * ell ^ j) = (y μ).val / (M * ell ^ j)
  rw [mul_comm M]; exact this.symm

/-- the forward box of side `D` at a point of `Ω_j` lies in `Ω_{j−1}` when `3D ≤ R M ℓ^{j−1}` -/
theorem region_sub_Om {ell M R k : ℕ} {S : Tower Lf} (hS : Admissible ell M R k S) {j : ℕ} (hj : j ≤ k)
    {z : PeriodicLatticeSite Lf} (hz : z ∈ S.Om (j + 1)) (D : ℕ) (hD : 3 * D ≤ R * bigSide M ell j)
    {v : PeriodicLatticeSite Lf} (hv : ∀ σ, off z v σ ≤ D) : v ∈ S.Om j := by
  obtain ⟨-, -, -, -, hcol, -⟩ := hS
  by_contra hvj
  have h1 := hcol j hj v hvj z hz
  have h2 := pdist_le_off z v
  have h3 : ∑ σ : Fin 3, off z v σ ≤ 3 * D := by
    rw [Fin.sum_univ_three]; have := hv 0; have := hv 1; have := hv 2; omega
  omega

/-- **`hT` from the stratified regime** -/
theorem hT_of_regime (ell M R k : ℕ) (hell : 2 ≤ ell) {S : Tower Lf} (hS : Admissible ell M R k S)
    (hRM : 18 ≤ R * M) (hbig : ∀ σ, 4 * ell ^ k < Lf σ + 1)
    (U : Cfg Lf) (ρ : ℝ) (hρ : 0 ≤ ρ) (hsmall : 4000000 * (ell : ℝ) ^ 2 * ρ ≤ 1)
    (hlink : ∀ j0, j0 ≤ k → ∀ b : Bond Lf, b.1 ∈ S.Om j0 → periodicLatticeShift b.1 b.2 ∈ S.Om j0 →
      dv (U b) ≤ ρ / (ell : ℝ) ^ j0)
    (hplaq : ∀ j0, j0 ≤ k → ∀ (y : PeriodicLatticeSite Lf) (ν μ : Fin 3),
      y ∈ S.Om j0 → coarseShift y 1 ν ∈ S.Om j0 → coarseShift y 1 μ ∈ S.Om j0 →
      coarseShift (coarseShift y 1 ν) 1 μ ∈ S.Om j0 → dv (pw 1 U y ν μ) ≤ ρ / (ell : ℝ) ^ (2 * j0)) :
    ∀ j, j ≤ k → ∀ y ∈ (geomOf ell k S).Lam j, ∀ i, i < j → ∀ z ∈ blockOf y (ell ^ j),
      z ∈ CoarseLattice Lf (ell ^ i) → ∀ μ : Fin 3, coarseShift z (ell ^ i) μ ∈ blockOf y (ell ^ j) →
      frobNorm ((bgTower (geomOf ell k S) U i (z, μ) : Matrix (Fin 2) (Fin 2) ℂ) - 1)
        ≤ ((ell : ℝ) + 3 * Real.pi * (ell : ℝ) ^ 2) * ρ * (ell : ℝ) ^ i / (ell : ℝ) ^ j := by
  intro j hj y hy i hij z hz hzal μ _
  have hell0 : 0 < ell := by omega
  obtain ⟨j1, rfl⟩ : ∃ j1, j = j1 + 1 := ⟨j - 1, by omega⟩
  have hj1 : j1 ≤ k := by omega
  have hi1 : i ≤ j1 := by omega
  have hzO : z ∈ S.Om (j1 + 1) := block_sub_Om hell0 hS hj hy hz
  -- the cone region lies in Ω_{j1}
  have hp : 1 ≤ ell ^ j1 := Nat.one_le_pow _ _ hell0
  have hii : ell ^ i ≤ ell ^ j1 := Nat.pow_le_pow_right hell0 hi1
  have hD : 3 * (4 * ell ^ i + 2) ≤ R * bigSide M ell j1 := by
    unfold bigSide
    have : 18 * ell ^ j1 ≤ R * M * ell ^ j1 := Nat.mul_le_mul_right _ hRM
    have e : R * (M * ell ^ j1) = R * M * ell ^ j1 := by ring
    rw [e]; omega
  have hreg : ∀ v, (∀ σ, off z v σ ≤ 4 * ell ^ i + 2) → v ∈ S.Om j1 :=
    fun v hv => region_sub_Om hS hj1 hzO _ hD hv
  -- the predicates of `link_tower_na_loc`
  set Rp : PeriodicLatticeSite Lf → Prop := fun w => ∀ ν μ : Fin 3,
    w ∈ S.Om j1 ∧ coarseShift w 1 ν ∈ S.Om j1 ∧ coarseShift w 1 μ ∈ S.Om j1 ∧
      coarseShift (coarseShift w 1 ν) 1 μ ∈ S.Om j1 with hRp
  set Rl : PeriodicLatticeEdge Lf → Prop := fun b => b.1 ∈ S.Om j1 ∧ periodicLatticeShift b.1 b.2 ∈ S.Om j1 with hRl
  set q0 : ℝ := ρ / (ell : ℝ) ^ (2 * j1) with hq0d
  set e : ℝ := ρ / (ell : ℝ) ^ j1 with hed
  have hellR : (2 : ℝ) ≤ ell := by exact_mod_cast hell
  have hpos : ∀ m : ℕ, (0 : ℝ) < (ell : ℝ) ^ m := fun m => by positivity
  have hq0 : 0 ≤ q0 := div_nonneg hρ (hpos _).le
  have h0 : ∀ w, Rp w → ∀ ν μ, dv (pw 1 U w ν μ) ≤ q0 := by
    intro w hw ν μ
    obtain ⟨a1, a2, a3, a4⟩ := hw ν μ
    exact hplaq j1 hj1 w ν μ a1 a2 a3 a4
  have he : ∀ b, Rl b → dv (U b) ≤ e := fun b hb => hlink j1 hj1 b hb.1 hb.2
  have hdvd : ∀ σ, ell ^ k ∣ Lf σ + 1 := hdvd_of_admissible hS
  have hdvdi : ∀ σ, ell ^ i ∣ Lf σ + 1 := fun σ => Dvd.dvd.trans (pow_dvd_pow ell (by omega)) (hdvd σ)
  have hik : ell ^ i ≤ ell ^ k := Nat.pow_le_pow_right hell0 (by omega)
  have hN : ∀ σ, 2 * ell ^ i < Lf σ + 1 := fun σ => by have := hbig σ; omega
  have hwr : ∀ σ, 4 * ell ^ i < Lf σ + 1 := fun σ => by have := hbig σ; omega
  have hsm : 4000000 * (ell : ℝ) ^ 2 * (((ell : ℝ) ^ 2) ^ i * q0) ≤ 1 := by
    have h1 : ((ell : ℝ) ^ 2) ^ i * q0 ≤ ρ := by
      rw [hq0d, ← pow_mul, mul_div_assoc']
      rw [div_le_iff₀ (hpos _)]
      have : (ell : ℝ) ^ (2 * i) ≤ (ell : ℝ) ^ (2 * j1) := pow_le_pow_right₀ (by linarith) (by omega)
      nlinarith
    have h2 : (0 : ℝ) ≤ 4000000 * (ell : ℝ) ^ 2 := by positivity
    nlinarith [mul_le_mul_of_nonneg_left h1 h2]
  have hgB : AdalyFormal.CurvBlock.GoodBd ell Rp i (z, μ) := by
    refine goodBd_of_region ell hell Rp i (z, μ) hzal hdvdi hwr (fun w hw0 => fun ν μ' => ?_)
    have hw : ∀ σ, off z w σ ≤ 4 * ell ^ i := hw0
    have hw2 : ∀ σ, off z w σ ≤ 4 * ell ^ i + 2 := fun σ => by have := hw σ; omega
    refine ⟨hreg w hw2, hreg _ (fun σ => ?_), hreg _ (fun σ => ?_), hreg _ (fun σ => ?_)⟩
    · have := off_shift_one_le z w ν σ; have := hw σ; omega
    · have := off_shift_one_le z w μ' σ; have := hw σ; omega
    · have h1 := off_shift_one_le z (coarseShift w 1 ν) μ' σ
      have h2 := off_shift_one_le z w ν σ; have := hw σ; omega
  have hgL : AdalyFormal.CurvBlock.goodL ell Rl i (z, μ) := by
    refine goodL_of_region ell hell Rl i (z, μ) hwr (fun b _ hb0 => ?_)
    have hb : ∀ σ, off z b.1 σ ≤ 4 * ell ^ i := hb0
    refine ⟨hreg _ (fun σ => ?_), hreg _ (fun σ => ?_)⟩
    · have := hb σ; omega
    · have h1 := off_shift_one_le z b.1 b.2 σ
      have : periodicLatticeShift b.1 b.2 = coarseShift b.1 1 b.2 := rfl
      rw [this]; have := hb σ; omega
  have hmain := link_tower_na_loc ell hell U Rp Rl q0 e hq0 h0 he i hdvdi hN hsm i le_rfl (z, μ) hzal hgB hgL
  -- arithmetic
  show dv (bgTower (geomOf ell k S) U i (z, μ)) ≤ _
  refine le_trans hmain ?_
  have hj1R : (ell : ℝ) ^ (j1 + 1) = (ell : ℝ) ^ j1 * ell := pow_succ _ _
  have hiR : (ell : ℝ) ^ i ≤ (ell : ℝ) ^ j1 := pow_le_pow_right₀ (by linarith) hi1
  have hiR' : (ell : ℝ) ^ i ≤ (ell : ℝ) ^ (j1 + 1) := pow_le_pow_right₀ (by linarith) (by omega)
  have hA : (ell : ℝ) ^ i * e = (ell : ℝ) * ρ * (ell : ℝ) ^ i / (ell : ℝ) ^ (j1 + 1) := by
    rw [hed, hj1R]; field_simp
  have hB : 3 * Real.pi * (((ell : ℝ) ^ 2) ^ i * q0)
      ≤ 3 * Real.pi * (ell : ℝ) ^ 2 * ρ * (ell : ℝ) ^ i / (ell : ℝ) ^ (j1 + 1) := by
    rw [hq0d, ← pow_mul]
    have hpi := Real.pi_pos
    have e1 : 3 * Real.pi * ((ell : ℝ) ^ (2 * i) * (ρ / (ell : ℝ) ^ (2 * j1)))
        = 3 * Real.pi * ρ * ((ell : ℝ) ^ i * (ell : ℝ) ^ i) / ((ell : ℝ) ^ j1 * (ell : ℝ) ^ j1) := by
      rw [show 2 * i = i + i by ring, show 2 * j1 = j1 + j1 by ring, pow_add, pow_add]; ring
    rw [e1, hj1R]
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have hρπ : 0 ≤ 3 * Real.pi * ρ := by positivity
    have hk : (ell : ℝ) ^ i * (ell : ℝ) ^ i * ((ell : ℝ) ^ j1 * (ell : ℝ)) ≤
        (ell : ℝ) ^ 2 * (ell : ℝ) ^ i * ((ell : ℝ) ^ j1 * (ell : ℝ) ^ j1) := by
      have h1 : (ell : ℝ) ^ i * (ell : ℝ) ≤ (ell : ℝ) ^ 2 * (ell : ℝ) ^ j1 := by
        have : (ell : ℝ) ≤ (ell : ℝ) ^ 2 := by nlinarith
        nlinarith [hpos i, hpos j1]
      have h2 : 0 ≤ (ell : ℝ) ^ i * (ell : ℝ) ^ j1 := by positivity
      nlinarith [mul_le_mul_of_nonneg_left h1 h2]
    nlinarith [mul_le_mul_of_nonneg_left hk hρπ]
  have hsplit : ((ell : ℝ) + 3 * Real.pi * (ell : ℝ) ^ 2) * ρ * (ell : ℝ) ^ i / (ell : ℝ) ^ (j1 + 1)
      = (ell : ℝ) * ρ * (ell : ℝ) ^ i / (ell : ℝ) ^ (j1 + 1)
        + 3 * Real.pi * (ell : ℝ) ^ 2 * ρ * (ell : ℝ) ^ i / (ell : ℝ) ^ (j1 + 1) := by ring
  rw [hsplit, hA]
  linarith

/-- **S1 under the stratified regime** (no tower hypothesis). -/
theorem site_coercive_M1 (ell M R k : ℕ) (hell : 2 ≤ ell) {S : Tower Lf} (hS : Admissible ell M R k S)
    (hRM : 18 ≤ R * M) (hbig : ∀ σ, 4 * ell ^ k < Lf σ + 1)
    (U : Cfg Lf) (a : ℝ) (ha : 0 < a) (ρ : ℝ) (hρ : 0 ≤ ρ) (hsmall : 4000000 * (ell : ℝ) ^ 2 * ρ ≤ 1)
    (hlink : ∀ j0, j0 ≤ k → ∀ b : Bond Lf, b.1 ∈ S.Om j0 → periodicLatticeShift b.1 b.2 ∈ S.Om j0 →
      dv (U b) ≤ ρ / (ell : ℝ) ^ j0)
    (hplaq : ∀ j0, j0 ≤ k → ∀ (y : PeriodicLatticeSite Lf) (ν μ : Fin 3),
      y ∈ S.Om j0 → coarseShift y 1 ν ∈ S.Om j0 → coarseShift y 1 μ ∈ S.Om j0 →
      coarseShift (coarseShift y 1 ν) 1 μ ∈ S.Om j0 → dv (pw 1 U y ν μ) ≤ ρ / (ell : ℝ) ^ (2 * j0))
    (f : SiteL2 Lf) :
    (1 - 216 * (((ell : ℝ) + 3 * Real.pi * (ell : ℝ) ^ 2) * ρ) ^ 2) * wNormSq (geomOf ell k S) f
      ≤ max 6 (16 / (3 * a)) * ⟪f, DelpA (geomOf ell k S) U a f⟫ := by
  have hell0 : 0 < ell := by omega
  have hellR : (2 : ℝ) ≤ ell := by exact_mod_cast hell
  set ρT := ((ell : ℝ) + 3 * Real.pi * (ell : ℝ) ^ 2) * ρ with hρT
  have hfac : 1 ≤ (ell : ℝ) + 3 * Real.pi * (ell : ℝ) ^ 2 := by
    have := Real.pi_pos; nlinarith
  have hρT0 : 0 ≤ ρT := by positivity
  have hρρT : ρ ≤ ρT := by nlinarith
  have hP := properTower_geomOf hell0 hS
  refine site_coercive_weighted ell k hell (hdvd_of_admissible hS) hP U a ha ρT hρT0 ?_ ?_ f
  · intro j hj y hy b hb
    rw [mem_inBlockBonds] at hb
    have h1 := hlink j hj b (block_sub_Om hell0 hS hj hy hb.1) (block_sub_Om hell0 hS hj hy hb.2)
    have : ρ / (ell : ℝ) ^ j ≤ ρT / (ell : ℝ) ^ j := div_le_div_of_nonneg_right hρρT (by positivity)
    exact h1.trans this
  · intro j hj y hy i hi z hz hzal μ hzs
    have := hT_of_regime ell M R k hell hS hRM hbig U ρ hρ hsmall hlink hplaq j hj y hy i hi z hz hzal μ hzs
    rw [hρT]
    calc _ ≤ _ := this
      _ = ((ell : ℝ) + 3 * Real.pi * (ell : ℝ) ^ 2) * ρ * (ell : ℝ) ^ i / (ell : ℝ) ^ j := rfl

#print axioms pcd_le_off
#print axioms pdist_le_off
#print axioms block_sub_Om
#print axioms region_sub_Om
#print axioms hT_of_regime
#print axioms site_coercive_M1

#print axioms off_shift_one_le

end AdalyFormal.M1Site
