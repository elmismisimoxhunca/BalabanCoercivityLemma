import DC

/-!
# DD -- the bump estimate: a constant value of `Δ h` on a cube is controlled by `h` on the cube (m1_w2_decay, 2026-10-13)

For a cube `C = blockOf y n` (`n ≥ 24`, fitting in the torus) and a site field `h` whose flat Laplacian is constant `= c` on `C`:
**`bump_bound`** : `‖c‖² · n⁷ ≤ Kb2 · Σ_{z ∈ C} ‖h z‖²`, `Kb2 = 36 · 48⁴ · 72⁶`.
Proof: test `Δ h` against `ψ c` with `ψ = smoothCut c₀ (4r) r r`, `r = n/24`, `c₀` the cube centre: `ψ` is supported (with its
Laplacian) inside `C`, `ψ = 1` on `Ball c₀ r` (so `Σ ψ ≥ (r/3+1)³`), and `|lapR ψ| ≤ 6/r²`.
No sorry / axiom.
-/
set_option autoImplicit false
set_option maxHeartbeats 8000000

namespace AdalyFormal.M1Decay

open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.StatementLane (pdist pcd)
open AdalyFormal.StatementLaneR8 (Ball pdist_comm pdist_triangle pdist_shift_le pdist_self)
open AdalyFormal.Balaban.CovariantOperators (SuTwo)
open AdalyFormal.Balaban.AdmissibleSubspace (blockOf mem_blockOf)
open AdalyFormal.Balaban.CovariantHjMinimizer (periodicLatticeShiftBack)

variable {L : PeriodicLatticeExtent}

/-- the bump constant. -/
noncomputable def Kb2 : ℝ := 36 * 48 ^ 4 * 72 ^ 6

theorem pcd_window (N a b t y n : ℕ) (hb : b < N) (ha1 : y + t ≤ a) (ha2 : a + t < y + n) (hyn : y + n ≤ N)
    (h : pcd N a b ≤ t) : y ≤ b ∧ b < y + n := by
  unfold pcd at h
  simp only [min_def] at h
  split_ifs at h <;> omega

theorem pcd_le_pdist (x z : PeriodicLatticeSite L) (μ : Fin 3) : pcd (L μ + 1) (x μ).val (z μ).val ≤ pdist x z := by
  unfold pdist
  exact Finset.single_le_sum (f := fun ν => pcd (L ν + 1) (x ν).val (z ν).val) (fun _ _ => Nat.zero_le _)
    (Finset.mem_univ μ)

section cube
variable (y : PeriodicLatticeSite L) (n : ℕ) (hn : 24 ≤ n) (hfit : ∀ μ, (y μ).val + n ≤ L μ + 1)

/-- the cube centre. -/
def cen : PeriodicLatticeSite L := fun μ => ⟨(y μ).val + n / 2, by have := hfit μ; omega⟩

include hn hfit

theorem cen_val (μ : Fin 3) : (cen y n hfit μ).val = (y μ).val + n / 2 := rfl

theorem mem_cube_of_near (z : PeriodicLatticeSite L) (hz : pdist (cen y n hfit) z ≤ 8 * (n / 24) + 1) :
    z ∈ blockOf y n := by
  rw [mem_blockOf]
  intro μ
  have h1 := (pcd_le_pdist (cen y n hfit) z μ).trans hz
  rw [cen_val y n hn hfit] at h1
  exact pcd_window (L μ + 1) _ _ (8 * (n / 24) + 1) (y μ).val n (z μ).isLt (by omega) (by omega) (hfit μ) h1

end cube

/-- the bump. -/
noncomputable def bump (y : PeriodicLatticeSite L) (n : ℕ) (_hn : 24 ≤ n) (hfit : ∀ μ, (y μ).val + n ≤ L μ + 1) :
    PeriodicLatticeSite L → ℝ :=
  smoothCut (cen y n hfit) (4 * (n / 24)) (n / 24) (n / 24)

theorem r_pos {y : PeriodicLatticeSite L} (n : ℕ) (hn : 24 ≤ n) (_hfit : ∀ μ, (y μ).val + n ≤ L μ + 1) :
    0 < n / 24 := by omega

section cube2
variable (y : PeriodicLatticeSite L) (n : ℕ) (hn : 24 ≤ n) (hfit : ∀ μ, (y μ).val + n ≤ L μ + 1)
include hn hfit

theorem bump_supp (z : PeriodicLatticeSite L) (hz : bump y n hn hfit z ≠ 0) : pdist (cen y n hfit) z ≤ 8 * (n / 24) := by
  by_contra hc
  exact hz (sc_zero _ _ _ _ (r_pos n hn hfit) (r_pos n hn hfit) z (by omega))

theorem bump_mem (z : PeriodicLatticeSite L) (hz : bump y n hn hfit z ≠ 0) : z ∈ blockOf y n :=
  mem_cube_of_near y n hn hfit z (by have := bump_supp y n hn hfit z hz; omega)

theorem lapR_bump_mem (z : PeriodicLatticeSite L) (hz : lapR (bump y n hn hfit) z ≠ 0) : z ∈ blockOf y n := by
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
  unfold lapR
  refine Finset.sum_eq_zero (fun μ _ => ?_)
  rw [h0 z (by rw [pdist_self]; omega), h0 _ (pdist_shift_le z μ), h0 _ (pdist_back_le z μ)]
  ring

theorem bump_one (z : PeriodicLatticeSite L) (hz : pdist (cen y n hfit) z ≤ n / 24) : bump y n hn hfit z = 1 :=
  sc_one _ _ _ _ (r_pos n hn hfit) (r_pos n hn hfit) (n / 24) (by omega) z hz

theorem bump_nonneg (z : PeriodicLatticeSite L) : 0 ≤ bump y n hn hfit z := sc_nonneg _ _ _ _ z

theorem bump_lapR (z : PeriodicLatticeSite L) : |lapR (bump y n hn hfit) z| ≤ 6 / (((n / 24 : ℕ) : ℝ) * (n / 24 : ℕ)) :=
  sc_lapR _ _ _ _ (r_pos n hn hfit) (r_pos n hn hfit) z

/-- the small inner cube. -/
theorem inner_cube_sub (z : PeriodicLatticeSite L) (hz : z ∈ blockOf (cen y n hfit) (n / 24 / 3 + 1)) :
    pdist (cen y n hfit) z ≤ n / 24 := by
  rw [mem_blockOf] at hz
  have : ∀ μ, pcd (L μ + 1) (cen y n hfit μ).val (z μ).val ≤ n / 24 / 3 := by
    intro μ
    have := hz μ
    refine (AdalyFormal.StatementLaneR8.pcd_le_diff _ _ _ this.1).trans ?_
    omega
  unfold pdist
  rw [Fin.sum_univ_three]
  have H := this
  have h0 := H 0; have h1 := H 1; have h2 := H 2
  omega

theorem sum_bump_ge : ((n / 24 / 3 + 1 : ℕ) : ℝ) ^ 3 ≤ ∑ z ∈ blockOf y n, bump y n hn hfit z := by
  set t := n / 24 / 3 + 1 with ht
  have hfit' : ∀ μ, (cen y n hfit μ).val + t ≤ L μ + 1 := by
    intro μ; rw [cen_val y n hn hfit]; have := hfit μ; omega
  have hsub : blockOf (cen y n hfit) t ⊆ blockOf y n := fun z hz =>
    mem_cube_of_near y n hn hfit z (by have := inner_cube_sub y n hn hfit z hz; omega)
  have hcard := AdalyFormal.M1Site.card_blockOf (cen y n hfit) t hfit'
  calc ((t : ℕ) : ℝ) ^ 3 = ∑ z ∈ blockOf (cen y n hfit) t, (1 : ℝ) := by
        rw [Finset.sum_const, hcard, nsmul_eq_mul, mul_one]; push_cast; ring
    _ = ∑ z ∈ blockOf (cen y n hfit) t, bump y n hn hfit z :=
        Finset.sum_congr rfl (fun z hz => (bump_one y n hn hfit z (inner_cube_sub y n hn hfit z hz)).symm)
    _ ≤ ∑ z ∈ blockOf y n, bump y n hn hfit z :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun z _ _ => bump_nonneg y n hn hfit z)

/-- **the bump bound**. -/
theorem bump_bound (h : SiteL2 L) (c : SuTwo) (hc : ∀ z ∈ blockOf y n, (lapFull (U0 L) h) z = c) :
    ‖c‖ ^ 2 * (n : ℝ) ^ 7 ≤ Kb2 * ∑ z ∈ blockOf y n, ‖h z‖ ^ 2 := by
  set ψ := bump y n hn hfit with hψ
  set C := blockOf y n with hC
  set φ : SiteL2 L := WithLp.toLp 2 (fun z => ψ z • c) with hφ
  set r : ℝ := ((n / 24 : ℕ) : ℝ) with hr
  have hr0 : 0 < r := by rw [hr]; exact_mod_cast r_pos n hn hfit
  -- ⟪φ, Δh⟫ = ‖c‖² Σ_C ψ
  have e1 : ⟪φ, lapFull (U0 L) h⟫ = ‖c‖ ^ 2 * ∑ z ∈ C, ψ z := by
    rw [PiLp.inner_apply]
    rw [← Finset.sum_subset (Finset.subset_univ C)]
    · rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun z hz => ?_)
      show ⟪ψ z • c, (lapFull (U0 L) h) z⟫ = _
      rw [hc z hz, real_inner_smul_left, real_inner_self_eq_norm_sq]; ring
    · intro z _ hz
      show ⟪ψ z • c, (lapFull (U0 L) h) z⟫ = 0
      have : ψ z = 0 := by
        by_contra h0; exact hz (bump_mem y n hn hfit z h0)
      rw [this, zero_smul, inner_zero_left]
  -- ⟪φ, Δh⟫ = ⟪Δφ, h⟫ ≤ (6/r²) ‖c‖ Σ_C ‖h‖
  have e2 : ⟪φ, lapFull (U0 L) h⟫ ≤ 6 / (r * r) * ‖c‖ * ∑ z ∈ C, ‖h z‖ := by
    rw [← lapFull_symm, PiLp.inner_apply]
    rw [← Finset.sum_subset (Finset.subset_univ C)]
    · rw [Finset.mul_sum]
      refine Finset.sum_le_sum (fun z _ => ?_)
      show ⟪(lapFull (U0 L) φ) z, h z⟫ ≤ _
      rw [hφ, lap_mulR_const, real_inner_smul_left]
      have h1 := real_inner_le_norm c (h z)
      have h2 := bump_lapR y n hn hfit z
      have h3 : lapR ψ z * ⟪c, h z⟫ ≤ |lapR ψ z| * (‖c‖ * ‖h z‖) := by
        calc lapR ψ z * ⟪c, h z⟫ ≤ |lapR ψ z * ⟪c, h z⟫| := le_abs_self _
          _ = |lapR ψ z| * |⟪c, h z⟫| := abs_mul _ _
          _ ≤ |lapR ψ z| * (‖c‖ * ‖h z‖) := mul_le_mul_of_nonneg_left (abs_real_inner_le_norm _ _) (abs_nonneg _)
      calc lapR ψ z * ⟪c, h z⟫ ≤ |lapR ψ z| * (‖c‖ * ‖h z‖) := h3
        _ ≤ 6 / (r * r) * (‖c‖ * ‖h z‖) := mul_le_mul_of_nonneg_right h2 (by positivity)
        _ = 6 / (r * r) * ‖c‖ * ‖h z‖ := by ring
    · intro z _ hz
      show ⟪(lapFull (U0 L) φ) z, h z⟫ = 0
      rw [hφ, lap_mulR_const]
      have : lapR ψ z = 0 := by by_contra h0; exact hz (lapR_bump_mem y n hn hfit z h0)
      rw [this, zero_smul, inner_zero_left]
  -- Cauchy-Schwarz on the cube
  have hcard : (C.card : ℝ) = (n : ℝ) ^ 3 := by
    rw [hC, AdalyFormal.M1Site.card_blockOf y n hfit]; push_cast; ring
  have hCS : (∑ z ∈ C, ‖h z‖) ^ 2 ≤ (n : ℝ) ^ 3 * ∑ z ∈ C, ‖h z‖ ^ 2 := by
    rw [← hcard]; exact sq_sum_le_card_mul_sum_sq
  set S1 := ∑ z ∈ C, ψ z with hS1
  set T := ∑ z ∈ C, ‖h z‖ with hT
  set t : ℝ := ((n / 24 / 3 + 1 : ℕ) : ℝ) with ht
  have hS1t : t ^ 3 ≤ S1 := sum_bump_ge y n hn hfit
  have ht0 : 0 < t := by rw [ht]; positivity
  have hT0 : 0 ≤ T := Finset.sum_nonneg (fun z _ => norm_nonneg _)
  -- ‖c‖ S1 ≤ (6/r²) T
  have key : ‖c‖ * S1 ≤ 6 / (r * r) * T := by
    have h := e1.symm.le.trans e2
    rcases (norm_nonneg c).eq_or_lt with h0 | hpos
    · rw [← h0, zero_mul]; positivity
    · have : ‖c‖ * (‖c‖ * S1) ≤ ‖c‖ * (6 / (r * r) * T) := by nlinarith
      exact le_of_mul_le_mul_left this hpos
  have key2 : (‖c‖ * S1) ^ 2 * (r * r) ^ 2 ≤ 36 * ((n : ℝ) ^ 3 * ∑ z ∈ C, ‖h z‖ ^ 2) := by
    have hk0 : 0 ≤ ‖c‖ * S1 := mul_nonneg (norm_nonneg _) (le_trans (by positivity) hS1t)
    have h1 := pow_le_pow_left₀ hk0 key 2
    have hrr : 0 < r * r := by positivity
    have e : (6 / (r * r) * T) ^ 2 * (r * r) ^ 2 = 36 * T ^ 2 := by field_simp; ring
    calc (‖c‖ * S1) ^ 2 * (r * r) ^ 2 ≤ (6 / (r * r) * T) ^ 2 * (r * r) ^ 2 :=
          mul_le_mul_of_nonneg_right h1 (by positivity)
      _ = 36 * T ^ 2 := e
      _ ≤ 36 * ((n : ℝ) ^ 3 * ∑ z ∈ C, ‖h z‖ ^ 2) := by linarith
  -- scale bounds: 48 r ≥ n, 72 t ≥ n
  have hn' : (24 : ℝ) ≤ n := by exact_mod_cast hn
  have hr48 : (n : ℝ) ≤ 48 * r := by
    have h1 : n < 24 * (n / 24 + 1) := by omega
    have h2 : 1 ≤ n / 24 := r_pos n hn hfit
    have : n ≤ 48 * (n / 24) := by omega
    rw [hr]; exact_mod_cast this
  have ht72 : (n : ℝ) ≤ 72 * t := by
    have : n ≤ 72 * (n / 24 / 3 + 1) := by omega
    rw [ht]; exact_mod_cast this
  have hn0 : (0 : ℝ) < n := by linarith
  -- n^10 ‖c‖² ≤ 48^4 72^6 (‖c‖ S1)^2 (r r)^2
  have hS1pow : ((n : ℝ) / 72) ^ 6 ≤ S1 ^ 2 := by
    have a1 : (n : ℝ) / 72 ≤ t := by linarith
    have a2 : ((n : ℝ) / 72) ^ 3 ≤ t ^ 3 := pow_le_pow_left₀ (by positivity) a1 3
    have a3 := a2.trans hS1t
    have a4 := pow_le_pow_left₀ (by positivity) a3 2
    rw [← pow_mul] at a4
    exact a4
  have hrpow : ((n : ℝ) / 48) ^ 4 ≤ (r * r) ^ 2 := by
    have a1 : (n : ℝ) / 48 ≤ r := by linarith
    have a2 := pow_le_pow_left₀ (by positivity) a1 4
    calc ((n : ℝ) / 48) ^ 4 ≤ r ^ 4 := a2
      _ = (r * r) ^ 2 := by ring
  have hprod : ((n : ℝ) / 72) ^ 6 * ((n : ℝ) / 48) ^ 4 * ‖c‖ ^ 2 ≤ (‖c‖ * S1) ^ 2 * (r * r) ^ 2 := by
    have := mul_le_mul hS1pow hrpow (by positivity) (sq_nonneg _)
    calc ((n : ℝ) / 72) ^ 6 * ((n : ℝ) / 48) ^ 4 * ‖c‖ ^ 2 ≤ S1 ^ 2 * (r * r) ^ 2 * ‖c‖ ^ 2 :=
          mul_le_mul_of_nonneg_right this (sq_nonneg _)
      _ = (‖c‖ * S1) ^ 2 * (r * r) ^ 2 := by ring
  have hfin := hprod.trans key2
  have e3 : ((n : ℝ) / 72) ^ 6 * ((n : ℝ) / 48) ^ 4 * ‖c‖ ^ 2
      = (n : ℝ) ^ 3 * (‖c‖ ^ 2 * (n : ℝ) ^ 7) / (72 ^ 6 * 48 ^ 4) := by ring
  rw [e3, div_le_iff₀ (by positivity)] at hfin
  have hn3 : (0 : ℝ) < (n : ℝ) ^ 3 := by positivity
  have : (n : ℝ) ^ 3 * (‖c‖ ^ 2 * (n : ℝ) ^ 7) ≤ (n : ℝ) ^ 3 * (Kb2 * ∑ z ∈ C, ‖h z‖ ^ 2) := by
    unfold Kb2; nlinarith
  exact le_of_mul_le_mul_left this hn3

end cube2

end AdalyFormal.M1Decay

#print axioms AdalyFormal.M1Decay.pcd_window
#print axioms AdalyFormal.M1Decay.mem_cube_of_near
#print axioms AdalyFormal.M1Decay.lapR_bump_mem
#print axioms AdalyFormal.M1Decay.sum_bump_ge
#print axioms AdalyFormal.M1Decay.bump_bound
