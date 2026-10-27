import LV9

/-!
# LV10 -- the mass on the patch in row form, the final algebra, and **`LemV` (PROVED)**

* `massP_rows` : `massP (patch) a y = a (Σ_small n ‖Rw n y‖² + Σ_big N ‖Rw N y‖²)`.
* `PhiP_flat_patch` : `PhiP (patch) flat a y = ‖curl y‖² + massP (patch) a y`.
* `final_alg` : the real-number combination of the bounds (α-weighted, `α = 1 - 1/(4ℓ²)`).
* **`lemV_patch`** / **`lemV`** : `Φ(Dφ) ≤ KV ℓ a · Φ(Dφ + c)` for every divergence-free `c`, with
  `KV ℓ a = 64 ℓ² + a (2304 ℓ² + 9216 ℓ⁵ + 248832 ℓ⁶ (ℓ+1)²)` (independent of `j`, the torus and `Rg`).
* **`lemIFlat`** : `LemIFlat ℓ a (CS ℓ a · KV ℓ a)` and **`w3flat`** : lane D's `W3FlatStmt`.
No sorry / axiom.
-/
set_option autoImplicit false
set_option maxHeartbeats 16000000
namespace AdalyFormal.LemIFlat

open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.FlatCoercivity (eU pathSite_eq)
open AdalyFormal.StatementLane (BlockClosed scaleUp)
open AdalyFormal.M1Patch (patchTower GP LemIFlat W3FlatStmt w3flat_of_LemI dvd_scaleUp PhiP mem_lam_j mem_lam_succ
  lam_lt omGe_of_mem not_omGe_of_not_mem onLat_back om0_univ)
open AdalyFormal.Balaban.CoarseCurl (coarseShift)

variable {L : PeriodicLatticeExtent}

theorem coarseShift_eq (y : PeriodicLatticeSite L) (m : ℕ) (μ : Fin 3) : coarseShift y m μ = y + m • eU L μ :=
  pathSite_eq y μ m

/-! ## the final algebra -/

theorem final_alg (l2 Gs Gb Fsm Fbg Sx Bx Dx Lx DPh FBs LPh LFv X M Er : ℝ) (hl2 : 1 ≤ l2)
    (hGs : 0 ≤ Gs) (hGb : 0 ≤ Gb) (hFsm : 0 ≤ Fsm) (hFbg : 0 ≤ Fbg)
    (hId : Sx + l2 * Bx = Dx + Lx)
    (hS : 2 * |Sx| ≤ (1 - 1 / (4 * l2)) * Gs + Fsm / (1 - 1 / (4 * l2)))
    (hB : 2 * |Bx| ≤ 6 / 5 * Gb + Fbg / (6 / 5))
    (hD : 2 * |Dx| ≤ l2 * (3 / 4 * DPh + FBs / (3 / 4))) (hDP : DPh ≤ 2 / l2 * Gs) (hFB : FBs ≤ Fbg)
    (hL : 2 * |Lx| ≤ 1 / (432 * l2 ^ 2) * LPh + LFv / (1 / (432 * l2 ^ 2)))
    (hLP : LPh ≤ 54 * l2 ^ 2 * Gs) (hLF : LFv ≤ X)
    (hMf : Gs + Gb + Fsm + Fbg + 2 * Sx + 2 * Bx ≤ 2 * M + Er) :
    Gs + Gb ≤ 64 * l2 * M + 32 * l2 * Er + 3456 * l2 ^ 2 * X := by
  have hl0 : 0 < l2 := by linarith
  set s : ℝ := 1 / (4 * l2) with hs
  have hs0 : 0 < s := by positivity
  have hsl : s * l2 = 1 / 4 := by rw [hs]; field_simp
  have hs1 : s ≤ 1 / 4 := by
    rw [hs, div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
  have hα : 0 < 1 - s := by linarith
  -- (i) the S-term
  have i1 : -(2 * Sx) ≤ (1 - s) * Gs + Fsm / (1 - s) := by
    have := neg_abs_le Sx; linarith
  have i2 : -(2 * Sx) * (1 - s) ≤ ((1 - s) * Gs + Fsm / (1 - s)) * (1 - s) := mul_le_mul_of_nonneg_right i1 hα.le
  have i3 : ((1 - s) * Gs + Fsm / (1 - s)) * (1 - s) = (1 - s) ^ 2 * Gs + Fsm := by field_simp; try ring
  -- (ii) the B-term
  have ii : -(2 * Bx) ≤ 6 / 5 * Gb + 5 / 6 * Fbg := by
    have := neg_abs_le Bx
    have e : Fbg / (6 / 5) = 5 / 6 * Fbg := by ring
    linarith
  -- (iii) the D-term
  have iii1 : -(2 * Dx) ≤ 3 / 2 * Gs + 4 / 3 * l2 * Fbg := by
    have := neg_abs_le Dx
    have e : l2 * (3 / 4 * DPh + FBs / (3 / 4)) = 3 / 4 * (l2 * DPh) + 4 / 3 * l2 * FBs := by ring
    have h1 : l2 * DPh ≤ 2 * Gs := by
      have := mul_le_mul_of_nonneg_left hDP hl0.le
      rw [show l2 * (2 / l2 * Gs) = 2 * Gs by field_simp] at this; exact this
    have h2 : l2 * FBs ≤ l2 * Fbg := mul_le_mul_of_nonneg_left hFB hl0.le
    nlinarith
  have iii : -(2 * Dx) * s ≤ 3 / 2 * (s * Gs) + 1 / 3 * Fbg := by
    have := mul_le_mul_of_nonneg_right iii1 hs0.le
    have e : (3 / 2 * Gs + 4 / 3 * l2 * Fbg) * s = 3 / 2 * (s * Gs) + 4 / 3 * (s * l2) * Fbg := by ring
    rw [e, hsl] at this; linarith
  -- (iv) the L-term
  have iv1 : -(2 * Lx) ≤ Gs / 8 + 432 * l2 ^ 2 * X := by
    have := neg_abs_le Lx
    have e1 : 1 / (432 * l2 ^ 2) * LPh ≤ Gs / 8 := by
      have := mul_le_mul_of_nonneg_left hLP (by positivity : (0 : ℝ) ≤ 1 / (432 * l2 ^ 2))
      rw [show 1 / (432 * l2 ^ 2) * (54 * l2 ^ 2 * Gs) = Gs / 8 by field_simp; ring] at this; exact this
    have e2 : LFv / (1 / (432 * l2 ^ 2)) ≤ 432 * l2 ^ 2 * X := by
      rw [div_div_eq_mul_div, div_one]
      nlinarith [sq_nonneg l2]
    linarith
  have iv : -(2 * Lx) * s ≤ (s * Gs) / 8 + 432 * (s * l2) * l2 * X := by
    have := mul_le_mul_of_nonneg_right iv1 hs0.le
    have e : (Gs / 8 + 432 * l2 ^ 2 * X) * s = (s * Gs) / 8 + 432 * (s * l2) * l2 * X := by ring
    rw [e] at this; exact this
  -- (v) the identity times s
  have v : s * Sx = s * Dx + s * Lx - Bx / 4 := by
    have := congrArg (fun t => s * t) hId
    have e : s * (Sx + l2 * Bx) = s * Sx + (s * l2) * Bx := by ring
    rw [e, hsl] at this; linarith
  -- (vi) s² Gs ≤ s Gs / 4
  have vi : s * (s * Gs) ≤ 1 / 4 * (s * Gs) := mul_le_mul_of_nonneg_right hs1 (by positivity)
  have vii : s / 8 * Gb ≤ 1 / 10 * Gb := mul_le_mul_of_nonneg_right (by linarith) hGb
  have hsGs : 0 ≤ s * Gs := by positivity
  -- combine: (s/8)(Gs + Gb) ≤ 2M + Er + 432 s l2² X
  have hcomb : s / 8 * (Gs + Gb) ≤ 2 * M + Er + 432 * (s * l2) * l2 * X := by
    have e1 : (1 - s) ^ 2 * Gs = Gs - 2 * (s * Gs) + s * (s * Gs) := by ring
    have e2 : -(2 * Sx) * (1 - s) = -(2 * Sx) + 2 * (s * Sx) := by ring
    have e3 : -(2 * Dx) * s = -(2 * (s * Dx)) := by ring
    have e4 : -(2 * Lx) * s = -(2 * (s * Lx)) := by ring
    nlinarith [i2, i3, ii, iii, iv, v, vi, vii, e1, e2, e3, e4]
  -- multiply by 32 l2 = 8/s
  have h8 : 32 * l2 * (s / 8) = 1 := by rw [hs]; field_simp; ring
  have := mul_le_mul_of_nonneg_left hcomb (by positivity : (0 : ℝ) ≤ 32 * l2)
  rw [← mul_assoc, h8, one_mul, hsl] at this
  nlinarith

theorem term_ineq (m : ℝ) (hm : 0 < m) (d F q : SuTwo) :
    m⁻¹ * ‖d‖ ^ 2 + 2 * ⟪d, F⟫ + m * ‖F‖ ^ 2 ≤ 2 * (m * ‖m⁻¹ • d + q‖ ^ 2) + 2 * (m * ‖q - F‖ ^ 2) := by
  have e : m⁻¹ * ‖d‖ ^ 2 + 2 * ⟪d, F⟫ + m * ‖F‖ ^ 2 = m * ‖m⁻¹ • d + F‖ ^ 2 := by
    rw [norm_add_sq_real, norm_smul, inner_smul_left, mul_pow, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hm)]
    simp only [conj_trivial]
    field_simp
    try ring
  rw [e]
  have h2 : ‖m⁻¹ • d + F‖ ^ 2 ≤ 2 * ‖m⁻¹ • d + q‖ ^ 2 + 2 * ‖q - F‖ ^ 2 := by
    have e2 : m⁻¹ • d + F = (m⁻¹ • d + q) - (q - F) := by abel
    rw [e2]
    have h3 := norm_sub_le (m⁻¹ • d + q) (q - F)
    have h0 := norm_nonneg ((m⁻¹ • d + q) - (q - F))
    have h4 := pow_le_pow_left₀ h0 h3 2
    nlinarith [sq_nonneg (‖m⁻¹ • d + q‖ - ‖q - F‖)]
  nlinarith

theorem mask_univ (f : AdalyFormal.Balaban.CovariantHjMinimizer.PlaqFnL2 L) :
    AdalyFormal.StatementLaneR6.plaqMask (plaqIn (Set.univ : Set (PeriodicLatticeSite L))) f = f := by
  ext p
  simp [AdalyFormal.StatementLaneR6.plaqMask, plaqIn]

/-! ## row form of the patch mass -/

section patch
variable {ell j : ℕ} (hell : 0 < ell) {Rg : Set (PeriodicLatticeSite L)} (hRg : BlockClosed (ell ^ (j + 1)) Rg)
  (hdvd : ∀ μ : Fin 3, ell ^ (j + 1) ∣ L μ + 1)
include hell hRg hdvd

theorem mem_rows_j (x : PeriodicLatticeSite L) (μ : Fin 3) :
    ((x, μ) : Bond L) ∈ bondsLam (GQ ell j Rg) j ↔ OnLatN (ell ^ j) x ∧ x ∉ Rg ∧ x + ell ^ j • eU L μ ∉ Rg := by
  have hdn' := hdn hell hRg hdvd
  rw [← coarseShift_eq]
  constructor
  · rintro ⟨h1, h2⟩
    have hx : OnLatN (ell ^ j) x := by
      rcases h1 with h | h
      · exact ((mem_lam_j ell j Rg _).mp h).1
      · exact onLat_back _ hdn' _ _ ((mem_lam_j ell j Rg _).mp h).1
    refine ⟨hx, fun hR => h2 (Or.inl (omGe_of_mem hell hRg _ hR)), fun hR => h2 (Or.inr (omGe_of_mem hell hRg _ hR))⟩
  · rintro ⟨hx, h0, h1⟩
    exact AdalyFormal.M1Patch.row_j_of_out hell hRg x hx μ h0 h1

theorem mem_rows_succ (x : PeriodicLatticeSite L) (μ : Fin 3) :
    ((x, μ) : Bond L) ∈ bondsLam (GQ ell j Rg) (j + 1)
      ↔ OnLatN (ell ^ j * ell) x ∧ (x ∈ Rg ∨ x + (ell ^ j * ell) • eU L μ ∈ Rg) := by
  have hdN : ∀ ν : Fin 3, ell ^ (j + 1) ∣ L ν + 1 := hdvd
  rw [show (ell ^ j * ell) • eU L μ = ell ^ (j + 1) • eU L μ by rw [pow_succ], ← coarseShift_eq]
  have hno : ¬ (OmGe (GQ ell j Rg) (j + 1 + 1) x ∨
      OmGe (GQ ell j Rg) (j + 1 + 1) (coarseShift x (ell ^ (j + 1)) μ)) := by
    rintro (h | h) <;>
      exact not_OmGe_of_lt (G := GQ ell j Rg) (by show j + 1 < j + 1 + 1; omega) _ h
  constructor
  · rintro ⟨h1, -⟩
    rcases h1 with h | h
    · have := (mem_lam_succ ell j Rg _).mp h
      exact ⟨this.1, Or.inl this.2⟩
    · have := (mem_lam_succ ell j Rg _).mp h
      exact ⟨onLat_back _ hdN _ _ this.1, Or.inr this.2⟩
  · rintro ⟨hx, h | h⟩
    · exact ⟨Or.inl ((mem_lam_succ ell j Rg _).mpr ⟨hx, h⟩), hno⟩
    · exact ⟨Or.inr ((mem_lam_succ ell j Rg _).mpr ⟨AdalyFormal.SliceCoerc.onLat_shift _ hdN _ hx _, h⟩), hno⟩

theorem PhiP_patch (a : ℝ) (y : BondFnL2 L) :
    PhiP (GQ ell j Rg) (flatCfg : Cfg L) a y
      = ‖AdalyFormal.Balaban.DeltaKFull.curlCovariantCLM_L2 (flatCfg : Cfg L) y‖ ^ 2 + massP (GQ ell j Rg) a y := by
  unfold PhiP massP
  rw [AdalyFormal.StatementLaneG.inner_DpiFull_flat, om0_univ j Rg ell, mask_univ]

open Classical in
theorem level_j_rows (a : ℝ) (y : BondFnL2 L) :
    ∑ b ∈ Finset.univ.filter (fun b => b ∈ bondsLam (GQ ell j Rg) j), a * (ell : ℝ) ^ j * ‖AdalyFormal.M1Patch.rv ell y j b‖ ^ 2
      = a * ∑ μ : Fin 3, ∑ z ∈ latF L (ell ^ j), (if z ∉ Rg ∧ z + ell ^ j • eU L μ ∉ Rg then
          ((ell ^ j : ℕ) : ℝ) * ‖Rw (ell ^ j) y.ofLp z μ‖ ^ 2 else 0) := by
  rw [Finset.sum_filter, Fintype.sum_prod_type, Finset.sum_comm, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun μ _ => ?_)
  rw [sum_latF, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  by_cases hb : ((x, μ) : Bond L) ∈ bondsLam (GQ ell j Rg) j
  · rw [if_pos hb]
    obtain ⟨hx, h0, h1⟩ := (mem_rows_j hell hRg hdvd x μ).mp hb
    rw [if_pos hx, if_pos ⟨h0, h1⟩]
    have hc : x ∈ AdalyFormal.Balaban.AdmissibleSubspace.CoarseLattice L (ell ^ j) := by
      simp only [AdalyFormal.Balaban.AdmissibleSubspace.CoarseLattice, Finset.mem_filter, Finset.mem_univ, true_and]
      intro ν; exact Nat.mod_eq_zero_of_dvd (hx ν)
    have hrv := AdalyFormal.M1Patch.rv_flat (J := j + 1) hell hdvd y (Nat.le_succ j) ((x, μ) : Bond L) hc
    rw [hrv, Rw_lcr (ell ^ j) y.ofLp (⟨x, hc⟩, μ) (fit_of_lat (hdn hell hRg hdvd) x hx)]
    push_cast; ring
  · rw [if_neg hb]
    by_cases hx : OnLatN (ell ^ j) x
    · rw [if_pos hx, if_neg (fun h => hb ((mem_rows_j hell hRg hdvd x μ).mpr ⟨hx, h.1, h.2⟩)), mul_zero]
    · rw [if_neg hx, mul_zero]

open Classical in
theorem level_succ_rows (a : ℝ) (y : BondFnL2 L) :
    ∑ b ∈ Finset.univ.filter (fun b => b ∈ bondsLam (GQ ell j Rg) (j + 1)),
        a * (ell : ℝ) ^ (j + 1) * ‖AdalyFormal.M1Patch.rv ell y (j + 1) b‖ ^ 2
      = a * ∑ μ : Fin 3, ∑ Z ∈ latF L (ell ^ j * ell), (if Z ∈ Rg ∨ Z + (ell ^ j * ell) • eU L μ ∈ Rg then
          ((ell ^ j * ell : ℕ) : ℝ) * ‖Rw (ell ^ j * ell) y.ofLp Z μ‖ ^ 2 else 0) := by
  have hdN : ∀ ν : Fin 3, ell ^ j * ell ∣ L ν + 1 := hdvd
  rw [Finset.sum_filter, Fintype.sum_prod_type, Finset.sum_comm, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun μ _ => ?_)
  rw [sum_latF, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  by_cases hb : ((x, μ) : Bond L) ∈ bondsLam (GQ ell j Rg) (j + 1)
  · rw [if_pos hb]
    obtain ⟨hx, h0⟩ := (mem_rows_succ hell hRg hdvd x μ).mp hb
    rw [if_pos hx, if_pos h0]
    have hc : x ∈ AdalyFormal.Balaban.AdmissibleSubspace.CoarseLattice L (ell ^ (j + 1)) := by
      simp only [AdalyFormal.Balaban.AdmissibleSubspace.CoarseLattice, Finset.mem_filter, Finset.mem_univ, true_and]
      intro ν; exact Nat.mod_eq_zero_of_dvd (hx ν)
    have hrv := AdalyFormal.M1Patch.rv_flat (J := j + 1) hell hdvd y (le_refl (j + 1)) ((x, μ) : Bond L) hc
    rw [hrv, Rw_lcr (ell ^ (j + 1)) y.ofLp (⟨x, hc⟩, μ) (fit_of_lat hdvd x hx)]
    rw [pow_succ]
    push_cast; ring
  · rw [if_neg hb]
    by_cases hx : OnLatN (ell ^ j * ell) x
    · rw [if_pos hx, if_neg (fun h => hb ((mem_rows_succ hell hRg hdvd x μ).mpr ⟨hx, h⟩)), mul_zero]
    · rw [if_neg hx, mul_zero]

open Classical in
/-- **the patch mass in row form**. -/
theorem massP_rows (a : ℝ) (y : BondFnL2 L) :
    massP (GQ ell j Rg) a y = a * (∑ μ : Fin 3, ∑ z ∈ latF L (ell ^ j), (if z ∉ Rg ∧ z + ell ^ j • eU L μ ∉ Rg then
          ((ell ^ j : ℕ) : ℝ) * ‖Rw (ell ^ j) y.ofLp z μ‖ ^ 2 else 0)
      + ∑ μ : Fin 3, ∑ Z ∈ latF L (ell ^ j * ell), (if Z ∈ Rg ∨ Z + (ell ^ j * ell) • eU L μ ∈ Rg then
          ((ell ^ j * ell : ℕ) : ℝ) * ‖Rw (ell ^ j * ell) y.ofLp Z μ‖ ^ 2 else 0)) := by
  have hF : massP (GQ ell j Rg) a y = AdalyFormal.M1Patch.massF (GQ ell j Rg) a y := rfl
  rw [hF, show AdalyFormal.M1Patch.massF (GQ ell j Rg) a y = _ from
    AdalyFormal.M1Patch.massF_eq ell (j + 1) (S := patchTower j Rg) a y, Fin.sum_univ_castSucc, Fin.sum_univ_castSucc]
  have hlow : ∑ i : Fin j, ∑ b ∈ Finset.univ.filter (fun b => b ∈ bondsLam (GQ ell j Rg)
      (((i.castSucc).castSucc : Fin (j + 1 + 1)) : ℕ)), a * (ell : ℝ) ^ (((i.castSucc).castSucc : Fin (j + 1 + 1)) : ℕ)
        * ‖AdalyFormal.M1Patch.rv ell y (((i.castSucc).castSucc : Fin (j + 1 + 1)) : ℕ) b‖ ^ 2 = 0 := by
    refine Finset.sum_eq_zero (fun i _ => Finset.sum_eq_zero (fun b hb => ?_))
    exfalso
    rw [Finset.mem_filter] at hb
    have hi : ((((i.castSucc).castSucc : Fin (j + 1 + 1)) : ℕ)) < j := by simp
    rcases hb.2.1 with h | h <;> rw [lam_lt ell j Rg hi] at h <;> exact h
  have e1 : ((((Fin.last j).castSucc : Fin (j + 1 + 1))) : ℕ) = j := by simp
  have e2 : (((Fin.last (j + 1)) : Fin (j + 1 + 1)) : ℕ) = j + 1 := by simp
  simp only [e1, e2] at hlow ⊢
  rw [hlow, zero_add, level_j_rows hell hRg hdvd, level_succ_rows hell hRg hdvd, mul_add]

end patch

/-! ## the coupling bound -/

/-- the `LemV` constant -/
noncomputable def KV (ell : ℕ) (a : ℝ) : ℝ :=
  64 * (ell : ℝ) ^ 2 + a * (2304 * (ell : ℝ) ^ 2 + 9216 * (ell : ℝ) ^ 5 + 248832 * (ell : ℝ) ^ 6 * ((ell : ℝ) + 1) ^ 2)

section patch2
variable {ell j : ℕ} (hell : 0 < ell) {Rg : Set (PeriodicLatticeSite L)} (hRg : BlockClosed (ell ^ (j + 1)) Rg)
  (hdvd : ∀ μ : Fin 3, ell ^ (j + 1) ∣ L μ + 1)
include hell hRg hdvd

open Classical in
/-- **`LemV` on one patch.** -/
theorem lemV_patch (a : ℝ) (ha : 0 ≤ a) (φ : SiteL2 L) (c : BondFnL2 L) (hc : gradAdj (flatCfg : Cfg L) c = 0) :
    PhiP (GQ ell j Rg) (flatCfg : Cfg L) a (gradL2 (flatCfg : Cfg L) φ)
      ≤ KV ell a * PhiP (GQ ell j Rg) (flatCfg : Cfg L) a (gradL2 (flatCfg : Cfg L) φ + c) := by
  have hn : 0 < ell ^ j := pow_pos hell j
  have hN : 0 < ell ^ j * ell := Nat.mul_pos hn hell
  have hnr : (0 : ℝ) < ((ell ^ j : ℕ) : ℝ) := by exact_mod_cast hn
  have hNr : (0 : ℝ) < ((ell ^ j * ell : ℕ) : ℝ) := by exact_mod_cast hN
  have hlr : (1 : ℝ) ≤ ell := by exact_mod_cast hell
  have hdn' := hdn hell hRg hdvd
  set Φf : PeriodicLatticeSite L → SuTwo := φ.ofLp with hΦf
  set cf : Bond L → SuTwo := c.ofLp with hcf
  set y : BondFnL2 L := gradL2 (flatCfg : Cfg L) φ + c with hy
  set E : ℝ := ∑ μ : Fin 3, E1 (fun x => cf (x, μ)) with hE
  have hE0 : 0 ≤ E := Finset.sum_nonneg (fun μ _ => E1_nonneg _)
  -- E = ‖curl c‖²
  have hEc : E = ‖AdalyFormal.Balaban.DeltaKFull.curlCovariantCLM_L2 (flatCfg : Cfg L) c‖ ^ 2 := by
    rw [hE, hodge c, hc, norm_zero]; ring
  -- Φ(y) = ‖curl c‖² + mass(y)
  have hcurl : AdalyFormal.Balaban.DeltaKFull.curlCovariantCLM_L2 (flatCfg : Cfg L) y
      = AdalyFormal.Balaban.DeltaKFull.curlCovariantCLM_L2 (flatCfg : Cfg L) c := by
    rw [hy, map_add, AdalyFormal.StatementLane3.curl_gradL2_flat, zero_add]
  have hPy : PhiP (GQ ell j Rg) (flatCfg : Cfg L) a y = E + massP (GQ ell j Rg) a y := by
    rw [PhiP_patch hell hRg hdvd, hcurl, hEc]
  have hPg : PhiP (GQ ell j Rg) (flatCfg : Cfg L) a (gradL2 (flatCfg : Cfg L) φ)
      = massP (GQ ell j Rg) a (gradL2 (flatCfg : Cfg L) φ) := PhiP_grad _ a φ
  -- row values
  have hRs : ∀ z μ, Rw (ell ^ j) y.ofLp z μ
      = ((ell ^ j : ℕ) : ℝ)⁻¹ • (Phm (ell ^ j) Φf (z + ell ^ j • eU L μ) - Phm (ell ^ j) Φf z) + Rw (ell ^ j) cf z μ := by
    intro z μ
    rw [hy, WithLp.ofLp_add, Rw_add, Rw_grad (ell ^ j) hn φ z μ]
  have hRb : ∀ Z μ, Rw (ell ^ j * ell) y.ofLp Z μ
      = ((ell ^ j * ell : ℕ) : ℝ)⁻¹ • (Phm (ell ^ j * ell) Φf (Z + (ell ^ j * ell) • eU L μ) - Phm (ell ^ j * ell) Φf Z)
        + Rw (ell ^ j * ell) cf Z μ := by
    intro Z μ
    rw [hy, WithLp.ofLp_add, Rw_add, Rw_grad (ell ^ j * ell) hN φ Z μ]
  -- the gradient mass is a (Gs + Gb)
  have hMg : massP (GQ ell j Rg) a (gradL2 (flatCfg : Cfg L) φ) = a * (Gs ell j Rg Φf + Gb ell j Rg Φf) := by
    rw [massP_rows hell hRg hdvd]
    congr 1
    unfold Gs Gb
    congr 1
    · refine Finset.sum_congr rfl (fun μ _ => Finset.sum_congr rfl (fun z _ => ?_))
      split_ifs
      · rw [Rw_grad (ell ^ j) hn φ z μ, norm_smul, mul_pow, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hnr)]
        field_simp
        try rfl
      · rfl
    · refine Finset.sum_congr rfl (fun μ _ => Finset.sum_congr rfl (fun Z _ => ?_))
      split_ifs
      · rw [Rw_grad (ell ^ j * ell) hN φ Z μ, norm_smul, mul_pow, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hNr)]
        field_simp
        try rfl
      · rfl
  -- the row form of mass(y)
  set Mq : ℝ := ∑ μ : Fin 3, ∑ z ∈ latF L (ell ^ j), (if z ∉ Rg ∧ z + ell ^ j • eU L μ ∉ Rg then
          ((ell ^ j : ℕ) : ℝ) * ‖Rw (ell ^ j) y.ofLp z μ‖ ^ 2 else 0)
      + ∑ μ : Fin 3, ∑ Z ∈ latF L (ell ^ j * ell), (if Z ∈ Rg ∨ Z + (ell ^ j * ell) • eU L μ ∈ Rg then
          ((ell ^ j * ell : ℕ) : ℝ) * ‖Rw (ell ^ j * ell) y.ofLp Z μ‖ ^ 2 else 0) with hMq
  have hMy : massP (GQ ell j Rg) a y = a * Mq := massP_rows hell hRg hdvd a y
  have hMq0 : 0 ≤ Mq := by
    rw [hMq]
    refine add_nonneg (Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => ?_)))
      (Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => ?_))) <;> split_ifs <;> positivity
  -- errors
  have hEs : ∑ μ : Fin 3, ∑ z ∈ latF L (ell ^ j), (if z ∉ Rg ∧ z + ell ^ j • eU L μ ∉ Rg then
      ((ell ^ j : ℕ) : ℝ) * ‖Rw (ell ^ j) cf z μ - Fl (ell ^ j) (ell ^ j) cf z μ‖ ^ 2 else 0) ≤ 36 * E := by
    rw [hE, Finset.mul_sum]
    refine Finset.sum_le_sum (fun μ _ => le_trans (Finset.sum_le_sum (fun z _ => ?_)) (err_small cf μ hn hdn'))
    split_ifs
    · exact le_refl _
    · positivity
  have hEb : ∑ μ : Fin 3, ∑ Z ∈ latF L (ell ^ j * ell), (if Z ∈ Rg ∨ Z + (ell ^ j * ell) • eU L μ ∈ Rg then
      ((ell ^ j * ell : ℕ) : ℝ) * ‖Rw (ell ^ j * ell) cf Z μ - Fl (ell ^ j) (ell ^ j * ell) cf Z μ‖ ^ 2 else 0)
        ≤ 144 * (ell : ℝ) ^ 3 * E := by
    rw [hE, Finset.mul_sum]
    refine Finset.sum_le_sum (fun μ _ => le_trans (Finset.sum_le_sum (fun Z _ => ?_)) (err_big cf μ hn hell hdn'))
    split_ifs
    · exact le_refl _
    · positivity
  -- Mf ≤ 2 Mq + 2 (36 + 144 ℓ³) E
  have hMf : Gs ell j Rg Φf + Gb ell j Rg Φf + Fsm ell j Rg cf + Fbg ell j Rg cf
      + 2 * Sx ell j Rg Φf cf + 2 * Bx ell j Rg Φf cf ≤ 2 * Mq + (72 + 288 * (ell : ℝ) ^ 3) * E := by
    have hs : Gs ell j Rg Φf + 2 * Sx ell j Rg Φf cf + Fsm ell j Rg cf
        ≤ 2 * (∑ μ : Fin 3, ∑ z ∈ latF L (ell ^ j), (if z ∉ Rg ∧ z + ell ^ j • eU L μ ∉ Rg then
          ((ell ^ j : ℕ) : ℝ) * ‖Rw (ell ^ j) y.ofLp z μ‖ ^ 2 else 0))
          + 2 * (∑ μ : Fin 3, ∑ z ∈ latF L (ell ^ j), (if z ∉ Rg ∧ z + ell ^ j • eU L μ ∉ Rg then
          ((ell ^ j : ℕ) : ℝ) * ‖Rw (ell ^ j) cf z μ - Fl (ell ^ j) (ell ^ j) cf z μ‖ ^ 2 else 0)) := by
      unfold Gs Sx Fsm
      simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_le_sum (fun μ _ => Finset.sum_le_sum (fun z _ => ?_))
      split_ifs
      · rw [hRs]
        exact term_ineq _ hnr _ _ _
      · simp
    have hb : Gb ell j Rg Φf + 2 * Bx ell j Rg Φf cf + Fbg ell j Rg cf
        ≤ 2 * (∑ μ : Fin 3, ∑ Z ∈ latF L (ell ^ j * ell), (if Z ∈ Rg ∨ Z + (ell ^ j * ell) • eU L μ ∈ Rg then
          ((ell ^ j * ell : ℕ) : ℝ) * ‖Rw (ell ^ j * ell) y.ofLp Z μ‖ ^ 2 else 0))
          + 2 * (∑ μ : Fin 3, ∑ Z ∈ latF L (ell ^ j * ell), (if Z ∈ Rg ∨ Z + (ell ^ j * ell) • eU L μ ∈ Rg then
          ((ell ^ j * ell : ℕ) : ℝ) * ‖Rw (ell ^ j * ell) cf Z μ - Fl (ell ^ j) (ell ^ j * ell) cf Z μ‖ ^ 2 else 0)) := by
      unfold Gb Bx Fbg
      simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_le_sum (fun μ _ => Finset.sum_le_sum (fun Z _ => ?_))
      split_ifs
      · rw [hRb]
        exact term_ineq _ hNr _ _ _
      · simp
    rw [hMq]
    nlinarith [hs, hb, hEs, hEb]
  -- the four bounds
  have hl2 : (1 : ℝ) ≤ (ell : ℝ) ^ 2 := by nlinarith
  have hS := bound_S (j := j) hell Rg Φf cf (1 - 1 / (4 * (ell : ℝ) ^ 2)) (by
    have : 1 / (4 * (ell : ℝ) ^ 2) ≤ 1 / 4 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
    linarith)
  have hB := bound_B (j := j) hell Rg Φf cf (6 / 5) (by norm_num)
  have hD := bound_D (j := j) hell Rg Φf cf (3 / 4) (by norm_num)
  have hL := bound_L (j := j) hell Rg Φf cf (1 / (432 * ((ell : ℝ) ^ 2) ^ 2)) (by positivity)
  have hDP := bound_DPh hell hRg hdvd Φf
  have hFB := bound_FBs hell hRg hdvd cf
  have hLP : LPh ell j Rg Φf ≤ 54 * ((ell : ℝ) ^ 2) ^ 2 * Gs ell j Rg Φf := by
    have := bound_LPh hell hRg hdvd Φf
    rw [show ((ell : ℝ) ^ 2) ^ 2 = (ell : ℝ) ^ 4 by ring]; exact this
  have hLF := bound_LF hell hRg hdvd cf
  have hId := key_identity hell hRg hdvd Φf c hc
  have hGs0 : 0 ≤ Gs ell j Rg Φf := by
    unfold Gs; exact Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => by split_ifs <;> positivity))
  have hGb0 : 0 ≤ Gb ell j Rg Φf := by
    unfold Gb; exact Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => by split_ifs <;> positivity))
  have hFs0 : 0 ≤ Fsm ell j Rg cf := by
    unfold Fsm; exact Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => by split_ifs <;> positivity))
  have hFb0 : 0 ≤ Fbg ell j Rg cf := by
    unfold Fbg; exact Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => by split_ifs <;> positivity))
  have hfin := final_alg ((ell : ℝ) ^ 2) (Gs ell j Rg Φf) (Gb ell j Rg Φf) (Fsm ell j Rg cf) (Fbg ell j Rg cf)
    (Sx ell j Rg Φf cf) (Bx ell j Rg Φf cf) (Dx ell j Rg Φf cf) (Lx ell j Rg Φf cf) (DPh ell j Rg Φf)
    (FBs ell j Rg cf) (LPh ell j Rg Φf) (LF ell j Rg cf)
    (72 * (ell : ℝ) ^ 2 * ((ell : ℝ) + 1) ^ 2 * E) Mq ((72 + 288 * (ell : ℝ) ^ 3) * E)
    hl2 hGs0 hGb0 hFs0 hFb0 hId hS hB hD hDP hFB hL hLP hLF hMf
  -- conclusion
  rw [hPg, hMg, hPy, hMy]
  unfold KV
  have hX : 32 * (ell : ℝ) ^ 2 * ((72 + 288 * (ell : ℝ) ^ 3) * E)
      + 3456 * ((ell : ℝ) ^ 2) ^ 2 * (72 * (ell : ℝ) ^ 2 * ((ell : ℝ) + 1) ^ 2 * E)
      = (2304 * (ell : ℝ) ^ 2 + 9216 * (ell : ℝ) ^ 5 + 248832 * (ell : ℝ) ^ 6 * ((ell : ℝ) + 1) ^ 2) * E := by ring
  have hC0 : 0 ≤ 2304 * (ell : ℝ) ^ 2 + 9216 * (ell : ℝ) ^ 5 + 248832 * (ell : ℝ) ^ 6 * ((ell : ℝ) + 1) ^ 2 := by
    positivity
  have h1 : Gs ell j Rg Φf + Gb ell j Rg Φf
      ≤ 64 * (ell : ℝ) ^ 2 * Mq + (2304 * (ell : ℝ) ^ 2 + 9216 * (ell : ℝ) ^ 5
          + 248832 * (ell : ℝ) ^ 6 * ((ell : ℝ) + 1) ^ 2) * E := by
    rw [← hX]; linarith
  have h2 := mul_le_mul_of_nonneg_left h1 ha
  have haM : 0 ≤ a * Mq := mul_nonneg ha hMq0
  nlinarith [mul_nonneg ha hC0, mul_nonneg (mul_nonneg ha hC0) hE0, mul_nonneg haM (by positivity : (0 : ℝ) ≤ 64 * (ell : ℝ) ^ 2),
    mul_nonneg hE0 (by positivity : (0 : ℝ) ≤ 64 * (ell : ℝ) ^ 2)]

end patch2

/-- **`LemV` (PROVED)** with the explicit `j`-free constant `KV ell a`. -/
theorem lemV (ell : ℕ) (hell : 0 < ell) (a : ℝ) (ha : 0 ≤ a) : LemV ell a (KV ell a) := by
  intro j Lu Rg hRg φ c hc
  exact lemV_patch hell hRg (dvd_scaleUp ell j Lu hell) a ha φ c hc

theorem KV_nonneg (ell : ℕ) (a : ℝ) (ha : 0 ≤ a) : 0 ≤ KV ell a := by
  unfold KV; positivity

/-- **`LemIFlat` (PROVED)**: the target of this lane, with the explicit `j`-free constant `CS ell a · KV ell a`. -/
theorem lemIFlat (ell : ℕ) (hell : 0 < ell) (a : ℝ) (ha : 0 < a) : LemIFlat ell a (CS ell a * KV ell a) :=
  lemIFlat_of_lemV ell hell a (KV ell a) ha (KV_nonneg ell a ha.le) (lemV ell hell a ha.le)

/-- **lane D's flat W3 statement (PROVED)**. -/
theorem w3flat {ell : ℕ} (hell : 2 ≤ ell) {a : ℝ} (ha : 0 < a) : W3FlatStmt ell (by omega) a :=
  w3flat_of_LemV hell ha (KV_nonneg ell a ha.le) (lemV ell (by omega) a ha.le)

#print axioms coarseShift_eq
#print axioms final_alg
#print axioms mem_rows_j
#print axioms mem_rows_succ
#print axioms term_ineq
#print axioms mask_univ
#print axioms PhiP_patch
#print axioms level_j_rows
#print axioms level_succ_rows
#print axioms massP_rows
#print axioms lemV_patch
#print axioms lemV
#print axioms KV_nonneg
#print axioms lemIFlat
#print axioms w3flat

end AdalyFormal.LemIFlat
