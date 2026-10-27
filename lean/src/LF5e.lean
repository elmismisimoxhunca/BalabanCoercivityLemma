import LF5d

/-!
# LF5e -- the deviation sum and the final M1 bound

* `dev_le_cube`: a cell's deviation from its virtual average is `≤ 9 ell (n/a) E'(Y)`, `E'(Y)` the small-row energy
  inside its virtual big block `Y` (cube Poincaré, `cube_dev`).
* `Dsum_le`: `Σ_corners dev ≤ 9 ell⁴ (n/a) rowS_j`.
* **`epsN_le_mass`**: for `v ⟂ N(Q')` on the patch at flat `U`,
  `epsN n v ≤ (1 + 165 ell⁴) (n/a) · mass(D v)`.
No sorry / axiom.
-/
set_option autoImplicit false
set_option maxHeartbeats 16000000
namespace AdalyFormal.LemIFlat

open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.M1Patch (patchTower corner corner_dvd mem_lam_j mem_lam_succ)
open AdalyFormal.StatementLane (BlockClosed)
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond blockOf mem_blockOf)
open AdalyFormal.Balaban.CoarseCurl (coarseShift coarseShift_val_eq coarseShift_apply_ne)
open AdalyFormal.SliceCoerc (OnLat onLat_shift)

variable {L : PeriodicLatticeExtent}

/-- the small-row energy inside the big block at `Y`. -/
noncomputable def Eblk (ell j : ℕ) (Rg : Set (PeriodicLatticeSite L)) (a : ℝ) (f : PeriodicLatticeSite L → SuTwo)
    (Y : PeriodicLatticeSite L) : ℝ :=
  ∑ ν : Fin 3, ∑ i ∈ (cube ell).filter (fun i => i ν + 1 < ell), rowF ell j Rg a j f (iota (ell ^ j) Y i, ν)

theorem Eblk_nonneg (ell j : ℕ) (Rg : Set (PeriodicLatticeSite L)) (a : ℝ) (ha : 0 ≤ a)
    (f : PeriodicLatticeSite L → SuTwo) (Y : PeriodicLatticeSite L) : 0 ≤ Eblk ell j Rg a f Y :=
  Finset.sum_nonneg (fun ν _ => Finset.sum_nonneg (fun i _ => rowF_nonneg ell j Rg a ha j f _))

section patch
variable {ell j : ℕ} (hell : 0 < ell) {Rg : Set (PeriodicLatticeSite L)} (hRg : BlockClosed (ell ^ (j + 1)) Rg)
  (hdvd : ∀ μ : Fin 3, ell ^ (j + 1) ∣ L μ + 1)
include hell hRg hdvd

theorem cube_edge (v : SiteL2 L) (hv : v ∈ (NQp (GQ ell j Rg) (flatCfg : Cfg L))ᗮ) (a : ℝ) (ha : 0 < a)
    (Y : PeriodicLatticeSite L) (hY : ∀ μ : Fin 3, ell ^ (j + 1) ∣ (Y μ).val) (hYR : Y ∉ Rg)
    (ν : Fin 3) (i : Fin 3 → ℕ) (hi : i ∈ cube ell) (hiν : i ν + 1 < ell) :
    ‖v.ofLp (iota (ell ^ j) Y (Function.update i ν (i ν + 1))) - v.ofLp (iota (ell ^ j) Y i)‖ ^ 2
      = (ell : ℝ) ^ j / a * rowF ell j Rg a j v.ofLp (iota (ell ^ j) Y i, ν) := by
  classical
  have hnr : (0 : ℝ) < (ell : ℝ) ^ j := by positivity
  have hi' : Function.update i ν (i ν + 1) ∈ cube ell := by
    rw [mem_cube]; intro μ
    by_cases h : μ = ν
    · subst h; simp; exact hiν
    · rw [Function.update_of_ne h]; exact (mem_cube ell i).mp hi μ
  have hsh := shift_iota (ell ^ j) Y i ν
  have hx0 : iota (ell ^ j) Y i ∉ Rg := fun h =>
    hYR ((mem_Rg_of_block hell hRg hY (iota_mem_block ell j hell hdvd Y hY i hi)).mp h)
  have hx1 : iota (ell ^ j) Y (Function.update i ν (i ν + 1)) ∉ Rg := fun h =>
    hYR ((mem_Rg_of_block hell hRg hY (iota_mem_block ell j hell hdvd Y hY _ hi')).mp h)
  have hrow : (iota (ell ^ j) Y i, ν) ∈ bondsLam (GQ ell j Rg) j := by
    refine ⟨Or.inl ((mem_lam_j ell j Rg _).mpr ⟨iota_onLat ell j hell hdvd Y hY i hi, hx0⟩), ?_⟩
    rintro (h | h)
    · exact hx0 (omGe_Rg hell hRg hdvd _ h)
    · exact hx1 (omGe_Rg hell hRg hdvd _ (by rw [← hsh]; exact h))
  unfold rowF; rw [if_pos hrow]
  unfold rowE
  show _ = (ell : ℝ) ^ j / a * (a / (ell : ℝ) ^ j *
    ‖Qa ell j Rg j v.ofLp (coarseShift (iota (ell ^ j) Y i) (ell ^ j) ν) - Qa ell j Rg j v.ofLp (iota (ell ^ j) Y i)‖ ^ 2)
  rw [hsh, Qa_cell hell hRg hdvd v hv _ (iota_onLat ell j hell hdvd Y hY _ hi'),
    Qa_cell hell hRg hdvd v hv _ (iota_onLat ell j hell hdvd Y hY i hi)]
  field_simp

theorem dev_le_cube (v : SiteL2 L) (hv : v ∈ (NQp (GQ ell j Rg) (flatCfg : Cfg L))ᗮ) (a : ℝ) (ha : 0 < a)
    (y : PeriodicLatticeSite L) (hy : OnLatN (ell ^ j) y) (hyR : y ∉ Rg) :
    dev ell j Rg v.ofLp y ≤ 9 * ell * ((ell : ℝ) ^ j / a) * Eblk ell j Rg a v.ofLp (corner (ell ^ (j + 1)) y) := by
  classical
  set Y := corner (ell ^ (j + 1)) y with hYdef
  have hY : ∀ μ : Fin 3, ell ^ (j + 1) ∣ (Y μ).val := corner_dvd _ y
  have hYR : Y ∉ Rg := fun h => hyR ((corner_mem_Rg hell hRg (pow_pos hell _) (dvd_refl _) y).mp h)
  unfold dev
  rw [if_neg hyR, Qa_big hell hRg hdvd v hv Y hY]
  set W : (Fin 3 → ℕ) → SuTwo := fun i => v.ofLp (iota (ell ^ j) Y i) with hW
  have hyW : v.ofLp y = W (idx (ell ^ j) (ell ^ (j + 1)) y) := by
    rw [hW]; simp only; rw [hYdef, iota_idx ell j hell hdvd y hy]
  rw [hyW]
  have hc := cube_dev ell hell W (idx (ell ^ j) (ell ^ (j + 1)) y) (idx_mem_cube ell j hell hdvd y hy)
  have hE : cubeE ell W = (ell : ℝ) ^ j / a * Eblk ell j Rg a v.ofLp Y := by
    unfold cubeE Eblk
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun ν _ => ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun i hi => ?_)
    rw [Finset.mem_filter] at hi
    exact cube_edge hell hRg hdvd v hv a ha Y hY hYR ν i hi.1 hi.2
  rw [hE] at hc
  calc _ ≤ 9 * (ell : ℝ) * ((ell : ℝ) ^ j / a * Eblk ell j Rg a v.ofLp Y) := hc
    _ = _ := by ring

theorem sum_cube_le (a : ℝ) (ha : 0 ≤ a) (f : PeriodicLatticeSite L → SuTwo) (ν : Fin 3) :
    ∑ Y : PeriodicLatticeSite L, (if (∀ μ : Fin 3, ell ^ (j + 1) ∣ (Y μ).val) then
        ∑ i ∈ (cube ell).filter (fun i => i ν + 1 < ell), rowF ell j Rg a j f (iota (ell ^ j) Y i, ν) else 0)
      ≤ ∑ y : PeriodicLatticeSite L, rowF ell j Rg a j f (y, ν) := by
  classical
  rw [← Finset.sum_filter, ← Finset.sum_product']
  set S := (Finset.univ.filter (fun Y : PeriodicLatticeSite L => ∀ μ : Fin 3, ell ^ (j + 1) ∣ (Y μ).val)) ×ˢ
    ((cube ell).filter (fun i => i ν + 1 < ell)) with hS
  have hinj : Set.InjOn (fun p : PeriodicLatticeSite L × (Fin 3 → ℕ) => iota (ell ^ j) p.1 p.2) (S : Set _) := by
    intro p hp q hq h
    simp only [hS, Finset.coe_product, Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_prod,
      Set.mem_setOf_eq] at hp hq
    have := iota_inj ell j hell hdvd p.1 q.1 hp.1 hq.1 p.2 q.2 hp.2.1 hq.2.1 h
    exact Prod.ext this.1 this.2
  have h1 : ∑ p ∈ S, rowF ell j Rg a j f (iota (ell ^ j) p.1 p.2, ν)
      = ∑ y ∈ S.image (fun p => iota (ell ^ j) p.1 p.2), rowF ell j Rg a j f (y, ν) :=
    (Finset.sum_image (f := fun y => rowF ell j Rg a j f (y, ν)) hinj).symm
  rw [h1]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
    (fun y _ _ => rowF_nonneg ell j Rg a ha j f (y, ν))

/-- **the deviation sum**. -/
theorem Dsum_le (v : SiteL2 L) (hv : v ∈ (NQp (GQ ell j Rg) (flatCfg : Cfg L))ᗮ) (a : ℝ) (ha : 0 < a) :
    Dsum ell j Rg v.ofLp ≤ 9 * (ell : ℝ) ^ 4 * ((ell : ℝ) ^ j / a) * rowS ell j Rg a j v.ofLp := by
  classical
  have hnr : (0 : ℝ) < (ell : ℝ) ^ j := by positivity
  set g : PeriodicLatticeSite L → ℝ := fun Y =>
    if (∀ μ : Fin 3, ell ^ (j + 1) ∣ (Y μ).val) ∧ Y ∉ Rg then Eblk ell j Rg a v.ofLp Y else 0 with hg
  have hg0 : ∀ Y, 0 ≤ g Y := by
    intro Y; rw [hg]; simp only; split_ifs
    · exact Eblk_nonneg ell j Rg a ha.le v.ofLp Y
    · exact le_refl 0
  have hpt : ∀ y : PeriodicLatticeSite L, (if OnLatN (ell ^ j) y then dev ell j Rg v.ofLp y else 0)
      ≤ 9 * ell * ((ell : ℝ) ^ j / a) * (if OnLatN (ell ^ j) y then g (corner (ell ^ (j + 1)) y) else 0) := by
    intro y
    by_cases hy : OnLatN (ell ^ j) y
    · rw [if_pos hy, if_pos hy]
      by_cases hyR : y ∈ Rg
      · have : dev ell j Rg v.ofLp y = 0 := by unfold dev; rw [if_pos hyR]
        rw [this]; have := hg0 (corner (ell ^ (j + 1)) y); positivity
      · have hc : g (corner (ell ^ (j + 1)) y) = Eblk ell j Rg a v.ofLp (corner (ell ^ (j + 1)) y) := by
          rw [hg]; simp only
          rw [if_pos ⟨corner_dvd _ y, fun h => hyR ((corner_mem_Rg hell hRg (pow_pos hell _) (dvd_refl _) y).mp h)⟩]
        rw [hc]
        exact dev_le_cube hell hRg hdvd v hv a ha y hy hyR
    · rw [if_neg hy, if_neg hy, mul_zero]
  have h1 : Dsum ell j Rg v.ofLp ≤ 9 * ell * ((ell : ℝ) ^ j / a) *
      ∑ y : PeriodicLatticeSite L, (if OnLatN (ell ^ j) y then g (corner (ell ^ (j + 1)) y) else 0) := by
    unfold Dsum
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum (fun y _ => hpt y)
  have h2 := sum_fiber hell hRg hdvd g hg0
  have h3 : ∑ Y : PeriodicLatticeSite L, g Y ≤ rowS ell j Rg a j v.ofLp := by
    have hle : ∀ Y, g Y ≤ ∑ ν : Fin 3, (if (∀ μ : Fin 3, ell ^ (j + 1) ∣ (Y μ).val) then
        ∑ i ∈ (cube ell).filter (fun i => i ν + 1 < ell), rowF ell j Rg a j v.ofLp (iota (ell ^ j) Y i, ν) else 0) := by
      intro Y
      rw [hg]; simp only
      by_cases hY : (∀ μ : Fin 3, ell ^ (j + 1) ∣ (Y μ).val)
      · simp only [if_pos hY]
        split_ifs
        · exact le_refl _
        · exact Finset.sum_nonneg (fun ν _ => Finset.sum_nonneg (fun i _ => rowF_nonneg ell j Rg a ha.le j _ _))
      · simp only [if_neg hY, Finset.sum_const_zero]
        split_ifs with h
        · exact absurd h.1 hY
        · exact le_refl _
    calc ∑ Y : PeriodicLatticeSite L, g Y
        ≤ ∑ Y : PeriodicLatticeSite L, ∑ ν : Fin 3, (if (∀ μ : Fin 3, ell ^ (j + 1) ∣ (Y μ).val) then
          ∑ i ∈ (cube ell).filter (fun i => i ν + 1 < ell), rowF ell j Rg a j v.ofLp (iota (ell ^ j) Y i, ν) else 0) :=
          Finset.sum_le_sum (fun Y _ => hle Y)
      _ = ∑ ν : Fin 3, ∑ Y : PeriodicLatticeSite L, (if (∀ μ : Fin 3, ell ^ (j + 1) ∣ (Y μ).val) then
          ∑ i ∈ (cube ell).filter (fun i => i ν + 1 < ell), rowF ell j Rg a j v.ofLp (iota (ell ^ j) Y i, ν) else 0) :=
          Finset.sum_comm
      _ ≤ ∑ ν : Fin 3, ∑ y : PeriodicLatticeSite L, rowF ell j Rg a j v.ofLp (y, ν) :=
          Finset.sum_le_sum (fun ν _ => sum_cube_le hell hRg hdvd a ha.le v.ofLp ν)
      _ = rowS ell j Rg a j v.ofLp := by
          unfold rowS; rw [Fintype.sum_prod_type, Finset.sum_comm]
  have hpos : 0 ≤ 9 * (ell : ℝ) * ((ell : ℝ) ^ j / a) := by positivity
  calc Dsum ell j Rg v.ofLp ≤ 9 * ell * ((ell : ℝ) ^ j / a) *
        ∑ y : PeriodicLatticeSite L, (if OnLatN (ell ^ j) y then g (corner (ell ^ (j + 1)) y) else 0) := h1
    _ ≤ 9 * ell * ((ell : ℝ) ^ j / a) * ((ell : ℝ) ^ 3 * ∑ Y : PeriodicLatticeSite L, g Y) :=
        mul_le_mul_of_nonneg_left h2 hpos
    _ ≤ 9 * ell * ((ell : ℝ) ^ j / a) * ((ell : ℝ) ^ 3 * rowS ell j Rg a j v.ofLp) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h3 (by positivity)) hpos
    _ = 9 * (ell : ℝ) ^ 4 * ((ell : ℝ) ^ j / a) * rowS ell j Rg a j v.ofLp := by ring

/-- **M1 on the patch**: the cell-edge energy of a block-constant field is controlled by its mass. -/
theorem epsN_le_mass (v : SiteL2 L) (hv : v ∈ (NQp (GQ ell j Rg) (flatCfg : Cfg L))ᗮ) (a : ℝ) (ha : 0 < a) :
    epsN (ell ^ j) v.ofLp
      ≤ (1 + 165 * (ell : ℝ) ^ 4) * ((ell : ℝ) ^ j / a) * massP (GQ ell j Rg) a (gradL2 (flatCfg : Cfg L) v) := by
  have h1 := epsN_split hell hRg hdvd v hv a ha
  have h2 := Dsum_le hell hRg hdvd v hv a ha
  have h3 := mass_ge hell hRg hdvd v a ha.le
  have hS0 : 0 ≤ rowS ell j Rg a j v.ofLp := Finset.sum_nonneg (fun b _ => rowF_nonneg ell j Rg a ha.le j _ b)
  have hS1 : 0 ≤ rowS ell j Rg a (j + 1) v.ofLp :=
    Finset.sum_nonneg (fun b _ => rowF_nonneg ell j Rg a ha.le (j + 1) _ b)
  have hnr : (0 : ℝ) < (ell : ℝ) ^ j := by positivity
  have hq : (0 : ℝ) < (ell : ℝ) ^ j / a := by positivity
  have hell1 : (0 : ℝ) ≤ (ell : ℝ) := Nat.cast_nonneg _
  have hpow : (ell : ℝ) ^ (j + 1) / a = (ell : ℝ) * ((ell : ℝ) ^ j / a) := by rw [pow_succ]; ring
  rw [hpow] at h1
  have h4 : (ell : ℝ) ^ 4 = (ell : ℝ) * (ell : ℝ) ^ 3 := by ring
  have hE4 : (0 : ℝ) ≤ (ell : ℝ) ^ 4 := by positivity
  -- epsN ≤ q (1 + 162 ell⁴) S0 + 3 ell⁴ q S1
  have h5 : epsN (ell ^ j) v.ofLp ≤ ((ell : ℝ) ^ j / a) * ((1 + 162 * (ell : ℝ) ^ 4) * rowS ell j Rg a j v.ofLp
      + 3 * (ell : ℝ) ^ 4 * rowS ell j Rg a (j + 1) v.ofLp) := by
    have : 3 * ((ell : ℝ) * ((ell : ℝ) ^ j / a)) * ((ell : ℝ) ^ 3 * rowS ell j Rg a (j + 1) v.ofLp)
        = ((ell : ℝ) ^ j / a) * (3 * (ell : ℝ) ^ 4 * rowS ell j Rg a (j + 1) v.ofLp) := by ring
    nlinarith
  have h6 : (1 + 162 * (ell : ℝ) ^ 4) * rowS ell j Rg a j v.ofLp + 3 * (ell : ℝ) ^ 4 * rowS ell j Rg a (j + 1) v.ofLp
      ≤ (1 + 165 * (ell : ℝ) ^ 4) * massP (GQ ell j Rg) a (gradL2 (flatCfg : Cfg L) v) := by
    nlinarith
  calc epsN (ell ^ j) v.ofLp ≤ ((ell : ℝ) ^ j / a) * ((1 + 162 * (ell : ℝ) ^ 4) * rowS ell j Rg a j v.ofLp
      + 3 * (ell : ℝ) ^ 4 * rowS ell j Rg a (j + 1) v.ofLp) := h5
    _ ≤ ((ell : ℝ) ^ j / a) * ((1 + 165 * (ell : ℝ) ^ 4) * massP (GQ ell j Rg) a (gradL2 (flatCfg : Cfg L) v)) :=
        mul_le_mul_of_nonneg_left h6 hq.le
    _ = _ := by ring

end patch

#print axioms cube_edge
#print axioms dev_le_cube
#print axioms sum_cube_le
#print axioms Dsum_le
#print axioms epsN_le_mass

#print axioms Eblk_nonneg

end AdalyFormal.LemIFlat
