import LF5c

/-!
# LF5d -- M1: `epsN n v ≤ (1 + 165 ell⁴)(n/a) · mass(D v)` for `v ⟂ N(Q')` on the patch (flat `U`)

* `edge_bound`: one cell edge is controlled by its small row, or by the big row of its big block plus the deviations
  of its two end cells from their virtual averages.
* `epsN_split`: summing over edges (fibres of `corner N` have `≤ ell³` corners; the `n`-shift permutes corners).
* `Dsum_le`: the total deviation is controlled by the small rows inside the virtual big blocks (cube Poincaré).
* `epsN_le_mass`.
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

open Classical in
/-- deviation of a cell value from the virtual average of its big block (zero inside `Rg`). -/
noncomputable def dev (ell j : ℕ) (Rg : Set (PeriodicLatticeSite L)) (f : PeriodicLatticeSite L → SuTwo)
    (z : PeriodicLatticeSite L) : ℝ :=
  if z ∈ Rg then 0 else ‖f z - Qa ell j Rg (j + 1) f (corner (ell ^ (j + 1)) z)‖ ^ 2

theorem dev_nonneg (ell j : ℕ) (Rg : Set (PeriodicLatticeSite L)) (f : PeriodicLatticeSite L → SuTwo)
    (z : PeriodicLatticeSite L) : 0 ≤ dev ell j Rg f z := by
  unfold dev; split_ifs <;> positivity

open Classical in
noncomputable def Dsum (ell j : ℕ) (Rg : Set (PeriodicLatticeSite L)) (f : PeriodicLatticeSite L → SuTwo) : ℝ :=
  ∑ y : PeriodicLatticeSite L, if OnLatN (ell ^ j) y then dev ell j Rg f y else 0

/-- `L μ + 1 = Nu μ · n`. -/
def NuOf (n : ℕ) (L : PeriodicLatticeExtent) : Fin 3 → ℕ := fun μ => (L μ + 1) / n

section patch
variable {ell j : ℕ} (hell : 0 < ell) {Rg : Set (PeriodicLatticeSite L)} (hRg : BlockClosed (ell ^ (j + 1)) Rg)
  (hdvd : ∀ μ : Fin 3, ell ^ (j + 1) ∣ L μ + 1)
include hell hRg hdvd

theorem hNuOf : ∀ μ : Fin 3, L μ + 1 = NuOf (ell ^ j) L μ * ell ^ j := by
  intro μ
  unfold NuOf
  exact (Nat.div_mul_cancel ((pow_dvd_pow ell (Nat.le_succ j)).trans (hdvd μ))).symm

theorem dev_ge (v : SiteL2 L) (hv : v ∈ (NQp (GQ ell j Rg) (flatCfg : Cfg L))ᗮ) (z : PeriodicLatticeSite L) :
    ‖v.ofLp z - Qa ell j Rg (j + 1) v.ofLp (corner (ell ^ (j + 1)) z)‖ ^ 2 ≤ dev ell j Rg v.ofLp z := by
  classical
  unfold dev
  by_cases hz : z ∈ Rg
  · rw [if_pos hz]
    have hc : corner (ell ^ (j + 1)) z ∈ Rg := (corner_mem_Rg hell hRg (pow_pos hell _) (dvd_refl _) z).mpr hz
    rw [Qa_Rg hell hRg hdvd v hv _ (corner_dvd _ z) hc, ← orth_big hell hRg v hv z hz, sub_self, norm_zero]
    norm_num
  · rw [if_neg hz]

/-- **one cell edge**. -/
theorem edge_bound (v : SiteL2 L) (hv : v ∈ (NQp (GQ ell j Rg) (flatCfg : Cfg L))ᗮ) (a : ℝ) (ha : 0 < a)
    (y : PeriodicLatticeSite L) (hy : ∀ μ : Fin 3, ell ^ j ∣ (y μ).val) (μ : Fin 3) :
    ‖v.ofLp (coarseShift y (ell ^ j) μ) - v.ofLp y‖ ^ 2
      ≤ ((ell : ℝ) ^ j / a) * rowF ell j Rg a j v.ofLp (y, μ)
        + 3 * ((ell : ℝ) ^ (j + 1) / a) * rowF ell j Rg a (j + 1) v.ofLp (corner (ell ^ (j + 1)) y, μ)
        + 3 * dev ell j Rg v.ofLp (coarseShift y (ell ^ j) μ) + 3 * dev ell j Rg v.ofLp y := by
  classical
  have hn : 0 < ell ^ j := pow_pos hell j
  have hN : 0 < ell ^ (j + 1) := pow_pos hell (j + 1)
  have hnN : ell ^ j ∣ ell ^ (j + 1) := pow_dvd_pow ell (Nat.le_succ j)
  have hnr : (0 : ℝ) < (ell : ℝ) ^ j := by positivity
  have hNr : (0 : ℝ) < (ell : ℝ) ^ (j + 1) := by positivity
  have hm : ∀ μ : Fin 3, ell ^ j ∣ L μ + 1 := fun μ => hnN.trans (hdvd μ)
  set yp := coarseShift y (ell ^ j) μ with hyp
  have hyp_lat : ∀ ν : Fin 3, ell ^ j ∣ (yp ν).val := onLat_shift (ell ^ j) hm y hy μ
  have h1 := rowF_nonneg ell j Rg a ha.le j v.ofLp (y, μ)
  have h2 := rowF_nonneg ell j Rg a ha.le (j + 1) v.ofLp (corner (ell ^ (j + 1)) y, μ)
  have h3 := dev_nonneg ell j Rg v.ofLp yp
  have h4 := dev_nonneg ell j Rg v.ofLp y
  have hc1 : 0 ≤ (ell : ℝ) ^ j / a * rowF ell j Rg a j v.ofLp (y, μ) := by positivity
  have hc2 : 0 ≤ 3 * ((ell : ℝ) ^ (j + 1) / a) * rowF ell j Rg a (j + 1) v.ofLp (corner (ell ^ (j + 1)) y, μ) := by
    positivity
  by_cases hA : y ∉ Rg ∧ yp ∉ Rg
  · -- a small row
    have hrow : (y, μ) ∈ bondsLam (GQ ell j Rg) j := by
      refine ⟨Or.inl ((mem_lam_j ell j Rg y).mpr ⟨hy, hA.1⟩), ?_⟩
      rintro (h | h)
      · exact hA.1 (omGe_Rg hell hRg hdvd y h)
      · exact hA.2 (omGe_Rg hell hRg hdvd _ h)
    have hF : rowF ell j Rg a j v.ofLp (y, μ) = a / (ell : ℝ) ^ j * ‖v.ofLp yp - v.ofLp y‖ ^ 2 := by
      unfold rowF; rw [if_pos hrow]
      unfold rowE
      rw [Qa_cell hell hRg hdvd v hv _ hyp_lat, Qa_cell hell hRg hdvd v hv _ hy]
    have : ‖v.ofLp yp - v.ofLp y‖ ^ 2 = (ell : ℝ) ^ j / a * rowF ell j Rg a j v.ofLp (y, μ) := by
      rw [hF]; field_simp
    linarith
  · have hor : y ∈ Rg ∨ yp ∈ Rg := by
      by_contra hcon; push_neg at hcon; exact hA hcon
    by_cases hB : corner (ell ^ (j + 1)) yp = corner (ell ^ (j + 1)) y
    · -- inside one top block
      have hiff : yp ∈ Rg ↔ y ∈ Rg := by
        rw [← corner_mem_Rg hell hRg hN (dvd_refl _) yp, hB, corner_mem_Rg hell hRg hN (dvd_refl _) y]
      have hyR : y ∈ Rg := hor.elim id hiff.mp
      have hypR : yp ∈ Rg := hiff.mpr hyR
      have : v.ofLp yp - v.ofLp y = 0 := by
        rw [orth_big hell hRg v hv yp hypR, orth_big hell hRg v hv y hyR, hB, sub_self]
      rw [this, norm_zero]
      have : (0 : ℝ) ^ 2 = 0 := by norm_num
      rw [this]; positivity
    · -- crossing into or out of `Rg`
      have hcr := crossing hell hRg hdvd y hy μ hB
      set Y := corner (ell ^ (j + 1)) y with hY
      have hYlat : ∀ ν : Fin 3, ell ^ (j + 1) ∣ (Y ν).val := corner_dvd _ y
      have hYplat : ∀ ν : Fin 3, ell ^ (j + 1) ∣ (corner (ell ^ (j + 1)) yp ν).val := corner_dvd _ yp
      have hrow : (Y, μ) ∈ bondsLam (GQ ell j Rg) (j + 1) := by
        refine ⟨?_, ?_⟩
        · rcases hor with h | h
          · exact Or.inl ((mem_lam_succ ell j Rg Y).mpr ⟨hYlat, (corner_mem_Rg hell hRg hN (dvd_refl _) y).mpr h⟩)
          · right
            show coarseShift Y (ell ^ (j + 1)) μ ∈ (GQ ell j Rg).Lam (j + 1)
            rw [← hcr]
            exact (mem_lam_succ ell j Rg _).mpr ⟨hYplat, (corner_mem_Rg hell hRg hN (dvd_refl _) yp).mpr h⟩
        · have hk : (GQ ell j Rg).k < j + 1 + 1 := by show j + 1 < j + 1 + 1; omega
          rintro (h | h) <;> exact not_OmGe_of_lt hk _ h
      have hF : rowF ell j Rg a (j + 1) v.ofLp (Y, μ)
          = a / (ell : ℝ) ^ (j + 1) * ‖Qa ell j Rg (j + 1) v.ofLp (corner (ell ^ (j + 1)) yp)
              - Qa ell j Rg (j + 1) v.ofLp Y‖ ^ 2 := by
        unfold rowF; rw [if_pos hrow]
        unfold rowE
        show a / (ell : ℝ) ^ (j + 1) * ‖Qa ell j Rg (j + 1) v.ofLp (coarseShift Y (ell ^ (j + 1)) μ)
          - Qa ell j Rg (j + 1) v.ofLp Y‖ ^ 2 = _
        rw [← hcr]
      have hsplit : v.ofLp yp - v.ofLp y
          = (Qa ell j Rg (j + 1) v.ofLp (corner (ell ^ (j + 1)) yp) - Qa ell j Rg (j + 1) v.ofLp Y)
            + (v.ofLp yp - Qa ell j Rg (j + 1) v.ofLp (corner (ell ^ (j + 1)) yp))
            + -(v.ofLp y - Qa ell j Rg (j + 1) v.ofLp Y) := by abel
      have hb := norm_add3_sq_le (Qa ell j Rg (j + 1) v.ofLp (corner (ell ^ (j + 1)) yp) - Qa ell j Rg (j + 1) v.ofLp Y)
        (v.ofLp yp - Qa ell j Rg (j + 1) v.ofLp (corner (ell ^ (j + 1)) yp))
        (-(v.ofLp y - Qa ell j Rg (j + 1) v.ofLp Y))
      rw [← hsplit, norm_neg] at hb
      have hd1 := dev_ge hell hRg hdvd v hv yp
      have hd2 := dev_ge hell hRg hdvd v hv y
      rw [← hY] at hd2
      have hQ : ‖Qa ell j Rg (j + 1) v.ofLp (corner (ell ^ (j + 1)) yp) - Qa ell j Rg (j + 1) v.ofLp Y‖ ^ 2
          = (ell : ℝ) ^ (j + 1) / a * rowF ell j Rg a (j + 1) v.ofLp (Y, μ) := by
        rw [hF]; field_simp
      rw [hQ] at hb
      linarith

/-! ### summation -/

theorem fiber_card (Y : PeriodicLatticeSite L) :
    ((Finset.univ.filter (fun y : PeriodicLatticeSite L => OnLatN (ell ^ j) y)).filter
      (fun y => corner (ell ^ (j + 1)) y = Y)).card ≤ ell ^ 3 := by
  classical
  have hsub : ((Finset.univ.filter (fun y : PeriodicLatticeSite L => OnLatN (ell ^ j) y)).filter
      (fun y => corner (ell ^ (j + 1)) y = Y)) ⊆ (cube ell).image (iota (ell ^ j) Y) := by
    intro y hy
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy
    rw [Finset.mem_image]
    refine ⟨idx (ell ^ j) (ell ^ (j + 1)) y, idx_mem_cube ell j hell hdvd y hy.1, ?_⟩
    rw [← hy.2]; exact iota_idx ell j hell hdvd y hy.1
  calc _ ≤ ((cube ell).image (iota (ell ^ j) Y)).card := Finset.card_le_card hsub
    _ ≤ (cube ell).card := Finset.card_image_le
    _ = ell ^ 3 := card_cube ell

theorem sum_fiber (g : PeriodicLatticeSite L → ℝ) (hg : ∀ Y, 0 ≤ g Y) :
    ∑ y : PeriodicLatticeSite L, (if OnLatN (ell ^ j) y then g (corner (ell ^ (j + 1)) y) else 0)
      ≤ (ell : ℝ) ^ 3 * ∑ Y : PeriodicLatticeSite L, g Y := by
  classical
  rw [← Finset.sum_filter]
  have h := sum_comp_le (Finset.univ.filter (fun y : PeriodicLatticeSite L => OnLatN (ell ^ j) y)) Finset.univ
    (corner (ell ^ (j + 1))) g (ell ^ 3) (fun _ _ => Finset.mem_univ _)
    (fun Y _ => fiber_card hell hRg hdvd Y) (fun Y _ => hg Y)
  push_cast at h
  exact h

theorem sum_shift_corner (g : PeriodicLatticeSite L → ℝ) (μ : Fin 3) :
    ∑ y : PeriodicLatticeSite L, (if OnLatN (ell ^ j) y then g (coarseShift y (ell ^ j) μ) else 0)
      = ∑ y : PeriodicLatticeSite L, (if OnLatN (ell ^ j) y then g y else 0) := by
  classical
  have hn : 0 < ell ^ j := pow_pos hell j
  have hN := hNuOf hell hRg hdvd
  have hiff : ∀ y : PeriodicLatticeSite L, OnLatN (ell ^ j) y ↔ OnLatN (ell ^ j) (coarseShift y (ell ^ j) μ) := by
    intro y
    constructor
    · intro h; exact onLat_coarseShift (ell ^ j) (NuOf (ell ^ j) L) hn hN μ y _ (dvd_refl _) h
    · intro h
      have := onLat_backN (ell ^ j) (NuOf (ell ^ j) L) hn hN μ _ h
      rwa [backN_shift (ell ^ j) (NuOf (ell ^ j) L) hn hN μ y] at this
  refine Fintype.sum_bijective (fun y => coarseShift y (ell ^ j) μ)
    ⟨fun a b h => by
      have := congrArg (backN (ell ^ j) μ) h
      simpa [backN_shift (ell ^ j) (NuOf (ell ^ j) L) hn hN μ] using this,
     fun z => ⟨backN (ell ^ j) μ z, shift_backN (ell ^ j) (NuOf (ell ^ j) L) hn hN μ z⟩⟩ _ _ (fun y => ?_)
  show (if OnLatN (ell ^ j) y then g (coarseShift y (ell ^ j) μ) else 0)
    = (if OnLatN (ell ^ j) (coarseShift y (ell ^ j) μ) then g (coarseShift y (ell ^ j) μ) else 0)
  by_cases h : OnLatN (ell ^ j) y
  · rw [if_pos h, if_pos ((hiff y).mp h)]
  · rw [if_neg h, if_neg (fun h' => h ((hiff y).mpr h'))]

/-- **summing the edge bound**. -/
theorem epsN_split (v : SiteL2 L) (hv : v ∈ (NQp (GQ ell j Rg) (flatCfg : Cfg L))ᗮ) (a : ℝ) (ha : 0 < a) :
    epsN (ell ^ j) v.ofLp
      ≤ ((ell : ℝ) ^ j / a) * rowS ell j Rg a j v.ofLp
        + 3 * ((ell : ℝ) ^ (j + 1) / a) * ((ell : ℝ) ^ 3 * rowS ell j Rg a (j + 1) v.ofLp)
        + 18 * Dsum ell j Rg v.ofLp := by
  classical
  have hnr : (0 : ℝ) < (ell : ℝ) ^ j := by positivity
  have hNr : (0 : ℝ) < (ell : ℝ) ^ (j + 1) := by positivity
  have hmu : ∀ μ : Fin 3, epsMu (ell ^ j) v.ofLp μ
      ≤ ((ell : ℝ) ^ j / a) * ∑ y : PeriodicLatticeSite L, rowF ell j Rg a j v.ofLp (y, μ)
        + 3 * ((ell : ℝ) ^ (j + 1) / a) * ((ell : ℝ) ^ 3 * ∑ Y : PeriodicLatticeSite L,
            rowF ell j Rg a (j + 1) v.ofLp (Y, μ))
        + 3 * Dsum ell j Rg v.ofLp + 3 * Dsum ell j Rg v.ofLp := by
    intro μ
    unfold epsMu
    have hpt : ∀ y : PeriodicLatticeSite L, (if OnLatN (ell ^ j) y then
          ‖v.ofLp (coarseShift y (ell ^ j) μ) - v.ofLp y‖ ^ 2 else 0)
        ≤ ((ell : ℝ) ^ j / a) * rowF ell j Rg a j v.ofLp (y, μ)
          + 3 * ((ell : ℝ) ^ (j + 1) / a) * (if OnLatN (ell ^ j) y then
              rowF ell j Rg a (j + 1) v.ofLp (corner (ell ^ (j + 1)) y, μ) else 0)
          + 3 * (if OnLatN (ell ^ j) y then dev ell j Rg v.ofLp (coarseShift y (ell ^ j) μ) else 0)
          + 3 * (if OnLatN (ell ^ j) y then dev ell j Rg v.ofLp y else 0) := by
      intro y
      by_cases hy : OnLatN (ell ^ j) y
      · simp only [if_pos hy]
        exact edge_bound hell hRg hdvd v hv a ha y hy μ
      · simp only [if_neg hy, mul_zero, add_zero]
        have := rowF_nonneg ell j Rg a ha.le j v.ofLp (y, μ)
        positivity
    refine (Finset.sum_le_sum (fun y _ => hpt y)).trans ?_
    simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
    have e1 := sum_fiber hell hRg hdvd (fun Y => rowF ell j Rg a (j + 1) v.ofLp (Y, μ))
      (fun Y => rowF_nonneg ell j Rg a ha.le (j + 1) v.ofLp (Y, μ))
    have e2 := sum_shift_corner hell hRg hdvd (fun z => dev ell j Rg v.ofLp z) μ
    simp only at e2
    rw [e2]
    unfold Dsum
    have : 0 ≤ 3 * ((ell : ℝ) ^ (j + 1) / a) := by positivity
    nlinarith [mul_le_mul_of_nonneg_left e1 this]
  unfold epsN
  calc ∑ μ : Fin 3, epsMu (ell ^ j) v.ofLp μ
      ≤ ∑ μ : Fin 3, (((ell : ℝ) ^ j / a) * ∑ y : PeriodicLatticeSite L, rowF ell j Rg a j v.ofLp (y, μ)
        + 3 * ((ell : ℝ) ^ (j + 1) / a) * ((ell : ℝ) ^ 3 * ∑ Y : PeriodicLatticeSite L,
            rowF ell j Rg a (j + 1) v.ofLp (Y, μ))
        + 3 * Dsum ell j Rg v.ofLp + 3 * Dsum ell j Rg v.ofLp) := Finset.sum_le_sum (fun μ _ => hmu μ)
    _ = ((ell : ℝ) ^ j / a) * rowS ell j Rg a j v.ofLp
        + 3 * ((ell : ℝ) ^ (j + 1) / a) * ((ell : ℝ) ^ 3 * rowS ell j Rg a (j + 1) v.ofLp)
        + 18 * Dsum ell j Rg v.ofLp := by
      unfold rowS
      rw [Fintype.sum_prod_type, Fintype.sum_prod_type]
      simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul]
      rw [Finset.sum_comm (f := fun y μ => rowF ell j Rg a j v.ofLp (y, μ)),
        Finset.sum_comm (f := fun y μ => rowF ell j Rg a (j + 1) v.ofLp (y, μ))]
      push_cast; ring

end patch

#print axioms dev_nonneg
#print axioms hNuOf
#print axioms dev_ge
#print axioms edge_bound
#print axioms fiber_card
#print axioms sum_fiber
#print axioms sum_shift_corner
#print axioms epsN_split

end AdalyFormal.LemIFlat
