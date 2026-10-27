import NsCvOF10

/-!
# CvOF11 -- chain rows of `isRowN` rows, and the row-sum data `hS` from `e - f0 in V` (lane omega)
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace AdalyFormal.CoverOmega


set_option linter.unusedSectionVars false
variable [CfData]
open scoped Matrix RealInnerProductSpace
open Finset
open AdalyFormal.Target.ClayStatement
open AdalyFormal.CoverNested
open AdalyFormal.CoverJacobi
open AdalyFormal.StatementLane (scaleUp)

variable {ell M R : ℕ}

/-- the chain row of an `isRowN` row. -/
theorem chain_row_of_isRowN (hg : NGeo ell M R) {j : ℕ} (hj : j ≤ 2) {r : ℕ} (hr : isRowN ell M R j r) :
    ∃ i, i < RN hg ∧ neP0 ell M R + stN ell M R i = r ∧ lnN ell M R i = ell ^ j := by
  have hell := hg.hell
  have hdv := (isRowN_dvd hr).1
  have hr' : ell ^ j * (r / ell ^ j) = r := Nat.mul_div_cancel' hdv
  have hI := hrowJ_nested hg hj r (by rw [hr']; exact hr)
  have hx : r - neP0 ell M R < nN ell M R := by unfold nN; omega
  obtain ⟨c1, c2⟩ := chain_row_level hg hx
  have hv : neP0 ell M R + (r - neP0 ell M R) = r := by omega
  rw [hv] at c1 c2
  have hlev : j = levN ell M R r := (row_unique hg hI hj).mp (by rw [hr']; exact hr)
  refine ⟨rowOfN ell M R (r - neP0 ell M R), (rowOfN_spec hg hx).1, ?_, ?_⟩
  · rw [c1]; unfold rstartN; rw [← hlev]; exact hr'
  · rw [c2, ← hlev]

/-- the profile `f0` of row sums: `ell^2` at the start of chain row `i1+p`, `-ell^2` at the start of row `i1+p+1`. -/
noncomputable def f0N (ell M R i1 p : ℕ) : Fin (nN ell M R) → ℝ := fun x =>
  (ell : ℝ) ^ 2 * (if x.val = stN ell M R (i1 + p) then 1 else 0) - (ell : ℝ) ^ 2 * (if x.val = stN ell M R (i1 + p + 1) then 1 else 0)

/-- the unit profile `g`: `+1` at slice `u0+p`, `-1` at `u0+p+1`. -/
noncomputable def gU (M R p : ℕ) : ℕ → ℝ := fun u =>
  (if u = u0N M R + p then 1 else 0) - (if u = u0N M R + p + 1 then 1 else 0)

theorem fSum_eq_rowsum (hg : NGeo ell M R) {j : ℕ} (hj : j ≤ 2) {r i : ℕ} (hiR : i < RN hg)
    (hir : neP0 ell M R + stN ell M R i = r) (hli : lnN ell M R i = ell ^ j) (e : Fin (nN ell M R) → ℝ) :
    fSum ell j (fe (neP0 ell M R) e) r =
      ∑ x ∈ (univ.filter (fun x : Fin (nN ell M R) => rowOfN ell M R x.val = i)), e x := by
  have G := nested_rowGeom hg
  rw [filter_sum_rowD G hiR e, fSum_eq_sum, ← hli, ← hir]
  rw [← Fin.sum_univ_eq_sum_range (fun k => fe (neP0 ell M R) e (neP0 ell M R + stN ell M R i + k)) (lnN ell M R i)]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  have := fe_at (neP0 ell M R) e ⟨stN ell M R i + k.val, by have := k.2; have := row_lt_nD G hiR; omega⟩
  simp only [] at this
  rw [← this]; congr 1; omega

theorem rowsum_f0N (hg : NGeo ell M R) {i1 p : ℕ} (hp : i1 + p + 1 < RN hg) {i : ℕ} (hiR : i < RN hg) :
    ∑ x ∈ (univ.filter (fun x : Fin (nN ell M R) => rowOfN ell M R x.val = i)), f0N ell M R i1 p x =
      (ell : ℝ) ^ 2 * ((if i1 + p = i then 1 else 0) - (if i1 + p + 1 = i then 1 else 0)) := by
  have G := nested_rowGeom hg
  have hn := stN_RN hg
  have hs1 : stN ell M R (i1 + p) < nN ell M R := by
    have := stN_strictMono hg (show i1 + p < RN hg by omega); omega
  have hs2 : stN ell M R (i1 + p + 1) < nN ell M R := by
    have := stN_strictMono hg (show i1 + p + 1 < RN hg by omega); omega
  have hrow1 : rowOfN ell M R (stN ell M R (i1 + p)) = i1 + p := by
    have := (G.row (i1 + p) (by omega) (stN ell M R (i1 + p)) hs1).mpr ⟨le_rfl, by have := G.ln1 (i1 + p) (by omega); omega⟩
    exact this
  have hrow2 : rowOfN ell M R (stN ell M R (i1 + p + 1)) = i1 + p + 1 := by
    have := (G.row (i1 + p + 1) (by omega) (stN ell M R (i1 + p + 1)) hs2).mpr ⟨le_rfl, by have := G.ln1 (i1 + p + 1) (by omega); omega⟩
    exact this
  unfold f0N
  rw [Finset.sum_sub_distrib]
  have e1 : ∑ x ∈ (univ.filter (fun x : Fin (nN ell M R) => rowOfN ell M R x.val = i)),
      (ell : ℝ) ^ 2 * (if x.val = stN ell M R (i1 + p) then 1 else 0) =
      (ell : ℝ) ^ 2 * (if i1 + p = i then 1 else 0) := by
    rw [← Finset.mul_sum, Finset.sum_filter]
    congr 1
    rw [Finset.sum_eq_single (⟨stN ell M R (i1 + p), hs1⟩ : Fin (nN ell M R))]
    · simp only [hrow1, if_true]
    · intro b _ hb
      have : b.val ≠ stN ell M R (i1 + p) := fun h => hb (Fin.ext h)
      simp [this]
    · intro h; exact absurd (Finset.mem_univ _) h
  have e2 : ∑ x ∈ (univ.filter (fun x : Fin (nN ell M R) => rowOfN ell M R x.val = i)),
      (ell : ℝ) ^ 2 * (if x.val = stN ell M R (i1 + p + 1) then 1 else 0) =
      (ell : ℝ) ^ 2 * (if i1 + p + 1 = i then 1 else 0) := by
    rw [← Finset.mul_sum, Finset.sum_filter]
    congr 1
    rw [Finset.sum_eq_single (⟨stN ell M R (i1 + p + 1), hs2⟩ : Fin (nN ell M R))]
    · simp only [hrow2, if_true]
    · intro b _ hb
      have : b.val ≠ stN ell M R (i1 + p + 1) := fun h => hb (Fin.ext h)
      simp [this]
    · intro h; exact absurd (Finset.mem_univ _) h
  rw [e1, e2]; ring

theorem hS_nested (hg : NGeo ell M R) {i1 : ℕ} (hi1 : i1 + (ell - 1) + R * M < RN hg)
    (hst : ∀ j, j ≤ ell → neP0 ell M R + stN ell M R (i1 + j) = ell ^ 2 * (u0N M R + j))
    (hln : ∀ j, j ≤ ell - 1 → lnN ell M R (i1 + j) = ell ^ 2) {p : ℕ} (hp : p + 1 ≤ ell - 1)
    (e : Fin (nN ell M R) → ℝ) (he : e - f0N ell M R i1 p ∈ Vsub (rowOfN ell M R)) :
    ∀ j, j ≤ 2 → ∀ r, isRowN ell M R j r →
      fSum ell j (fe (neP0 ell M R) e) r = (ell : ℝ) ^ j * rhoY ell (gU M R p) j r := by
  intro j hj r hr
  have hell := hg.hell
  have hRM := hg.cRM
  obtain ⟨i, hiR, hir, hli⟩ := chain_row_of_isRowN hg hj hr
  rw [fSum_eq_rowsum hg hj hiR hir hli e]
  have h0 := he i
  simp only [Pi.sub_apply, Finset.sum_sub_distrib] at h0
  have hsub : ∑ x ∈ (univ.filter (fun x : Fin (nN ell M R) => rowOfN ell M R x.val = i)), e x =
      ∑ x ∈ (univ.filter (fun x : Fin (nN ell M R) => rowOfN ell M R x.val = i)), f0N ell M R i1 p x := by
    linarith
  rw [hsub, rowsum_f0N hg (by omega) hiR]
  unfold rhoY gU
  by_cases hj2 : j = 2
  · subst hj2
    simp only [if_true]
    have hdv : ell ^ 2 ∣ r := (isRowN_dvd hr).1
    have hr2 : ell ^ 2 * (r / ell ^ 2) = r := Nat.mul_div_cancel' hdv
    have hpos : 0 < ell ^ 2 := by positivity
    have hiff1 : (i1 + p = i) ↔ (r / ell ^ 2 = u0N M R + p) := by
      constructor
      · intro h
        have := hst p (by omega)
        rw [h, hir] at this
        have h3 : ell ^ 2 * (r / ell ^ 2) = ell ^ 2 * (u0N M R + p) := by rw [hr2]; exact this
        exact Nat.eq_of_mul_eq_mul_left hpos h3
      · intro h
        have := hst p (by omega)
        have h4 : neP0 ell M R + stN ell M R i = neP0 ell M R + stN ell M R (i1 + p) := by
          rw [hir, this, ← h, hr2]
        exact (stN_inj hg (by omega)).symm
    have hiff2 : (i1 + p + 1 = i) ↔ (r / ell ^ 2 = u0N M R + p + 1) := by
      constructor
      · intro h
        have := hst (p + 1) (by omega)
        have e : i1 + (p + 1) = i1 + p + 1 := by omega
        rw [e, h, hir] at this
        have h3 : ell ^ 2 * (r / ell ^ 2) = ell ^ 2 * (u0N M R + p + 1) := by rw [hr2, this]; ring
        exact Nat.eq_of_mul_eq_mul_left hpos h3
      · intro h
        have := hst (p + 1) (by omega)
        have e : i1 + (p + 1) = i1 + p + 1 := by omega
        rw [e] at this
        have h4 : neP0 ell M R + stN ell M R i = neP0 ell M R + stN ell M R (i1 + p + 1) := by
          rw [hir, this]
          have h5 : r = ell ^ 2 * (u0N M R + p + 1) := by rw [← hr2, h]
          rw [h5]; ring
        exact (stN_inj hg (by omega)).symm
    simp only [← hiff1, ← hiff2]
  · simp only [if_neg hj2, mul_zero]
    have hlj : ell ^ j ≠ ell ^ 2 := by
      intro h
      exact hj2 (Nat.pow_right_injective (by omega) h)
    have hc1 : ¬ (i1 + p = i) := by
      intro h; apply hlj; rw [← hli, ← h]; exact (hln p (by omega)).symm ▸ rfl
    have hc2 : ¬ (i1 + p + 1 = i) := by
      intro h; apply hlj; rw [← hli, ← h]; exact (hln (p + 1) (by omega)).symm ▸ rfl
    simp [hc1, hc2]

#print axioms hS_nested

end AdalyFormal.CoverOmega
