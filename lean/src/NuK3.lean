import NuK2
import NuE8

/-!
# NuK3 -- the trial vectors realise the Z-part of the competitor: `Q x_e = zrow (rhoY (gbar uE))` (lane ncwdh_ell2_20261018)
-/
set_option autoImplicit false
set_option maxHeartbeats 16000000

namespace AdalyFormal.NcwdhTwo

open Finset
open AdalyFormal.Target.ClayStatement
open AdalyFormal.CoverNested
open AdalyFormal.CoverJacobi
open AdalyFormal.CoverOmega
open AdalyFormal.Balaban.SuTwoLogExp
open AdalyFormal.StatementLane (scaleUp)
open AdalyFormal.StatementLaneG
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Balaban.CovariantOperators
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)

section
variable [CfData]
variable {M R : ℕ}

theorem zrow_congr_nested2 (hg : NGeo 2 M R) (hM : 0 < M) (ρ ρ' : ℕ → ℕ → ℝ)
    (h : ∀ j, j ≤ 2 → ∀ r, isRowN 2 M R j r → ρ j r = ρ' j r) :
    zrow (geomOf 2 2 (neS 2 M R)) ρ = zrow (geomOf 2 2 (neS 2 M R)) ρ' := by
  refine PiLp.ext (fun p => ?_)
  show (if p.2.1.2 = 1 then dgS (ρ (p.1 : ℕ) (p.2.1.1 0).val) else 0) = (if p.2.1.2 = 1 then dgS (ρ' (p.1 : ℕ) (p.2.1.1 0).val) else 0)
  by_cases h1 : p.2.1.2 = 1
  · rw [if_pos h1, if_pos h1]
    congr 1
    have hj : (p.1 : ℕ) ≤ 2 := by have := p.1.2; simp [geomOf] at this ⊢; omega
    have hmem : (p.2.1.1, (1 : Fin 3)) ∈ bondsLam (geomOf 2 2 (neS 2 M R)) (p.1 : ℕ) := by
      have := p.2.2
      have hq : ((p.2.1.1, (1 : Fin 3))) = p.2.1 := Prod.ext rfl h1.symm
      rw [hq]
      exact this
    exact h _ hj _ (((bondsLam_one_iff hg hM hj p.2.1.1).mp hmem).2)
  · rw [if_neg h1, if_neg h1]

/-- the sum of a single delta over a row. -/
theorem rowsum_single (hg : NGeo 2 M R) {i i' : ℕ} (hi' : i' < RN hg) :
    ∑ y ∈ (univ.filter (fun y : Fin (nN 2 M R) => rowOfN 2 M R y.val = i)),
      (Pi.single (⟨stN 2 M R i', by
        have := stN_strictMono hg hi'; rw [stN_RN hg] at this; exact this⟩ : Fin (nN 2 M R)) (1 : ℝ) : Fin (nN 2 M R) → ℝ) y =
      if i' = i then 1 else 0 := by
  classical
  rw [Finset.sum_pi_single']
  have hrow : rowOfN 2 M R (stN 2 M R i') = i' := by
    have hlt : stN 2 M R i' < nN 2 M R := by
      have := stN_strictMono hg hi'; rw [stN_RN hg] at this; exact this
    have := ((nested_rowGeom hg).row i' hi' (stN 2 M R i') hlt).mpr ⟨le_rfl, by have := (nested_rowGeom hg).ln1 i' hi'; omega⟩
    exact this
  by_cases h : i' = i
  · subst h; simp [hrow]
  · simp [hrow, h]


/-- **the trial vectors realise the Z-part of the competitor.** -/
theorem Qx_pair (hdvd : 2 ∣ M) (hM : 0 < M) (hR : 1 ≤ R) (t a : ℝ) (ht : |t| < Real.pi / 2) {i1 p uE : ℕ}
    (hp : i1 + p + 1 < RN (nGeo_two (le_refl 2) hdvd hM hR))
    (hlnE : lnN 2 M R (i1 + p) = 4) (hlnO : lnN 2 M R (i1 + p + 1) = 4)
    (hsE : neP0 2 M R + stN 2 M R (i1 + p) = 4 * uE) (hsO : neP0 2 M R + stN 2 M R (i1 + p + 1) = 4 * (uE + 1))
    {es : Fin (nN 2 M R) → ℝ} (hes : es ∈ Vsub (rowOfN 2 M R)) (τ : ℝ) :
    (Pt 2 M R (by norm_num) (neC0 2 M R) t a).data.Q
        (xE (nGeo_two (le_refl 2) hdvd hM hR) (le_refl 2) hM hR (f0pair (nGeo_two (le_refl 2) hdvd hM hR) i1 p hp + τ • es)) =
      zrow (geomOf 2 2 (neS 2 M R)) (rhoY 2 (gbar uE)) := by
  have hg := nGeo_two (le_refl 2) hdvd hM hR
  have S := nested_z0Setup (le_refl 2) (by norm_num) hdvd hM hR t ht
  have hQ : (Pt 2 M R (by norm_num) (neC0 2 M R) t a).data.Q
      (xE hg (le_refl 2) hM hR (f0pair hg i1 p hp + τ • es)) =
      QfullOf (geomOf 2 2 (neS 2 M R)) (stag0Cfg (L := scaleUp 2 2 (neLu M R)) (neC0 2 M R) t)
        (zfield (fe (neP0 2 M R) (f0pair hg i1 p hp + τ • es))) := rfl
  rw [hQ, Qfull_zfield_eq_zrow0 S]
  apply zrow_congr_nested2 hg hM
  intro j hj r hr
  obtain ⟨i, hiR, hir, hli⟩ := chain_row_of_isRowN hg hj hr
  have hsum := fSum_eq_rowsum hg hj hiR hir hli (f0pair hg i1 p hp + τ • es)
  rw [hsum]
  -- the row sum of the trial vector
  have hrs : ∑ x ∈ (univ.filter (fun x : Fin (nN 2 M R) => rowOfN 2 M R x.val = i)), (f0pair hg i1 p hp + τ • es) x =
      (if i1 + p = i then (1 : ℝ) else 0) - (if i1 + p + 1 = i then (1 : ℝ) else 0) := by
    have h1 := rowsum_single hg (i := i) (show i1 + p < RN hg by omega)
    have h2 := rowsum_single hg (i := i) hp
    have h3 : ∑ x ∈ (univ.filter (fun x : Fin (nN 2 M R) => rowOfN 2 M R x.val = i)), es x = 0 := hes i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_add_distrib, ← Finset.mul_sum, h3, mul_zero, add_zero]
    unfold f0pair
    simp only [Pi.sub_apply, Finset.sum_sub_distrib]
    rw [h1, h2]
  rw [hrs]
  unfold rhoY
  have h4 : ((2 : ℕ) : ℝ) = 2 := by norm_num
  rw [h4]
  by_cases hj2 : j = 2
  · subst hj2
    rw [if_pos rfl]
    have hli4 : lnN 2 M R i = 4 := by rw [hli]; norm_num
    by_cases hiE : i = i1 + p
    · subst hiE
      have hr : r = 4 * uE := by omega
      have hr4 : r / 2 ^ 2 = uE := by rw [hr]; omega
      rw [hr4]
      unfold gbar
      simp only [if_true, show ¬ (uE = uE + 1) by omega, if_false, show ¬ (i1 + p + 1 = i1 + p) by omega]
      norm_num
    · by_cases hiO : i = i1 + p + 1
      · subst hiO
        have hr : r = 4 * (uE + 1) := by omega
        have hr4 : r / 2 ^ 2 = uE + 1 := by rw [hr]; omega
        rw [hr4]
        unfold gbar
        simp only [if_true, show ¬ (uE + 1 = uE) by omega, if_false, show ¬ (i1 + p = i1 + p + 1) by omega]
        norm_num
      · have hne1 : ¬ (i1 + p = i) := fun h => hiE h.symm
        have hne2 : ¬ (i1 + p + 1 = i) := fun h => hiO h.symm
        rw [if_neg hne1, if_neg hne2]
        have hr4a : r / 4 ≠ uE := by
          intro h
          have hr' : r = 4 * uE := by
            have hdv := (isRowN_dvd hr).1
            norm_num at hdv
            omega
          apply hiE
          exact stN_inj hg (by omega)
        have hr4b : r / 4 ≠ uE + 1 := by
          intro h
          have hr' : r = 4 * (uE + 1) := by
            have hdv := (isRowN_dvd hr).1
            norm_num at hdv
            omega
          apply hiO
          exact stN_inj hg (by omega)
        unfold gbar
        simp [hr4a, hr4b]
  · rw [if_neg hj2]
    have hjl : j < 2 := by omega
    have hne1 : ¬ (i1 + p = i) := by
      intro h; subst h
      rw [hlnE] at hli
      have : (2:ℕ) ^ j < 4 := by interval_cases j <;> norm_num
      omega
    have hne2 : ¬ (i1 + p + 1 = i) := by
      intro h; subst h
      rw [hlnO] at hli
      have : (2:ℕ) ^ j < 4 := by interval_cases j <;> norm_num
      omega
    rw [if_neg hne1, if_neg hne2]; ring

end

end AdalyFormal.NcwdhTwo
