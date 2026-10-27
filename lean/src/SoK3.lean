import SoE8
import SoK2
import SoG4
import NuK3

/-!
# SoK3 -- the trial vectors realise the Z-part of the competitor for general `ell`: `Q x_e = zrow (rhoY (gbar ell uE))` (lane sites_only_20261019)
-/
set_option autoImplicit false
set_option maxHeartbeats 16000000

namespace AdalyFormal.SitesOnly

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
open AdalyFormal.NcwdhTwo

section
variable [CfData]
variable {ell M R : ℕ}

theorem zrow_congr_nested2 (hg : NGeo ell M R) (hM : 0 < M) (ρ ρ' : ℕ → ℕ → ℝ)
    (h : ∀ j, j ≤ 2 → ∀ r, isRowN ell M R j r → ρ j r = ρ' j r) :
    zrow (geomOf ell 2 (neS ell M R)) ρ = zrow (geomOf ell 2 (neS ell M R)) ρ' := by
  refine PiLp.ext (fun p => ?_)
  show (if p.2.1.2 = 1 then dgS (ρ (p.1 : ℕ) (p.2.1.1 0).val) else 0) = (if p.2.1.2 = 1 then dgS (ρ' (p.1 : ℕ) (p.2.1.1 0).val) else 0)
  by_cases h1 : p.2.1.2 = 1
  · rw [if_pos h1, if_pos h1]
    congr 1
    have hj : (p.1 : ℕ) ≤ 2 := by have := p.1.2; simp [geomOf] at this ⊢; omega
    have hmem : (p.2.1.1, (1 : Fin 3)) ∈ bondsLam (geomOf ell 2 (neS ell M R)) (p.1 : ℕ) := by
      have := p.2.2
      have hq : ((p.2.1.1, (1 : Fin 3))) = p.2.1 := Prod.ext rfl h1.symm
      rw [hq]
      exact this
    exact h _ hj _ (((bondsLam_one_iff hg hM hj p.2.1.1).mp hmem).2)
  · rw [if_neg h1, if_neg h1]

/-- the sum of a single delta over a row. -/
theorem rowsum_single (hg : NGeo ell M R) {i i' : ℕ} (hi' : i' < RN hg) :
    ∑ y ∈ (univ.filter (fun y : Fin (nN ell M R) => rowOfN ell M R y.val = i)),
      (Pi.single (⟨stN ell M R i', by
        have := stN_strictMono hg hi'; rw [stN_RN hg] at this; exact this⟩ : Fin (nN ell M R)) (1 : ℝ) : Fin (nN ell M R) → ℝ) y =
      if i' = i then 1 else 0 := by
  classical
  rw [Finset.sum_pi_single']
  have hrow : rowOfN ell M R (stN ell M R i') = i' := by
    have hlt : stN ell M R i' < nN ell M R := by
      have := stN_strictMono hg hi'; rw [stN_RN hg] at this; exact this
    have := ((nested_rowGeom hg).row i' hi' (stN ell M R i') hlt).mpr ⟨le_rfl, by have := (nested_rowGeom hg).ln1 i' hi'; omega⟩
    exact this
  by_cases h : i' = i
  · subst h; simp [hrow]
  · simp [hrow, h]

variable {C : ℕ} (hCp : CPos ell M R C)
include hCp

/-- **the trial vectors realise the Z-part of the competitor.** -/
theorem Qx_pair (hell2 : 2 ≤ ell) (hE : 2 ∣ ell) (hdvd : ell ∣ M) (hM : 0 < M) (hR : 1 ≤ R) (t a : ℝ) (ht : |t| < Real.pi / 2) {i1 p uE : ℕ}
    (hp : i1 + p + 1 < RN (nGeo_two hell2 hdvd hM hR))
    (hlnE : lnN ell M R (i1 + p) = ell ^ 2) (hlnO : lnN ell M R (i1 + p + 1) = ell ^ 2)
    (hsE : neP0 ell M R + stN ell M R (i1 + p) = ell ^ 2 * uE) (hsO : neP0 ell M R + stN ell M R (i1 + p + 1) = ell ^ 2 * (uE + 1))
    {es : Fin (nN ell M R) → ℝ} (hes : es ∈ Vsub (rowOfN ell M R)) (τ : ℝ) :
    (Pt ell M R (by omega) C t a).data.Q
        (xE (nGeo_two hell2 hdvd hM hR) hell2 hM hR (f0pair (nGeo_two hell2 hdvd hM hR) i1 p hp + τ • es)) =
      zrow (geomOf ell 2 (neS ell M R)) (rhoY ell (gbar ell uE)) := by
  have hg := nGeo_two hell2 hdvd hM hR
  have hell : 0 < ell := by omega
  have S := nested_z0Setup_S hCp hell2 hE hdvd hM hR t ht
  have hQ : (Pt ell M R (by omega) C t a).data.Q
      (xE hg hell2 hM hR (f0pair hg i1 p hp + τ • es)) =
      QfullOf (geomOf ell 2 (neS ell M R)) (stag0Cfg (L := scaleUp ell 2 (neLu M R)) C t)
        (zfield (fe (neP0 ell M R) (f0pair hg i1 p hp + τ • es))) := rfl
  rw [hQ, Qfull_zfield_eq_zrow0 S]
  apply zrow_congr_nested2 hg hM
  intro j hj r hr
  obtain ⟨i, hiR, hir, hli⟩ := chain_row_of_isRowN hg hj hr
  have hsum := fSum_eq_rowsum hg hj hiR hir hli (f0pair hg i1 p hp + τ • es)
  rw [hsum]
  -- the row sum of the trial vector
  have hrs : ∑ x ∈ (univ.filter (fun x : Fin (nN ell M R) => rowOfN ell M R x.val = i)), (f0pair hg i1 p hp + τ • es) x =
      (if i1 + p = i then (1 : ℝ) else 0) - (if i1 + p + 1 = i then (1 : ℝ) else 0) := by
    have h1 := rowsum_single hg (i := i) (show i1 + p < RN hg by omega)
    have h2 := rowsum_single hg (i := i) hp
    have h3 : ∑ x ∈ (univ.filter (fun x : Fin (nN ell M R) => rowOfN ell M R x.val = i)), es x = 0 := hes i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_add_distrib, ← Finset.mul_sum, h3, mul_zero, add_zero]
    unfold f0pair
    simp only [Pi.sub_apply, Finset.sum_sub_distrib]
    rw [h1, h2]
  rw [hrs]
  unfold rhoY
  have hne : (ell : ℝ) ≠ 0 := by exact_mod_cast hell.ne'
  have hpos : 0 < ell ^ 2 := pow_pos hell 2
  by_cases hj2 : j = 2
  · subst hj2
    rw [if_pos rfl]
    by_cases hiE : i = i1 + p
    · subst hiE
      have hr : r = ell ^ 2 * uE := by omega
      have hr4 : r / ell ^ 2 = uE := by rw [hr]; exact Nat.mul_div_cancel_left uE hpos
      rw [hr4]
      unfold gbar
      simp only [if_true, show ¬ (uE = uE + 1) by omega, if_false, show ¬ (i1 + p + 1 = i1 + p) by omega]
      field_simp
      ring
    · by_cases hiO : i = i1 + p + 1
      · subst hiO
        have hr : r = ell ^ 2 * (uE + 1) := by omega
        have hr4 : r / ell ^ 2 = uE + 1 := by rw [hr]; exact Nat.mul_div_cancel_left (uE + 1) hpos
        rw [hr4]
        unfold gbar
        simp only [if_true, show ¬ (uE + 1 = uE) by omega, if_false, show ¬ (i1 + p = i1 + p + 1) by omega]
        field_simp
        ring
      · have hne1 : ¬ (i1 + p = i) := fun h => hiE h.symm
        have hne2 : ¬ (i1 + p + 1 = i) := fun h => hiO h.symm
        rw [if_neg hne1, if_neg hne2]
        have hdv := (isRowN_dvd hr).1
        obtain ⟨q, hq⟩ := hdv
        have hrq : r / ell ^ 2 = q := by rw [hq]; exact Nat.mul_div_cancel_left q hpos
        have hr4a : r / ell ^ 2 ≠ uE := by
          intro h
          have hr' : r = ell ^ 2 * uE := by rw [hq, ← h, hrq]
          apply hiE
          exact stN_inj hg (by omega)
        have hr4b : r / ell ^ 2 ≠ uE + 1 := by
          intro h
          have hr' : r = ell ^ 2 * (uE + 1) := by rw [hq, ← h, hrq]
          apply hiO
          exact stN_inj hg (by omega)
        unfold gbar
        simp [hr4a, hr4b]
  · rw [if_neg hj2]
    have hjl : j < 2 := by omega
    have hne1 : ¬ (i1 + p = i) := by
      intro h; subst h
      rw [hlnE] at hli
      have : ell ^ j < ell ^ 2 := Nat.pow_lt_pow_right (by omega) hjl
      omega
    have hne2 : ¬ (i1 + p + 1 = i) := by
      intro h; subst h
      rw [hlnO] at hli
      have : ell ^ j < ell ^ 2 := Nat.pow_lt_pow_right (by omega) hjl
      omega
    rw [if_neg hne1, if_neg hne2]; ring

end

#print axioms Qx_pair

end AdalyFormal.SitesOnly
