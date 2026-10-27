import NtPtQ2

/-!
# PtQ3 -- the peak bond of a row is covered only by rows of at least its level, and by no other row of the same level (lane omega/near2/point)
-/
set_option autoImplicit false
set_option maxHeartbeats 16000000
set_option linter.unusedSectionVars false

namespace AdalyFormal.CoverOmega


set_option linter.unusedSectionVars false
variable [CfData]
open scoped RealInnerProductSpace
open Finset
open AdalyFormal.Target.ClayStatement
open AdalyFormal.CoverNested
open AdalyFormal.StatementLane (scaleUp)
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Balaban.AdmissibleSubspace (Bond blockOf mem_blockOf CoarseLattice)
open AdalyFormal.Balaban.QOne (pathSite)

variable {ell M R : ℕ}

/-- the necessary x₀-condition of a direction-0 row of level `j` starting at slice `v`. -/
def Rw0 (ell M R : ℕ) : ℕ → ℕ → Prop
  | 0, v => (neP0 ell M R ≤ v + 1 ∧ v + 2 ≤ neP1 ell M R) ∨ (neQ1 ell M R ≤ v ∧ v + 1 ≤ neQ0 ell M R)
  | 1, v => (neP1 ell M R ≤ v + ell ∧ v + 2 * ell ≤ neA' ell M R) ∨ (neB' ell M R ≤ v ∧ v + 2 * ell ≤ neA ell M R) ∨
      (neB ell M R ≤ v ∧ v + ell ≤ neQ1 ell M R)
  | 2, v => (neA' ell M R ≤ v + ell ^ 2 ∧ v + ell ^ 2 ≤ neB' ell M R) ∨ (neA ell M R ≤ v + ell ^ 2 ∧ v + ell ^ 2 ≤ neB ell M R)
  | _, _ => False

theorem row0_cond (hP : PGeo ell M R) {j : ℕ} (hj : j ≤ 2) (Y : PeriodicLatticeSite (scaleUp ell 2 (neLu M R)))
    (hb : (Y, (0 : Fin 3)) ∈ bondsLam (geomOf ell 2 (neS ell M R)) j) :
    Rw0 ell M R j (Y 0).val := by
  rcases (show j = 0 ∨ j = 1 ∨ j = 2 by omega) with rfl | rfl | rfl
  · exact dir0_row_lvl0 hP Y hb
  · exact (dir0_row_lvl1 hP Y hb).2
  · exact (dir0_row_lvl2 hP Y hb).2

theorem rw0_bound (hP : PGeo ell M R) {j : ℕ} (hj : j ≤ 2) {v : ℕ} (h : Rw0 ell M R j v) :
    v + 2 * ell ^ j ≤ neN ell M R := by
  have hell : 0 < ell := by have := hP.hell; omega
  have hell2 : 1 ≤ ell ^ 2 := Nat.one_le_pow _ _ hell
  have hl2 : ell ≤ ell ^ 2 := by nlinarith [pow_two ell]
  have c1 := hP.hpa; have c2 := hP.hab; have c3 := hP.hba; have c4 := hP.hab2; have c5 := hP.hbq; have c6 := hP.hq1q0
  have hqN := hP.hqN
  rcases (show j = 0 ∨ j = 1 ∨ j = 2 by omega) with rfl | rfl | rfl
  · simp only [Rw0, pow_zero] at h ⊢; omega
  · simp only [Rw0, pow_one] at h ⊢; omega
  · simp only [Rw0] at h; omega

theorem eq_of_window {n a b : ℕ} (ha : n ∣ a) (hb : n ∣ b) (h1 : a ≤ b) (h2 : b < a + n) : a = b := by
  by_contra hne
  have := step_le ha hb (lt_of_le_of_ne h1 hne)
  omega


theorem site_ext {L : PeriodicLatticeExtent} {A B : PeriodicLatticeSite L} (h0 : (A 0).val = (B 0).val)
    (h1 : (A 1).val = (B 1).val) (h2 : (A 2).val = (B 2).val) : A = B := by
  funext ν
  apply Fin.ext
  fin_cases ν
  · exact h0
  · exact h1
  · exact h2

theorem nc_dir0 (hP : PGeo ell M R) {j j' : ℕ} (hj : j ≤ 2) (hj' : j' ≤ 2) (hjj : j' ≤ j)
    (Y Y' : PeriodicLatticeSite (scaleUp ell 2 (neLu M R)))
    (hb : (Y, (0 : Fin 3)) ∈ bondsLam (geomOf ell 2 (neS ell M R)) j)
    (hb' : (Y', (0 : Fin 3)) ∈ bondsLam (geomOf ell 2 (neS ell M R)) j')
    (hit : 0 < hits Y' 0 (ell ^ j') (pathSite Y 0 (ell ^ j - 1), 0)) : j' = j ∧ Y' = Y := by
  have hg : NGeo ell M R := nGeo hP.hell hP.hdell hP.hM hP.hR
  have hell : 0 < ell := by have := hP.hell; omega
  obtain ⟨-, y, hy, i, hi, hne, hmod⟩ := hit_extract Y' 0 0 (ell ^ j) (ell ^ j') Y hit
  have hRw := row0_cond hP hj Y hb
  have hRw' := row0_cond hP hj' Y' hb'
  have hcrs : Crs (ell ^ j) Y := crs_of_bondsLam hg hP.hM hj (Y, 0) hb
  have hcrs' : Crs (ell ^ j') Y' := crs_of_bondsLam hg hP.hM hj' (Y', 0) hb'
  have hB := rw0_bound hP hj hRw
  have hB' := rw0_bound hP hj' hRw'
  have hpos : 0 < ell ^ j := pow_pos hell j
  have hpos' : 0 < ell ^ j' := pow_pos hell j'
  have hpowle : ell ^ j' ≤ ell ^ j := Nat.pow_le_pow_right hell hjj
  have hy0 := hy 0
  have hlt1 : (y 0).val + i < neN ell M R := by omega
  have hlt2 : (Y 0).val + (ell ^ j - 1) < neN ell M R := by omega
  rw [Nat.mod_eq_of_lt (lt_of_lt_of_eq hlt1 (hNL hP).symm), Nat.mod_eq_of_lt (lt_of_lt_of_eq hlt2 (hNL hP).symm)] at hmod
  rcases Nat.lt_or_ge j' j with hlt | hge
  · -- lower level: contradiction
    exfalso
    have c1 := hP.hpa; have c2 := hP.hab; have c3 := hP.hba; have c4 := hP.hab2; have c5 := hP.hbq; have c6 := hP.hq1q0
    have hcp := hP.collar_p; have hcq := hP.collar_q; have hrm := hP.rm2; have hp := hP.hp
    have hell2 : 1 ≤ ell ^ 2 := Nat.one_le_pow _ _ hell
    have hl2 : ell ≤ ell ^ 2 := by nlinarith [pow_two ell]
    rcases (show j = 1 ∨ j = 2 by omega) with rfl | rfl <;> rcases (show j' = 0 ∨ j' = 1 by omega) with rfl | rfl <;>
      first
      | (exfalso; omega)
      | (simp only [Rw0, pow_zero, pow_one] at hRw hRw' hmod hy0 hi; omega)
      | (simp only [Rw0, pow_zero, pow_one, pow_two] at hRw hRw' hmod hy0 hi; omega)
  · have hjeq : j' = j := le_antisymm hjj hge
    subst hjeq
    refine ⟨rfl, ?_⟩
    have hh1 : (Y' 0).val ≤ (Y 0).val := by
      by_contra hc
      push_neg at hc
      have := step_le (hcrs 0) (hcrs' 0) hc
      omega
    have hh2 : (Y 0).val < (Y' 0).val + ell ^ j' := by omega
    have e0 : (Y' 0).val = (Y 0).val := eq_of_window (hcrs' 0) (hcrs 0) hh1 hh2
    have e1 : (Y' 1).val = (Y 1).val := by
      have w := hy 1
      have := hne 1 (by decide)
      exact eq_of_window (hcrs' 1) (hcrs 1) (by omega) (by omega)
    have e2 : (Y' 2).val = (Y 2).val := by
      have w := hy 2
      have := hne 2 (by decide)
      exact eq_of_window (hcrs' 2) (hcrs 2) (by omega) (by omega)
    exact site_ext e0 e1 e2


theorem nc_trans (hP : PGeo ell M R) {j j' : ℕ} (hj : j ≤ 2) (hj' : j' ≤ 2) (hjj : j' ≤ j)
    (Y Y' : PeriodicLatticeSite (scaleUp ell 2 (neLu M R))) (μ : Fin 3) (hμ : μ ≠ 0)
    (hb : (Y, μ) ∈ bondsLam (geomOf ell 2 (neS ell M R)) j)
    (hb' : (Y', μ) ∈ bondsLam (geomOf ell 2 (neS ell M R)) j')
    (hit : 0 < hits Y' μ (ell ^ j') (pathSite Y μ (ell ^ j - 1), μ)) : j' = j ∧ Y' = Y := by
  have hell : 0 < ell := by have := hP.hell; omega
  obtain ⟨hcrs, hrow⟩ := (bondsLam_trans_iff hP hj μ hμ Y).mp hb
  obtain ⟨hcrs', hrow'⟩ := (bondsLam_trans_iff hP hj' μ hμ Y').mp hb'
  obtain ⟨-, y, hy, i, hi, hne, hmod⟩ := hit_extract Y' μ μ (ell ^ j) (ell ^ j') Y hit
  have hpos : 0 < ell ^ j := pow_pos hell j
  have hpos' : 0 < ell ^ j' := pow_pos hell j'
  have hdN : ∀ k, k ≤ 2 → ell ^ k ∣ neN ell M R := fun k hk => dvd_trans (pow_dvd_pow ell hk) hP.hNd
  have hy0 := hy 0
  have hne0 : (y 0).val = (Y 0).val := hne 0 (Ne.symm hμ)
  rcases Nat.lt_or_ge j' j with hlt | hge
  · exfalso
    have c1 := hP.hpa; have c2 := hP.hab; have c3 := hP.hba; have c4 := hP.hab2; have c5 := hP.hbq; have c6 := hP.hq1q0
    have hcp := hP.collar_p; have hcq := hP.collar_q; have hrm := hP.rm2; have hp := hP.hp
    rcases (show j = 1 ∨ j = 2 by omega) with rfl | rfl <;> rcases (show j' = 0 ∨ j' = 1 by omega) with rfl | rfl <;>
      first
      | (exfalso; omega)
      | (simp only [isRowN, reg0, reg1, reg2, pow_zero, pow_one] at hrow hrow' hy0 hne0; omega)
      | (have hY0 : (Y 0).val = (Y' 0).val := by
           simp only [isRowN, pow_one] at hrow hrow' hy0 hne0
           have h1 := hcrs 0
           have h2 : ell ∣ (Y 0).val := dvd_trans (dvd_pow_self ell (by norm_num)) h1
           exact (eq_of_window hrow'.1 h2 (by omega) (by omega)).symm
         simp only [isRowN, reg0, reg1, reg2, pow_one] at hrow hrow'
         omega)
  · have hjeq : j' = j := le_antisymm hjj hge
    subst hjeq
    refine ⟨rfl, ?_⟩
    have hother : ∀ ν, ν ≠ μ → (Y' ν).val = (Y ν).val := by
      intro ν hν
      have w := hy ν
      have e := hne ν hν
      exact eq_of_window (hcrs' ν) (hcrs ν) (by omega) (by omega)
    have hμeq : (Y' μ).val = (Y μ).val := by
      have hYμ : (Y μ).val < neN ell M R := lt_of_lt_of_eq (Y μ).isLt (hNLμ hP μ)
      have hY'μ : (Y' μ).val < neN ell M R := lt_of_lt_of_eq (Y' μ).isLt (hNLμ hP μ)
      have f1 := step_le (hcrs μ) (hdN j' hj') hYμ
      have f2 := step_le (hcrs' μ) (hdN j' hj') hY'μ
      have w := hy μ
      have hnle : ell ^ j' ≤ neN ell M R := by omega
      rw [← hNLμ hP μ] at f1 f2 hnle
      have hmod' := hmod
      rw [Nat.mod_eq_of_lt (show (Y μ).val + (ell ^ j' - 1) < scaleUp ell 2 (neLu M R) μ + 1 by omega)] at hmod'
      by_cases hwr : (y μ).val + i < scaleUp ell 2 (neLu M R) μ + 1
      · rw [Nat.mod_eq_of_lt hwr] at hmod'
        have h1 : (Y' μ).val ≤ (Y μ).val := by
          by_contra hc
          push_neg at hc
          have := step_le (hcrs μ) (hcrs' μ) hc
          omega
        exact eq_of_window (hcrs' μ) (hcrs μ) h1 (by omega)
      · exfalso
        have hge' : scaleUp ell 2 (neLu M R) μ + 1 ≤ (y μ).val + i := by omega
        rw [Nat.mod_eq_sub_mod hge', Nat.mod_eq_of_lt (by omega)] at hmod'
        omega
    refine site_ext ?_ ?_ ?_
    · exact hother 0 (Ne.symm hμ)
    · by_cases h1 : (1 : Fin 3) = μ
      · subst h1; exact hμeq
      · exact hother 1 h1
    · by_cases h2 : (2 : Fin 3) = μ
      · subst h2; exact hμeq
      · exact hother 2 h2

end AdalyFormal.CoverOmega
