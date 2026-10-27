import NtPtH4

/-!
# PtH5 -- the chain applied to a kernel field (lane omega/near2/point)
-/
set_option autoImplicit false
set_option maxHeartbeats 8000000
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
open AdalyFormal.Balaban.AdmissibleSubspace (Bond CoarseLattice mem_CoarseLattice)
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)

variable {ell M R : ℕ}

theorem cube_sub_const {E : Type*} [AddCommGroup E] [Module ℝ E] (g : ℕ → ℕ → ℕ → E) (v : E) (n a b c : ℕ) :
    cube (fun a b c => g a b c - v) n a b c = cube g n a b c - ((n : ℝ) ^ 3) • v := by
  unfold cube
  simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range]
  simp only [← Nat.cast_smul_eq_nsmul ℝ, smul_smul]
  congr 2; ring

theorem crs_mkS (hP : PGeo ell M R) (n a b d : ℕ) (ha : a < neN ell M R) (hb : b < neN ell M R) (hd : d < neN ell M R)
    (da : n ∣ a) (db : n ∣ b) (dd : n ∣ d) : Crs n (mkS (scaleUp ell 2 (neLu M R)) a b d) := by
  obtain ⟨e0, e1, e2⟩ := mkS_val_lt hP a b d ha hb hd
  intro μ
  fin_cases μ
  · simp only [Fin.zero_eta]; rw [e0]; exact da
  · simp only [Fin.mk_one]; rw [e1]; exact db
  · simp only [Fin.reduceFinMk]; rw [e2]; exact dd

theorem dvd_N1 (hP : PGeo ell M R) : ell ∣ neN ell M R :=
  dvd_trans (dvd_pow_self ell (by norm_num)) hP.hNd

section chainapp
variable {x : BondFnL2 (scaleUp ell 2 (neLu M R))} {g : ℕ → ℕ → ℕ → SuTwo}

theorem chain_apply (hP : PGeo ell M R) (hk : KD ell M R x) (hpd : PD ell M R x g) :
    (g (neQ1 ell M R) 0 0 - g 0 0 0 = 0) ∧
    (∀ Y0 Y1 Y2, ell ∣ Y0 → ell ∣ Y1 → ell ∣ Y2 → Y1 < neN ell M R → Y2 < neN ell M R →
      ((neP1 ell M R ≤ Y0 ∧ Y0 < neA' ell M R) ∨ (neB' ell M R ≤ Y0 ∧ Y0 < neA ell M R) ∨
        (neB ell M R ≤ Y0 ∧ Y0 < neQ1 ell M R)) →
      cube (fun a b d => g a b d - g 0 0 0) ell Y0 Y1 Y2 = 0) ∧
    (∀ Y0 Y1 Y2, ell ^ 2 ∣ Y0 → ell ^ 2 ∣ Y1 → ell ^ 2 ∣ Y2 → Y1 < neN ell M R → Y2 < neN ell M R →
      ((neA' ell M R ≤ Y0 ∧ Y0 < neB' ell M R) ∨ (neA ell M R ≤ Y0 ∧ Y0 < neB ell M R)) →
      cube (fun a b d => g a b d - g 0 0 0) (ell ^ 2) Y0 Y1 Y2 = 0) := by
  have hell : 0 < ell := by have := hP.hell; omega
  have hLc := left_const hP hk hpd
  have hRc := right_const hP hk hpd
  have hN := hP.hqN
  have hq := hP.hq1q0
  have hell2 : 1 ≤ ell ^ 2 := Nat.one_le_pow _ _ hell
  have hl2 : ell ≤ ell ^ 2 := by nlinarith [pow_two ell]
  have hrmq : neQ1 ell M R + ell ≤ neQ0 ell M R := by have := hP.collar_q; have := hP.rm_ell; omega
  have c1 := hP.hpa; have c2 := hP.hab; have c3 := hP.hba; have c4 := hP.hab2; have c5 := hP.hbq
  have hdN := dvd_N1 hP
  -- row relations for g
  have R1 : ∀ Y0 Y1 Y2, ell ∣ Y0 → ell ∣ Y1 → ell ∣ Y2 → Y1 < neN ell M R → Y2 < neN ell M R →
      ((neP1 ell M R ≤ Y0 + ell ∧ Y0 + 2 * ell ≤ neA' ell M R) ∨ (neB' ell M R ≤ Y0 ∧ Y0 + 2 * ell ≤ neA ell M R) ∨
        (neB ell M R ≤ Y0 ∧ Y0 + ell ≤ neQ1 ell M R)) →
      cube g ell (Y0 + ell) Y1 Y2 = cube g ell Y0 Y1 Y2 := by
    intro Y0 Y1 Y2 d0 d1 d2 hY1 hY2 hcl
    have hY0 : Y0 < neN ell M R := by omega
    have hc := crs_mkS hP ell Y0 Y1 Y2 hY0 hY1 hY2 d0 d1 d2
    have hmem := bondsLam_dir0_lvl1 hP (mkS (scaleUp ell 2 (neLu M R)) Y0 Y1 Y2) hc (by
      rw [x0val hP Y0 Y1 Y2 hY0]; exact hcl)
    have := row_cube0 hP hk g hpd.rel0 (j := 1) (by norm_num) Y0 Y1 Y2 (by rw [pow_one]; omega)
      (by rw [pow_one]; exact (step_le d1 hdN hY1)) (by rw [pow_one]; exact (step_le d2 hdN hY2))
      (by rw [pow_one]; exact d0) (by rw [pow_one]; exact d1) (by rw [pow_one]; exact d2) hmem
    simpa [pow_one] using this
  have R1y : ∀ Y0 Y1 Y2, ell ∣ Y0 → ell ∣ Y1 → ell ∣ Y2 → Y1 + ell < neN ell M R → Y2 < neN ell M R →
      neB' ell M R ≤ Y0 → Y0 + ell ≤ neA ell M R → cube g ell Y0 (Y1 + ell) Y2 = cube g ell Y0 Y1 Y2 := by
    intro Y0 Y1 Y2 d0 d1 d2 hY1 hY2 hb hl
    have hY0 : Y0 < neN ell M R := by omega
    have hY1' : Y1 < neN ell M R := by omega
    have hc := crs_mkS hP ell Y0 Y1 Y2 hY0 hY1' hY2 d0 d1 d2
    have hmem : (mkS (scaleUp ell 2 (neLu M R)) Y0 Y1 Y2, (1 : Fin 3)) ∈ bondsLam (geomOf ell 2 (neS ell M R)) 1 := by
      refine (bondsLam_trans_iff hP (j := 1) (by norm_num) 1 (by decide) _).mpr ⟨by simpa [pow_one] using hc, ?_⟩
      rw [x0val hP Y0 Y1 Y2 hY0]
      simp only [isRowN, reg1, reg2]
      refine ⟨d0, ⟨by omega, by omega⟩, by omega⟩
    have := row_cube1 hP hk g hpd.rel1 (j := 1) (by norm_num) Y0 Y1 Y2 (by rw [pow_one]; omega)
      (by rw [pow_one]; omega) (by rw [pow_one]; exact (step_le d2 hdN hY2))
      (by rw [pow_one]; exact d0) (by rw [pow_one]; exact d1) (by rw [pow_one]; exact d2) hmem
    simpa [pow_one] using this
  have R1z : ∀ Y0 Y1 Y2, ell ∣ Y0 → ell ∣ Y1 → ell ∣ Y2 → Y1 < neN ell M R → Y2 + ell < neN ell M R →
      neB' ell M R ≤ Y0 → Y0 + ell ≤ neA ell M R → cube g ell Y0 Y1 (Y2 + ell) = cube g ell Y0 Y1 Y2 := by
    intro Y0 Y1 Y2 d0 d1 d2 hY1 hY2 hb hl
    have hY0 : Y0 < neN ell M R := by omega
    have hY2' : Y2 < neN ell M R := by omega
    have hc := crs_mkS hP ell Y0 Y1 Y2 hY0 hY1 hY2' d0 d1 d2
    have hmem : (mkS (scaleUp ell 2 (neLu M R)) Y0 Y1 Y2, (2 : Fin 3)) ∈ bondsLam (geomOf ell 2 (neS ell M R)) 1 := by
      refine (bondsLam_trans_iff hP (j := 1) (by norm_num) 2 (by decide) _).mpr ⟨by simpa [pow_one] using hc, ?_⟩
      rw [x0val hP Y0 Y1 Y2 hY0]
      simp only [isRowN, reg1, reg2]
      refine ⟨d0, ⟨by omega, by omega⟩, by omega⟩
    have := row_cube2 hP hk g hpd.rel2 (j := 1) (by norm_num) Y0 Y1 Y2 (by rw [pow_one]; omega)
      (by rw [pow_one]; exact (step_le d1 hdN hY1)) (by rw [pow_one]; omega)
      (by rw [pow_one]; exact d0) (by rw [pow_one]; exact d1) (by rw [pow_one]; exact d2) hmem
    simpa [pow_one] using this
  have R2 : ∀ Y0 Y1 Y2, ell ^ 2 ∣ Y0 → ell ^ 2 ∣ Y1 → ell ^ 2 ∣ Y2 → Y1 < neN ell M R → Y2 < neN ell M R →
      ((neA' ell M R ≤ Y0 + ell ^ 2 ∧ Y0 + ell ^ 2 ≤ neB' ell M R) ∨ (neA ell M R ≤ Y0 + ell ^ 2 ∧ Y0 + ell ^ 2 ≤ neB ell M R)) →
      cube g (ell ^ 2) (Y0 + ell ^ 2) Y1 Y2 = cube g (ell ^ 2) Y0 Y1 Y2 := by
    intro Y0 Y1 Y2 d0 d1 d2 hY1 hY2 hcl
    have hY0 : Y0 < neN ell M R := by omega
    have hc := crs_mkS hP (ell ^ 2) Y0 Y1 Y2 hY0 hY1 hY2 d0 d1 d2
    have hmem := bondsLam_dir0_lvl2 hP (mkS (scaleUp ell 2 (neLu M R)) Y0 Y1 Y2) hc (by
      rw [x0val hP Y0 Y1 Y2 hY0]; exact hcl)
    exact row_cube0 hP hk g hpd.rel0 (j := 2) (by norm_num) Y0 Y1 Y2 (by omega)
      (step_le d1 hP.hNd hY1) (step_le d2 hP.hNd hY2) d0 d1 d2 hmem
  have hmain := chain_main ell (neP1 ell M R) (neA' ell M R) (neB' ell M R) (neA ell M R) (neB ell M R) (neQ1 ell M R)
    (neN ell M R) hell hP.hNd hP.d1p hP.d1q hP.d2a' hP.d2b' hP.d2a hP.d2b hP.hNpos hP.hp hP.hpa hP.hab hP.hba hP.hab2 hP.hbq
    (fun a b d => g a b d - g 0 0 0) (g (neQ1 ell M R) 0 0 - g 0 0 0)
    (fun a ha b d => by simp only [hLc a ha b d, sub_self])
    (fun a ha1 ha2 b d => by simp only [hRc a ha1 (by omega) b d])
    (fun Y0 Y1 Y2 d0 d1 d2 hY1 hY2 hcl => by
      rw [cube_sub_const, cube_sub_const, R1 Y0 Y1 Y2 d0 d1 d2 hY1 hY2 hcl])
    (fun Y0 Y1 Y2 d0 d1 d2 hY1 hY2 hb hl => by
      rw [cube_sub_const, cube_sub_const, R1y Y0 Y1 Y2 d0 d1 d2 hY1 hY2 hb hl])
    (fun Y0 Y1 Y2 d0 d1 d2 hY1 hY2 hb hl => by
      rw [cube_sub_const, cube_sub_const, R1z Y0 Y1 Y2 d0 d1 d2 hY1 hY2 hb hl])
    (fun Y0 Y1 Y2 d0 d1 d2 hY1 hY2 hcl => by
      rw [cube_sub_const, cube_sub_const, R2 Y0 Y1 Y2 d0 d1 d2 hY1 hY2 hcl])
  exact hmain

end chainapp

end AdalyFormal.CoverOmega
