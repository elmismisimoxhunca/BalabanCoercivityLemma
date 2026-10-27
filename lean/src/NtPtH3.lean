import NtPtH2

/-!
# PtH3 -- the cube-sum row relations of a kernel field (lane omega/near2/point)
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
open AdalyFormal.Balaban.LineIntegralCovariant (lineCoarseRestrictSuTwo)

variable {ell M R : ℕ}

theorem hNLμ (hP : PGeo ell M R) (μ : Fin 3) : scaleUp ell 2 (neLu M R) μ + 1 = neN ell M R :=
  ne_scaleUp (by have := hP.hell; omega) hP.hM μ

theorem mkS_val_lt (hP : PGeo ell M R) (a b c : ℕ) (ha : a < neN ell M R) (hb : b < neN ell M R) (hc : c < neN ell M R) :
    ((mkS (scaleUp ell 2 (neLu M R)) a b c) 0).val = a ∧ ((mkS (scaleUp ell 2 (neLu M R)) a b c) 1).val = b ∧
      ((mkS (scaleUp ell 2 (neLu M R)) a b c) 2).val = c := by
  refine ⟨?_, ?_, ?_⟩
  · rw [mkS_val0]; exact Nat.mod_eq_of_lt (lt_of_lt_of_eq ha (hNLμ hP 0).symm)
  · rw [mkS_val1]; exact Nat.mod_eq_of_lt (lt_of_lt_of_eq hb (hNLμ hP 1).symm)
  · rw [mkS_val2]; exact Nat.mod_eq_of_lt (lt_of_lt_of_eq hc (hNLμ hP 2).symm)

theorem mkS_crs (hP : PGeo ell M R) (n : ℕ) (a b c : ℕ) (ha : a < neN ell M R) (hb : b < neN ell M R) (hc : c < neN ell M R)
    (da : n ∣ a) (db : n ∣ b) (dc : n ∣ c) :
    mkS (scaleUp ell 2 (neLu M R)) a b c ∈ CoarseLattice (scaleUp ell 2 (neLu M R)) n := by
  obtain ⟨e0, e1, e2⟩ := mkS_val_lt hP a b c ha hb hc
  rw [mem_CoarseLattice]
  intro μ
  fin_cases μ
  · simp only [Fin.zero_eta]; rw [e0]; exact Nat.mod_eq_zero_of_dvd da
  · simp only [Fin.mk_one]; rw [e1]; exact Nat.mod_eq_zero_of_dvd db
  · simp only [Fin.reduceFinMk]; rw [e2]; exact Nat.mod_eq_zero_of_dvd dc

/-- the cube relation of a row in direction `0`. -/
theorem row_cube0 (hP : PGeo ell M R) {x : BondFnL2 (scaleUp ell 2 (neLu M R))} (hk : KD ell M R x)
    (g : ℕ → ℕ → ℕ → SuTwo)
    (rel0 : ∀ a b d, x (mkS (scaleUp ell 2 (neLu M R)) a b d, 0) = g (a + 1) b d - g a b d)
    {j : ℕ} (hj : j ≤ 2) (Y0 Y1 Y2 : ℕ)
    (h0 : Y0 + ell ^ j ≤ neN ell M R) (h1 : Y1 + ell ^ j ≤ neN ell M R) (h2 : Y2 + ell ^ j ≤ neN ell M R)
    (d0 : ell ^ j ∣ Y0) (d1 : ell ^ j ∣ Y1) (d2 : ell ^ j ∣ Y2)
    (hmem : (mkS (scaleUp ell 2 (neLu M R)) Y0 Y1 Y2, (0 : Fin 3)) ∈ bondsLam (geomOf ell 2 (neS ell M R)) j) :
    cube g (ell ^ j) (Y0 + ell ^ j) Y1 Y2 = cube g (ell ^ j) Y0 Y1 Y2 := by
  have hell : 0 < ell := by have := hP.hell; omega
  have hpos : 0 < ell ^ j := pow_pos hell j
  have hY0 : Y0 < neN ell M R := by omega
  have hY1 : Y1 < neN ell M R := by omega
  have hY2 : Y2 < neN ell M R := by omega
  have hcl := mkS_crs hP (ell ^ j) Y0 Y1 Y2 hY0 hY1 hY2 d0 d1 d2
  obtain ⟨e0, e1, e2⟩ := mkS_val_lt hP Y0 Y1 Y2 hY0 hY1 hY2
  have hdvdJ : ∀ ν, (geomOf ell 2 (neS ell M R)).ell ^ 2 ∣ scaleUp ell 2 (neLu M R) ν + 1 := fun ν => dvd_scaleUp (R := R) hell hP.hM ν le_rfl
  let p : BIdx (geomOf ell 2 (neS ell M R)) := ⟨⟨j, by show j < 2 + 1; omega⟩, ⟨(mkS (scaleUp ell 2 (neLu M R)) Y0 Y1 Y2, (0 : Fin 3)), hmem⟩⟩
  have hrow := Qfull_flat_row (geomOf ell 2 (neS ell M R)) hell 2 hdvdJ p hj hcl x
  have hz : (QfullOf (geomOf ell 2 (neS ell M R)) (flatCfg : Cfg (scaleUp ell 2 (neLu M R))) x) p = 0 := by
    rw [hk.hQ]; rfl
  rw [hz] at hrow
  have hfit : ∀ μ, ((mkS (scaleUp ell 2 (neLu M R)) Y0 Y1 Y2) μ).val + ell ^ j ≤ scaleUp ell 2 (neLu M R) μ + 1 := by
    intro μ
    fin_cases μ
    · simp only [Fin.zero_eta]; exact le_of_le_of_eq (by rw [e0]; exact h0) (hNLμ hP _).symm
    · simp only [Fin.mk_one]; exact le_of_le_of_eq (by rw [e1]; exact h1) (hNLμ hP _).symm
    · simp only [Fin.reduceFinMk]; exact le_of_le_of_eq (by rw [e2]; exact h2) (hNLμ hP _).symm
  have hlcr := lcr_dir0 (WithLp.ofLp x) g (mkS (scaleUp ell 2 (neLu M R)) Y0 Y1 Y2) (ell ^ j) hfit hcl
    (fun a b c _ _ _ _ _ _ => rel0 a b c)
  rw [e0, e1, e2] at hlcr
  have hrow' : lineCoarseRestrictSuTwo (ell ^ j) (WithLp.ofLp x) ⟨⟨mkS (scaleUp ell 2 (neLu M R)) Y0 Y1 Y2, hcl⟩, 0⟩ = 0 :=
    hrow.symm
  rw [hlcr] at hrow'
  have hn : ((1 : ℝ) / ((ell ^ j : ℕ) : ℝ) ^ 4) ≠ 0 := by positivity
  have := (smul_eq_zero.mp hrow').resolve_left hn
  exact sub_eq_zero.mp this


/-- the cube relation of a row in direction `1`. -/
theorem row_cube1 (hP : PGeo ell M R) {x : BondFnL2 (scaleUp ell 2 (neLu M R))} (hk : KD ell M R x)
    (g : ℕ → ℕ → ℕ → SuTwo)
    (rel1 : ∀ a b d, x (mkS (scaleUp ell 2 (neLu M R)) a b d, 1) = g a (b + 1) d - g a b d)
    {j : ℕ} (hj : j ≤ 2) (Y0 Y1 Y2 : ℕ)
    (h0 : Y0 + ell ^ j ≤ neN ell M R) (h1 : Y1 + ell ^ j ≤ neN ell M R) (h2 : Y2 + ell ^ j ≤ neN ell M R)
    (d0 : ell ^ j ∣ Y0) (d1 : ell ^ j ∣ Y1) (d2 : ell ^ j ∣ Y2)
    (hmem : (mkS (scaleUp ell 2 (neLu M R)) Y0 Y1 Y2, (1 : Fin 3)) ∈ bondsLam (geomOf ell 2 (neS ell M R)) j) :
    cube g (ell ^ j) Y0 (Y1 + ell ^ j) Y2 = cube g (ell ^ j) Y0 Y1 Y2 := by
  have hell : 0 < ell := by have := hP.hell; omega
  have hpos : 0 < ell ^ j := pow_pos hell j
  have hY0 : Y0 < neN ell M R := by omega
  have hY1 : Y1 < neN ell M R := by omega
  have hY2 : Y2 < neN ell M R := by omega
  have hcl := mkS_crs hP (ell ^ j) Y0 Y1 Y2 hY0 hY1 hY2 d0 d1 d2
  obtain ⟨e0, e1, e2⟩ := mkS_val_lt hP Y0 Y1 Y2 hY0 hY1 hY2
  have hdvdJ : ∀ ν, (geomOf ell 2 (neS ell M R)).ell ^ 2 ∣ scaleUp ell 2 (neLu M R) ν + 1 := fun ν => dvd_scaleUp (R := R) hell hP.hM ν le_rfl
  let p : BIdx (geomOf ell 2 (neS ell M R)) := ⟨⟨j, by show j < 2 + 1; omega⟩, ⟨(mkS (scaleUp ell 2 (neLu M R)) Y0 Y1 Y2, (1 : Fin 3)), hmem⟩⟩
  have hrow := Qfull_flat_row (geomOf ell 2 (neS ell M R)) hell 2 hdvdJ p hj hcl x
  have hz : (QfullOf (geomOf ell 2 (neS ell M R)) (flatCfg : Cfg (scaleUp ell 2 (neLu M R))) x) p = 0 := by
    rw [hk.hQ]; rfl
  rw [hz] at hrow
  have hfit : ∀ μ, ((mkS (scaleUp ell 2 (neLu M R)) Y0 Y1 Y2) μ).val + ell ^ j ≤ scaleUp ell 2 (neLu M R) μ + 1 := by
    intro μ
    fin_cases μ
    · simp only [Fin.zero_eta]; exact le_of_le_of_eq (by rw [e0]; exact h0) (hNLμ hP _).symm
    · simp only [Fin.mk_one]; exact le_of_le_of_eq (by rw [e1]; exact h1) (hNLμ hP _).symm
    · simp only [Fin.reduceFinMk]; exact le_of_le_of_eq (by rw [e2]; exact h2) (hNLμ hP _).symm
  have hlcr := lcr_dir1 (WithLp.ofLp x) g (mkS (scaleUp ell 2 (neLu M R)) Y0 Y1 Y2) (ell ^ j) hfit hcl
    (fun a b c _ _ _ _ _ _ => rel1 a b c)
  rw [e0, e1, e2] at hlcr
  have hrow' : lineCoarseRestrictSuTwo (ell ^ j) (WithLp.ofLp x) ⟨⟨mkS (scaleUp ell 2 (neLu M R)) Y0 Y1 Y2, hcl⟩, 1⟩ = 0 :=
    hrow.symm
  rw [hlcr] at hrow'
  have hn : ((1 : ℝ) / ((ell ^ j : ℕ) : ℝ) ^ 4) ≠ 0 := by positivity
  have := (smul_eq_zero.mp hrow').resolve_left hn
  exact sub_eq_zero.mp this


/-- the cube relation of a row in direction `2`. -/
theorem row_cube2 (hP : PGeo ell M R) {x : BondFnL2 (scaleUp ell 2 (neLu M R))} (hk : KD ell M R x)
    (g : ℕ → ℕ → ℕ → SuTwo)
    (rel2 : ∀ a b d, x (mkS (scaleUp ell 2 (neLu M R)) a b d, 2) = g a b (d + 1) - g a b d)
    {j : ℕ} (hj : j ≤ 2) (Y0 Y1 Y2 : ℕ)
    (h0 : Y0 + ell ^ j ≤ neN ell M R) (h1 : Y1 + ell ^ j ≤ neN ell M R) (h2 : Y2 + ell ^ j ≤ neN ell M R)
    (d0 : ell ^ j ∣ Y0) (d1 : ell ^ j ∣ Y1) (d2 : ell ^ j ∣ Y2)
    (hmem : (mkS (scaleUp ell 2 (neLu M R)) Y0 Y1 Y2, (2 : Fin 3)) ∈ bondsLam (geomOf ell 2 (neS ell M R)) j) :
    cube g (ell ^ j) Y0 Y1 (Y2 + ell ^ j) = cube g (ell ^ j) Y0 Y1 Y2 := by
  have hell : 0 < ell := by have := hP.hell; omega
  have hpos : 0 < ell ^ j := pow_pos hell j
  have hY0 : Y0 < neN ell M R := by omega
  have hY1 : Y1 < neN ell M R := by omega
  have hY2 : Y2 < neN ell M R := by omega
  have hcl := mkS_crs hP (ell ^ j) Y0 Y1 Y2 hY0 hY1 hY2 d0 d1 d2
  obtain ⟨e0, e1, e2⟩ := mkS_val_lt hP Y0 Y1 Y2 hY0 hY1 hY2
  have hdvdJ : ∀ ν, (geomOf ell 2 (neS ell M R)).ell ^ 2 ∣ scaleUp ell 2 (neLu M R) ν + 1 := fun ν => dvd_scaleUp (R := R) hell hP.hM ν le_rfl
  let p : BIdx (geomOf ell 2 (neS ell M R)) := ⟨⟨j, by show j < 2 + 1; omega⟩, ⟨(mkS (scaleUp ell 2 (neLu M R)) Y0 Y1 Y2, (2 : Fin 3)), hmem⟩⟩
  have hrow := Qfull_flat_row (geomOf ell 2 (neS ell M R)) hell 2 hdvdJ p hj hcl x
  have hz : (QfullOf (geomOf ell 2 (neS ell M R)) (flatCfg : Cfg (scaleUp ell 2 (neLu M R))) x) p = 0 := by
    rw [hk.hQ]; rfl
  rw [hz] at hrow
  have hfit : ∀ μ, ((mkS (scaleUp ell 2 (neLu M R)) Y0 Y1 Y2) μ).val + ell ^ j ≤ scaleUp ell 2 (neLu M R) μ + 1 := by
    intro μ
    fin_cases μ
    · simp only [Fin.zero_eta]; exact le_of_le_of_eq (by rw [e0]; exact h0) (hNLμ hP _).symm
    · simp only [Fin.mk_one]; exact le_of_le_of_eq (by rw [e1]; exact h1) (hNLμ hP _).symm
    · simp only [Fin.reduceFinMk]; exact le_of_le_of_eq (by rw [e2]; exact h2) (hNLμ hP _).symm
  have hlcr := lcr_dir2 (WithLp.ofLp x) g (mkS (scaleUp ell 2 (neLu M R)) Y0 Y1 Y2) (ell ^ j) hfit hcl
    (fun a b c _ _ _ _ _ _ => rel2 a b c)
  rw [e0, e1, e2] at hlcr
  have hrow' : lineCoarseRestrictSuTwo (ell ^ j) (WithLp.ofLp x) ⟨⟨mkS (scaleUp ell 2 (neLu M R)) Y0 Y1 Y2, hcl⟩, 2⟩ = 0 :=
    hrow.symm
  rw [hlcr] at hrow'
  have hn : ((1 : ℝ) / ((ell ^ j : ℕ) : ℝ) ^ 4) ≠ 0 := by positivity
  have := (smul_eq_zero.mp hrow').resolve_left hn
  exact sub_eq_zero.mp this


end AdalyFormal.CoverOmega
