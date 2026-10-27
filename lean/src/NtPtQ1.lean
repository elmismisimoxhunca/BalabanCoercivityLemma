import NtPtI1

/-!
# PtQ1 -- necessary conditions for direction-0 rows of the nested tower (lane omega/near2/point)
-/
set_option autoImplicit false
set_option maxHeartbeats 16000000
set_option linter.unusedSectionVars false

namespace AdalyFormal.CoverOmega


set_option linter.unusedSectionVars false
variable [CfData]
open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.CoverNested
open AdalyFormal.StatementLane (scaleUp)
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Balaban.CoarseCurl (coarseShift coarseShift_apply_ne coarseShift_val_eq)

variable {ell M R : ℕ}

theorem dir0_row_lvl0 (hP : PGeo ell M R) (y : PeriodicLatticeSite (scaleUp ell 2 (neLu M R)))
    (h : (y, (0 : Fin 3)) ∈ bondsLam (geomOf ell 2 (neS ell M R)) 0) :
    (neP0 ell M R ≤ (y 0).val + 1 ∧ (y 0).val + 2 ≤ neP1 ell M R) ∨
      (neQ1 ell M R ≤ (y 0).val ∧ (y 0).val + 1 ≤ neQ0 ell M R) := by
  have hg : NGeo ell M R := nGeo hP.hell hP.hdell hP.hM hP.hR
  have hell : 0 < ell := by have := hP.hell; omega
  have hM := hP.hM
  have hG : (geomOf ell 2 (neS ell M R)).ell = ell := rfl
  have hy0 : (y 0).val < neN ell M R := lt_of_lt_of_eq (y 0).isLt (hNLμ hP 0)
  have hqN := hP.hqN
  have hcp := hP.collar_p; have hcq := hP.collar_q; have hrm := hP.rm2
  have hell2 : 1 ≤ ell ^ 2 := Nat.one_le_pow _ _ hell
  have c1 := hP.hpa; have c2 := hP.hab; have c3 := hP.hba; have c4 := hP.hab2; have c5 := hP.hbq; have c6 := hP.hq1q0
  have hp0 := hP.p0pos
  unfold bondsLam at h
  simp only [Set.mem_setOf_eq, hG, pow_zero] at h
  rw [coarseShift_one'] at h
  rw [mem_Lam 0 y ∅, mem_Lam 0 _ ∅, omGe_iff _ y hell hM, omGe_iff _ _ hell hM, omGe0_1 hg, omGe0_1 hg] at h
  by_cases hw : (y 0).val + 1 < neN ell M R
  · rw [sh_x0 hP y hw] at h
    simp only [Omv] at h
    omega
  · have hw' : (y 0).val + 1 = neN ell M R := by omega
    have hz : ((periodicLatticeShift y 0) 0).val = 0 := by
      rw [shift_x0]; simp only [if_true]
      have : ((y 0).val + 1) % (scaleUp ell 2 (neLu M R) 0 + 1) = 0 := by
        rw [show (y 0).val + 1 = scaleUp ell 2 (neLu M R) 0 + 1 from hw'.trans (hNL hP).symm]
        exact Nat.mod_self _
      exact this
    rw [hz] at h
    simp only [Omv] at h
    omega


theorem cs_wrap (hP : PGeo ell M R) (n : ℕ) (hn : n ≤ neN ell M R) (y : PeriodicLatticeSite (scaleUp ell 2 (neLu M R)))
    (h : neN ell M R ≤ (y 0).val + n) : ((coarseShift y n 0) 0).val = (y 0).val + n - neN ell M R := by
  rw [coarseShift_val_eq]
  have hN := hNL hP
  have hge : scaleUp ell 2 (neLu M R) 0 + 1 ≤ (y 0).val + n := by omega
  rw [Nat.mod_eq_sub_mod hge]
  exact Nat.mod_eq_of_lt (by have := (y 0).isLt; omega) |>.trans (by omega)

theorem dir0_row_lvl1 (hP : PGeo ell M R) (y : PeriodicLatticeSite (scaleUp ell 2 (neLu M R)))
    (h : (y, (0 : Fin 3)) ∈ bondsLam (geomOf ell 2 (neS ell M R)) 1) :
    Crs ell y ∧
    ((neP1 ell M R ≤ (y 0).val + ell ∧ (y 0).val + 2 * ell ≤ neA' ell M R) ∨
     (neB' ell M R ≤ (y 0).val ∧ (y 0).val + 2 * ell ≤ neA ell M R) ∨
     (neB ell M R ≤ (y 0).val ∧ (y 0).val + ell ≤ neQ1 ell M R)) := by
  have hg : NGeo ell M R := nGeo hP.hell hP.hdell hP.hM hP.hR
  have hell : 0 < ell := by have := hP.hell; omega
  have hM := hP.hM
  have hG : (geomOf ell 2 (neS ell M R)).ell = ell := rfl
  have hy0 : (y 0).val < neN ell M R := lt_of_lt_of_eq (y 0).isLt (hNLμ hP 0)
  have hqN := hP.hqN
  have hell2 : 1 ≤ ell ^ 2 := Nat.one_le_pow _ _ hell
  have hl2 : ell ≤ ell ^ 2 := by nlinarith [pow_two ell]
  have c1 := hP.hpa; have c2 := hP.hab; have c3 := hP.hba; have c4 := hP.hab2; have c5 := hP.hbq; have c6 := hP.hq1q0
  have hcp := hP.collar_p; have hcq := hP.collar_q; have hrm := hP.rm2; have hp := hP.hp
  have hdiv := dvd_scaleUp (R := R) hell hM
  have hz1 : Crs ell (coarseShift y ell 0) ↔ Crs ell y :=
    crs_coarseShift_iff (fun μ => by simpa using hdiv μ (j := 1) (by norm_num)) y 0 ell dvd_rfl
  unfold bondsLam at h
  simp only [Set.mem_setOf_eq, hG, pow_one] at h
  rw [mem_Lam 1 y ∅, mem_Lam 1 _ ∅, omGe_iff _ y hell hM, omGe_iff _ _ hell hM, omGe0_2 hg, omGe0_2 hg] at h
  simp only [pow_one] at h
  have hlN : ell ≤ neN ell M R := by omega
  have hwrap : (y 0).val + ell < neN ell M R := by
    by_contra hnot
    have hz := cs_wrap hP ell hlN y (by omega)
    rw [hz] at h
    simp only [Omv, reg2] at h
    omega
  rw [cs_x0 hP ell y hwrap] at h
  simp only [Omv, reg2] at h
  have hcy : Crs ell y := by
    rcases h.1 with ⟨hc, _⟩ | ⟨hc, _⟩
    · exact hc
    · exact hz1.mp hc
  refine ⟨hcy, ?_⟩
  have hv := hcy 0
  have hv2 : ell ∣ (y 0).val + ell := dvd_add hv dvd_rfl
  have dp1 := hP.d1p
  have dq1 := hP.d1q
  have da' : ell ∣ neA' ell M R := dvd_trans (dvd_pow_self ell (by norm_num)) hP.d2a'
  have db' : ell ∣ neB' ell M R := dvd_trans (dvd_pow_self ell (by norm_num)) hP.d2b'
  have da : ell ∣ neA ell M R := dvd_trans (dvd_pow_self ell (by norm_num)) hP.d2a
  have db : ell ∣ neB ell M R := dvd_trans (dvd_pow_self ell (by norm_num)) hP.d2b
  have A1 := fun hl => step_le hv dp1 hl
  have A2 := fun hl => step_le hv da' hl
  have A3 := fun hl => step_le hv db' hl
  have A4 := fun hl => step_le hv da hl
  have A5 := fun hl => step_le hv db hl
  have A6 := fun hl => step_le hv dq1 hl
  have B1 := fun hl => step_le hv2 dp1 hl
  have B2 := fun hl => step_le hv2 da' hl
  have B3 := fun hl => step_le hv2 db' hl
  have B4 := fun hl => step_le hv2 da hl
  have B5 := fun hl => step_le hv2 db hl
  have B6 := fun hl => step_le hv2 dq1 hl
  omega


theorem dir0_row_lvl2 (hP : PGeo ell M R) (y : PeriodicLatticeSite (scaleUp ell 2 (neLu M R)))
    (h : (y, (0 : Fin 3)) ∈ bondsLam (geomOf ell 2 (neS ell M R)) 2) :
    Crs (ell ^ 2) y ∧
    ((neA' ell M R ≤ (y 0).val + ell ^ 2 ∧ (y 0).val + ell ^ 2 ≤ neB' ell M R) ∨
     (neA ell M R ≤ (y 0).val + ell ^ 2 ∧ (y 0).val + ell ^ 2 ≤ neB ell M R)) := by
  have hg : NGeo ell M R := nGeo hP.hell hP.hdell hP.hM hP.hR
  have hell : 0 < ell := by have := hP.hell; omega
  have hM := hP.hM
  have hG : (geomOf ell 2 (neS ell M R)).ell = ell := rfl
  have hy0 : (y 0).val < neN ell M R := lt_of_lt_of_eq (y 0).isLt (hNLμ hP 0)
  have hqN := hP.hqN
  have hell2 : 1 ≤ ell ^ 2 := Nat.one_le_pow _ _ hell
  have c1 := hP.hpa; have c2 := hP.hab; have c3 := hP.hba; have c4 := hP.hab2; have c5 := hP.hbq; have c6 := hP.hq1q0
  have hcp := hP.collar_p; have hcq := hP.collar_q; have hrm := hP.rm2; have hp := hP.hp
  have hdiv := dvd_scaleUp (R := R) hell hM
  have hz1 : Crs (ell ^ 2) (coarseShift y (ell ^ 2) 0) ↔ Crs (ell ^ 2) y :=
    crs_coarseShift_iff (fun μ => hdiv μ (j := 2) le_rfl) y 0 (ell ^ 2) dvd_rfl
  unfold bondsLam at h
  simp only [Set.mem_setOf_eq, hG] at h
  rw [mem_Lam 2 y ∅, mem_Lam 2 _ ∅] at h
  have hlN : ell ^ 2 ≤ neN ell M R := by omega
  have hwrap : (y 0).val + ell ^ 2 < neN ell M R := by
    by_contra hnot
    have hz := cs_wrap hP (ell ^ 2) hlN y (by omega)
    rw [hz] at h
    simp only [Omv, reg2] at h
    omega
  rw [cs_x0 hP (ell ^ 2) y hwrap] at h
  simp only [Omv, reg2] at h
  have hcy : Crs (ell ^ 2) y := by
    rcases h.1 with ⟨hc, _⟩ | ⟨hc, _⟩
    · exact hc
    · exact hz1.mp hc
  refine ⟨hcy, ?_⟩
  have hv := hcy 0
  have da' := hP.d2a'
  have db' := hP.d2b'
  have da := hP.d2a
  have db := hP.d2b
  have A2 := fun hl => step_le hv db' hl
  have A4 := fun hl => step_le hv db hl
  rcases h.1 with ⟨-, h1, -⟩ | ⟨-, h1, -⟩
  · omega
  · omega

end AdalyFormal.CoverOmega
