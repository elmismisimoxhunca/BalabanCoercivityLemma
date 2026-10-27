import NuPtZ3

/-!
# PtZ4 -- `Bq*` is injective at the flat nested point (lane omega/near2/point)
-/
set_option autoImplicit false
set_option maxHeartbeats 16000000
set_option linter.unusedSectionVars false

namespace AdalyFormal.CoverOmegaTwo
open AdalyFormal.CoverOmega


set_option linter.unusedSectionVars false
variable [CfData]
open scoped RealInnerProductSpace
open Finset
open AdalyFormal.Target.ClayStatement
open AdalyFormal.CoverNested
open AdalyFormal.StatementLane (scaleUp)
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Balaban.AdmissibleSubspace (Bond blockOf mem_blockOf CoarseLattice mem_CoarseLattice)
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.CoverOmega.Struct

variable {ell M R : ℕ}

theorem lev_le_row (ρ : RowIdx (geomOf ell 2 (neS ell M R))) : (ρ.1.1 : ℕ) ≤ 2 := by
  have := ρ.1.1.isLt
  have e : (geomOf ell 2 (neS ell M R)).k = 2 := rfl
  omega

theorem corner_zero (hP : PGeo ell M R) (hell : 0 < ell) (w : WQ (geomOf ell 2 (neS ell M R)))
    (hperp : ∀ u : SiteL2 (scaleUp ell 2 (neLu M R)),
      ⟪Bq (geomOf ell 2 (neS ell M R)) (flatCfg : Cfg (scaleUp ell 2 (neLu M R))) u, w⟫ = 0)
    (ρ : RowIdx (geomOf ell 2 (neS ell M R)))
    (hhigh : ∀ ρ' : RowIdx (geomOf ell 2 (neS ell M R)), (ρ.1.1 : ℕ) < (ρ'.1.1 : ℕ) → w ρ' = 0) : w ρ = 0 := by
  have hg : NGeo ell M R := AdalyFormal.NcwdhTwo.nGeo_two hP.hell hP.hdell hP.hM hP.hR
  obtain ⟨⟨jf, y⟩, hy⟩ := ρ
  let ρ0 : RowIdx (geomOf ell 2 (neS ell M R)) := ⟨(jf, y), hy⟩
  have hj : (jf : ℕ) ≤ 2 := lev_le_row ρ0
  obtain ⟨hyc, hfit⟩ := lam_crs_fit hP hj y hy
  have hcrs : Crs (ell ^ (jf : ℕ)) y := ((mem_Lam (jf : ℕ) y ∅).mp hy).1
  set v : SuTwo := w ρ0 with hv
  have h0 := hperp (dS y v)
  rw [PiLp.inner_apply] at h0
  have key : ∀ ρ' : RowIdx (geomOf ell 2 (neS ell M R)), ρ' ≠ ρ0 →
      ⟪(Bq (geomOf ell 2 (neS ell M R)) (flatCfg : Cfg (scaleUp ell 2 (neLu M R))) (dS y v)) ρ', w ρ'⟫ = 0 := by
    intro ρ' hne
    by_cases hlev : (jf : ℕ) < (ρ'.1.1 : ℕ)
    · rw [hhigh ρ' hlev, inner_zero_right]
    · have hle : (ρ'.1.1 : ℕ) ≤ (jf : ℕ) := by omega
      have hj' := lev_le_row ρ'
      obtain ⟨hyc', hfit'⟩ := lam_crs_fit hP hj' ρ'.1.2 ρ'.2
      have hcrs' : Crs (ell ^ (ρ'.1.1 : ℕ)) ρ'.1.2 := ((mem_Lam (ρ'.1.1 : ℕ) ρ'.1.2 ∅).mp ρ'.2).1
      rw [Bq_apply, Qlev_flat_cube _ hell _ _ hyc' hfit']
      have hzero : cube (fun a b c => (WithLp.ofLp (dS y v)) (mkS (scaleUp ell 2 (neLu M R)) a b c))
          ((geomOf ell 2 (neS ell M R)).ell ^ (ρ'.1.1 : ℕ)) (ρ'.1.2 0).val (ρ'.1.2 1).val (ρ'.1.2 2).val = 0 := by
        refine cube_zero_of _ _ _ _ _ (fun a b c ha hb hc => ?_)
        show (if mkS (scaleUp ell 2 (neLu M R)) ((ρ'.1.2 0).val + a) ((ρ'.1.2 1).val + b) ((ρ'.1.2 2).val + c) = y then v else 0) = 0
        rw [if_neg]
        intro heq
        apply hne
        have hf0 := hfit' 0; have hf1 := hfit' 1; have hf2 := hfit' 2
        have hN0 := hNLμ hP 0; have hN1 := hNLμ hP 1; have hN2 := hNLμ hP 2
        obtain ⟨e0, e1, e2⟩ := mkS_val_lt hP ((ρ'.1.2 0).val + a) ((ρ'.1.2 1).val + b) ((ρ'.1.2 2).val + c)
          (by show _ < _; omega) (by show _ < _; omega) (by show _ < _; omega)
        have h0' := congrArg (fun z => (z 0).val) heq
        have h1' := congrArg (fun z => (z 1).val) heq
        have h2' := congrArg (fun z => (z 2).val) heq
        rw [e0] at h0'; rw [e1] at h1'; rw [e2] at h2'
        have hpow : ell ^ (ρ'.1.1 : ℕ) ∣ ell ^ (jf : ℕ) := pow_dvd_pow ell hle
        have hn' : (geomOf ell 2 (neS ell M R)).ell ^ (ρ'.1.1 : ℕ) = ell ^ (ρ'.1.1 : ℕ) := rfl
        rw [hn'] at ha hb hc
        have q0 : (ρ'.1.2 0).val = (y 0).val := eq_of_window (hcrs' 0) (dvd_trans hpow (hcrs 0)) (by omega) (by omega)
        have q1 : (ρ'.1.2 1).val = (y 1).val := eq_of_window (hcrs' 1) (dvd_trans hpow (hcrs 1)) (by omega) (by omega)
        have q2 : (ρ'.1.2 2).val = (y 2).val := eq_of_window (hcrs' 2) (dvd_trans hpow (hcrs 2)) (by omega) (by omega)
        have hsite : ρ'.1.2 = y := site_ext q0 q1 q2
        -- levels
        have hlam' := ρ'.2
        rw [hsite] at hlam'
        have hjj : (ρ'.1.1 : ℕ) = (jf : ℕ) := by
          by_contra hneq
          have hlt : (ρ'.1.1 : ℕ) < (jf : ℕ) := by omega
          obtain ⟨-, hO1, hN1'⟩ := (mem_Lam (ρ'.1.1 : ℕ) y ∅).mp hlam'
          obtain ⟨-, hO2, -⟩ := (mem_Lam (jf : ℕ) y ∅).mp hy
          have c1 := hP.hpa; have c2 := hP.hab; have c3 := hP.hba; have c4 := hP.hab2; have c5 := hP.hbq
          have hell2 : 1 ≤ ell ^ 2 := Nat.one_le_pow _ _ hell
          rcases (show (jf : ℕ) = 1 ∨ (jf : ℕ) = 2 by omega) with h1 | h1 <;>
            rcases (show (ρ'.1.1 : ℕ) = 0 ∨ (ρ'.1.1 : ℕ) = 1 by omega) with h2 | h2 <;>
            first
            | omega
            | (rw [h1] at hO2; rw [h2] at hN1'; simp only [Omv, reg2] at hO2 hN1'; omega)
        have hfin : ρ'.1.1 = jf := Fin.ext hjj
        apply Subtype.ext
        apply Prod.ext
        · exact hfin
        · exact hsite
      rw [hzero, smul_zero, inner_zero_left]
  rw [Finset.sum_eq_single ρ0
    (fun ρ' _ hne => key ρ' hne) (fun h => absurd (Finset.mem_univ _) h)] at h0
  have hself : (Bq (geomOf ell 2 (neS ell M R)) (flatCfg : Cfg (scaleUp ell 2 (neLu M R))) (dS y v)) ρ0
      = (1 / (((ell ^ (jf : ℕ) : ℕ)) : ℝ) ^ 3) • v := by
    rw [Bq_apply, Qlev_flat_cube _ hell _ _ hyc hfit]
    congr 1
    have := cube_dS_self hP y (ell ^ (jf : ℕ)) (pow_pos hell _) (fun μ => by
      have := hfit μ
      have h' := hNLμ hP μ
      show _ ≤ _
      have : (y μ).val + ell ^ (jf : ℕ) ≤ scaleUp ell 2 (neLu M R) μ + 1 := hfit μ
      omega) v
    exact this
  rw [hself, real_inner_smul_left, real_inner_self_eq_norm_sq] at h0
  have hK : 0 < (1 / (((ell ^ (jf : ℕ) : ℕ)) : ℝ) ^ 3) := by
    have : (0 : ℝ) < ((ell ^ (jf : ℕ) : ℕ) : ℝ) := by exact_mod_cast pow_pos hell _
    positivity
  have hn : ‖v‖ ^ 2 = 0 := by
    rcases mul_eq_zero.mp h0 with h | h
    · exact absurd h hK.ne'
    · exact h
  exact norm_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp hn)

end AdalyFormal.CoverOmegaTwo
