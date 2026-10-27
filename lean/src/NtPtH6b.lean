import NtPtH6a

/-!
# PtH6b -- the kernel of the flat nested `Ginv` is trivial: `x = D ξ` with `ξ ∈ N(Q')` (lane omega/near2/point)
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
open AdalyFormal.Balaban.AdmissibleSubspace (Bond blockOf CoarseLattice mem_CoarseLattice)
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)

variable {ell M R : ℕ}

/-- the site function of a corrected potential, normalised by its value at the origin. -/
noncomputable def xiOf (ell M R : ℕ) (g : ℕ → ℕ → ℕ → SuTwo) : SiteL2 (scaleUp ell 2 (neLu M R)) :=
  WithLp.toLp 2 (fun u => g (u 0).val (u 1).val (u 2).val - g 0 0 0)

theorem xiOf_mk (hP : PGeo ell M R) {g : ℕ → ℕ → ℕ → SuTwo} {x : BondFnL2 (scaleUp ell 2 (neLu M R))}
    (hpd : PD ell M R x g) (a b d : ℕ) :
    (WithLp.ofLp (xiOf ell M R g)) (mkS (scaleUp ell 2 (neLu M R)) a b d) = g (a % neN ell M R) b d - g 0 0 0 := by
  show g ((mkS (scaleUp ell 2 (neLu M R)) a b d) 0).val ((mkS (scaleUp ell 2 (neLu M R)) a b d) 1).val
      ((mkS (scaleUp ell 2 (neLu M R)) a b d) 2).val - g 0 0 0 = _
  rw [mkS_val0, mkS_val1, mkS_val2, hNLμ hP 0, hNLμ hP 1, hNLμ hP 2, hpd.mod1, hpd.mod2]


section main
variable {x : BondFnL2 (scaleUp ell 2 (neLu M R))} {g : ℕ → ℕ → ℕ → SuTwo}

/-- facts on the constants: all of `g` outside the slab and on its collars equals `g 0 0 0`. -/
theorem left_zero (hP : PGeo ell M R) (hk : KD ell M R x) (hpd : PD ell M R x g) :
    ∀ a, a < neP1 ell M R → ∀ b d, g a b d - g 0 0 0 = 0 := by
  intro a ha b d
  rw [left_const hP hk hpd a ha b d, sub_self]

theorem right_zero (hP : PGeo ell M R) (hk : KD ell M R x) (hpd : PD ell M R x g)
    (hκ : g (neQ1 ell M R) 0 0 - g 0 0 0 = 0) :
    ∀ a, neQ1 ell M R ≤ a → a < neN ell M R → ∀ b d, g a b d - g 0 0 0 = 0 := by
  intro a ha1 ha2 b d
  rw [right_const hP hk hpd a ha1 ha2 b d]
  exact hκ

theorem xi_grad (hP : PGeo ell M R) (hk : KD ell M R x) (hpd : PD ell M R x g)
    (hκ : g (neQ1 ell M R) 0 0 - g 0 0 0 = 0) :
    x = gradL2 (flatCfg : Cfg (scaleUp ell 2 (neLu M R))) (xiOf ell M R g) := by
  have hg : NGeo ell M R := nGeo hP.hell hP.hdell hP.hM hP.hR
  have hLz := left_zero hP hk hpd
  have hRz := right_zero hP hk hpd hκ
  have hq := hP.hq1q0
  have hell2 : 1 ≤ ell ^ 2 := Nat.one_le_pow _ _ (by have := hP.hell; omega)
  have hqN := hP.hqN
  have hp1 : 1 ≤ neP1 ell M R := by have := hP.p0pos; have := hP.collar_p; have := hP.rm2; omega
  refine PiLp.ext (fun b => ?_)
  obtain ⟨u, μ⟩ := b
  have hex : ∃ a b' d, u = mkS (scaleUp ell 2 (neLu M R)) a b' d ∧ a < neN ell M R :=
    ⟨(u 0).val, (u 1).val, (u 2).val, (mkS_eta u).symm, lt_of_lt_of_eq (u 0).isLt (hNLμ hP 0)⟩
  obtain ⟨a, b', d, rfl, ha⟩ := hex
  show x (mkS (scaleUp ell 2 (neLu M R)) a b' d, μ) = _
  rw [AdalyFormal.GenuineU1H.gradL2_flat_apply]
  show _ = (WithLp.ofLp (xiOf ell M R g)) (periodicLatticeShift (mkS (scaleUp ell 2 (neLu M R)) a b' d) μ)
      - (WithLp.ofLp (xiOf ell M R g)) (mkS (scaleUp ell 2 (neLu M R)) a b' d)
  fin_cases μ
  · simp only [Fin.zero_eta]
    rw [shift_mkS0, xiOf_mk hP hpd, xiOf_mk hP hpd, Nat.mod_eq_of_lt ha]
    by_cases hw : a + 1 < neN ell M R
    · rw [Nat.mod_eq_of_lt hw, hpd.rel0]; abel
    · have haN : a + 1 = neN ell M R := by omega
      have hz : (a + 1) % neN ell M R = 0 := by rw [haN]; exact Nat.mod_self _
      rw [hz]
      have e1 : g 0 b' d - g 0 0 0 = 0 := hLz 0 (by omega) b' d
      have e2 : g a b' d - g 0 0 0 = 0 := hRz a (by omega) ha b' d
      have e3 : x (mkS (scaleUp ell 2 (neLu M R)) a b' d, 0) = 0 := by
        refine hk.zero_off1 hg hP.hM _ ?_ ?_
        · show ¬ Omv ell M R 1 ((mkS (scaleUp ell 2 (neLu M R)) a b' d) 0).val
          rw [x0val hP a b' d ha]; simp only [Omv]; omega
        · show ¬ Omv ell M R 1 ((periodicLatticeShift (mkS (scaleUp ell 2 (neLu M R)) a b' d) 0) 0).val
          rw [shift_mkS0, mkS_val0, hNLμ hP 0, hz]; simp only [Omv]; omega
      rw [e3, e1, e2]; simp
  · simp only [Fin.mk_one]
    rw [shift_mkS1, xiOf_mk hP hpd, xiOf_mk hP hpd, Nat.mod_eq_of_lt ha, hpd.rel1 a b' d]
    abel
  · simp only [Fin.reduceFinMk]
    rw [shift_mkS2, xiOf_mk hP hpd, xiOf_mk hP hpd, Nat.mod_eq_of_lt ha, hpd.rel2 a b' d]
    abel

theorem xi_nqp (hP : PGeo ell M R) (hk : KD ell M R x) (hpd : PD ell M R x g) :
    xiOf ell M R g ∈ NQp (geomOf ell 2 (neS ell M R)) (flatCfg : Cfg (scaleUp ell 2 (neLu M R))) := by
  have hell : 0 < ell := by have := hP.hell; omega
  obtain ⟨hκ, hl1, hl2⟩ := chain_apply hP hk hpd
  have hLz := left_zero hP hk hpd
  have hRz := right_zero hP hk hpd hκ
  have hq := hP.hq1q0
  have hqN := hP.hqN
  have hell2 : 1 ≤ ell ^ 2 := Nat.one_le_pow _ _ hell
  have hl2' : ell ≤ ell ^ 2 := by nlinarith [pow_two ell]
  have c1 := hP.hpa; have c2 := hP.hab; have c3 := hP.hba; have c4 := hP.hab2; have c5 := hP.hbq
  have hcp := hP.collar_p
  have hcq := hP.collar_q
  have hrm := hP.rm2
  have hdN : ∀ j, j ≤ 2 → ell ^ j ∣ neN ell M R := fun j hj =>
    dvd_trans (pow_dvd_pow ell hj) hP.hNd
  refine ⟨?_, ?_⟩
  · intro u hu
    have hu' : ¬ Omv ell M R 0 (u 0).val := fun h => hu ((Omv_site 0 u).mpr h)
    have hlt : (u 0).val < neN ell M R := lt_of_lt_of_eq (u 0).isLt (hNLμ hP 0)
    show g (u 0).val (u 1).val (u 2).val - g 0 0 0 = 0
    simp only [Omv] at hu'
    by_cases h : (u 0).val < neP0 ell M R
    · exact hLz _ (by omega) _ _
    · exact hRz _ (by omega) hlt _ _
  · intro j hj y hy
    have hj2 : j ≤ 2 := hj
    obtain ⟨hc, hO, hN⟩ := (mem_Lam j y ∅).mp hy
    have hyc : y ∈ CoarseLattice (scaleUp ell 2 (neLu M R)) ((geomOf ell 2 (neS ell M R)).ell ^ j) := by
      rw [mem_CoarseLattice]; intro μ; exact Nat.mod_eq_zero_of_dvd (hc μ)
    have hfit : ∀ μ, (y μ).val + (geomOf ell 2 (neS ell M R)).ell ^ j ≤ scaleUp ell 2 (neLu M R) μ + 1 := by
      intro μ
      have := step_le (hc μ) (hdN j hj2) (lt_of_lt_of_eq (y μ).isLt (hNLμ hP μ))
      exact le_of_le_of_eq this (hNLμ hP μ).symm
    rw [Qlev_flat_cube (geomOf ell 2 (neS ell M R)) hell j y hyc hfit]
    have hcube : cube (fun a b c => (WithLp.ofLp (xiOf ell M R g)) (mkS (scaleUp ell 2 (neLu M R)) a b c))
        ((geomOf ell 2 (neS ell M R)).ell ^ j) (y 0).val (y 1).val (y 2).val
        = cube (fun a b d => g a b d - g 0 0 0) (ell ^ j) (y 0).val (y 1).val (y 2).val := by
      refine cube_congr _ _ _ _ _ _ (fun i j' k hi hj' hk => ?_)
      have hi' : i < ell ^ j := hi
      have h0' : (y 0).val + ell ^ j ≤ neN ell M R := le_of_le_of_eq (hfit 0) (hNLμ hP 0)
      have hlt : (y 0).val + i < neN ell M R := by omega
      rw [xiOf_mk hP hpd, Nat.mod_eq_of_lt hlt]
    rw [hcube]
    have hy0 : (y 0).val < neN ell M R := lt_of_lt_of_eq (y 0).isLt (hNLμ hP 0)
    have hy1 : (y 1).val < neN ell M R := lt_of_lt_of_eq (y 1).isLt (hNLμ hP 1)
    have hy2 : (y 2).val < neN ell M R := lt_of_lt_of_eq (y 2).isLt (hNLμ hP 2)
    have key : cube (fun a b d => g a b d - g 0 0 0) (ell ^ j) (y 0).val (y 1).val (y 2).val = 0 := by
      rcases (show j = 0 ∨ j = 1 ∨ j = 2 by omega) with rfl | rfl | rfl
      · simp only [pow_zero, cube_one]
        simp only [Omv] at hO hN
        by_cases h : (y 0).val < neP1 ell M R
        · exact hLz _ h _ _
        · exact hRz _ (by omega) hy0 _ _
      · simp only [pow_one]
        simp only [pow_one] at hc
        simp only [Omv, reg2] at hO hN
        exact hl1 (y 0).val (y 1).val (y 2).val (hc 0) (hc 1) (hc 2) hy1 hy2 (by omega)
      · simp only [Omv, reg2] at hO hN
        exact hl2 (y 0).val (y 1).val (y 2).val (hc 0) (hc 1) (hc 2) hy1 hy2 (by omega)
    rw [key, smul_zero]

end main

end AdalyFormal.CoverOmega
