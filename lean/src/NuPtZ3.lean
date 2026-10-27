import NuPtZ2

/-!
# PtZ3 -- `Bq*` is injective and `Bq (mask u) = Bq u` at the flat nested point (lane omega/near2/point)
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

theorem lam_crs_fit (hP : PGeo ell M R) {j : ℕ} (hj : j ≤ 2) (y : PeriodicLatticeSite (scaleUp ell 2 (neLu M R)))
    (hy : y ∈ (geomOf ell 2 (neS ell M R)).Lam j) :
    y ∈ CoarseLattice (scaleUp ell 2 (neLu M R)) ((geomOf ell 2 (neS ell M R)).ell ^ j) ∧
    ∀ μ, (y μ).val + (geomOf ell 2 (neS ell M R)).ell ^ j ≤ scaleUp ell 2 (neLu M R) μ + 1 := by
  have hell : 0 < ell := by have := hP.hell; omega
  obtain ⟨hc, hO, hN⟩ := (mem_Lam j y ∅).mp hy
  have hdN : ell ^ j ∣ neN ell M R := dvd_trans (pow_dvd_pow ell hj) hP.hNd
  refine ⟨?_, ?_⟩
  · rw [mem_CoarseLattice]; intro μ; exact Nat.mod_eq_zero_of_dvd (hc μ)
  · intro μ
    have := step_le (hc μ) hdN (lt_of_lt_of_eq (y μ).isLt (hNLμ hP μ))
    exact le_of_le_of_eq this (hNLμ hP μ).symm

theorem Bq_mask (hP : PGeo ell M R) (hell : 0 < ell) (u : SiteL2 (scaleUp ell 2 (neLu M R))) :
    Bq (geomOf ell 2 (neS ell M R)) (flatCfg : Cfg (scaleUp ell 2 (neLu M R)))
        (siteMask (geomOf ell 2 (neS ell M R)).Om0 u)
      = Bq (geomOf ell 2 (neS ell M R)) (flatCfg : Cfg (scaleUp ell 2 (neLu M R))) u := by
  refine PiLp.ext (fun ρ => ?_)
  rw [Bq_apply, Bq_apply]
  have hj : (ρ.1.1 : ℕ) ≤ 2 := by
    have := ρ.1.1.isLt
    have e : (geomOf ell 2 (neS ell M R)).k = 2 := rfl
    omega
  obtain ⟨hyc, hfit⟩ := lam_crs_fit hP hj ρ.1.2 ρ.2
  rw [Qlev_flat_cube _ hell _ _ hyc hfit, Qlev_flat_cube _ hell _ _ hyc hfit]
  congr 1
  refine cube_congr _ _ _ _ _ _ (fun i j' k hi hj' hk => ?_)
  have hmem : mkS (scaleUp ell 2 (neLu M R)) ((ρ.1.2 0).val + i) ((ρ.1.2 1).val + j') ((ρ.1.2 2).val + k)
      ∈ blockOf ρ.1.2 ((geomOf ell 2 (neS ell M R)).ell ^ (ρ.1.1 : ℕ)) :=
    mkS_mem_block ρ.1.2 _ hfit i j' k hi hj' hk
  have hOm := block_Om0 hP hj ρ.1.2 ρ.2 _ hmem
  rw [siteMask_apply, if_pos hOm]


/-- the site field supported at one site. -/
noncomputable def dS {L : PeriodicLatticeExtent} (y : PeriodicLatticeSite L) (v : SuTwo) : SiteL2 L :=
  WithLp.toLp 2 (fun x => if x = y then v else 0)

theorem coord_lt (hP : PGeo ell M R) (y : PeriodicLatticeSite (scaleUp ell 2 (neLu M R))) (μ : Fin 3) :
    (y μ).val < neN ell M R := lt_of_lt_of_eq (y μ).isLt (hNLμ hP μ)

/-- the value of the cube sum of the delta at the corner of a block. -/
theorem cube_dS_self (hP : PGeo ell M R) (y : PeriodicLatticeSite (scaleUp ell 2 (neLu M R))) (n : ℕ) (hn : 0 < n)
    (hfit : ∀ μ, (y μ).val + n ≤ neN ell M R) (v : SuTwo) :
    cube (fun a b c => (WithLp.ofLp (dS y v)) (mkS (scaleUp ell 2 (neLu M R)) a b c)) n (y 0).val (y 1).val (y 2).val = v := by
  unfold cube
  have key : ∀ a b c : ℕ, a < n → b < n → c < n →
      (WithLp.ofLp (dS y v)) (mkS (scaleUp ell 2 (neLu M R)) ((y 0).val + a) ((y 1).val + b) ((y 2).val + c))
        = if a = 0 ∧ b = 0 ∧ c = 0 then v else 0 := by
    intro a b c ha hb hc
    show (if mkS (scaleUp ell 2 (neLu M R)) ((y 0).val + a) ((y 1).val + b) ((y 2).val + c) = y then v else 0) = _
    have e0 := x0val hP ((y 0).val + a) ((y 1).val + b) ((y 2).val + c) (by have := hfit 0; omega)
    have e1 := (mkS_val_lt hP ((y 0).val + a) ((y 1).val + b) ((y 2).val + c) (by have := hfit 0; omega)
      (by have := hfit 1; omega) (by have := hfit 2; omega))
    by_cases h : a = 0 ∧ b = 0 ∧ c = 0
    · obtain ⟨rfl, rfl, rfl⟩ := h
      simp only [add_zero]
      rw [if_pos (mkS_eta y)]; simp
    · rw [if_neg h, if_neg]
      intro heq
      apply h
      have h0 := congrArg (fun z => (z 0).val) heq
      have h1 := congrArg (fun z => (z 1).val) heq
      have h2 := congrArg (fun z => (z 2).val) heq
      rw [e1.1] at h0
      rw [e1.2.1] at h1
      rw [e1.2.2] at h2
      omega
  rw [Finset.sum_eq_single 0, Finset.sum_eq_single 0, Finset.sum_eq_single 0]
  · beta_reduce
    rw [key 0 0 0 hn hn hn]; simp
  · intro c hc hne
    beta_reduce
    rw [key 0 0 c hn hn (Finset.mem_range.mp hc)]
    simp [hne]
  · intro h; exact absurd (Finset.mem_range.mpr hn) h
  · intro b hb hne
    refine Finset.sum_eq_zero (fun c hc => ?_)
    beta_reduce
    rw [key 0 b c hn (Finset.mem_range.mp hb) (Finset.mem_range.mp hc)]
    simp [hne]
  · intro h; exact absurd (Finset.mem_range.mpr hn) h
  · intro a ha hne
    refine Finset.sum_eq_zero (fun b hb => Finset.sum_eq_zero (fun c hc => ?_))
    beta_reduce
    rw [key a b c (Finset.mem_range.mp ha) (Finset.mem_range.mp hb) (Finset.mem_range.mp hc)]
    simp [hne]
  · intro h; exact absurd (Finset.mem_range.mpr hn) h

end AdalyFormal.CoverOmegaTwo
