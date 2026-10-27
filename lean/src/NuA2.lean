import NuA1

/-!
# NuA2 -- the per-cube constant-family form at `ell = 2` (lane ncwdh_ell2_20261018)

* `exists_classCube_ne_two`   : fork of `NtFam3.exists_classCube_ne` for `2 ≤ ell` (class cube of factor `cf`, index `1`, `R ≥ cf`).
* `not_covPlaqF_two`          : at `ell = 2` the plaquette-coverage clause `CovPlaqF` fails for `constFam c` (the central dir-0 bond, hence the `(0,1)`-plaquette through it, lies in no class cube).
* `constFam_witness_two`      : the refuting configurations carry a class cube, regular class cubes, `WellDefG`, a bond of `Ω₀` in no class cube (so `CovPlaqF` fails), and a failing competitor.
* `not_familyTorusNCConstAt_two`.
-/
set_option autoImplicit false
set_option maxHeartbeats 16000000
set_option maxRecDepth 8000

namespace NcwdhFam

open AdalyFormal.Target.ClayStatement
open AdalyFormal.CoverNested
open AdalyFormal.CoverJacobi
open AdalyFormal.CoverOmega
open AdalyFormal.CoverOmega.Struct
open AdalyFormal.NcwdhStrong
open AdalyFormal.NcwdhTwo
open AdalyFormal.StatementLane (scaleUp)
open AdalyFormal.StatementLane
open AdalyFormal.StatementLane2
open AdalyFormal.StatementLaneG
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Balaban.CovariantOperators (SuTwo)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
open AdalyFormal.Balaban.RegularUPerturbation (bondEnergy)
open AdalyFormal.NonVac (mem_box_N shift_val_N)
open MXQ.AllC
open MXQ.Total

section
variable [CfData]

theorem exists_classCube_ne_two {ell M R : ℕ} (hell : 2 ≤ ell) (hM : 0 < M) (hR1 : 1 ≤ R) (hR : CfData.cf ≤ R) :
    ∃ (sites : Set (PeriodicLatticeSite (scaleUp ell 2 (neLu M R)))) (j : ℕ),
      IsClassCube ell M CfData.cf 2 (neS ell M R) sites j := by
  obtain ⟨l1, l2, l3, l4, l5, l6, l7, l8⟩ := ne_lin_two hell hM hR1
  obtain ⟨c1, c2, c3, c4, c5⟩ := ne_lin_c2 (M := M) hell
  have hcf := CfData.hcf
  have hN := ne_scaleUp (ell := ell) (R := R) (by omega) hM
  have hNe : neN ell M R = 4 * (ell * (ell * (R * M))) + 2 * (CfData.cf * (ell * (ell * M))) + 6 * (ell * (ell * M)) := rfl
  -- P1 is a multiple of the level-1 block side
  have hP1 : neP1 ell M R = M * ell ^ 1 * (R * (ell - 1) + ell) := by
    obtain ⟨e, rfl⟩ : ∃ e, ell = e + 1 := ⟨ell - 1, by omega⟩
    simp only [neP1, neA', Nat.add_sub_cancel]
    apply Nat.sub_eq_of_eq_add
    ring
  -- the cube side `s = cf * (M * ell)` fits in `[P1, A')`
  have hs : CfData.cf * (M * ell ^ 1) = CfData.cf * (ell * M) := by ring
  have hRs : CfData.cf * (ell * M) ≤ ell * (R * M) := by
    calc CfData.cf * (ell * M) ≤ R * (ell * M) := Nat.mul_le_mul_right _ hR
      _ = ell * (R * M) := by ring
  have hspos : 0 < CfData.cf * (ell * M) := by omega
  have hP1lt : neP1 ell M R + CfData.cf * (ell * M) ≤ neA' ell M R := by
    simp only [neP1, neA']; omega
  have hA'N : neA' ell M R < neN ell M R := by simp only [neA']; omega
  have hlt : ∀ y : PeriodicLatticeSite (scaleUp ell 2 (neLu M R)), ∀ μ, (y μ).val < neN ell M R :=
    fun y μ => by have := (y μ).isLt; have := hN μ; omega
  let z : PeriodicLatticeSite (scaleUp ell 2 (neLu M R)) :=
    fun μ => ⟨if μ = 0 then neP1 ell M R else 0, by
      have := hN μ; split_ifs <;> omega⟩
  have hz0 : (z 0).val = neP1 ell M R := by simp [z]
  have hz1 : (z 1).val = 0 := by simp [z]
  have hz2 : (z 2).val = 0 := by simp [z]
  have hsub : ∀ x ∈ siteBox z (CfData.cf * bigSide M ell 1),
      x ∈ (neS ell M R).Om 1 ∧ x ∉ (neS ell M R).Om 2 := by
    intro x hx
    have h0 := ((mem_box_N hN z x _).1 hx).1
    simp only [bigSide, hs, hz0] at h0
    obtain ⟨hlo, hhi⟩ := box_coord (hlt x 0) (by omega) h0
    refine ⟨?_, ?_⟩
    · rw [neS_om1]; simp only [neP1, neQ1, neB, neA'] at hlo hhi ⊢; omega
    · rw [neS_om2]; simp only [neP1, neA', neB', neA, neB] at hlo hhi ⊢; omega
  refine ⟨siteBox z (CfData.cf * bigSide M ell 1), 1, ⟨⟨by norm_num, ⟨z, ?_, rfl⟩, ?_, ?_⟩, ?_⟩⟩
  · intro μ
    fin_cases μ
    · show (z 0).val % bigSide M ell 1 = 0
      rw [hz0, hP1]; simp only [bigSide]; exact Nat.mul_mod_right _ _
    · show (z 1).val % bigSide M ell 1 = 0
      rw [hz1]; exact Nat.zero_mod _
    · show (z 2).val % bigSide M ell 1 = 0
      rw [hz2]; exact Nat.zero_mod _
  · intro x hx
    left
    exact hsub x hx
  · refine ⟨z, ?_, ?_⟩
    · rw [mem_box_N hN z z _]
      simp only [bigSide, hs]
      refine ⟨?_, ?_, ?_⟩ <;> simp [Nat.add_sub_cancel] <;> omega
    · have hh : neP1 ell M R + 0 ≤ neP1 ell M R := le_refl _
      refine ⟨?_, ?_⟩
      · rw [neS_om1]; simp only [neP1, neQ1, neB, neA']
        rw [show (z 0).val = neP1 ell M R from hz0]; simp only [neP1, neA', neQ1, neB]; omega
      · rw [neS_om2]; rw [show (z 0).val = neP1 ell M R from hz0]
        simp only [neP1, neA', neB', neA, neB]; omega
  · rintro i ⟨hi, -, hsub', ⟨w, hw, hwB⟩⟩
    have hwB1 := hsub w hw
    rcases (show i = 0 ∨ i = 1 ∨ i = 2 by omega) with rfl | rfl | rfl
    · exfalso
      -- w ∈ Ω₀ \ Ω₁ but w ∈ Ω₁
      exact hwB.2 hwB1.1
    · rfl
    · exfalso
      exact hwB1.2 hwB.1


/-- the lower endpoint site of the central bond and its `x₀`-shift lie in `Ω₀` of the nested tower. -/
theorem om0_of_val {M R : ℕ} (hM : 0 < M) (hR : 1 ≤ R) (y : PeriodicLatticeSite (scaleUp 2 2 (neLu M R)))
    (hy : (y 0).val = neC0 2 M R ∨ (y 0).val = neC0 2 M R + 1) : y ∈ (neS 2 M R).Om 0 := by
  obtain ⟨l1, l2, l3, l4, l5, l6, l7, l8⟩ := ne_lin_two (ell := 2) (le_refl 2) hM hR
  have hcf := CfData.hcf
  have e1 : CfData.cf * (2 * (2 * M)) = 2 * (CfData.cf * (2 * M)) := by ring
  have hc2M : 10 * (2 * M) ≤ CfData.cf * (2 * M) := Nat.mul_le_mul_right _ hcf
  rw [neS_om0]
  simp only [neP0, neP1, neQ0, neQ1, neB, neA', neC0] at hy ⊢
  omega

theorem not_covPlaqF_two {M R : ℕ} (hM : 0 < M) (hR : 1 ≤ R) :
    ¬ CovPlaqF 2 M (constFam CfData.cf (scaleUp 2 2 (neLu M R))) 2 (neS 2 M R) := by
  intro hcov
  obtain ⟨l1, l2, l3, l4, l5, l6, l7, l8⟩ := ne_lin_two (ell := 2) (le_refl 2) hM hR
  have hN := ne_scaleUp (ell := 2) (R := R) (by norm_num) hM
  have hNdef : neN 2 M R = 4 * (2 * (2 * (R * M))) + 2 * (CfData.cf * (2 * (2 * M))) + 6 * (2 * (2 * M)) := rfl
  have hcf := CfData.hcf
  have e1 : CfData.cf * (2 * (2 * M)) = 2 * (CfData.cf * (2 * M)) := by ring
  have hc2M : 10 * (2 * M) ≤ CfData.cf * (2 * M) := Nat.mul_le_mul_right _ hcf
  have hN1 : 1 < neN 2 M R := by omega
  have hCN : neC0 2 M R + 1 < neN 2 M R := by simp only [neC0, neA']; omega
  let x : PeriodicLatticeSite (scaleUp 2 2 (neLu M R)) :=
    fun μ => ⟨if μ = 0 then neC0 2 M R else 0, by have := hN μ; split_ifs <;> omega⟩
  have hx0 : (x 0).val = neC0 2 M R := by simp [x]
  have hv : ∀ (y : PeriodicLatticeSite (scaleUp 2 2 (neLu M R))) (μ : Fin 3),
      ((periodicLatticeShift y μ) 0).val = if (0 : Fin 3) = μ then ((y 0).val + 1) % neN 2 M R else (y 0).val :=
    fun y μ => shift_val_N hN hN1 y μ 0
  have hv0 : ∀ y : PeriodicLatticeSite (scaleUp 2 2 (neLu M R)), (y 0).val = neC0 2 M R →
      ((periodicLatticeShift y 0) 0).val = neC0 2 M R + 1 := by
    intro y hy
    rw [hv, if_pos rfl, hy]; exact Nat.mod_eq_of_lt hCN
  have hvn : ∀ (y : PeriodicLatticeSite (scaleUp 2 2 (neLu M R))) (μ : Fin 3), μ ≠ 0 →
      ((periodicLatticeShift y μ) 0).val = (y 0).val := by
    intro y μ hμ
    rw [hv, if_neg (fun h => hμ h.symm)]
  have h1 : (1 : Fin 3) ≠ 0 := by decide
  have hx0' := hv0 x hx0
  have hx1 := hvn x 1 h1
  have hxx : (x, ((0 : Fin 3), (1 : Fin 3))) = (x, ((0 : Fin 3), (1 : Fin 3))) := rfl
  have h01 : ((0 : Fin 3), (1 : Fin 3)).1 < ((0 : Fin 3), (1 : Fin 3)).2 := by decide
  have hp := hcov (x, ⟨((0 : Fin 3), (1 : Fin 3)), h01⟩) (by
    intro e he
    simp only [periodicPlaquetteBoundaryEdges, Finset.mem_insert, Finset.mem_singleton] at he
    rcases he with rfl | rfl | rfl | rfl
    · exact ⟨om0_of_val hM hR _ (Or.inl hx0), om0_of_val hM hR _ (Or.inr hx0')⟩
    · refine ⟨om0_of_val hM hR _ (Or.inr hx0'), om0_of_val hM hR _ (Or.inr ?_)⟩
      rw [hvn _ 1 h1]; exact hx0'
    · refine ⟨om0_of_val hM hR _ (Or.inl ?_), om0_of_val hM hR _ (Or.inr ?_)⟩
      · rw [hx1]; exact hx0
      · rw [hv0 _ (by rw [hx1]; exact hx0)]
    · exact ⟨om0_of_val hM hR _ (Or.inl hx0), om0_of_val hM hR _ (Or.inl (by rw [hx1]; exact hx0))⟩)
  obtain ⟨sites, j, ⟨f, hmem, hq⟩, hcb⟩ := hp
  have hf : f = CfData.cf := mem_constFam.1 hmem
  rw [hf] at hq
  have hb := hcb (x, 0) (by simp [periodicPlaquetteBoundaryEdges])
  exact ne2_bond_uncovered hM hR x hx0 sites j hq hb

end

end NcwdhFam
