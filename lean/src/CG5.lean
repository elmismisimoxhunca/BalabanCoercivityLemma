import CG4c

/-!
# CG5 -- `CoverGeomU` (the `j ≤ 1` half of the COVER_GEOM interface)
-/
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option linter.unusedVariables false

namespace AdalyFormal.CoverGeom

open AdalyFormal.Target.ClayStatement AdalyFormal.StatementLane AdalyFormal.StatementLane2
open AdalyFormal.StatementLaneR8 (Ball)
open AdalyFormal.M2Glue3 (Z3 ev iota iota_shift iota_shift2)
open AdalyFormal.M2Glue2 (GChart shift_comm')
open AdalyFormal.Balaban.SuTwoLogExp (SU2 M2)
open AdalyFormal.Balaban.RMapLipschitz (frobNorm)
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
open AdalyFormal.UnifLane.Z
open AdalyFormal.M2BallCharts (iota_mem_ball Bz plq plq_class)
open AdalyFormal.StatementLaneG (LambdaOK2)

variable {L : PeriodicLatticeExtent}

theorem hol_eq_plq (U : LinkCfg L) (w : PeriodicLatticeSite L) (q : Z3) (μ ν : Fin 3) :
    hol (Wof U w) q μ ν = plq U (fun _ => 1) (iota w q) μ ν := by
  simp [hol, plq, Wof, periodicGaugeTransform, iota_shift]

theorem hol_swap (W : Z3 → Fin 3 → SU2) (q : Z3) (μ ν : Fin 3) : hol W q μ ν = (hol W q ν μ)⁻¹ := by
  simp only [hol]; group

theorem hol_self (W : Z3 → Fin 3 → SU2) (q : Z3) (μ : Fin 3) : hol W q μ μ = 1 := by
  simp only [hol]; group

theorem bigSide_zero_dvd (M ell i : ℕ) : bigSide M ell 0 ∣ bigSide M ell i := by
  unfold bigSide; exact Nat.mul_dvd_mul_left M (by simp)

theorem frobNorm_zero' : frobNorm (0 : M2) = 0 := by
  simp [AdalyFormal.Balaban.RMapLipschitz.frobNorm, AdalyFormal.Balaban.RMapLipschitz.frobSq]

theorem coverGeomU : CoverGeomU := by
  intro ell hell
  refine ⟨0, 0, 4, 1 / 2, by norm_num, fun m hm R hR => ⟨by norm_num, ?_⟩⟩
  intro k hk Lu α₀ hα hsα hT S hS Lam hL U hU hloc j w r hj hB
  have hell0 : 0 < ell := by omega
  have hM0 : 0 < ell ^ m := pow_pos hell0 m
  have hj0 : j - 1 = 0 := by omega
  have hbs : bigSide (ell ^ m) ell (j - 1) = ell ^ m := by simp [bigSide, hj0]
  have hX1 : X1 ell (ell ^ m) α₀ j = 12 * ((ell ^ m : ℕ) : ℝ) * α₀ := by unfold X1; rw [hj0]; simp
  have hX2 : X2 ell (ell ^ m) α₀ j = 12 * ((ell ^ m : ℕ) : ℝ) * α₀ := by unfold X2; rw [hj0]; simp
  have hX0 : 0 ≤ 12 * ((ell ^ m : ℕ) : ℝ) * α₀ := by positivity
  have hη : (0 : ℝ) < ((ell : ℝ) ^ k)⁻¹ := by positivity
  obtain ⟨hcov, hP⟩ := hU
  have hjk : j ≤ k := hB.1
  have hBΩ : ∀ x ∈ Ball w r, x ∈ S.Om (j - 1) := hB.2.2.2.2.1
  have hanti : Antitone S.Om := antitone_nat_of_succ_le hS.1
  have hΩ0 : ∀ q ∈ Bz r, iota w q ∈ S.Om 0 := fun q hq => hanti (Nat.zero_le _) (hBΩ _ (iota_mem_ball hq))
  have hN : ∀ μ, ell ^ m ∣ scaleUp ell k Lu μ + 1 := by
    intro μ
    have := hS.2.2.1 0 (Nat.zero_le k) μ
    simpa [bigSide] using this
  rw [hbs, hX1, hX2]
  refine ⟨fun c => ?_, ?_⟩
  · by_cases hne : (cellSet (((ell ^ m : ℕ)) : ℤ) (wo w) r c).Nonempty
    · obtain ⟨p₀, hp₀⟩ := hne
      have hp₀B : p₀ ∈ Bz r := hp₀.1
      obtain ⟨sites, i, hcl, hq₀⟩ := hcov.1 (iota w p₀) (hΩ0 p₀ hp₀B)
      have hMi : ell ^ m ∣ bigSide (ell ^ m) ell i := dvd_mul_right _ _
      have hD : ∀ p ∈ cellSet (((ell ^ m : ℕ)) : ℤ) (wo w) r c, iota w p ∈ sites := by
        intro p hp
        refine classCube_sat hS hcl hM0 hMi hq₀ (fun μ => ?_)
        have a := iota_cell w hM0 μ (hN μ) p₀
        have b := iota_cell w hM0 μ (hN μ) p
        have e1 := hp₀.2 μ
        have e2 := hp.2 μ
        have : (((iota w p₀ μ).val / ell ^ m : ℕ) : ℤ) = (((iota w p μ).val / ell ^ m : ℕ) : ℤ) := by
          rw [a, b, e1, e2]
        exact_mod_cast this
      have hu0 : 0 < ((ell : ℝ) ^ i)⁻¹ := by positivity
      have hu1 : ((ell : ℝ) ^ i)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ (by exact_mod_cast hell0))
      have hc12 : ((12 : ℕ) : ℝ) = 12 := by norm_num
      have hsm : ((12 : ℕ) : ℝ) * ((ell ^ m : ℕ) : ℝ) * α₀ * ((ell : ℝ) ^ i)⁻¹
          + ((12 : ℕ) : ℝ) * ((ell ^ m : ℕ) : ℝ) * α₀ * (((ell : ℝ) ^ i)⁻¹) ^ 2 ≤ 1 := by
        rw [hc12]
        set X : ℝ := 12 * ((ell ^ m : ℕ) : ℝ) * α₀ with hXd
        set u : ℝ := ((ell : ℝ) ^ i)⁻¹ with hud
        have h2 : u ^ 2 ≤ 1 := by nlinarith
        have e1 : X * u ≤ X := by nlinarith
        have e2 : X * u ^ 2 ≤ X := by nlinarith
        linarith
      obtain ⟨G, hG1, -⟩ := cube_C12 hη hP hcl hsm hell0 w _ hD
      refine ⟨G, hG1.mono (fun p hp => hp) ?_⟩
      rw [hc12]
      set X : ℝ := 12 * ((ell ^ m : ℕ) : ℝ) * α₀ with hXd
      set u : ℝ := ((ell : ℝ) ^ i)⁻¹ with hud
      have e1 : X * u ≤ X := by nlinarith
      linarith
    · exact ⟨fun _ => 1, fun p ν hp => absurd ⟨p, hp⟩ hne⟩
  · intro q μ ν hq h1 h2 h3
    rcases lt_trichotomy μ ν with hlt | heq | hgt
    · rw [hol_eq_plq]
      have hv : ∀ q', q' ∈ Bz r → iota w q' ∈ S.Om 0 := hΩ0
      have := plq_class (R := R) hcov hell0 hη hα.le hP hsα hlt (hΩ0 q hq)
        (by rw [iota_shift]; exact hΩ0 _ h1) (by rw [iota_shift]; exact hΩ0 _ h2)
        (by rw [iota_shift2]; exact hΩ0 _ h3) (shift_comm' _ _ _) (fun _ => 1)
      linarith
    · subst heq
      rw [hol_self]
      simp [frobNorm_zero']
      positivity
    · have h3' : q + ev ν + ev μ ∈ Bz r := by rw [add_right_comm]; exact h3
      rw [hol_swap, show (hol (Wof U w) q ν μ)⁻¹ = (hol (Wof U w) q ν μ)⁻¹ from rfl, n_inv, hol_eq_plq]
      have := plq_class (R := R) hcov hell0 hη hα.le hP hsα hgt (hΩ0 q hq)
        (by rw [iota_shift]; exact hΩ0 _ h2) (by rw [iota_shift]; exact hΩ0 _ h1)
        (by rw [iota_shift2]; exact hΩ0 _ h3') (shift_comm' _ _ _) (fun _ => 1)
      linarith

end AdalyFormal.CoverGeom
