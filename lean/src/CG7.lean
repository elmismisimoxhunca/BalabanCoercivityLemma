import CG6e

/-!
# CG7 -- `CoverGeomBoxU` (the `j ≥ 2` half of the COVER_GEOM interface)
-/
set_option autoImplicit false
set_option maxHeartbeats 16000000
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
open AdalyFormal.M2BallCharts (iota_mem_ball Bz plq plq_conj)

theorem coverGeomBoxU : CoverGeomBoxU := by
  classical
  intro ell hell
  refine ⟨0, 24 * ell + 25, 7, 1 / 2, by norm_num, fun m hm R hR => ⟨by norm_num, ?_⟩⟩
  intro k hk Lu α₀ hα hsα hT S hS Lam hL U hU hloc j w r hj hB
  have hell0 : 0 < ell := by omega
  have hM0 : 0 < ell ^ m := pow_pos hell0 m
  obtain ⟨hcov, hP⟩ := hU
  obtain ⟨hjk, ⟨x₀, hx₀, hw⟩, -⟩ := hB
  have hanti : Antitone S.Om := antitone_nat_of_succ_le hS.1
  set s : ℕ := bigSide (ell ^ m) ell (j - 1) with hsdef
  have hs2 : 2 ≤ s := by
    have h1 : 1 ≤ ell ^ m := hM0
    have h2 : ell ≤ ell ^ (j - 1) := by
      calc ell = ell ^ 1 := (pow_one _).symm
        _ ≤ ell ^ (j - 1) := Nat.pow_le_pow_right hell0 (by omega)
    calc 2 ≤ ell := hell
      _ ≤ ell ^ (j - 1) := h2
      _ = 1 * ell ^ (j - 1) := (one_mul _).symm
      _ ≤ ell ^ m * ell ^ (j - 1) := Nat.mul_le_mul_right _ h1
  have hs0 : 0 < s := by omega
  have hN : ∀ τ, s ∣ scaleUp ell k Lu τ + 1 := fun τ => hS.2.2.1 (j - 1) (by omega) τ
  have hnpos : ∀ τ, 0 < (scaleUp ell k Lu τ + 1) / s := by
    intro τ
    obtain ⟨n, hn⟩ := hN τ
    have hpos : 0 < scaleUp ell k Lu τ + 1 := Nat.succ_pos _
    rw [hn, Nat.mul_div_cancel_left _ hs0]
    rcases Nat.eq_zero_or_pos n with h | h
    · rw [h] at hn; omega
    · exact h
  have hnmul : ∀ τ, scaleUp ell k Lu τ + 1 = s * ((scaleUp ell k Lu τ + 1) / s) :=
    fun τ => (Nat.mul_div_cancel' (hN τ)).symm
  have hc12 : ((12 : ℕ) : ℝ) = 12 := by norm_num
  set X : ℝ := ((12 : ℕ) : ℝ) * ((ell ^ m : ℕ) : ℝ) * α₀ with hXd
  have hX0 : 0 ≤ X := by positivity
  have hXh : X ≤ 1 / 2 := by rw [hXd, hc12]; exact hsα
  have hη : (0 : ℝ) < ((ell : ℝ) ^ k)⁻¹ := by positivity
  have hX1 : X1 ell (ell ^ m) α₀ j = X * ((ell : ℝ) ^ (j - 1))⁻¹ := rfl
  have hX2 : X2 ell (ell ^ m) α₀ j = X * (((ell : ℝ) ^ (j - 1))⁻¹) ^ 2 := rfl
  have hU1 : ((ell : ℝ) ^ (j - 1))⁻¹ ≤ 1 :=
    inv_le_one_of_one_le₀ (one_le_pow₀ (by exact_mod_cast hell0))
  have hU1' : 0 ≤ ((ell : ℝ) ^ (j - 1))⁻¹ := by positivity
  rw [hX1, hX2]
  refine ⟨fun c c' hc hc' hcc' => ?_, ?_⟩
  · -- pair charts
    have hrange : ∀ p : Z3, p ∈ cellBox (s : ℤ) (wo w) c ∪ cellBox (s : ℤ) (wo w) c' →
        ∀ μ, wo w μ / (s : ℤ) - ((7 * ell : ℕ) : ℤ) ≤ cellZ (s : ℤ) (wo w) p μ ∧
          cellZ (s : ℤ) (wo w) p μ ≤ wo w μ / (s : ℤ) + ((7 * ell : ℕ) : ℤ) := by
      intro p hp μ
      rcases hp with hp | hp
      · rw [hp μ]; exact hc μ
      · rw [hp μ]; exact hc' μ
    have hfree : ∃ ρ : Fin 3, ¬ (c' ρ ≠ c ρ) := by
      rcases hcc' with h | ⟨μ, h⟩
      · exact ⟨0, by rw [h]; simp⟩
      · by_cases h0 : μ = 0
        · exact ⟨1, by rw [h]; simp [ev, h0]⟩
        · exact ⟨0, by rw [h]; simp [ev, Ne.symm h0]⟩
    obtain ⟨ρ0, hρ0⟩ := hfree
    have hu : ∀ τ, cellU s (scaleUp ell k Lu) c τ < (scaleUp ell k Lu τ + 1) / s :=
      fun τ => cellU_lt (s := s) (c := c) (hnpos τ)
    have hOmreg : ∀ x ∈ CellReg s (fun τ => (scaleUp ell k Lu τ + 1) / s) (cellU s (scaleUp ell k Lu) c)
        (fun τ => c' τ ≠ c τ), x ∈ S.Om (j - 1) := by
      intro x hx
      obtain ⟨p, hp, rfl⟩ := region_preimage w hs0 hN hnpos hcc' hx
      exact (box_pt_near hS hell hM0 hj hjk hR hx₀ hw (hrange p hp)).2
    have hWidx : ∀ (sites : Set (PeriodicLatticeSite (scaleUp ell k Lu))) (i : ℕ),
        IsClassCube ell (ell ^ m) 12 k S sites i →
        (∃ y ∈ sites, y ∈ CellReg s (fun τ => (scaleUp ell k Lu τ + 1) / s) (cellU s (scaleUp ell k Lu) c)
          (fun τ => c' τ ≠ c τ)) → s ∣ bigSide (ell ^ m) ell i := by
      rintro sites i hcl ⟨y, hys, hyreg⟩
      obtain ⟨p, hp, hpy⟩ := region_preimage w hs0 hN hnpos hcc' hyreg
      have hq : iota w p ∈ sites := by rw [hpy]; exact hys
      have hi := box_idx hS hell hM0 hj hjk hR hx₀ hw (hrange p hp) hcl hq
      rw [hsdef]; unfold bigSide
      exact Nat.mul_dvd_mul_left _ (pow_dvd_pow ell hi)
    obtain ⟨sites, i, hcl, hreg⟩ := cellbox_wrap (c := 12) s hs2 hS hcov (fun τ => (scaleUp ell k Lu τ + 1) / s)
      (cellU s (scaleUp ell k Lu) c) hnmul hu (fun τ => c' τ ≠ c τ) ⟨ρ0, hρ0⟩
      (fun x hx => hanti (Nat.zero_le _) hx) hOmreg hWidx
    have hD : ∀ p ∈ cellBox (s : ℤ) (wo w) c ∪ cellBox (s : ℤ) (wo w) c', iota w p ∈ sites :=
      fun p hp => hreg (region_image w hs0 hN hnpos hcc' hp)
    let p₀ : Z3 := fun τ => (s : ℤ) * c τ - wo w τ
    have hp₀ : p₀ ∈ cellBox (s : ℤ) (wo w) c := by
      intro τ
      show (p₀ τ + wo w τ) / (s : ℤ) = c τ
      have : p₀ τ + wo w τ = (s : ℤ) * c τ + 0 := by simp [p₀]
      rw [this]
      have hsI : (0 : ℤ) < s := by exact_mod_cast hs0
      exact int_cell_div (n := 0) hsI le_rfl hsI
    have hi := box_idx hS hell hM0 hj hjk hR hx₀ hw (hrange p₀ (Or.inl hp₀)) hcl (hD p₀ (Or.inl hp₀))
    have hu0 : 0 < ((ell : ℝ) ^ i)⁻¹ := by positivity
    have hu1 : ((ell : ℝ) ^ i)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ (by exact_mod_cast hell0))
    have hsm : X * ((ell : ℝ) ^ i)⁻¹ + X * (((ell : ℝ) ^ i)⁻¹) ^ 2 ≤ 1 := by
      have h2 : (((ell : ℝ) ^ i)⁻¹) ^ 2 ≤ 1 := by nlinarith
      have e1 : X * ((ell : ℝ) ^ i)⁻¹ ≤ X := by nlinarith
      have e2 : X * (((ell : ℝ) ^ i)⁻¹) ^ 2 ≤ X := by nlinarith
      linarith
    obtain ⟨G, hG1, hG2⟩ := cube_C12 hη hP hcl hsm hell0 w _ hD
    have hUi : ((ell : ℝ) ^ i)⁻¹ ≤ ((ell : ℝ) ^ (j - 1))⁻¹ :=
      inv_anti₀ (pow_pos (by exact_mod_cast hell0) _)
        (pow_le_pow_right₀ (by exact_mod_cast (by omega : 1 ≤ ell)) hi)
    obtain ⟨b1, b2, -⟩ := t_bounds hX0 hXh hu0.le hUi hU1
    refine ⟨G, hG1.mono (fun p hp => hp) ?_, hG2.mono (fun p hp => hp) ?_⟩
    · have : 0 ≤ X * ((ell : ℝ) ^ (j - 1))⁻¹ := by positivity
      rw [← hXd]; linarith
    · have : 0 ≤ X * (((ell : ℝ) ^ (j - 1))⁻¹) ^ 2 := by positivity
      rw [← hXd]; linarith
  · -- plaquette bound on the box
    have hrQ : ∀ p : Z3, p ∈ BoxR (s : ℤ) (wo w) (7 * ell) →
        ∀ μ, wo w μ / (s : ℤ) - ((7 * ell : ℕ) : ℤ) ≤ cellZ (s : ℤ) (wo w) p μ ∧
          cellZ (s : ℤ) (wo w) p μ ≤ wo w μ / (s : ℤ) + ((7 * ell : ℕ) : ℤ) := fun p hp => hp
    have hΩQ : ∀ p : Z3, p ∈ BoxR (s : ℤ) (wo w) (7 * ell) → iota w p ∈ S.Om (j - 1) :=
      fun p hp => (box_pt_near hS hell hM0 hj hjk hR hx₀ hw (hrQ p hp)).2
    have key : ∀ (q : Z3) (μ ν : Fin 3), μ < ν → q ∈ BoxR (s : ℤ) (wo w) (7 * ell) →
        q + ev μ ∈ BoxR (s : ℤ) (wo w) (7 * ell) → q + ev ν ∈ BoxR (s : ℤ) (wo w) (7 * ell) →
        q + ev μ + ev ν ∈ BoxR (s : ℤ) (wo w) (7 * ell) →
        frobNorm (((hol (Wof U w) q μ ν : SU2) : M2) - 1) ≤ 7 * (X * (((ell : ℝ) ^ (j - 1))⁻¹) ^ 2) := by
      intro q μ ν hlt hq h1 h2 h3
      rw [hol_eq_plq]
      have hx0 : iota w q ∈ S.Om (j - 1) := hΩQ q hq
      have hx1 : periodicLatticeShift (iota w q) μ ∈ S.Om (j - 1) := by rw [iota_shift]; exact hΩQ _ h1
      have hx2 : periodicLatticeShift (iota w q) ν ∈ S.Om (j - 1) := by rw [iota_shift]; exact hΩQ _ h2
      have hx3 : periodicLatticeShift (periodicLatticeShift (iota w q) μ) ν ∈ S.Om (j - 1) := by
        rw [iota_shift, iota_shift]; exact hΩQ _ h3
      have hx3' : periodicLatticeShift (periodicLatticeShift (iota w q) ν) μ ∈ S.Om (j - 1) := by
        rw [← shift_comm']; exact hx3
      let P : PeriodicLatticePlaquette (scaleUp ell k Lu) := (iota w q, ⟨(μ, ν), hlt⟩)
      have hp : ∀ e ∈ periodicPlaquetteBoundaryEdges P, CubeBond (S.Om 0) e := by
        intro e he
        simp only [periodicPlaquetteBoundaryEdges, P, Finset.mem_insert, Finset.mem_singleton] at he
        rcases he with rfl | rfl | rfl | rfl
        · exact ⟨hanti (Nat.zero_le _) hx0, hanti (Nat.zero_le _) hx1⟩
        · exact ⟨hanti (Nat.zero_le _) hx1, hanti (Nat.zero_le _) hx3⟩
        · exact ⟨hanti (Nat.zero_le _) hx2, hanti (Nat.zero_le _) hx3'⟩
        · exact ⟨hanti (Nat.zero_le _) hx0, hanti (Nat.zero_le _) hx2⟩
      obtain ⟨sites, i, hcl, hb⟩ := hcov.2 P hp
      have hbm : ∀ e ∈ periodicPlaquetteBoundaryEdges P, CubeBond sites e := hb
      have b1 := hbm (iota w q, μ) (by simp [periodicPlaquetteBoundaryEdges, P])
      have b2 := hbm (periodicLatticeShift (iota w q) μ, ν) (by simp [periodicPlaquetteBoundaryEdges, P])
      have b3 := hbm (periodicLatticeShift (iota w q) ν, μ) (by simp [periodicPlaquetteBoundaryEdges, P])
      have hi := box_idx hS hell hM0 hj hjk hR hx₀ hw (hrQ q hq) hcl b1.1
      have hu0 : 0 < ((ell : ℝ) ^ i)⁻¹ := by positivity
      have hu1 : ((ell : ℝ) ^ i)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ (by exact_mod_cast hell0))
      have hsm : ((12 : ℕ) : ℝ) * ((ell ^ m : ℕ) : ℝ) * α₀ * ((ell : ℝ) ^ i)⁻¹
          + ((12 : ℕ) : ℝ) * ((ell ^ m : ℕ) : ℝ) * α₀ * (((ell : ℝ) ^ i)⁻¹) ^ 2 ≤ 1 := by
        rw [← hXd]
        have h2' : (((ell : ℝ) ^ i)⁻¹) ^ 2 ≤ 1 := by nlinarith
        have e1 : X * ((ell : ℝ) ^ i)⁻¹ ≤ X := by nlinarith
        have e2 : X * (((ell : ℝ) ^ i)⁻¹) ^ 2 ≤ X := by nlinarith
        linarith
      obtain ⟨g, hg⟩ := AdalyFormal.M2Glue2.gchart_of_cube hη hP hcl hsm hell0
      have hpl := plq_near_of_gchart hg (iota w q) μ ν b1.1 b1.2 b3.1 b2.2
      have hc := shift_comm' (iota w q) μ ν
      rw [plq_conj U (fun _ => 1) g (iota w q) μ ν hc, AdalyFormal.M2Glue2.frobNorm_conj_sub_one]
      have hUi : ((ell : ℝ) ^ i)⁻¹ ≤ ((ell : ℝ) ^ (j - 1))⁻¹ :=
        inv_anti₀ (pow_pos (by exact_mod_cast hell0) _)
          (pow_le_pow_right₀ (by exact_mod_cast (by omega : 1 ≤ ell)) hi)
      obtain ⟨-, -, b3'⟩ := t_bounds hX0 hXh hu0.le hUi hU1
      refine hpl.trans ?_
      rw [← hXd]
      exact b3'
    intro q μ ν hq h1 h2 h3
    rcases lt_trichotomy μ ν with hlt | heq | hgt
    · exact key q μ ν hlt hq h1 h2 h3
    · subst heq
      rw [hol_self]
      simp [frobNorm_zero']
      positivity
    · have h3' : q + ev ν + ev μ ∈ BoxR (s : ℤ) (wo w) (7 * ell) := by rw [add_right_comm]; exact h3
      rw [hol_swap, n_inv]
      exact key q ν μ hgt hq h2 h1 h3'

end AdalyFormal.CoverGeom
