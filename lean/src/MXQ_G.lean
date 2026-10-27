import MXQ_A
import MXQ_CG4b
import MXQ_GG5
import MXQ_CG
import MXQ_BLC7
import TT_G

/-!
# TT_G -- the COVER_GEOM interface with CUBE-FACTOR-FREE geometry (lane total_20261017)

Cells at scale `b_{j-2} = M ℓ^{j-2}` (instead of `b_{j-1}`), box of `7 ℓ²` cells (the same lattice radius `7 b_j`).  A class cube of ANY factor through a point
of `Ω_{j-1}` has index `≥ j-2` (`AC_CF.cubeIndex_ge_pred`), so it is a union of `b_{j-2}`-cells with no collar term in `fc`: the threshold is
`R₁ = 24 ℓ + 25` (the fc-free collar of the box inside `Ω_{j-1}`), and `fc ≥ 10` is quantified after the constants (`ClassFamT`).
Text copy of `UMG` (`coverGeomUH`, `coverGeomBoxUH`) with these changes only.  Chart constants (`4`, `7`) and smallness (`1/2`) unchanged;
the clause bounds are `X ℓ^{-(j-2)}` and `X ℓ^{-2(j-2)}`.
-/
set_option autoImplicit false
set_option maxHeartbeats 16000000
set_option linter.unusedVariables false

namespace MXQ.Total
open MXQ.AllC (CF CubeFamOK)
open AdalyFormal.Total

open AdalyFormal.Target.ClayStatement AdalyFormal.StatementLane AdalyFormal.StatementLane2
open AdalyFormal.StatementLaneR8 (Ball)
open AdalyFormal.M2Glue3 (Z3 ev iota iota_shift iota_shift2)
open AdalyFormal.M2Glue2 (GChart shift_comm')
open AdalyFormal.Balaban.SuTwoLogExp (SU2 M2)
open AdalyFormal.Balaban.RMapLipschitz (frobNorm)
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
open AdalyFormal.UnifLane.Z
open AdalyFormal.CoverGeom
open AdalyFormal.M2BallCharts (iota_mem_ball Bz plq plq_conj)
open MXQ.M2BallCharts (plq_classACΦ)
open MXQ.CoverGeom (cellbox_wrapΦ)
open AdalyFormal.StatementLaneG (LambdaOK2)
open MXQ.AllC (CubeFamOK IsClassCubeQ)
open MXQ.AllC (gchart_of_cubeHΦ)

/-- the two chart constants at cell scale `b_{j-2}` (without the factor `c`). -/
noncomputable def Y1 (ell M : ℕ) (α₀ : ℝ) (j : ℕ) : ℝ := ((12 : ℕ) : ℝ) * M * α₀ * ((ell : ℝ) ^ (j - 2))⁻¹
noncomputable def Y2 (ell M : ℕ) (α₀ : ℝ) (j : ℕ) : ℝ := ((12 : ℕ) : ℝ) * M * α₀ * (((ell : ℝ) ^ (j - 2))⁻¹) ^ 2

/-- **COVER_GEOM INTERFACE, `j ≤ 1`** (as `UMZ.CoverGeomUH`, cube factor after the constants). -/
def CoverGeomUTΦ : Prop :=
  ∀ (ell : ℕ), 2 ≤ ell →
    ClassFamT ell ℝ (fun _ _ c => 1 ≤ c) (fun M _ k _ c S Lam U α₀ =>
      ∀ j w r, j ≤ 1 → BallHyp ell M k S j w r →
        CoverGeomZ (Wof U w) ((bigSide M ell (j - 1) : ℕ) : ℤ) (wo w) r (c * X1 ell M α₀ j) (c * X2 ell M α₀ j))

/-- **COVER_GEOM INTERFACE, `j ≥ 2`**: cells of side `b_{j-2}`, box of `7 ℓ²` cells, bounds `c · 12 M α₀ ℓ^{-(j-2)}`, `c · 12 M α₀ ℓ^{-2(j-2)}`. -/
def CoverGeomBoxUTΦ : Prop :=
  ∀ (ell : ℕ), 2 ≤ ell →
    ClassFamT ell ℝ (fun _ _ c => 1 ≤ c) (fun M _ k _ c S Lam U α₀ =>
      ∀ j w r, 2 ≤ j → BallHyp ell M k S j w r →
        CoverGeomBox (Wof U w) ((bigSide M ell (j - 2) : ℕ) : ℤ) (wo w) (7 * ell ^ 2) (c * Y1 ell M α₀ j) (c * Y2 ell M α₀ j))


/-- the `IsClassCubeQ` versions of the factor-generic cube lemmas. -/
theorem classCube_satΦ {L : PeriodicLatticeExtent} {ell M R k : ℕ} {Fm : CF} {S : Tower L} (hadm : Admissible ell M R k S)
    {sites : Set (PeriodicLatticeSite L)} {i : ℕ} (hc : IsClassCubeQ ell M Fm k S sites i)
    {W : ℕ} (hW : 0 < W) (hWi : W ∣ bigSide M ell i)
    {x y : PeriodicLatticeSite L} (hx : x ∈ sites) (hxy : ∀ μ, (x μ).val / W = (y μ).val / W) : y ∈ sites := by
  obtain ⟨f, hf, hc⟩ := hc
  exact AdalyFormal.CoverGeom.classCube_sat hadm hc hW hWi hx hxy

theorem cube_C12HΦ {L : PeriodicLatticeExtent} {ell M k : ℕ} {Fm : CF} [CubeFamOK Fm] {S : Tower L} {α₀ η : ℝ} (hη : 0 < η)
    {U : LinkCfg L} (hP : MXQ.AllC.PerCubeRegular2HQ ell M Fm 12 k S α₀ η U)
    {sites : Set (PeriodicLatticeSite L)} {i : ℕ} (hq : IsClassCubeQ ell M Fm k S sites i)
    (hsm : ((12 : ℕ) : ℝ) * M * α₀ * ((ell : ℝ) ^ i)⁻¹ + ((12 : ℕ) : ℝ) * M * α₀ * (((ell : ℝ) ^ i)⁻¹) ^ 2 ≤ 1)
    (hell : 0 < ell) (w : PeriodicLatticeSite L) (D : Set Z3) (hD : ∀ p ∈ D, iota w p ∈ sites) :
    ∃ G : Z3 → SU2, C1 (Wof U w) G D (((12 : ℕ) : ℝ) * M * α₀ * ((ell : ℝ) ^ i)⁻¹) ∧
      C2 (Wof U w) G D ((1 + 4 * (((12 : ℕ) : ℝ) * M * α₀ * ((ell : ℝ) ^ i)⁻¹)) * (((12 : ℕ) : ℝ) * M * α₀ * (((ell : ℝ) ^ i)⁻¹) ^ 2)) := by
  obtain ⟨f, hf, hq⟩ := hq
  have hfp : 0 < f := CubeFamOK.pos hf
  exact MXQ.CoverGeom.cube_C12RB hη (hP f _ _ hf hq) hsm hell w D hD

section geoΦ
variable {L : PeriodicLatticeExtent}

/-- **the cube-factor-free index bound**: a class cube of ANY factor through a box point has index `≥ j - 2`. -/
theorem box_idxTΦ {Fm : CF} {ell M R k j : ℕ} {S : Tower L} (hadm : Admissible ell M R k S) (hell : 2 ≤ ell) (hM : 0 < M)
    (hj : 2 ≤ j) (hjk : j ≤ k) (hR : 24 * ell + 25 ≤ R) {w x₀ : PeriodicLatticeSite L} (hx₀ : x₀ ∈ S.Om j)
    (hw : pdist w x₀ ≤ 3 * (M * ell ^ j)) {p : Z3}
    (hp : ∀ μ, wo w μ / ((bigSide M ell (j - 2) : ℕ) : ℤ) - ((7 * ell ^ 2 : ℕ) : ℤ) ≤ cellZ ((bigSide M ell (j - 2) : ℕ) : ℤ) (wo w) p μ ∧
      cellZ ((bigSide M ell (j - 2) : ℕ) : ℤ) (wo w) p μ ≤ wo w μ / ((bigSide M ell (j - 2) : ℕ) : ℤ) + ((7 * ell ^ 2 : ℕ) : ℤ))
    {sites : Set (PeriodicLatticeSite L)} {i : ℕ} (hcl : IsClassCubeQ ell M Fm k S sites i) (hq : iota w p ∈ sites) :
    j - 2 ≤ i := by
  obtain ⟨-, hΩ⟩ := box_pt_nearT hadm hell hM hj hjk hR hx₀ hw hp
  obtain ⟨f, hf, hcl⟩ := hcl
  have := AdalyFormal.M2GlueGeo.cubeIndex_ge_pred hadm hcl hq hΩ
  omega

end geoΦ

variable {Fm : CF}

theorem coverGeomUTΦ : CoverGeomUTΦ := by
  intro ell hell
  refine ⟨0, 0, 4, 1 / 2, by norm_num, fun Fm hFm m hm R hR => ⟨by norm_num, ?_⟩⟩
  haveI : CubeFamOK Fm := hFm
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
        refine classCube_satΦ hS hcl hM0 hMi hq₀ (fun μ => ?_)
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
      obtain ⟨G, hG1, -⟩ := cube_C12HΦ hη hP hcl hsm hell0 w _ hD
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
      have := plq_classACΦ (R := R) hcov hell0 hη hα.le hP hsα hlt (hΩ0 q hq)
        (by rw [iota_shift]; exact hΩ0 _ h1) (by rw [iota_shift]; exact hΩ0 _ h2)
        (by rw [iota_shift2]; exact hΩ0 _ h3) (shift_comm' _ _ _) (fun _ => 1)
      linarith
    · subst heq
      rw [hol_self]
      simp [AdalyFormal.CoverGeom.frobNorm_zero']
      positivity
    · have h3' : q + ev ν + ev μ ∈ Bz r := by rw [add_right_comm]; exact h3
      rw [hol_swap, show (hol (Wof U w) q ν μ)⁻¹ = (hol (Wof U w) q ν μ)⁻¹ from rfl, n_inv, hol_eq_plq]
      have := plq_classACΦ (R := R) hcov hell0 hη hα.le hP hsα hgt (hΩ0 q hq)
        (by rw [iota_shift]; exact hΩ0 _ h2) (by rw [iota_shift]; exact hΩ0 _ h1)
        (by rw [iota_shift2]; exact hΩ0 _ h3') (shift_comm' _ _ _) (fun _ => 1)
      linarith



theorem coverGeomBoxUTΦ : CoverGeomBoxUTΦ := by
  classical
  intro ell hell
  refine ⟨1, 24 * ell + 25, 7, 1 / 2, by norm_num, fun Fm hFm m hm R hR => ⟨by norm_num, ?_⟩⟩
  haveI : CubeFamOK Fm := hFm
  intro k hk Lu α₀ hα hsα hT S hS Lam hL U hU hloc j w r hj hB
  have hell0 : 0 < ell := by omega
  have hM0 : 0 < ell ^ m := pow_pos hell0 m
  obtain ⟨hcov, hP⟩ := hU
  obtain ⟨hjk, ⟨x₀, hx₀, hw⟩, -⟩ := hB
  have hanti : Antitone S.Om := antitone_nat_of_succ_le hS.1
  set s : ℕ := bigSide (ell ^ m) ell (j - 2) with hsdef
  have hs2 : 2 ≤ s := by
    have h1 : 1 ≤ ell ^ (j - 2) := Nat.one_le_pow _ _ hell0
    have h2 : ell ≤ ell ^ m := by
      calc ell = ell ^ 1 := (pow_one _).symm
        _ ≤ ell ^ m := Nat.pow_le_pow_right hell0 hm
    calc 2 ≤ ell := hell
      _ ≤ ell ^ m := h2
      _ = ell ^ m * 1 := (mul_one _).symm
      _ ≤ ell ^ m * ell ^ (j - 2) := Nat.mul_le_mul_left _ h1
  have hs0 : 0 < s := by omega
  have hN : ∀ τ, s ∣ scaleUp ell k Lu τ + 1 := fun τ => hS.2.2.1 (j - 2) (by omega) τ
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
  have hX1 : Y1 ell (ell ^ m) α₀ j = X * ((ell : ℝ) ^ (j - 2))⁻¹ := rfl
  have hX2 : Y2 ell (ell ^ m) α₀ j = X * (((ell : ℝ) ^ (j - 2))⁻¹) ^ 2 := rfl
  have hU1 : ((ell : ℝ) ^ (j - 2))⁻¹ ≤ 1 :=
    inv_le_one_of_one_le₀ (one_le_pow₀ (by exact_mod_cast hell0))
  have hU1' : 0 ≤ ((ell : ℝ) ^ (j - 2))⁻¹ := by positivity
  rw [hX1, hX2]
  refine ⟨fun c c' hc hc' hcc' => ?_, ?_⟩
  · -- pair charts
    have hrange : ∀ p : Z3, p ∈ cellBox (s : ℤ) (wo w) c ∪ cellBox (s : ℤ) (wo w) c' →
        ∀ μ, wo w μ / (s : ℤ) - ((7 * ell ^ 2 : ℕ) : ℤ) ≤ cellZ (s : ℤ) (wo w) p μ ∧
          cellZ (s : ℤ) (wo w) p μ ≤ wo w μ / (s : ℤ) + ((7 * ell ^ 2 : ℕ) : ℤ) := by
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
      exact (box_pt_nearT hS hell hM0 hj hjk (by omega) hx₀ hw (hrange p hp)).2
    have hWidx : ∀ (sites : Set (PeriodicLatticeSite (scaleUp ell k Lu))) (i : ℕ),
        IsClassCubeQ ell (ell ^ m) Fm k S sites i →
        (∃ y ∈ sites, y ∈ CellReg s (fun τ => (scaleUp ell k Lu τ + 1) / s) (cellU s (scaleUp ell k Lu) c)
          (fun τ => c' τ ≠ c τ)) → s ∣ bigSide (ell ^ m) ell i := by
      rintro sites i hcl ⟨y, hys, hyreg⟩
      obtain ⟨p, hp, hpy⟩ := region_preimage w hs0 hN hnpos hcc' hyreg
      have hq : iota w p ∈ sites := by rw [hpy]; exact hys
      have hi := box_idxTΦ hS hell hM0 hj hjk hR hx₀ hw (hrange p hp) hcl hq
      rw [hsdef]; unfold bigSide
      exact Nat.mul_dvd_mul_left _ (pow_dvd_pow ell hi)
    obtain ⟨sites, i, hcl, hreg⟩ := cellbox_wrapΦ s hs2 hS hcov (fun τ => (scaleUp ell k Lu τ + 1) / s)
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
    have hi := box_idxTΦ hS hell hM0 hj hjk hR hx₀ hw (hrange p₀ (Or.inl hp₀)) hcl (hD p₀ (Or.inl hp₀))
    have hu0 : 0 < ((ell : ℝ) ^ i)⁻¹ := by positivity
    have hu1 : ((ell : ℝ) ^ i)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ (by exact_mod_cast hell0))
    have hsm : X * ((ell : ℝ) ^ i)⁻¹ + X * (((ell : ℝ) ^ i)⁻¹) ^ 2 ≤ 1 := by
      have h2 : (((ell : ℝ) ^ i)⁻¹) ^ 2 ≤ 1 := by nlinarith
      have e1 : X * ((ell : ℝ) ^ i)⁻¹ ≤ X := by nlinarith
      have e2 : X * (((ell : ℝ) ^ i)⁻¹) ^ 2 ≤ X := by nlinarith
      linarith
    obtain ⟨G, hG1, hG2⟩ := cube_C12HΦ hη hP hcl hsm hell0 w _ hD
    have hUi : ((ell : ℝ) ^ i)⁻¹ ≤ ((ell : ℝ) ^ (j - 2))⁻¹ :=
      inv_anti₀ (pow_pos (by exact_mod_cast hell0) _)
        (pow_le_pow_right₀ (by exact_mod_cast (by omega : 1 ≤ ell)) hi)
    obtain ⟨b1, b2, -⟩ := t_bounds hX0 hXh hu0.le hUi hU1
    refine ⟨G, hG1.mono (fun p hp => hp) ?_, hG2.mono (fun p hp => hp) ?_⟩
    · have : 0 ≤ X * ((ell : ℝ) ^ (j - 2))⁻¹ := by positivity
      rw [← hXd]; linarith
    · have : 0 ≤ X * (((ell : ℝ) ^ (j - 2))⁻¹) ^ 2 := by positivity
      rw [← hXd]; linarith
  · -- plaquette bound on the box
    have hrQ : ∀ p : Z3, p ∈ BoxR (s : ℤ) (wo w) (7 * ell ^ 2) →
        ∀ μ, wo w μ / (s : ℤ) - ((7 * ell ^ 2 : ℕ) : ℤ) ≤ cellZ (s : ℤ) (wo w) p μ ∧
          cellZ (s : ℤ) (wo w) p μ ≤ wo w μ / (s : ℤ) + ((7 * ell ^ 2 : ℕ) : ℤ) := fun p hp => hp
    have hΩQ : ∀ p : Z3, p ∈ BoxR (s : ℤ) (wo w) (7 * ell ^ 2) → iota w p ∈ S.Om (j - 1) :=
      fun p hp => (box_pt_nearT hS hell hM0 hj hjk (by omega) hx₀ hw (hrQ p hp)).2
    have key : ∀ (q : Z3) (μ ν : Fin 3), μ < ν → q ∈ BoxR (s : ℤ) (wo w) (7 * ell ^ 2) →
        q + ev μ ∈ BoxR (s : ℤ) (wo w) (7 * ell ^ 2) → q + ev ν ∈ BoxR (s : ℤ) (wo w) (7 * ell ^ 2) →
        q + ev μ + ev ν ∈ BoxR (s : ℤ) (wo w) (7 * ell ^ 2) →
        frobNorm (((hol (Wof U w) q μ ν : SU2) : M2) - 1) ≤ 7 * (X * (((ell : ℝ) ^ (j - 2))⁻¹) ^ 2) := by
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
      have hi := box_idxTΦ hS hell hM0 hj hjk hR hx₀ hw (hrQ q hq) hcl b1.1
      have hu0 : 0 < ((ell : ℝ) ^ i)⁻¹ := by positivity
      have hu1 : ((ell : ℝ) ^ i)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ (by exact_mod_cast hell0))
      have hsm : ((12 : ℕ) : ℝ) * ((ell ^ m : ℕ) : ℝ) * α₀ * ((ell : ℝ) ^ i)⁻¹
          + ((12 : ℕ) : ℝ) * ((ell ^ m : ℕ) : ℝ) * α₀ * (((ell : ℝ) ^ i)⁻¹) ^ 2 ≤ 1 := by
        rw [← hXd]
        have h2' : (((ell : ℝ) ^ i)⁻¹) ^ 2 ≤ 1 := by nlinarith
        have e1 : X * ((ell : ℝ) ^ i)⁻¹ ≤ X := by nlinarith
        have e2 : X * (((ell : ℝ) ^ i)⁻¹) ^ 2 ≤ X := by nlinarith
        linarith
      obtain ⟨g, hg⟩ := gchart_of_cubeHΦ hη hP hcl hsm hell0
      have hpl := plq_near_of_gchart hg (iota w q) μ ν b1.1 b1.2 b3.1 b2.2
      have hc := shift_comm' (iota w q) μ ν
      rw [plq_conj U (fun _ => 1) g (iota w q) μ ν hc, AdalyFormal.M2Glue2.frobNorm_conj_sub_one]
      have hUi : ((ell : ℝ) ^ i)⁻¹ ≤ ((ell : ℝ) ^ (j - 2))⁻¹ :=
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
      simp [AdalyFormal.CoverGeom.frobNorm_zero']
      positivity
    · have h3' : q + ev ν + ev μ ∈ BoxR (s : ℤ) (wo w) (7 * ell ^ 2) := by rw [add_right_comm]; exact h3
      rw [hol_swap, n_inv]
      exact key q ν μ hgt hq h2 h1 h3'



end MXQ.Total
