import CG1
import CG3
import CG4a
import M2B8

/-!
# CG4b -- collar / index lemmas and the transfer of a class-cube gauge chart to ball coordinates (lane cover_geom)
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false

namespace AdalyFormal.CoverGeom

open AdalyFormal.Target.ClayStatement AdalyFormal.StatementLane AdalyFormal.StatementLane2
open AdalyFormal.StatementLaneR8 (Ball pdist_comm pdist_triangle)
open AdalyFormal.M2Glue3 (Z3 ev iota iota_shift iota_shift2)
open AdalyFormal.M2Glue2 (GChart)
open AdalyFormal.Balaban.SuTwoLogExp (SU2 M2)
open AdalyFormal.Balaban.RMapLipschitz (frobNorm)
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
open AdalyFormal.UnifLane.Z (Wof gt_iota C1 C2 gt)
open AdalyFormal.M2Bridge (pdist_lt_three_s')
open AdalyFormal.M2BallCharts (iota_mem_ball Bz plq plq_conj)

variable {L : PeriodicLatticeExtent}

/-- collar, general radius. -/
theorem near_Om_gen {ell M R k j : ℕ} {S : Tower L} (hadm : Admissible ell M R k S) (hj1 : 1 ≤ j) (hjk : j ≤ k)
    {w x₀ p : PeriodicLatticeSite L} {P : ℕ} (hx₀ : x₀ ∈ S.Om j)
    (hw : pdist w x₀ ≤ 3 * (M * ell ^ j)) (hp : pdist w p ≤ P)
    (hbig : P + 3 * (M * ell ^ j) < R * (M * ell ^ (j - 1)) + 1) : p ∈ S.Om (j - 1) := by
  by_contra hnot
  have h5 := hadm.2.2.2.2.1 (j - 1) (by omega) p hnot x₀ (by
    have : j - 1 + 1 = j := by omega
    rw [this]; exact hx₀)
  have htri : pdist p x₀ ≤ pdist p w + pdist w x₀ := pdist_triangle p w x₀
  rw [pdist_comm p w] at htri
  unfold bigSide at h5
  omega

/-- no class cube of index `j-2` reaches a point of `Ω_{j-1}` near `w` (collar). -/
theorem idx_ge {ell M R c k j : ℕ} {S : Tower L} (hadm : Admissible ell M R k S) (hj1 : 1 ≤ j) (hjk : j ≤ k)
    {sites : Set (PeriodicLatticeSite L)} {i : ℕ} (hq : IsClassCube ell M c k S sites i)
    {q w x₀ : PeriodicLatticeSite L} {P : ℕ} (hqs : q ∈ sites) (hqΩ : q ∈ S.Om (j - 1))
    (hx₀ : x₀ ∈ S.Om j) (hw : pdist w x₀ ≤ 3 * (M * ell ^ j)) (hqw : pdist w q ≤ P)
    (hbig : P + 3 * (M * ell ^ j) + 3 * (c * (M * ell ^ (j - 2))) < R * (M * ell ^ (j - 1)) + 1) :
    j - 1 ≤ i := by
  have hji := classCube_index_ge hadm.1 hq hqs hqΩ
  by_contra hlt
  have hi : i + 2 = j := by omega
  have hq' := hq
  obtain ⟨⟨hik, ⟨z, hgrid, hsites⟩, hsub, ⟨y, hys, hyB⟩⟩, -⟩ := hq'
  have hy1 : y ∉ S.Om (j - 1) := by
    have : i + 1 = j - 1 := by omega
    rw [← this]; exact hyB.2
  have h5 := hadm.2.2.2.2.1 (j - 1) (by omega) y hy1 x₀ (by
    have : j - 1 + 1 = j := by omega
    rw [this]; exact hx₀)
  have hyq : pdist y q < 3 * (c * bigSide M ell i) := by
    rw [hsites] at hys hqs
    exact pdist_lt_three_s' hys hqs
  have htri1 : pdist y x₀ ≤ pdist y q + pdist q x₀ := pdist_triangle y q x₀
  have htri2 : pdist q x₀ ≤ pdist q w + pdist w x₀ := pdist_triangle q w x₀
  rw [pdist_comm q w] at htri2
  have hbi : bigSide M ell i = M * ell ^ (j - 2) := by unfold bigSide; congr 2; omega
  unfold bigSide at h5
  rw [hbi] at hyq
  omega

theorem pdist_iota_le (w : PeriodicLatticeSite L) (p : Z3) :
    pdist w (iota w p) ≤ (p 0).natAbs + (p 1).natAbs + (p 2).natAbs := by
  have hb : p ∈ Bz ((p 0).natAbs + (p 1).natAbs + (p 2).natAbs) := by
    show (p 0).natAbs + (p 1).natAbs + (p 2).natAbs ≤ (p 0).natAbs + (p 1).natAbs + (p 2).natAbs
    exact le_refl _
  exact iota_mem_ball (w := w) hb

/-- **class cube ⇒ ℤ³ charts (clauses 1 and 2) on any set of ball coordinates whose torus images lie in the cube.** -/
theorem cube_C12 {ell M f k : ℕ} {S : Tower L} {α₀ η : ℝ} (hη : 0 < η)
    {U : LinkCfg L} (hP : PerCubeRegular2 ell M f k S α₀ η U)
    {sites : Set (PeriodicLatticeSite L)} {i : ℕ} (hq : IsClassCube ell M f k S sites i)
    (hsm : (f : ℝ) * M * α₀ * ((ell : ℝ) ^ i)⁻¹ + (f : ℝ) * M * α₀ * (((ell : ℝ) ^ i)⁻¹) ^ 2 ≤ 1)
    (hell : 0 < ell) (w : PeriodicLatticeSite L) (D : Set Z3) (hD : ∀ p ∈ D, iota w p ∈ sites) :
    ∃ G : Z3 → SU2, C1 (Wof U w) G D ((f : ℝ) * M * α₀ * ((ell : ℝ) ^ i)⁻¹) ∧
      C2 (Wof U w) G D ((1 + 4 * ((f : ℝ) * M * α₀ * ((ell : ℝ) ^ i)⁻¹)) * ((f : ℝ) * M * α₀ * (((ell : ℝ) ^ i)⁻¹) ^ 2)) := by
  obtain ⟨g, hg1, hg2⟩ := AdalyFormal.M2Glue2.gchart_of_cube hη hP hq hsm hell
  refine ⟨fun p => g (iota w p), ?_, ?_⟩
  · intro p ν hp hpν
    rw [gt_iota]
    exact hg1 (iota w p) ν (hD p hp) (by rw [iota_shift]; exact hD _ hpν)
  · intro p μ ν hp hpν hpμ hpμν
    have e1 : ∀ q, gt (Wof U w) (fun q => g (iota w q)) q ν = periodicGaugeTransform g U (iota w q, ν) := fun q => gt_iota U w g q ν
    rw [e1, e1]
    refine hg2 (iota w p) μ ν (hD p hp) (by rw [iota_shift]; exact hD _ hpν) (by rw [iota_shift]; exact hD _ hpμ)
      (by rw [iota_shift2]; exact hD _ hpμν) |> fun h => ?_
    rw [iota_shift] at h
    exact h

end AdalyFormal.CoverGeom
