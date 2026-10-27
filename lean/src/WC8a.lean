import TL5

/-!
# WC8a -- the blocked link at level `l` over a CUBE chart (cutoff-free copy of TL5 `tower_link_loc`)

`tower_link_cube` : `CubeChart` data on the bonds of a set of sites `sites` (clauses 1, 2 of `PerCubeRegular2` at scale index `i`)
and the cone `{w : pdist z w ≤ 14 ℓ^l} ⊆ sites` give
`dv (Ū^l(U^g)(z, μ)) ≤ ℓ^l e + 3π (ℓ²)^l q0`, `e = ρ1/ℓ^i`, `q0 = ρ1/ℓ^{2i}`, `ρ1 = (4π+4) a`.
No cutoff, no global M1 regime: the region is the cube.
No sorry / native_decide / axiom.
-/
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 8000

namespace AdalyFormal.M2W6

open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane (Tower Admissible scaleUp pdist CubeBond)
open AdalyFormal.StatementLaneR8 (pdist_triangle pdist_comm pdist_self pdist_coarseShift_le)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond CoarseLattice mem_CoarseLattice)
open AdalyFormal.Balaban.CoarseCurl (coarseShift)
open AdalyFormal.Balaban.RMapLipschitz (frobNorm)
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
open AdalyFormal.Balaban.SuTwoLogExp (SU2)
open AdalyFormal.CurvBlock (dv pw PlaqT plaqIn CubeChart cube_link cube_plaq link_tower_na_loc GoodBd goodL)
open AdalyFormal.M1DK (goodBd_pd goodL_pd)
open AdalyFormal.TowerLoc (pdist_shift1)

/-- **the blocked link at level `l` over a cube chart** -/
theorem tower_link_cube {ell k : ℕ} {Lu : PeriodicLatticeExtent} (hell2 : 2 ≤ ell) (hell : 0 < ell)
    (hT3 : ∀ μ, 3 ≤ Lu μ + 1) (U : LinkCfg (scaleUp ell k Lu)) (sites : Set (PeriodicLatticeSite (scaleUp ell k Lu)))
    (i : ℕ) {a η : ℝ}
    (K : CubeChart U (fun b : Bond (scaleUp ell k Lu) => CubeBond sites b) η
      (a * (((ell : ℝ) ^ i * η)⁻¹ ^ 1)) (a * (((ell : ℝ) ^ i * η)⁻¹ ^ 2)))
    (hη : 0 < η) (ha0 : 0 ≤ a) (ha1 : a ≤ 1)
    (l : ℕ) (hlk : l < k)
    (hsm : 4000000 * (ell : ℝ) ^ 2 * (((ell : ℝ) ^ 2) ^ l * ((4 * Real.pi + 4) * a / (ell : ℝ) ^ (2 * i))) ≤ 1)
    (z : PeriodicLatticeSite (scaleUp ell k Lu)) (hz : z ∈ CoarseLattice (scaleUp ell k Lu) (ell ^ l)) (μ : Fin 3)
    (hcone : ∀ w, pdist z w ≤ 14 * ell ^ l → w ∈ sites) :
    dv (AdalyFormal.Balaban.BlockedBackground.ubarTowerSU2 ell (periodicGaugeTransform K.g U) l (z, μ))
      ≤ (ell : ℝ) ^ l * ((4 * Real.pi + 4) * a / (ell : ℝ) ^ i)
        + 3 * Real.pi * (((ell : ℝ) ^ 2) ^ l * ((4 * Real.pi + 4) * a / (ell : ℝ) ^ (2 * i))) := by
  have hs1 : 1 ≤ ell ^ l := Nat.one_le_pow _ _ hell
  set ρ1 : ℝ := (4 * Real.pi + 4) * a with hρ1
  have hpi := Real.pi_pos
  have hρ0 : 0 ≤ ρ1 := by rw [hρ1]; positivity
  set q0 : ℝ := ρ1 / (ell : ℝ) ^ (2 * i) with hq0d
  set e : ℝ := ρ1 / (ell : ℝ) ^ i with hed
  have hq0 : 0 ≤ q0 := by positivity
  have hP : (0 : ℝ) < (ell : ℝ) ^ i := pow_pos (by exact_mod_cast hell) i
  have hP1 : (1 : ℝ) ≤ (ell : ℝ) ^ i := one_le_pow₀ (by exact_mod_cast hell)
  have hpow : (ell : ℝ) ^ (2 * i) = ((ell : ℝ) ^ i) ^ 2 := by rw [← pow_mul, mul_comm]
  have e1 : η * (a * (((ell : ℝ) ^ i * η)⁻¹ ^ 1)) = a / (ell : ℝ) ^ i := by field_simp
  have e2 : η ^ 2 * (a * (((ell : ℝ) ^ i * η)⁻¹ ^ 2)) = a / (ell : ℝ) ^ (2 * i) := by
    rw [hpow]; field_simp
  have hsmall : η * (a * (((ell : ℝ) ^ i * η)⁻¹ ^ 1)) ≤ 1 := by
    rw [e1, div_le_one hP]; linarith
  have h0 : ∀ w, (∀ ν μ' : Fin 3, plaqIn (CubeBond sites) (w, ν, μ')) → ∀ ν μ',
      dv (pw 1 (periodicGaugeTransform K.g U) w ν μ') ≤ q0 := by
    intro w hw ν μ'
    have hK := cube_plaq hη K hsmall (w, ν, μ') (hw ν μ')
    have hK' : dv (pw 1 (periodicGaugeTransform K.g U) w ν μ') ≤ 2 * (η ^ 2 * (a * (((ell : ℝ) ^ i * η)⁻¹ ^ 2)))
        + (4 * Real.pi + 2) * (η * (a * (((ell : ℝ) ^ i * η)⁻¹ ^ 1))) ^ 2 := hK
    rw [e2, e1] at hK'
    refine hK'.trans ?_
    have hq : (0 : ℝ) < (ell : ℝ) ^ (2 * i) := by positivity
    have e3 : (a / (ell : ℝ) ^ i) ^ 2 = a ^ 2 / (ell : ℝ) ^ (2 * i) := by rw [hpow]; field_simp
    rw [e3]
    have : 2 * (a / (ell : ℝ) ^ (2 * i)) + (4 * Real.pi + 2) * (a ^ 2 / (ell : ℝ) ^ (2 * i))
        = (2 * a + (4 * Real.pi + 2) * a ^ 2) / (ell : ℝ) ^ (2 * i) := by ring
    rw [this]
    apply div_le_div_of_nonneg_right _ hq.le
    have hsq : a ^ 2 ≤ a := by
      have := mul_le_mul_of_nonneg_left ha1 ha0
      linarith
    have hc : 0 ≤ 4 * Real.pi + 2 := by linarith
    have := mul_le_mul_of_nonneg_left hsq hc
    linarith
  have he : ∀ b, CubeBond sites b → dv (periodicGaugeTransform K.g U b) ≤ e := by
    intro b hb
    have hK := cube_link hη K b hb
    rw [e1] at hK
    refine hK.trans ?_
    apply div_le_div_of_nonneg_right _ hP.le
    have : 1 * a ≤ (4 * Real.pi + 4) * a := mul_le_mul_of_nonneg_right (by linarith) ha0
    linarith
  have hdvd : ∀ ρ, ell ^ l ∣ scaleUp ell k Lu ρ + 1 := fun ρ => by
    rw [AdalyFormal.GaugeCov.scaleUp_succ ell k Lu hell ρ]
    exact Dvd.dvd.mul_left (pow_dvd_pow ell hlk.le) _
  have hN : ∀ ρ, 2 * ell ^ l < scaleUp ell k Lu ρ + 1 := fun ρ => by
    rw [AdalyFormal.GaugeCov.scaleUp_succ ell k Lu hell ρ]
    have h1 : ell ^ l ≤ ell ^ k := Nat.pow_le_pow_right hell hlk.le
    have h2 := Nat.mul_le_mul (hT3 ρ) h1
    omega
  have hBK : ∀ w, pdist z w ≤ 13 * ell ^ l → ∀ d : Fin 3, CubeBond sites (w, d) := by
    intro w hw d
    refine ⟨hcone w (by omega), hcone _ ?_⟩
    have := pdist_shift1 hw d
    show pdist z (coarseShift w 1 d) ≤ 14 * ell ^ l
    omega
  have hgB : GoodBd ell (fun w => ∀ ν μ' : Fin 3, plaqIn (CubeBond sites) (w, ν, μ')) l (z, μ) := by
    refine goodBd_pd ell hell2 (fun w => ∀ ν μ' : Fin 3, plaqIn (CubeBond sites) (w, ν, μ')) l _ hz hdvd (fun w hw0 => fun ν μ' => ?_)
    have hw : pdist z w ≤ 12 * ell ^ l := hw0
    have hw1 : ∀ d, pdist z (coarseShift w 1 d) ≤ 13 * ell ^ l := fun d => by
      have := pdist_shift1 hw d; omega
    exact ⟨hBK w (by omega) ν, hBK _ (hw1 ν) μ', hBK _ (hw1 μ') ν, hBK w (by omega) μ'⟩
  have hgL : goodL ell (CubeBond sites) l (z, μ) := by
    refine goodL_pd ell hell2 (CubeBond sites) l _ (fun b _ hb => ?_)
    have hb' : pdist z b.1 ≤ 13 * ell ^ l := by
      have : pdist (z, μ).1 b.1 ≤ ell ^ l := hb
      simp only at this; omega
    exact hBK b.1 hb' b.2
  exact link_tower_na_loc ell hell2 (periodicGaugeTransform K.g U)
    (fun w => ∀ ν μ' : Fin 3, plaqIn (CubeBond sites) (w, ν, μ')) (CubeBond sites) q0 e hq0 h0 he l hdvd hN hsm l le_rfl _ hz hgB hgL

end AdalyFormal.M2W6

#print axioms AdalyFormal.M2W6.tower_link_cube
