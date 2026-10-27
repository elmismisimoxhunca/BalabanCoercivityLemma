import BLC6
import AC_BLC5
import AC_Base

/-! AC copy of BLC6: affected declarations only (lane allc_20261016); 12 literal kept (control build). -/
set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace AdalyFormal.M2BallCharts

open AdalyFormal.AllC
variable {fc : ℕ} [CubeFactor fc]

open AdalyFormal.Target.ClayStatement AdalyFormal.M2Glue3 AdalyFormal.M2Glue2 AdalyFormal.M2GlueGeo
open AdalyFormal.StatementLane AdalyFormal.StatementLane2
open AdalyFormal.StatementLaneR8 (Ball)
open AdalyFormal.Balaban.SuTwoLogExp (SU2 M2)
open AdalyFormal.Balaban.RMapLipschitz (frobNorm)

variable {L : PeriodicLatticeExtent}

theorem ball_chart_posAC {ell M R k : ℕ} {S : Tower L} (hS : Admissible ell M R k S)
    (hcov : CoversOm0p ell M fc k S) (hell : 2 ≤ ell) (hM : 24 ≤ M) {j : ℕ} (hj1 : 1 ≤ j) (hjk : j ≤ k)
    {x0 : PeriodicLatticeSite L} (hx0 : x0 ∈ S.Om j) {w : PeriodicLatticeSite L} (hw : pdist w x0 ≤ 3 * (M * ell ^ j))
    {r : ℕ} (hr7 : r ≤ 7 * M * ell ^ j) (hnw : ∀ σ : Fin 3, 2 * r + 2 ≤ L σ + 1) (hR : 45 * ell + 30 + 2 * fc ≤ R)
    {α₀ η : ℝ} (hη : 0 < η) (hα : 0 ≤ α₀) {U : LinkCfg L} (hP : PerCubeRegular2H ell M fc 12 k S α₀ η U)
    (hX : (12 : ℝ) * M * α₀ ≤ Xthr ell M) :
    ∃ g : PeriodicLatticeSite L → SU2, GChart U g (Ball w r)
      (CC ell M * ((12 : ℝ) * M * α₀ * ((ell : ℝ) ^ (j - 1))⁻¹))
      (CC ell M * ((12 : ℝ) * M * α₀ * (((ell : ℝ) ^ (j - 1))⁻¹) ^ 2)) := by
  set s := bigSide M ell (j - 1) with hsdef
  set X : ℝ := (12 : ℝ) * M * α₀ with hXdef
  set u : ℝ := ((ell : ℝ) ^ (j - 1))⁻¹ with hudef
  have hL : ∀ μ, 2 * r + 1 < L μ + 1 := fun μ => by have := hnw μ; omega
  have hM0 : 0 < M := by omega
  have hM' : (0 : ℝ) < M := by exact_mod_cast hM0
  have hell0 : (0 : ℝ) < ell := by exact_mod_cast (show 0 < ell by omega)
  have hs24 : 24 ≤ s := by
    have : M ≤ s := by rw [hsdef, bigSide]; exact Nat.le_mul_of_pos_right _ (pow_pos (by omega) _)
    omega
  have hpow : (0 : ℝ) < (ell : ℝ) ^ (j - 1) := by positivity
  have hu0 : 0 < u := by positivity
  have hu1 : u ≤ 1 := by
    rw [hudef]; exact inv_le_one_of_one_le₀ (one_le_pow₀ (by exact_mod_cast (show 1 ≤ ell by omega)))
  have hsu : (s : ℝ) * u = M := by
    rw [hsdef, bigSide, hudef]; push_cast; field_simp
  have hMl : M * ell ^ j = ell * s := by
    rw [hsdef, bigSide]
    have : ell ^ j = ell * ell ^ (j - 1) := by rw [← pow_succ']; congr 1; omega
    rw [this]; ring
  have hr : r ≤ 7 * ell * s := by
    have : 7 * M * ell ^ j = 7 * ell * s := by rw [mul_assoc, hMl]; ring
    omega
  have hX0 : 0 ≤ X := by positivity
  obtain ⟨c1, c2, c3, c4, c5, c6, c7, c8⟩ := consts_nonneg ell M
  have hcb : 0 ≤ cB 1152 5 := by unfold cB; positivity
  -- the threshold pieces
  have t47 : X ≤ 1 / 47 := hX.trans (min_le_left _ _)
  have tsm : X ≤ 1 / (18 * (4 * cB 1152 5 + 1) * (M : ℝ) ^ 2) := hX.trans ((min_le_right _ _).trans (min_le_left _ _))
  have tc1 : X ≤ 2 / (1 + cτ ell M (a1 M)) :=
    hX.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have tc2 : X ≤ 2 / (1 + cτ ell M (a2 ell M)) :=
    hX.trans ((min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))))
  have tc3 : X ≤ 2 / (1 + cτ ell M (a3 ell M)) :=
    hX.trans ((min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))))
  have hX1 : X ≤ 1 := by linarith
  -- vertex constants
  have hFv : Fv ell M (j - 1) α₀ ≤ 2 * X * u ^ 2 := by
    unfold Fv
    rw [← hXdef, ← hudef]
    have hXu : X * u ≤ X := by nlinarith
    nlinarith [mul_nonneg hX0 (sq_nonneg u)]
  have hFv0 : 0 ≤ Fv ell M (j - 1) α₀ := by unfold Fv; rw [← hXdef, ← hudef]; positivity
  have hR3 : (3 * ((s - 4 : ℕ) : ℝ) + 2) ≤ 3 * s := by
    have : ((s - 4 : ℕ) : ℝ) = (s : ℝ) - 4 := by push_cast [Nat.cast_sub (show 4 ≤ s by omega)]; ring
    rw [this]; linarith
  have hR30 : 0 ≤ (3 * ((s - 4 : ℕ) : ℝ) + 2) := by positivity
  have hv1 : KT1 4 1152 * (3 * ((s - 4 : ℕ) : ℝ) + 2) * Fv ell M (j - 1) α₀ ≤ a1 M * X * u := by
    have k1 := KT1_nonneg
    calc KT1 4 1152 * (3 * ((s - 4 : ℕ) : ℝ) + 2) * Fv ell M (j - 1) α₀
        ≤ KT1 4 1152 * (3 * s) * (2 * X * u ^ 2) := by gcongr
      _ = 6 * KT1 4 1152 * ((s : ℝ) * u) * X * u := by ring
      _ = a1 M * X * u := by rw [hsu]; unfold a1; ring
  have hv2 : KT2 4 1152 * Fv ell M (j - 1) α₀ ≤ b1 * X * u ^ 2 := by
    have k2 := KT2_nonneg
    calc KT2 4 1152 * Fv ell M (j - 1) α₀ ≤ KT2 4 1152 * (2 * X * u ^ 2) := by gcongr
      _ = b1 * X * u ^ 2 := by unfold b1; ring
  have hsmall : (4 * cB 1152 5 + 1) * (3 * ((s - 4 : ℕ) : ℝ) + 2) ^ 2 * Fv ell M (j - 1) α₀ ≤ 1 := by
    have hq : (3 * ((s - 4 : ℕ) : ℝ) + 2) ^ 2 ≤ (3 * s) ^ 2 := pow_le_pow_left₀ hR30 hR3 2
    calc (4 * cB 1152 5 + 1) * (3 * ((s - 4 : ℕ) : ℝ) + 2) ^ 2 * Fv ell M (j - 1) α₀
        ≤ (4 * cB 1152 5 + 1) * (3 * s) ^ 2 * (2 * X * u ^ 2) := by gcongr
      _ = 18 * (4 * cB 1152 5 + 1) * ((s : ℝ) * u) ^ 2 * X := by ring
      _ = 18 * (4 * cB 1152 5 + 1) * (M : ℝ) ^ 2 * X := by rw [hsu]
      _ ≤ 1 := by
        have hpos : 0 < 18 * (4 * cB 1152 5 + 1) * (M : ℝ) ^ 2 := by positivity
        rw [le_div_iff₀ hpos] at tsm; linarith
  have hsm : X * u + X * u ^ 2 ≤ 1 := by nlinarith
  have ht12 : X * u ≤ 2 := by nlinarith
  -- level 0: vertex charts
  have hV : ∀ n : Fin 3 → ℕ, ∃ g : PeriodicLatticeSite L → SU2,
      ZCh U g w (Ib r s (qv r s w n) (insert (0 : Fin 3) ({1, 2} : Finset (Fin 3))))
        (fun _ => a1 M * X * u) (fun _ => b1 * X * u ^ 2) := by
    intro n
    have huniv : insert (0 : Fin 3) ({1, 2} : Finset (Fin 3)) = Finset.univ := by decide
    rw [huniv]
    obtain ⟨g, hg⟩ := vertex_zchAC hS hcov hell hM0 hj1 hjk hx0 hw hr7 hR hs24 hη hα hP
      (by rw [← hXdef, ← hudef]; exact hsm) (by rw [← hXdef, ← hudef]; exact ht12) hsmall n
    exact ⟨g, zch_mono hg subset_rfl hv1 hv2⟩
  -- level 1: rows (σ = 0, T = {1,2})
  have hL1 : ∀ n : Fin 3 → ℕ, ∃ g : PeriodicLatticeSite L → SU2,
      ZCh U g w (Ib r s (qv r s w n) (insert (1 : Fin 3) ({2} : Finset (Fin 3))))
        (fun _ => a2 ell M * X * u) (fun _ => b2 ell M * X * u ^ 2) := by
    intro n
    have he : insert (1 : Fin 3) ({2} : Finset (Fin 3)) = ({1, 2} : Finset (Fin 3)) := by decide
    rw [he]
    exact level_scaled hL hs24 hM0 hr w 0 {1, 2} (by decide) hX0 hX1 hu0.le hsu c1 c2
      (cτ_small c1 hX0 tc1) hV n
  -- level 2: slabs (σ = 1, T = {2})
  have hL2 : ∀ n : Fin 3 → ℕ, ∃ g : PeriodicLatticeSite L → SU2,
      ZCh U g w (Ib r s (qv r s w n) (insert (2 : Fin 3) (∅ : Finset (Fin 3))))
        (fun _ => a3 ell M * X * u) (fun _ => b3 ell M * X * u ^ 2) := by
    intro n
    have he : insert (2 : Fin 3) (∅ : Finset (Fin 3)) = ({2} : Finset (Fin 3)) := by decide
    rw [he]
    exact level_scaled hL hs24 hM0 hr w 1 {2} (by decide) hX0 hX1 hu0.le hsu c3 c4
      (cτ_small c3 hX0 tc2) hL1 n
  -- level 3: the box (σ = 2, T = ∅)
  obtain ⟨G, hG⟩ := level_scaled hL hs24 hM0 hr w 2 ∅ (by decide) hX0 hX1 hu0.le hsu c5 c6
    (cτ_small c5 hX0 tc3) hL2 (fun _ => 0)
  -- to sites, then to the ball
  have hGs := gchart_sub_of_zch (v := w) hL (S := Box r) subset_rfl (P := fun _ => True)
    (T := Ib r s (qv r s w (fun _ => 0)) ∅) (fun p hp _ => mem_Ib.mpr ⟨hp, fun i hi => absurd hi (Finset.notMem_empty i)⟩) hG
  refine ⟨G, hGs.mono (fun x hx => ⟨ball_sub_lift w r hx, trivial⟩) ?_ ?_⟩
  · have : aF ell M * X * u ≤ CC ell M * (X * u) := by
      unfold CC; have : 0 ≤ X * u := by positivity
      nlinarith
    exact this
  · have : bF ell M * X * u ^ 2 ≤ CC ell M * (X * u ^ 2) := by
      unfold CC; have : 0 ≤ X * u ^ 2 := by positivity
      nlinarith
    exact this

end AdalyFormal.M2BallCharts

