import MXQ_G
import MXQ_Orig
import UMZ
import UW12

/-!
# TT_Z -- `BallChartsGT` (ball charts, constants before the cube factor `fc >= 10`) from the cube-factor-free interface (lane total_20261017)

Text copies of `UMZ` (`BallChartsGUJH`, `ballChartsGUH_of_split`, `ballChartsGUJH_le1`) with `ClassFamUH ell fc` replaced by `ClassFamT ell`, and a NEW
`ballChartsGUJT_ge2` for the interface `CoverGeomBoxUT` (cells of side `b_{j-2}`, `7 ℓ²` cells): chart constant
`C = ℓ² · Kst^{2n} (Kst^{2n} (Kst^{2n} c))`, `n = 7 ℓ²`, threshold `min s_G (1/C)`, `m₁' = max m₁ 1`; all depend on `ℓ` and the interface constant only.
-/
set_option autoImplicit false
set_option maxHeartbeats 16000000

namespace MXQ.Total
open MXQ.AllC (CF CubeFamOK)
open AdalyFormal.Total

open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane (Tower Admissible scaleUp TorusOK pdist bigSide)
open AdalyFormal.StatementLane2 (ClassCoupled)
open AdalyFormal.StatementLaneG (LambdaOK2)
open AdalyFormal.StatementLaneR8 (Ball)
open AdalyFormal.M2Glue3 (Z3 ev)
open AdalyFormal.M2Glue2 (GChart GChart.mono)
open AdalyFormal.M2BallCharts (Bz)
open AdalyFormal.Balaban.SuTwoLogExp (SU2 M2)
open AdalyFormal.Balaban.RMapLipschitz (frobNorm)
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
open AdalyFormal.UnifLane.Z

/-- `BallChartsGU` restricted to the levels with `P j`. -/
def BallChartsGUJT (P : ℕ → Prop) : Prop :=
  ∀ (ell : ℕ), 2 ≤ ell →
    ClassFamT ell ℝ (fun _ _ C => 1 ≤ C) (fun M _ k _ C S Lam U α₀ => BallChartsAtGJ P ell M k S U C α₀)

/-- **the two halves give the residual.** -/
theorem ballChartsGT_of_split (h1 : BallChartsGUJT (· ≤ 1)) (h2 : BallChartsGUJT (2 ≤ ·)) : BallChartsGT := by
  intro ell hell
  obtain ⟨m₁, R₁, C₁, s₁, hs₁, hf₁⟩ := h1 ell hell
  obtain ⟨m₂, R₂, C₂, s₂, hs₂, hf₂⟩ := h2 ell hell
  refine ⟨max m₁ m₂, max R₁ R₂, max C₁ C₂, min s₁ s₂, lt_min hs₁ hs₂, fun Fm hFm m hm R hR => ⟨?_, ?_⟩⟩
  · exact le_max_of_le_left (hf₁ Fm hFm m (le_of_max_le_left hm) R (le_of_max_le_left hR)).1
  intro k hk Lu α₀ hα hsα hT S hS Lam hL U hU hloc
  refine ballChartsAtG_of_J (fun j w r hB => ?_)
  rcases le_or_gt j 1 with hj | hj
  · obtain ⟨-, hf⟩ := hf₁ Fm hFm m (le_of_max_le_left hm) R (le_of_max_le_left hR)
    obtain ⟨g, hg⟩ := hf k hk Lu α₀ hα (hsα.trans (min_le_left _ _)) hT S hS Lam hL U hU hloc j w r hj hB
    exact ⟨g, hg.mono subset_rfl (mul_le_mul_of_nonneg_right (le_max_left _ _) (X1_nonneg hα.le j))
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (X2_nonneg hα.le j))⟩
  · obtain ⟨-, hf⟩ := hf₂ Fm hFm m (le_of_max_le_right hm) R (le_of_max_le_right hR)
    obtain ⟨g, hg⟩ := hf k hk Lu α₀ hα (hsα.trans (min_le_right _ _)) hT S hS Lam hL U hU hloc j w r hj hB
    exact ⟨g, hg.mono subset_rfl (mul_le_mul_of_nonneg_right (le_max_right _ _) (X1_nonneg hα.le j))
      (mul_le_mul_of_nonneg_right (le_max_right _ _) (X2_nonneg hα.le j))⟩

/-- **`BallChartsGU` for `j ≤ 1` from the interface.** -/
theorem ballChartsGUJT_le1 (hCG : CoverGeomUTΦ) : BallChartsGUJT (· ≤ 1) := by
  intro ell hell
  obtain ⟨m₁, R₁, c, sG, hsG, hF⟩ := hCG ell hell
  have hc1 : 1 ≤ c := (hF (MXQ.AllC.famC 10) (MXQ.AllC.famC_ok' le_rfl) m₁ le_rfl R₁ le_rfl).1
  set C : ℝ := 2 * (1 + 6 * ((7 * ell : ℕ) : ℝ)) ^ 3 * c with hC
  have hCc : 1 ≤ C := by
    have h7 : (0 : ℝ) ≤ ((7 * ell : ℕ) : ℝ) := Nat.cast_nonneg _
    have h1 : (1 : ℝ) ≤ 1 + 6 * ((7 * ell : ℕ) : ℝ) := by linarith
    have : (1 : ℝ) ≤ (1 + 6 * ((7 * ell : ℕ) : ℝ)) ^ 3 := one_le_pow₀ h1
    rw [hC]; nlinarith
  refine ⟨m₁, R₁, C, sG, hsG, fun Fm hFm m hm R hR => ⟨hCc, ?_⟩⟩
  intro k hk Lu α₀ hα hsα hT S hS Lam hLam U hU hloc j w r hj hB
  have hCZ := (hF Fm hFm m hm R hR).2 k hk Lu α₀ hα hsα hT S hS Lam hLam U hU hloc j w r hj hB
  obtain ⟨hcells, hhol⟩ := hCZ
  have hj0 : j - 1 = 0 := by omega
  have hX1 : X1 ell (ell ^ m) α₀ j = ((12 : ℕ) : ℝ) * ((ell ^ m : ℕ) : ℝ) * α₀ := by
    unfold X1; rw [hj0]; simp
  have hX2 : X2 ell (ell ^ m) α₀ j = ((12 : ℕ) : ℝ) * ((ell ^ m : ℕ) : ℝ) * α₀ := by
    unfold X2; rw [hj0]; simp
  set X : ℝ := ((12 : ℕ) : ℝ) * ((ell ^ m : ℕ) : ℝ) * α₀ with hXd
  have hX0 : 0 ≤ X := by positivity
  have hs : (0 : ℤ) < ((bigSide (ell ^ m) ell (j - 1) : ℕ) : ℤ) := by
    have : 0 < bigSide (ell ^ m) ell (j - 1) := Nat.mul_pos (pow_pos (by omega) m) (pow_pos (by omega) _)
    exact_mod_cast this
  have hrn : (r : ℤ) ≤ ((7 * ell : ℕ) : ℤ) * ((bigSide (ell ^ m) ell (j - 1) : ℕ) : ℤ) := by
    obtain ⟨-, -, hr7, -⟩ := hB
    have hpj : ell ^ j ≤ ell := by
      rcases Nat.lt_or_ge j 1 with h | h
      · have : j = 0 := by omega
        subst this; simp; omega
      · have : j = 1 := by omega
        subst this; simp
    have hb : bigSide (ell ^ m) ell (j - 1) = ell ^ m := by simp [bigSide, hj0]
    rw [hb]
    have : r ≤ 7 * ell * ell ^ m := by
      calc r ≤ 7 * ell ^ m * ell ^ j := hr7
        _ ≤ 7 * ell ^ m * ell := Nat.mul_le_mul_left _ hpj
        _ = 7 * ell * ell ^ m := by ring
    exact_mod_cast this
  have hcellc : ∀ cc : Z3, ∃ G, C1 (Wof U w) G {p | p ∈ Bz r ∧ ∀ μ,
      cellZ ((bigSide (ell ^ m) ell (j - 1) : ℕ) : ℤ) (wo w) p μ = cc μ} (c * X) := by
    intro cc
    obtain ⟨G, hG1⟩ := hcells cc
    rw [hX1] at hG1
    exact ⟨G, hG1⟩
  rw [hX2] at hhol
  have hcX : 0 ≤ c * X := by positivity
  obtain ⟨G, hG⟩ := ball_chart1 (Wof U w) hs (wo w) hrn hcX hcX hhol hcellc
  have hT3 := T3_le (n := 7 * ell) (le_refl (c * X)) (le_refl (c * X)) hcX hcX
  have hL : ∀ μ, 2 * r + 1 < scaleUp ell k Lu μ + 1 := fun μ => by have := hB.2.2.2.1 μ; omega
  obtain ⟨g, hg⟩ := gchart_of_C12 U w hL hG (C2_of_C1 hG)
  refine ⟨g, hg.mono subset_rfl ?_ ?_⟩
  · calc _ ≤ (1 + 6 * ((7 * ell : ℕ) : ℝ)) ^ 3 * (c * X) := hT3
      _ ≤ C * X := by rw [hC]; nlinarith [pow_pos (show (0 : ℝ) < 1 + 6 * ((7 * ell : ℕ) : ℝ) by positivity) 3]
      _ = C * X1 ell (ell ^ m) α₀ j := by rw [hX1]
  · calc _ ≤ 2 * ((1 + 6 * ((7 * ell : ℕ) : ℝ)) ^ 3 * (c * X)) := by linarith
      _ = C * X := by rw [hC]; ring
      _ = C * X2 ell (ell ^ m) α₀ j := by rw [hX2]

/-- **`BallChartsGU` for `j ≥ 2` from the cube-factor-free interface.** -/
theorem ballChartsGUJT_ge2 (hCB : CoverGeomBoxUTΦ) : BallChartsGUJT (2 ≤ ·) := by
  intro ell hell
  obtain ⟨m₁, R₁, c, sG, hsG, hF⟩ := hCB ell hell
  have hc1 : 1 ≤ c := (hF (MXQ.AllC.famC 10) (MXQ.AllC.famC_ok' le_rfl) m₁ le_rfl R₁ le_rfl).1
  have hK := one_le_Kst
  have hell0 : 0 < ell := by omega
  have hKp : (1 : ℝ) ≤ Kst ^ (2 * (7 * ell ^ 2)) := one_le_pow₀ hK
  set K3 : ℝ := Kst ^ (2 * (7 * ell ^ 2)) * (Kst ^ (2 * (7 * ell ^ 2)) * (Kst ^ (2 * (7 * ell ^ 2)) * c)) with hK3
  have hK31 : 1 ≤ K3 := by
    have a1 : 1 ≤ Kst ^ (2 * (7 * ell ^ 2)) * c := by nlinarith
    have a2 : 1 ≤ Kst ^ (2 * (7 * ell ^ 2)) * (Kst ^ (2 * (7 * ell ^ 2)) * c) := by nlinarith
    rw [hK3]; nlinarith
  have hl1 : (1 : ℝ) ≤ (ell : ℝ) ^ 2 := one_le_pow₀ (by exact_mod_cast hell0)
  set C : ℝ := (ell : ℝ) ^ 2 * K3 with hC
  have hC1 : 1 ≤ C := by rw [hC]; nlinarith
  have hC0 : 0 < C := by linarith
  refine ⟨max m₁ 1, R₁, C, min sG (1 / C), lt_min hsG (by positivity), fun Fm hFm m hm R hR => ⟨hC1, ?_⟩⟩
  have hm1 : 1 ≤ m := le_trans (le_max_right _ _) hm
  have hmm : m₁ ≤ m := le_trans (le_max_left _ _) hm
  intro k hk Lu α₀ hα hsα hT S hS Lam hLam U hU hloc j w r hj hB
  obtain ⟨hcells, hhol⟩ := (hF Fm hFm m hmm R hR).2 k hk Lu α₀ hα (hsα.trans (min_le_left _ _)) hT S hS Lam hLam U hU hloc
    j w r hj hB
  have hq1 : 1 ≤ ell ^ (j - 2) := Nat.one_le_pow _ _ hell0
  have hM2 : 2 ≤ ell ^ m := by
    calc 2 ≤ ell := hell
      _ = ell ^ 1 := (pow_one ell).symm
      _ ≤ ell ^ m := Nat.pow_le_pow_right hell0 hm1
  have hsz : (2 : ℤ) ≤ ((bigSide (ell ^ m) ell (j - 2) : ℕ) : ℤ) := by
    have : 2 ≤ bigSide (ell ^ m) ell (j - 2) := by
      unfold bigSide
      calc 2 ≤ ell ^ m := hM2
        _ = ell ^ m * 1 := (mul_one _).symm
        _ ≤ ell ^ m * ell ^ (j - 2) := Nat.mul_le_mul_left _ hq1
    exact_mod_cast this
  have hs0 : (0 : ℤ) < ((bigSide (ell ^ m) ell (j - 2) : ℕ) : ℤ) := by omega
  set Y := Y2 ell (ell ^ m) α₀ j with hYd
  have hqpos : (0 : ℝ) < ((ell ^ (j - 2) : ℕ) : ℝ) := by exact_mod_cast (show 0 < ell ^ (j - 2) by omega)
  have hY1 : Y1 ell (ell ^ m) α₀ j = ((ell ^ (j - 2) : ℕ) : ℝ) * Y := by
    rw [hYd]; unfold Y1 Y2
    have e : ((ell ^ (j - 2) : ℕ) : ℝ) = (ell : ℝ) ^ (j - 2) := by push_cast; ring
    rw [e] at hqpos ⊢
    field_simp
  have hqY : ((ell ^ (j - 2) : ℕ) : ℝ) * ((ell ^ (j - 2) : ℕ) : ℝ) * Y = (12 : ℝ) * ((ell ^ m : ℕ) : ℝ) * α₀ := by
    rw [hYd]; unfold Y2
    have e : ((ell ^ (j - 2) : ℕ) : ℝ) = (ell : ℝ) ^ (j - 2) := by push_cast; ring
    rw [e] at hqpos ⊢
    field_simp
    push_cast; ring
  have hY : 0 ≤ Y := by rw [hYd]; unfold Y2; positivity
  have hsm : K3 * ((ell ^ (j - 2) : ℕ) : ℝ) * ((ell ^ (j - 2) : ℕ) : ℝ) * Y ≤ 1 := by
    have h12 : (12 : ℝ) * ((ell ^ m : ℕ) : ℝ) * α₀ ≤ 1 / C := hsα.trans (min_le_right _ _)
    have h12' : (12 : ℝ) * ((ell ^ m : ℕ) : ℝ) * α₀ * C ≤ 1 := by
      rw [le_div_iff₀ hC0] at h12; exact h12
    have hX0 : 0 ≤ (12 : ℝ) * ((ell ^ m : ℕ) : ℝ) * α₀ := by positivity
    have e : K3 * ((ell ^ (j - 2) : ℕ) : ℝ) * ((ell ^ (j - 2) : ℕ) : ℝ) * Y
        = K3 * ((12 : ℝ) * ((ell ^ m : ℕ) : ℝ) * α₀) := by rw [← hqY]; ring
    rw [e]
    have : K3 * ((12 : ℝ) * ((ell ^ m : ℕ) : ℝ) * α₀) ≤ C * ((12 : ℝ) * ((ell ^ m : ℕ) : ℝ) * α₀) := by
      rw [hC]; nlinarith [mul_nonneg (mul_nonneg hX0 (by linarith : (0:ℝ) ≤ K3)) (sub_nonneg.2 hl1)]
    calc _ ≤ C * ((12 : ℝ) * ((ell ^ m : ℕ) : ℝ) * α₀) := this
      _ = (12 : ℝ) * ((ell ^ m : ℕ) : ℝ) * α₀ * C := mul_comm _ _
      _ ≤ 1 := h12'
  have hcell : ∀ cc : Z3, (∀ μ, wo w μ / ((bigSide (ell ^ m) ell (j - 2) : ℕ) : ℤ) - ((7 * ell ^ 2 : ℕ) : ℤ) ≤ cc μ ∧
      cc μ ≤ wo w μ / ((bigSide (ell ^ m) ell (j - 2) : ℕ) : ℤ) + ((7 * ell ^ 2 : ℕ) : ℤ)) →
      ∃ G : Z3 → SU2, C1 (Wof U w) G (cellBox ((bigSide (ell ^ m) ell (j - 2) : ℕ) : ℤ) (wo w) cc)
          (c * (((ell ^ (j - 2) : ℕ) : ℝ) * Y)) ∧
        C2 (Wof U w) G (cellBox ((bigSide (ell ^ m) ell (j - 2) : ℕ) : ℤ) (wo w) cc) (c * Y) := by
    intro cc hcc
    obtain ⟨G, g1, g2⟩ := hcells cc cc hcc hcc (Or.inl rfl)
    rw [Set.union_self] at g1 g2
    rw [hY1] at g1
    exact ⟨G, g1, g2⟩
  have hbox := box_chart (Wof U w) hsz (wo w) (7 * ell ^ 2) hq1 hY (by linarith) hsm hcell hhol
  obtain ⟨G, g1, g2⟩ := hbox
  have hrn : (r : ℤ) ≤ ((7 * ell ^ 2 : ℕ) : ℤ) * ((bigSide (ell ^ m) ell (j - 2) : ℕ) : ℤ) := by
    obtain ⟨-, -, hr7, -⟩ := hB
    have e : 7 * ell ^ m * ell ^ j = 7 * ell ^ 2 * bigSide (ell ^ m) ell (j - 2) := by
      unfold bigSide
      have : ell ^ j = ell ^ (j - 2) * ell ^ 2 := by rw [← pow_add]; congr 1; omega
      rw [this]; ring
    have : r ≤ 7 * ell ^ 2 * bigSide (ell ^ m) ell (j - 2) := e ▸ hr7
    exact_mod_cast this
  have hBz : Bz r ⊆ BoxR ((bigSide (ell ^ m) ell (j - 2) : ℕ) : ℤ) (wo w) (7 * ell ^ 2) :=
    fun p hp μ => cell_range hs0 (wo w) hrn hp μ
  have hL : ∀ μ, 2 * r + 1 < scaleUp ell k Lu μ + 1 := fun μ => by have := hB.2.2.2.1 μ; omega
  obtain ⟨g, hg⟩ := gchart_of_C12 U w hL (g1.mono hBz le_rfl) (g2.mono hBz le_rfl)
  -- X1 j * ell = Y1 j,  X2 j * ell^2 = Y2 j
  have hu : ((ell : ℝ) ^ (j - 1))⁻¹ * ell = ((ell : ℝ) ^ (j - 2))⁻¹ := by
    have : (ell : ℝ) ^ (j - 1) = (ell : ℝ) ^ (j - 2) * ell := by rw [← pow_succ]; congr 1; omega
    have hl : (ell : ℝ) ≠ 0 := by exact_mod_cast hell0.ne'
    rw [this]; field_simp
  have hX1 : X1 ell (ell ^ m) α₀ j * ell = Y1 ell (ell ^ m) α₀ j := by
    unfold X1 Y1; rw [mul_assoc, hu]
  have hX2 : X2 ell (ell ^ m) α₀ j * (ell : ℝ) ^ 2 = Y := by
    rw [hYd]; unfold X2 Y2
    have : (((ell : ℝ) ^ (j - 1))⁻¹) ^ 2 * (ell : ℝ) ^ 2 = (((ell : ℝ) ^ (j - 2))⁻¹) ^ 2 := by
      rw [← mul_pow, hu]
    calc ((12 : ℕ) : ℝ) * ((ell ^ m : ℕ) : ℝ) * α₀ * (((ell : ℝ) ^ (j - 1))⁻¹) ^ 2 * (ell : ℝ) ^ 2
        = ((12 : ℕ) : ℝ) * ((ell ^ m : ℕ) : ℝ) * α₀ * ((((ell : ℝ) ^ (j - 1))⁻¹) ^ 2 * (ell : ℝ) ^ 2) := by ring
      _ = _ := by rw [this]
  have hX10 : 0 ≤ X1 ell (ell ^ m) α₀ j := X1_nonneg hα.le j
  have hX20 : 0 ≤ X2 ell (ell ^ m) α₀ j := X2_nonneg hα.le j
  have hK30 : 0 ≤ K3 := by linarith
  have hlr : (1 : ℝ) ≤ ell := by exact_mod_cast (show 1 ≤ ell by omega)
  refine ⟨g, hg.mono subset_rfl ?_ ?_⟩
  · show K3 * ((ell ^ (j - 2) : ℕ) : ℝ) * Y ≤ C * X1 ell (ell ^ m) α₀ j
    have e : K3 * ((ell ^ (j - 2) : ℕ) : ℝ) * Y = K3 * ((ell : ℝ) * X1 ell (ell ^ m) α₀ j) := by
      rw [mul_assoc, ← hY1, ← hX1]; ring
    rw [e, hC]
    have : (ell : ℝ) ≤ (ell : ℝ) ^ 2 := by nlinarith
    nlinarith [mul_nonneg hK30 hX10]
  · show K3 * Y ≤ C * X2 ell (ell ^ m) α₀ j
    have e : K3 * Y = (ell : ℝ) ^ 2 * K3 * X2 ell (ell ^ m) α₀ j := by rw [← hX2]; ring
    rw [e, hC]


/-- **the residual `BallChartsGT`, proved** (constants before `fc ≥ 10`, `m`, `R`). -/
theorem ballChartsGT_proved : BallChartsGT :=
  ballChartsGT_of_split (ballChartsGUJT_le1 coverGeomUTΦ) (ballChartsGUJT_ge2 coverGeomBoxUTΦ)

end MXQ.Total
