import UMA
import UW12

/-!
# UMZ -- the ball charts at cube factor `fc` from the COVER_GEOM interface at `fc` (lane unif_20261016, milestone 7)

Text copies of `UZ5` (`BallChartsGUJ`, `ballChartsGU_of_split`, `CoverGeomU`, `CoverGeomBoxU`, `ballChartsGUJ_le1`) and of `UW12`
(`ballChartsGUJ_ge2`) with `ClassFamU ell` replaced by `ClassFamUH ell fc`.  The proofs never open the class hypothesis (they pass it to
the interface), so the bodies are unchanged; the chart constants are those of milestone 6 (`ℓ`- and interface-dependent only).
-/
set_option autoImplicit false
set_option maxHeartbeats 16000000

namespace AdalyFormal.UnifMax

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

variable {fc : ℕ}

/-- `BallChartsGU` restricted to the levels with `P j`. -/
def BallChartsGUJH (fc : ℕ) (P : ℕ → Prop) : Prop :=
  ∀ (ell : ℕ), 2 ≤ ell →
    ClassFamUH ell fc ℝ (fun _ _ C => 1 ≤ C) (fun M _ k _ C S Lam U α₀ => BallChartsAtGJ P ell M k S U C α₀)

/-- **the two halves give the residual.** -/
theorem ballChartsGUH_of_split (h1 : BallChartsGUJH fc (· ≤ 1)) (h2 : BallChartsGUJH fc (2 ≤ ·)) : BallChartsGUH fc := by
  intro ell hell
  obtain ⟨m₁, R₁, C₁, s₁, hs₁, hf₁⟩ := h1 ell hell
  obtain ⟨m₂, R₂, C₂, s₂, hs₂, hf₂⟩ := h2 ell hell
  refine ⟨max m₁ m₂, max R₁ R₂, max C₁ C₂, min s₁ s₂, lt_min hs₁ hs₂, fun m hm R hR => ⟨?_, ?_⟩⟩
  · exact le_max_of_le_left (hf₁ m (le_of_max_le_left hm) R (le_of_max_le_left hR)).1
  intro k hk Lu α₀ hα hsα hT S hS Lam hL U hU hloc
  refine ballChartsAtG_of_J (fun j w r hB => ?_)
  rcases le_or_gt j 1 with hj | hj
  · obtain ⟨-, hf⟩ := hf₁ m (le_of_max_le_left hm) R (le_of_max_le_left hR)
    obtain ⟨g, hg⟩ := hf k hk Lu α₀ hα (hsα.trans (min_le_left _ _)) hT S hS Lam hL U hU hloc j w r hj hB
    exact ⟨g, hg.mono subset_rfl (mul_le_mul_of_nonneg_right (le_max_left _ _) (X1_nonneg hα.le j))
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (X2_nonneg hα.le j))⟩
  · obtain ⟨-, hf⟩ := hf₂ m (le_of_max_le_right hm) R (le_of_max_le_right hR)
    obtain ⟨g, hg⟩ := hf k hk Lu α₀ hα (hsα.trans (min_le_right _ _)) hT S hS Lam hL U hU hloc j w r hj hB
    exact ⟨g, hg.mono subset_rfl (mul_le_mul_of_nonneg_right (le_max_right _ _) (X1_nonneg hα.le j))
      (mul_le_mul_of_nonneg_right (le_max_right _ _) (X2_nonneg hα.le j))⟩

/-- **COVER_GEOM INTERFACE, `j ≤ 1` part** (cells of the `ℓ¹` ball, clause 1). -/
def CoverGeomUH (fc : ℕ) : Prop :=
  ∀ (ell : ℕ), 2 ≤ ell →
    ClassFamUH ell fc ℝ (fun _ _ c => 1 ≤ c) (fun M _ k _ c S Lam U α₀ =>
      ∀ j w r, j ≤ 1 → BallHyp ell M k S j w r →
        CoverGeomZ (Wof U w) ((bigSide M ell (j - 1) : ℕ) : ℤ) (wo w) r (c * X1 ell M α₀ j) (c * X2 ell M α₀ j))

/-- **COVER_GEOM INTERFACE, `j ≥ 2` part** (full cells of the box of `7ℓ` cells around the centre; pairs; clauses 1, 2). -/
def CoverGeomBoxUH (fc : ℕ) : Prop :=
  ∀ (ell : ℕ), 2 ≤ ell →
    ClassFamUH ell fc ℝ (fun _ _ c => 1 ≤ c) (fun M _ k _ c S Lam U α₀ =>
      ∀ j w r, 2 ≤ j → BallHyp ell M k S j w r →
        CoverGeomBox (Wof U w) ((bigSide M ell (j - 1) : ℕ) : ℤ) (wo w) (7 * ell) (c * X1 ell M α₀ j) (c * X2 ell M α₀ j))

/-- **`BallChartsGU` for `j ≤ 1` from the interface.** -/
theorem ballChartsGUJH_le1 (hCG : CoverGeomUH fc) : BallChartsGUJH fc (· ≤ 1) := by
  intro ell hell
  obtain ⟨m₁, R₁, c, sG, hsG, hF⟩ := hCG ell hell
  have hc1 : 1 ≤ c := (hF m₁ le_rfl R₁ le_rfl).1
  set C : ℝ := 2 * (1 + 6 * ((7 * ell : ℕ) : ℝ)) ^ 3 * c with hC
  have hCc : 1 ≤ C := by
    have h7 : (0 : ℝ) ≤ ((7 * ell : ℕ) : ℝ) := Nat.cast_nonneg _
    have h1 : (1 : ℝ) ≤ 1 + 6 * ((7 * ell : ℕ) : ℝ) := by linarith
    have : (1 : ℝ) ≤ (1 + 6 * ((7 * ell : ℕ) : ℝ)) ^ 3 := one_le_pow₀ h1
    rw [hC]; nlinarith
  refine ⟨m₁, R₁, C, sG, hsG, fun m hm R hR => ⟨hCc, ?_⟩⟩
  intro k hk Lu α₀ hα hsα hT S hS Lam hLam U hU hloc j w r hj hB
  have hCZ := (hF m hm R hR).2 k hk Lu α₀ hα hsα hT S hS Lam hLam U hU hloc j w r hj hB
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

/-- **`BallChartsGU` for `j ≥ 2` from the interface.** -/
theorem ballChartsGUJH_ge2 (hCB : CoverGeomBoxUH fc) : BallChartsGUJH fc (2 ≤ ·) := by
  intro ell hell
  obtain ⟨m₁, R₁, c, sG, hsG, hF⟩ := hCB ell hell
  have hc1 : 1 ≤ c := (hF m₁ le_rfl R₁ le_rfl).1
  have hK := one_le_Kst
  have hKp : (1 : ℝ) ≤ Kst ^ (2 * (7 * ell)) := one_le_pow₀ hK
  set C : ℝ := Kst ^ (2 * (7 * ell)) * (Kst ^ (2 * (7 * ell)) * (Kst ^ (2 * (7 * ell)) * c)) with hC
  have hC1 : 1 ≤ C := by
    have a1 : 1 ≤ Kst ^ (2 * (7 * ell)) * c := by nlinarith
    have a2 : 1 ≤ Kst ^ (2 * (7 * ell)) * (Kst ^ (2 * (7 * ell)) * c) := by nlinarith
    rw [hC]; nlinarith
  have hC0 : 0 < C := by linarith
  refine ⟨m₁, R₁, C, min sG (1 / C), lt_min hsG (by positivity), fun m hm R hR => ⟨hC1, ?_⟩⟩
  intro k hk Lu α₀ hα hsα hT S hS Lam hLam U hU hloc j w r hj hB
  obtain ⟨hcells, hhol⟩ := (hF m hm R hR).2 k hk Lu α₀ hα (hsα.trans (min_le_left _ _)) hT S hS Lam hLam U hU hloc
    j w r hj hB
  have hj1 : 1 ≤ j - 1 := by omega
  have hq1 : 1 ≤ ell ^ (j - 1) := Nat.one_le_pow _ _ (by omega)
  have hq2 : 2 ≤ ell ^ (j - 1) := by
    calc 2 ≤ ell := hell
      _ = ell ^ 1 := (pow_one ell).symm
      _ ≤ ell ^ (j - 1) := Nat.pow_le_pow_right (by omega) hj1
  have hM1 : 1 ≤ ell ^ m := Nat.one_le_pow _ _ (by omega)
  have hsz : (2 : ℤ) ≤ ((bigSide (ell ^ m) ell (j - 1) : ℕ) : ℤ) := by
    have : 2 ≤ bigSide (ell ^ m) ell (j - 1) := by
      unfold bigSide
      calc 2 = 1 * 2 := by ring
        _ ≤ ell ^ m * ell ^ (j - 1) := Nat.mul_le_mul hM1 hq2
    exact_mod_cast this
  have hs0 : (0 : ℤ) < ((bigSide (ell ^ m) ell (j - 1) : ℕ) : ℤ) := by omega
  set Y := X2 ell (ell ^ m) α₀ j with hYd
  have hqpos : (0 : ℝ) < ((ell ^ (j - 1) : ℕ) : ℝ) := by exact_mod_cast (show 0 < ell ^ (j - 1) by omega)
  have hX1 : X1 ell (ell ^ m) α₀ j = ((ell ^ (j - 1) : ℕ) : ℝ) * Y := by
    rw [hYd]; unfold X1 X2
    have e : ((ell ^ (j - 1) : ℕ) : ℝ) = (ell : ℝ) ^ (j - 1) := by push_cast; ring
    rw [e] at hqpos ⊢
    field_simp
  have hqY : ((ell ^ (j - 1) : ℕ) : ℝ) * ((ell ^ (j - 1) : ℕ) : ℝ) * Y = (12 : ℝ) * ((ell ^ m : ℕ) : ℝ) * α₀ := by
    rw [hYd]; unfold X2
    have e : ((ell ^ (j - 1) : ℕ) : ℝ) = (ell : ℝ) ^ (j - 1) := by push_cast; ring
    rw [e] at hqpos ⊢
    field_simp
    push_cast; ring
  have hY : 0 ≤ Y := by rw [hYd]; exact X2_nonneg hα.le j
  have hsm : C * ((ell ^ (j - 1) : ℕ) : ℝ) * ((ell ^ (j - 1) : ℕ) : ℝ) * Y ≤ 1 := by
    have h12 : (12 : ℝ) * ((ell ^ m : ℕ) : ℝ) * α₀ ≤ 1 / C := hsα.trans (min_le_right _ _)
    have e : C * ((ell ^ (j - 1) : ℕ) : ℝ) * ((ell ^ (j - 1) : ℕ) : ℝ) * Y
        = C * ((12 : ℝ) * ((ell ^ m : ℕ) : ℝ) * α₀) := by rw [← hqY]; ring
    rw [e]
    calc C * ((12 : ℝ) * ((ell ^ m : ℕ) : ℝ) * α₀) ≤ C * (1 / C) := mul_le_mul_of_nonneg_left h12 hC0.le
      _ = 1 := by field_simp
  have hcell : ∀ cc : Z3, (∀ μ, wo w μ / ((bigSide (ell ^ m) ell (j - 1) : ℕ) : ℤ) - ((7 * ell : ℕ) : ℤ) ≤ cc μ ∧
      cc μ ≤ wo w μ / ((bigSide (ell ^ m) ell (j - 1) : ℕ) : ℤ) + ((7 * ell : ℕ) : ℤ)) →
      ∃ G : Z3 → SU2, C1 (Wof U w) G (cellBox ((bigSide (ell ^ m) ell (j - 1) : ℕ) : ℤ) (wo w) cc)
          (c * (((ell ^ (j - 1) : ℕ) : ℝ) * Y)) ∧
        C2 (Wof U w) G (cellBox ((bigSide (ell ^ m) ell (j - 1) : ℕ) : ℤ) (wo w) cc) (c * Y) := by
    intro cc hcc
    obtain ⟨G, g1, g2⟩ := hcells cc cc hcc hcc (Or.inl rfl)
    rw [Set.union_self] at g1 g2
    rw [hX1] at g1
    exact ⟨G, g1, g2⟩
  have hbox := box_chart (Wof U w) hsz (wo w) (7 * ell) hq1 hY (by linarith) hsm hcell hhol
  obtain ⟨G, g1, g2⟩ := hbox
  have hrn : (r : ℤ) ≤ ((7 * ell : ℕ) : ℤ) * ((bigSide (ell ^ m) ell (j - 1) : ℕ) : ℤ) := by
    obtain ⟨-, -, hr7, -⟩ := hB
    have e : 7 * ell ^ m * ell ^ j = 7 * ell * bigSide (ell ^ m) ell (j - 1) := by
      unfold bigSide
      have : ell ^ j = ell ^ (j - 1) * ell := by rw [← pow_succ]; congr 1; omega
      rw [this]; ring
    have : r ≤ 7 * ell * bigSide (ell ^ m) ell (j - 1) := e ▸ hr7
    exact_mod_cast this
  have hBz : Bz r ⊆ BoxR ((bigSide (ell ^ m) ell (j - 1) : ℕ) : ℤ) (wo w) (7 * ell) :=
    fun p hp μ => cell_range hs0 (wo w) hrn hp μ
  have hL : ∀ μ, 2 * r + 1 < scaleUp ell k Lu μ + 1 := fun μ => by have := hB.2.2.2.1 μ; omega
  obtain ⟨g, hg⟩ := gchart_of_C12 U w hL (g1.mono hBz le_rfl) (g2.mono hBz le_rfl)
  refine ⟨g, hg.mono subset_rfl ?_ ?_⟩
  · rw [hX1]; exact le_of_eq (by ring)
  · exact le_rfl

/-- **`BallChartsGUH fc` from the interface at `fc`.** -/
theorem ballChartsGUH_of_cover (hCG : CoverGeomUH fc) (hCB : CoverGeomBoxUH fc) : BallChartsGUH fc :=
  ballChartsGUH_of_split (ballChartsGUJH_le1 hCG) (ballChartsGUJH_ge2 hCB)

end AdalyFormal.UnifMax
