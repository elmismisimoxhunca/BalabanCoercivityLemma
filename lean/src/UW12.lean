import UW11
import UD

/-!
# UW12 -- **`BallChartsGU` and `P428Target8Unif` from the COVER_GEOM interface** (lane unif_20261016)

* `ballChartsGUJ_ge2 : CoverGeomBoxU → BallChartsGUJ (2 ≤ ·)`, chart constant `C = Kst^{42 ℓ} c` (`Kst = 10⁷`, `c` the
  interface constant), smallness threshold `min s_G (1 / C)`; both depend on `ℓ` only.  Only the single-cell part
  (`c' = c`) of `CoverGeomBox` is used; the face-adjacent pair charts are not consumed.
* `ballChartsGU_of_cover : CoverGeomU → CoverGeomBoxU → BallChartsGU`.
* `unif_of_cover : CoverGeomU → CoverGeomBoxU → ZT5A.P428Target8Unif`.
-/
set_option autoImplicit false
set_option maxHeartbeats 16000000

namespace AdalyFormal.UnifLane.Z

open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane (Tower Admissible scaleUp TorusOK pdist bigSide)
open AdalyFormal.StatementLaneG (P428Target8Unif)
open AdalyFormal.M2Glue3 (Z3 ev)
open AdalyFormal.M2Glue2 (GChart GChart.mono)
open AdalyFormal.M2BallCharts (Bz)
open AdalyFormal.Balaban.SuTwoLogExp (SU2 M2)
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
open AdalyFormal.UnifLane (ClassFamU BallChartsGU unif_of_ballChartsGU)

/-- **`BallChartsGU` for `j ≥ 2` from the interface.** -/
theorem ballChartsGUJ_ge2 (hCB : CoverGeomBoxU) : BallChartsGUJ (2 ≤ ·) := by
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

/-- **`BallChartsGU` from the COVER_GEOM interface.** -/
theorem ballChartsGU_of_cover (hCG : CoverGeomU) (hCB : CoverGeomBoxU) : BallChartsGU :=
  ballChartsGU_of_split (ballChartsGUJ_le1 hCG) (ballChartsGUJ_ge2 hCB)

/-- **`P428Target8Unif` from the COVER_GEOM interface.** -/
theorem unif_of_cover (hCG : CoverGeomU) (hCB : CoverGeomBoxU) : P428Target8Unif :=
  unif_of_ballChartsGU (ballChartsGU_of_cover hCG hCB)

end AdalyFormal.UnifLane.Z
