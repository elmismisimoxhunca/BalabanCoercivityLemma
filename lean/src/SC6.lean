import SC5b
import GFC16

/-!
# SC6 -- the `κ`-weighted TORUS coercivity from any cell inequality of the form
`c Σ‖w‖² ≤ g1 + κ g2 + S` (copy of `eigen_coercive` / `torus_coercive` of the flat-coercivity lane with the
mass weight `κ` on `L2`).  With `cell_coercive_explicit` this gives an EXPLICIT, volume-independent torus bound.
Standard axioms only.
-/
set_option autoImplicit false
set_option maxHeartbeats 8000000
open scoped BigOperators ComplexInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.FlatCoercivity

namespace AdalyFormal.ScaledCoercivity

variable {L : PeriodicLatticeExtent} {n : ℕ}

/-- eigen-field coercivity with mass weight `κ` -/
theorem eigen_coercive_kappa (hn : 0 < n) {c κ : ℝ}
    (hc : ∀ (z : Fin 3 → Circle) (w : Fin 3 → CV n) (S : ℝ), 0 ≤ S →
      (∀ u : CV n, ⟪epsV n, u⟫ = 0 →
        ‖⟪(cellSym hn z).Dstar w, (cellSym hn z).Lap u⟫‖ ^ 2 ≤ S * ‖(cellSym hn z).Lap u‖ ^ 2) →
      c * ∑ μ, ‖w μ‖ ^ 2 ≤ g1 hn (z, w) + κ * g2 hn (z, w) + S)
    (hdvd : ∀ μ, n ∣ L μ + 1) (χ : AddChar (Site L) ℂ) (A : TB L) (hA : IsEig n χ A) :
    c * ‖A‖ ^ 2 ≤ ‖L1 L A‖ ^ 2 + κ * ‖L2 hdvd A‖ ^ 2 + ‖L3 hdvd A‖ ^ 2 := by
  by_cases hA0 : A = 0
  · subst hA0; simp
  have hzM := twist_pow_one hn hdvd χ A hA hA0
  have hM := Mnum_pos hn hdvd
  have hnormA : ‖A‖ ^ 2 = Mnum L n * ∑ μ, ‖vOf hdvd A μ‖ ^ 2 := by
    rw [normB_eig hn hdvd χ A hA]
    congr 1
    refine Finset.sum_congr rfl (fun μ _ => ?_)
    rw [EuclideanSpace.norm_sq_eq]
    rfl
  have hS : 0 ≤ ‖L3 hdvd A‖ ^ 2 / Mnum L n := by positivity
  have key := hc (zOf χ) (fun μ => vOf hdvd A μ) (‖L3 hdvd A‖ ^ 2 / Mnum L n) hS
    (fun u hu => L3_ratio hn hdvd χ A hA hzM u hu)
  have h1 := L1_cell hn hdvd χ A hA
  have h2 := L2_cell hn hdvd χ A hA
  rw [h1, h2, hnormA]
  have := mul_le_mul_of_nonneg_left key hM.le
  calc c * (Mnum L n * ∑ μ, ‖vOf hdvd A μ‖ ^ 2) = Mnum L n * (c * ∑ μ, ‖vOf hdvd A μ‖ ^ 2) := by ring
    _ ≤ Mnum L n * (g1 hn (zOf χ, fun μ => vOf hdvd A μ) + κ * g2 hn (zOf χ, fun μ => vOf hdvd A μ)
          + ‖L3 hdvd A‖ ^ 2 / Mnum L n) := this
    _ = _ := by field_simp

set_option maxHeartbeats 4000000 in
/-- **VOLUME-INDEPENDENT TORUS COERCIVITY with mass weight `κ`** (complex scalar model) -/
theorem torus_coercive_kappa (hn : 0 < n) {c κ : ℝ} (hκ : 0 ≤ κ)
    (hc : ∀ (z : Fin 3 → Circle) (w : Fin 3 → CV n) (S : ℝ), 0 ≤ S →
      (∀ u : CV n, ⟪epsV n, u⟫ = 0 →
        ‖⟪(cellSym hn z).Dstar w, (cellSym hn z).Lap u⟫‖ ^ 2 ≤ S * ‖(cellSym hn z).Lap u‖ ^ 2) →
      c * ∑ μ, ‖w μ‖ ^ 2 ≤ g1 hn (z, w) + κ * g2 hn (z, w) + S)
    (L : PeriodicLatticeExtent) (hdvd : ∀ μ, n ∣ L μ + 1) (A : TB L) :
    c * ‖A‖ ^ 2 ≤ ‖L1 L A‖ ^ 2 + κ * ‖L2 hdvd A‖ ^ 2 + ‖L3 hdvd A‖ ^ 2 := by
  have hT0 : Tl n (0 : Site L) (Fin 3) = LinearMap.id := by
    ext1 f; rw [Tl_apply]; exact shiftE_zero _ f
  have hTadd : ∀ g h : Site L, Tl n (g + h) (Fin 3) = (Tl n g (Fin 3)).comp (Tl n h (Fin 3)) := by
    intro g h; ext1 f
    simp only [LinearMap.comp_apply, Tl_apply]
    exact shiftE_add _ g h f
  have hTu : ∀ (g : Site L) (x y : TB L), ⟪Tl n g (Fin 3) x, Tl n g (Fin 3) y⟫ = ⟪x, y⟫ := by
    intro g x y; simp only [Tl_apply]; exact (shiftE n g (Fin 3)).inner_map_map x y
  have hU1 : ∀ (g : Site L) (x y : TP L), ⟪Tl n g (Fin 3 × Fin 3) x, Tl n g (Fin 3 × Fin 3) y⟫ = ⟪x, y⟫ := by
    intro g x y; simp only [Tl_apply]; exact (shiftE n g (Fin 3 × Fin 3)).inner_map_map x y
  have hU3 : ∀ (g : Site L) (x y : TS L), ⟪Tls n g x, Tls n g y⟫ = ⟪x, y⟫ := by
    intro g x y; simp only [Tls_apply]; exact (shiftS n g).inner_map_map x y
  have h1 : ∀ (g : Site L) (z : TB L), L1 L (Tl n g (Fin 3) z) = Tl n g (Fin 3 × Fin 3) (L1 L z) :=
    fun g z => L1_equiv g z
  have h2 : ∀ (g : Site L) (z : TB L), L2 hdvd (Tl n g (Fin 3) z) = Tl n g (Fin 3) (L2 hdvd z) :=
    fun g z => L2_equiv hdvd g z
  have h3 : ∀ (g : Site L) (z : TB L), L3 hdvd (Tl n g (Fin 3) z) = Tls n g (L3 hdvd z) :=
    fun g z => L3_equiv hdvd g z
  set r : ℂ := ((Real.sqrt κ : ℝ) : ℂ) with hr
  have h2' : ∀ (g : Site L) (z : TB L), (r • L2 hdvd) (Tl n g (Fin 3) z) = Tl n g (Fin 3) ((r • L2 hdvd) z) := by
    intro g z
    simp only [LinearMap.smul_apply, h2, map_smul]
  have hcc : ∀ (χ : AddChar (Site L) ℂ) (z : TB L), (∀ g, Tl n g (Fin 3) z = χ g • z) →
      c * ‖z‖ ^ 2 ≤ ‖L1 L z‖ ^ 2 + ‖(r • L2 hdvd) z‖ ^ 2 + ‖L3 hdvd z‖ ^ 2 := by
    intro χ z hz
    have hn2 : ‖(r • L2 hdvd) z‖ ^ 2 = κ * ‖L2 hdvd z‖ ^ 2 := by
      rw [LinearMap.smul_apply, norm_smul, mul_pow, hr, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (Real.sqrt_nonneg _), Real.sq_sqrt hκ]
    rw [hn2]
    refine eigen_coercive_kappa hn hc hdvd χ z (fun g x b => ?_)
    have := congrArg (fun F => F (x, b)) (hz g)
    simpa [Tl_apply, shiftE_apply] using this
  have := bloch_coercive_three (Γ := Site L) (H := TB L) (K₁ := TP L) (K₂ := TB L) (K₃ := TS L)
    (fun g => Tl n g (Fin 3)) hT0 hTadd hTu (fun g => Tl n g (Fin 3 × Fin 3)) hU1
    (fun g => Tl n g (Fin 3)) hTu (fun g => Tls n g) hU3 (L1 L) (r • L2 hdvd) (L3 hdvd) h1 h2' h3 c hcc A
  have hn2 : ‖(r • L2 hdvd) A‖ ^ 2 = κ * ‖L2 hdvd A‖ ^ 2 := by
    rw [LinearMap.smul_apply, norm_smul, mul_pow, hr, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg _), Real.sq_sqrt hκ]
  rw [hn2] at this
  exact this

#print axioms torus_coercive_kappa

end AdalyFormal.ScaledCoercivity
