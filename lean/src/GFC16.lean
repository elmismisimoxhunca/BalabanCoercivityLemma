import GFC15

/-!
# GFC16 -- `torus_coercive`: a constant `c(n) > 0` valid on every torus tiled by `n`-cells.  Standard axioms only.
-/
set_option autoImplicit false
open scoped BigOperators ComplexInnerProductSpace
open AdalyFormal.Target.ClayStatement

namespace AdalyFormal.FlatCoercivity

variable {L : PeriodicLatticeExtent} {n : ℕ}

theorem shiftE_zero (β : Type*) [Fintype β] (f : EuclideanSpace ℂ (Site L × β)) :
    shiftE n (0 : Site L) β f = f := by
  ext ⟨x, b⟩; rw [shiftE_apply]; simp

theorem shiftE_add (β : Type*) [Fintype β] (g h : Site L) (f : EuclideanSpace ℂ (Site L × β)) :
    shiftE n (g + h) β f = shiftE n g β (shiftE n h β f) := by
  ext ⟨x, b⟩
  simp only [shiftE_apply, smul_add, add_assoc]

/-- translation as a linear map -/
noncomputable def Tl (n : ℕ) (g : Site L) (β : Type*) [Fintype β] :
    EuclideanSpace ℂ (Site L × β) →ₗ[ℂ] EuclideanSpace ℂ (Site L × β) :=
  (shiftE n g β).toLinearEquiv.toLinearMap

theorem Tl_apply (g : Site L) (β : Type*) [Fintype β] (f : EuclideanSpace ℂ (Site L × β)) :
    Tl n g β f = shiftE n g β f := rfl

noncomputable def Tls (n : ℕ) (g : Site L) : TS L →ₗ[ℂ] TS L := (shiftS n g).toLinearEquiv.toLinearMap

theorem Tls_apply (g : Site L) (f : TS L) : Tls n g f = shiftS n g f := rfl

set_option maxHeartbeats 2000000 in
/-- **VOLUME-INDEPENDENT TORUS COERCIVITY (complex scalar model)** -/
theorem torus_coercive (hn : 0 < n) : ∃ c : ℝ, 0 < c ∧ ∀ (L : PeriodicLatticeExtent) (hdvd : ∀ μ, n ∣ L μ + 1) (A : TB L),
    c * ‖A‖ ^ 2 ≤ ‖L1 L A‖ ^ 2 + ‖L2 hdvd A‖ ^ 2 + ‖L3 hdvd A‖ ^ 2 := by
  obtain ⟨c, hc0, hc⟩ := cell_coercive hn
  refine ⟨c, hc0, ?_⟩
  intro L hdvd A
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
  have h1 : ∀ (g : Site L) (z : TB L), L1 L (Tl n g (Fin 3) z) = Tl n g (Fin 3 × Fin 3) (L1 L z) := fun g z => L1_equiv g z
  have h2 : ∀ (g : Site L) (z : TB L), L2 hdvd (Tl n g (Fin 3) z) = Tl n g (Fin 3) (L2 hdvd z) := fun g z => L2_equiv hdvd g z
  have h3 : ∀ (g : Site L) (z : TB L), L3 hdvd (Tl n g (Fin 3) z) = Tls n g (L3 hdvd z) := fun g z => L3_equiv hdvd g z
  have hcc : ∀ (χ : AddChar (Site L) ℂ) (z : TB L), (∀ g, Tl n g (Fin 3) z = χ g • z) →
      c * ‖z‖ ^ 2 ≤ ‖L1 L z‖ ^ 2 + ‖L2 hdvd z‖ ^ 2 + ‖L3 hdvd z‖ ^ 2 := by
    intro χ z hz
    refine eigen_coercive hn hc hdvd χ z (fun g x b => ?_)
    have := congrArg (fun F => F (x, b)) (hz g)
    simpa [Tl_apply, shiftE_apply] using this
  exact bloch_coercive_three (Γ := Site L) (H := TB L) (K₁ := TP L) (K₂ := TB L) (K₃ := TS L)
    (fun g => Tl n g (Fin 3)) hT0 hTadd hTu (fun g => Tl n g (Fin 3 × Fin 3)) hU1
    (fun g => Tl n g (Fin 3)) hTu (fun g => Tls n g) hU3 (L1 L) (L2 hdvd) (L3 hdvd) h1 h2 h3 c hcc A

#print axioms torus_coercive

end AdalyFormal.FlatCoercivity
