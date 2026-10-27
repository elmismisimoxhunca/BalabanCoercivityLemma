import GFC8

/-!
# GFC9 -- characters of the torus group, their phases, and the lift relation for eigen-fields.
Standard axioms only.
-/
set_option autoImplicit false
open scoped BigOperators ComplexInnerProductSpace
open AdalyFormal.Target.ClayStatement

namespace AdalyFormal.FlatCoercivity

variable {L : PeriodicLatticeExtent} {n : ℕ}

/-- complex bond fields of the torus -/
abbrev TB (L : PeriodicLatticeExtent) := EuclideanSpace ℂ (Site L × Fin 3)

/-- the twist of a character -/
noncomputable def zOf (χ : AddChar (Site L) ℂ) : Fin 3 → Circle := fun μ =>
  ⟨χ (eU L μ), mem_sphere_zero_iff_norm.mpr (AddChar.norm_apply χ _)⟩

theorem zOf_coe (χ : AddChar (Site L) ℂ) (μ : Fin 3) : ((zOf χ μ : Circle) : ℂ) = χ (eU L μ) := rfl

/-- a character evaluated on the image of `ℤ³` is the phase of its twist -/
theorem chi_ιz (χ : AddChar (Site L) ℂ) (k : Z3) : χ (ιz L k) = phase (fun μ => ((zOf χ μ : Circle) : ℂ)) k := by
  set z : Fin 3 → ℂ := fun μ => ((zOf χ μ : Circle) : ℂ) with hz
  have hz0 : ∀ μ, z μ ≠ 0 := z_ne (zOf χ)
  have hχ0 : ∀ k, χ (ιz L k) ≠ 0 := fun k h => by
    have := AddChar.norm_apply χ (ιz L k); rw [h] at this; simp at this
  have hp0 : ∀ k, phase z k ≠ 0 := fun k => by
    have := norm_phase (z := z) (fun μ => Circle.norm_coe (zOf χ μ)) k
    intro h; rw [h] at this; simp at this
  let f : Z3 → ℂ := fun k => χ (ιz L k) / phase z k
  have hstep : ∀ k μ, f (k + ev μ) = f k := by
    intro k μ
    simp only [f]
    rw [ιz_add, ιz_ev, AddChar.map_add_eq_mul, phase_add hz0, phase_ev]
    have h1 : χ (eU L μ) = z μ := rfl
    rw [h1]
    have := hz0 μ
    have := hp0 k
    field_simp
  have h := const_of_step f hstep k
  have h0 : f 0 = 1 := by
    simp only [f]
    rw [ιz_zero, AddChar.map_zero_eq_one, phase_zero]; simp
  rw [h0] at h
  simp only [f] at h
  have := hp0 k
  field_simp at h
  exact h

/-- cell restriction of a torus field -/
noncomputable def vOf (hdvd : ∀ μ, n ∣ L μ + 1) (A : TB L) (μ : Fin 3) : CV n :=
  WithLp.toLp 2 (fun t => A (ιc hdvd t, μ))

/-- **THE LIFT RELATION**: for an eigen-field `A` (`A(x + n g, μ) = χ(g) A(x, μ)`) the values at integer points
are the quasi-periodic lift of the cell restriction. -/
theorem lift_relation (hn : 0 < n) (hdvd : ∀ μ, n ∣ L μ + 1) (χ : AddChar (Site L) ℂ) (A : TB L)
    (hA : ∀ (g : Site L) (x : Site L) (μ : Fin 3), A (x + n • g, μ) = χ g * A (x, μ))
    (μ : Fin 3) (x : Z3) :
    A (ιz L x, μ) = lift hn (fun ν => ((zOf χ ν : Circle) : ℂ)) (vOf hdvd A μ) x := by
  have hx := eq_cc_modc_add hn x
  have h1 : ιz L x = ιc hdvd (modc n hn x) + n • ιz L (fun ν => x ν / (n : ℤ)) := by
    conv_lhs => rw [hx]
    rw [ιz_add, ιz_cc hdvd]
    congr 1
    rw [natCast_zsmul, ιz_nsmul]
  rw [h1, hA, chi_ιz]
  unfold lift
  rfl

#print axioms chi_ιz

end AdalyFormal.FlatCoercivity
