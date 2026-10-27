import Pointwise
set_option autoImplicit false
namespace HConstruction.DRepair.Hodge
open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.AdmissibleSubspace
open AdalyFormal.Balaban.LatticeOperators
open AdalyFormal.Balaban.U1AnchorPoincare
variable {Λ : PeriodicLatticeExtent}

def CurlFree (A : Bond Λ → ℝ) : Prop := ∀ p : PeriodicLatticePlaquette Λ, curlValue A p = 0

theorem curlFree_eq_grad_add_const {A : Bond Λ → ℝ} (hA : CurlFree A) :
    ∃ (f : PeriodicLatticeSite Λ → ℝ) (c : Fin 3 → ℝ),
      ∀ b : Bond Λ, A b = f (periodicLatticeShift b.1 b.2) - f b.1 + c b.2 := by
  classical
  -- Step 0: remove the harmonic classes
  obtain ⟨c, hcurl0, hhol0⟩ :
      ∃ c : Fin 3 → ℝ, CurlFree (fun b : Bond Λ => A b - c b.2) ∧
        ∀ (z : PeriodicLatticeSite Λ) (ρ : Fin 3),
          holonomy (fun b : Bond Λ => A b - c b.2) z ρ = 0 := by
    refine ⟨fun ν => holonomy A (fun _ => 0) ν / ((Λ ν : ℝ) + 1), ?_, ?_⟩
    · intro p
      have hcv := curlValue_of_const (Λ := Λ)
        (fun ν => holonomy A (fun _ => 0) ν / ((Λ ν : ℝ) + 1)) p
      rw [curlValue_sub, hA p, hcv]
      ring
    · intro z ρ
      have hcf := holonomy_const_field (Λ := Λ)
        (fun ν => holonomy A (fun _ => 0) ν / ((Λ ν : ℝ) + 1)) z ρ
      have hb := holonomy_const hA z (fun _ => 0) ρ
      rw [holonomy_sub, hcf, hb]
      have hne : ((Λ ρ : ℝ) + 1) ≠ 0 := by positivity
      field_simp
      ring
  -- Sweep 1: direction 0
  obtain ⟨f0, hcurl1, hhol1, hz1, -⟩ :=
    gauge_step hcurl0 hhol0 0 (fun _ => False) (fun _ h => absurd h (by simp)) (by simp)
  -- Sweep 2: direction 1, preserving direction 0
  obtain ⟨f1, hcurl2, hhol2, hz2, hz2'⟩ :=
    gauge_step hcurl1 hhol1 1 (fun δ => δ = 0)
      (by rintro δ rfl y; exact hz1 y) (by decide)
  -- Sweep 3: direction 2, preserving directions 0 and 1
  obtain ⟨f2, -, -, hz3, hz3'⟩ :=
    gauge_step hcurl2 hhol2 2 (fun δ => δ = 0 ∨ δ = 1)
      (by
        rintro δ (rfl | rfl) y
        · exact hz2' 0 rfl y
        · exact hz2 y)
      (by decide)
  refine ⟨fun x => f0 x + f1 x + f2 x, c, ?_⟩
  rintro ⟨y, μ⟩
  have hall : (fun b : Bond Λ => A b - c b.2) (y, μ) - gradValue f0 (y, μ)
      - gradValue f1 (y, μ) - gradValue f2 (y, μ) = 0 := by
    have hcase : ∀ m : Fin 3, m = 0 ∨ m = 1 ∨ m = 2 := by decide
    rcases hcase μ with rfl | rfl | rfl
    · exact hz3' 0 (Or.inl rfl) y
    · exact hz3' 1 (Or.inr rfl) y
    · exact hz3 y
  simp only [gradValue] at hall ⊢
  linarith

end HConstruction.DRepair.Hodge
