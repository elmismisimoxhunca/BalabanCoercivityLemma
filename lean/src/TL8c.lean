import TL8b

/-!
# TL8c -- `Cov` for sigma types and transport along an equivalence
-/
set_option autoImplicit false
namespace AdalyFormal.Thin

section more
variable {D : Type} [Fintype D]

/-- transport the total space along an equivalence -/
def Cov.transport {Xt Xt' X : Type} [Fintype Xt] [Fintype Xt'] [Fintype X] (c : Cov D Xt X) (e : Xt' ≃ Xt) :
    Cov D Xt' X where
  π := fun x => c.π (e x)
  τ := fun d => e.trans ((c.τ d).trans e.symm)
  surj := fun x => by
    obtain ⟨y, hy⟩ := c.surj x
    exact ⟨e.symm y, by simpa using hy⟩
  π_τ := fun d x => by simp [c.π_τ]
  free := fun x y hxy => by
    obtain ⟨d, hd, hu⟩ := c.free (e x) (e y) hxy
    refine ⟨d, ?_, fun d' hd' => hu d' ?_⟩
    · simp [hd]
    · simpa using congrArg e hd'

/-- sigma over a finite index type -/
def Cov.sigma {J : Type} [Fintype J] {Xt X : J → Type} [∀ j, Fintype (Xt j)] [∀ j, Fintype (X j)]
    (c : ∀ j, Cov D (Xt j) (X j)) : Cov D (Σ j, Xt j) (Σ j, X j) where
  π := fun p => ⟨p.1, (c p.1).π p.2⟩
  τ := fun d => Equiv.sigmaCongrRight (fun j => (c j).τ d)
  surj := fun p => by
    obtain ⟨y, hy⟩ := (c p.1).surj p.2
    exact ⟨⟨p.1, y⟩, by simp [hy]⟩
  π_τ := fun d p => by
    obtain ⟨j, y⟩ := p
    show (⟨j, (c j).π ((c j).τ d y)⟩ : Σ j, X j) = ⟨j, (c j).π y⟩
    rw [(c j).π_τ]
  free := fun p q hpq => by
    obtain ⟨j, y⟩ := p
    obtain ⟨j', y'⟩ := q
    have hinj := Sigma.mk.inj hpq
    obtain ⟨h1, h2⟩ := hinj
    simp only at h1
    subst h1
    have h2' : (c j).π y = (c j).π y' := eq_of_heq h2
    obtain ⟨d, hd, hu⟩ := (c j).free y y' h2'
    refine ⟨d, ?_, fun d' hd' => hu d' ?_⟩
    · show (⟨j, (c j).τ d y⟩ : Σ j, Xt j) = ⟨j, y'⟩
      rw [hd]
    · have := Sigma.mk.inj hd'
      exact eq_of_heq this.2

end more

end AdalyFormal.Thin
