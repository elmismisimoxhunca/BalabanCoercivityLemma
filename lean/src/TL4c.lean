import TL4b

/-!
# TL4c -- `Cov` structures: sites, edges, plaquettes, and constructors (products, subtypes, sigma types)
-/
set_option autoImplicit false
namespace AdalyFormal.Thin
open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)

/-- deck cover of sites -/
def covS {Lt L : PeriodicLatticeExtent} (h : Covers Lt L) : Cov (DeckIdx Lt L) (PeriodicLatticeSite Lt) (PeriodicLatticeSite L) where
  π := projS h
  τ := tauS h
  surj := projS_surj h
  π_τ := projS_tauS h
  free := fun x y hxy => site_free h x y hxy

section cons
variable {D Xt X : Type} [Fintype D] [Fintype Xt] [Fintype X]

/-- product with a fixed finite factor -/
def Cov.prodR (c : Cov D Xt X) (K : Type) [Fintype K] : Cov D (Xt × K) (X × K) where
  π := fun p => (c.π p.1, p.2)
  τ := fun d => Equiv.prodCongr (c.τ d) (Equiv.refl K)
  surj := fun p => by
    obtain ⟨x, hx⟩ := c.surj p.1
    exact ⟨(x, p.2), by simp [hx]⟩
  π_τ := fun d p => by simp [c.π_τ]
  free := fun p q hpq => by
    obtain ⟨h1, h2⟩ := Prod.mk.inj hpq
    obtain ⟨d, hd, hu⟩ := c.free p.1 q.1 h1
    refine ⟨d, ?_, ?_⟩
    · ext <;> simp [hd, h2]
    · intro d' hd'
      apply hu
      exact congrArg Prod.fst hd'

open Classical in
/-- restriction to a deck-invariant subset (the predicate is on the base) -/
def Cov.sub (c : Cov D Xt X) (P : X → Prop) : Cov D {xt : Xt // P (c.π xt)} {x : X // P x} where
  π := fun xt => ⟨c.π xt.1, xt.2⟩
  τ := fun d => {
    toFun := fun xt => ⟨c.τ d xt.1, by rw [c.π_τ]; exact xt.2⟩
    invFun := fun xt => ⟨(c.τ d).symm xt.1, by
      have := c.π_τ d ((c.τ d).symm xt.1)
      rw [Equiv.apply_symm_apply] at this
      rw [← this]; exact xt.2⟩
    left_inv := fun xt => by ext; simp
    right_inv := fun xt => by ext; simp }
  surj := fun x => by
    obtain ⟨xt, hxt⟩ := c.surj x.1
    exact ⟨⟨xt, by rw [hxt]; exact x.2⟩, Subtype.ext hxt⟩
  π_τ := fun d xt => Subtype.ext (c.π_τ d xt.1)
  free := fun p q hpq => by
    have h1 : c.π p.1 = c.π q.1 := congrArg Subtype.val hpq
    obtain ⟨d, hd, hu⟩ := c.free p.1 q.1 h1
    refine ⟨d, Subtype.ext hd, fun d' hd' => hu d' (congrArg Subtype.val hd')⟩

end cons

end AdalyFormal.Thin
