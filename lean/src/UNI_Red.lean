import UNI_Tor
import MXQ_Tor

/-!
# UNI_Red -- relations between the union headline and the box headline / sub-class readings (lane union_cubes_20261018)

* `famTorusP_of_equiv`: the headline for the class `Cl` implies the headline for any class `Cl'` that equals `Cl ∧ Sh` (under `Admissible`) for a shape predicate `Sh` that does not mention the tower (filter the family by `Sh`).
* box reading: `MXQ.Total.P428Target8FamilyTorus` is `FamTorusP boxClass` (`rfl`) and `boxClass ↔ unionClass ∧ boxShape` under `Admissible`; hence `P428Target8FamilyTorusU → P428Target8FamilyTorus`.
* size reading `unionBoxClass` (union contained in an axis box of side `f M ℓ^j`) and "several" reading `unionSeveralClass` (at least two blocks): both follow.
-/
set_option autoImplicit false

namespace UNI.Total

open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
open UNI.AllC

theorem famTorusP_of_equiv {Cl Cl' : ClassPred}
    (Sh : ∀ (L : PeriodicLatticeExtent) (ell M f : ℕ) (_sites : Set (PeriodicLatticeSite L)) (_j : ℕ), Prop)
    (hequiv : ∀ (ell m R k : ℕ) (Lu : PeriodicLatticeExtent) (S : Tower (scaleUp ell k Lu)),
      Admissible ell (ell ^ m) R k S → ∀ (f : ℕ) (sites : Set (PeriodicLatticeSite (scaleUp ell k Lu))) (j : ℕ),
        Cl' (scaleUp ell k Lu) ell (ell ^ m) k S f sites j ↔
          (Cl (scaleUp ell k Lu) ell (ell ^ m) k S f sites j ∧ Sh (scaleUp ell k Lu) ell (ell ^ m) f sites j))
    (h : FamTorusP Cl) : FamTorusP Cl' := by
  intro ell hell a ha
  obtain ⟨m₁, hm₁, R₁, a₀, ha₀, γ₀, hγ, hF⟩ := h ell hell a ha
  refine ⟨m₁, hm₁, R₁, a₀, ha₀, γ₀, hγ, fun m hm R hR k hk Lu α₀ hα F hFs hT S hS Lam hL U hU => ?_⟩
  let F' : CubeFam (scaleUp ell k Lu) := {t | t ∈ F ∧ Sh (scaleUp ell k Lu) ell (ell ^ m) t.2.2 t.1 t.2.1}
  refine hF m hm R hR k hk Lu α₀ hα F' (fun s j f hmem => hFs s j f hmem.1) hT S hS Lam hL U ?_
  obtain ⟨c1, c2, c3⟩ := hU
  refine ⟨fun x hx => ?_, fun p hp => ?_, fun f sites j hmem hCl => ?_⟩
  · obtain ⟨sites, j, ⟨f, hf, hq⟩, hx'⟩ := c1 x hx
    have hq' := (hequiv ell m R k Lu S hS f sites j).1 hq
    exact ⟨sites, j, ⟨f, ⟨hf, hq'.2⟩, hq'.1⟩, hx'⟩
  · obtain ⟨sites, j, ⟨f, hf, hq⟩, hx'⟩ := c2 p hp
    have hq' := (hequiv ell m R k Lu S hS f sites j).1 hq
    exact ⟨sites, j, ⟨f, ⟨hf, hq'.2⟩, hq'.1⟩, hx'⟩
  · exact c3 f sites j hmem.1 ((hequiv ell m R k Lu S hS f sites j).2 ⟨hCl, hmem.2⟩)

/-! ## the box reading -/

/-- the grid-aligned box shape of the r8 `DescribedAt`. -/
def boxShape (L : PeriodicLatticeExtent) (ell M f : ℕ) (sites : Set (PeriodicLatticeSite L)) (j : ℕ) : Prop :=
  ∃ z : PeriodicLatticeSite L, GridCorner (bigSide M ell j) z ∧ sites = siteBox z (f * bigSide M ell j)

theorem unionAt_of_described {L : PeriodicLatticeExtent} {ell M R f k : ℕ} {S : Tower L} (hS : Admissible ell M R k S)
    {sites : Set (PeriodicLatticeSite L)} {i : ℕ} (hd : DescribedAt ell M f k S sites i) : UnionAt ell M k S sites i := by
  have hc : IsClassCube ell M f k S sites i := AdalyFormal.Thin.isClassCube_of_described hS.1 hd
  obtain ⟨hik, -, hsub, hne⟩ := hd
  have hb : 0 < bigSide M ell i := AdalyFormal.Thin.bigSide_pos hS hik
  refine ⟨hik, fun x hx y hxy => ?_, hsub, hne⟩
  exact AdalyFormal.CoverGeom.classCube_sat hS hc hb dvd_rfl hx (fun μ => (hxy μ).symm)

theorem boxClass_iff {L : PeriodicLatticeExtent} {ell M R k : ℕ} {S : Tower L} (hS : Admissible ell M R k S) (f : ℕ)
    (sites : Set (PeriodicLatticeSite L)) (j : ℕ) :
    IsClassCube ell M f k S sites j ↔ (IsClassUnion ell M k S sites j ∧ boxShape L ell M f sites j) := by
  constructor
  · intro hc
    exact ⟨isClassUnion_of_unionAt hS.1 (unionAt_of_described hS hc.1), hc.1.2.1⟩
  · rintro ⟨hu, hz⟩
    obtain ⟨⟨hik, -, hsub, hne⟩, -⟩ := hu
    exact AdalyFormal.Thin.isClassCube_of_described hS.1 ⟨hik, hz, hsub, hne⟩

theorem boxClass_equiv (ell m R k : ℕ) (Lu : PeriodicLatticeExtent) (S : Tower (scaleUp ell k Lu))
    (hS : Admissible ell (ell ^ m) R k S) (f : ℕ) (sites : Set (PeriodicLatticeSite (scaleUp ell k Lu))) (j : ℕ) :
    boxClass (scaleUp ell k Lu) ell (ell ^ m) k S f sites j ↔
      (unionClass (scaleUp ell k Lu) ell (ell ^ m) k S f sites j ∧ boxShape (scaleUp ell k Lu) ell (ell ^ m) f sites j) :=
  boxClass_iff hS f sites j

/-- `MXQ.Total.P428Target8FamilyTorus` is the headline for the box class. -/
theorem familyTorus_eq_box : MXQ.Total.P428Target8FamilyTorus ↔ FamTorusP boxClass := Iff.rfl

/-- **the union headline implies the box headline**. -/
theorem famTorusU_imp_box : P428Target8FamilyTorusU → MXQ.Total.P428Target8FamilyTorus := fun h =>
  familyTorus_eq_box.2 (famTorusP_of_equiv boxShape (fun ell m R k Lu S hS f sites j => boxClass_equiv ell m R k Lu S hS f sites j) h)

/-! ## sub-class readings of the printed class (each follows from the union headline) -/

/-- reading U1: a union of blocks contained in an axis-aligned box of side `f·M·ℓ^j` (the printed "its size ... is O(1) M L^j η"). -/
def unionBoxClass : ClassPred := fun L ell M k S f sites j =>
  IsClassUnion ell M k S sites j ∧ ∃ z : PeriodicLatticeSite L, sites ⊆ siteBox z (f * bigSide M ell j)

/-- reading U2: a union of at least two level-`j` blocks ("several"). -/
def unionSeveralClass : ClassPred := fun L ell M k S f sites j =>
  IsClassUnion ell M k S sites j ∧
    ∃ x ∈ sites, ∃ y ∈ sites, ∃ μ : Fin 3, (x μ).val / bigSide M ell j ≠ (y μ).val / bigSide M ell j

theorem famTorus_unionBox : P428Target8FamilyTorusU → FamTorusP unionBoxClass := fun h =>
  famTorusP_of_equiv (Cl := unionClass)
    (fun L ell M f sites j => ∃ z : PeriodicLatticeSite L, sites ⊆ siteBox z (f * bigSide M ell j))
    (fun _ _ _ _ _ _ _ _ _ _ => Iff.rfl) h

theorem famTorus_unionSeveral : P428Target8FamilyTorusU → FamTorusP unionSeveralClass := fun h =>
  famTorusP_of_equiv (Cl := unionClass)
    (fun L ell M f sites j => ∃ x ∈ sites, ∃ y ∈ sites, ∃ μ : Fin 3, (x μ).val / bigSide M ell j ≠ (y μ).val / bigSide M ell j)
    (fun _ _ _ _ _ _ _ _ _ _ => Iff.rfl) h

end UNI.Total

#print axioms UNI.Total.famTorusU_imp_box
#print axioms UNI.Total.famTorus_unionBox
#print axioms UNI.Total.famTorus_unionSeveral
#print axioms UNI.Total.famTorusP_of_equiv
