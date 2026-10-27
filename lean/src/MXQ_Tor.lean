import MXQ_F

/-!
# MXQ_Tor -- the family headline stated for ONE torus, in primitive terms (lane mixed_20261017, round 2)

`CF` (a family on every torus) is a presentational device of MXQ_F.  Here the family is a `CubeFam (scaleUp ell k Lu)`, chosen after `k, Lu, m, R, α₀`, and the class hypothesis `ClassCoupledF` is written with the
r8 `IsClassCube` and the clause body `RegBodyH` (pinned to `PerCubeRegular2` by `perCubeRegular2_iff := Iff.rfl`, MXQ_Base), with no reference to `CF`.
`embedFam F` extends `F` by the empty family on every other torus; `P428Target8Family` instantiated at `embedFam F` gives `P428Target8FamilyTorus`.
-/
set_option autoImplicit false

namespace MXQ.Total

open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLaneG
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
open MXQ.AllC

/-- a family on one torus, extended by the empty family elsewhere. -/
def embedFam {L0 : PeriodicLatticeExtent} (F : CubeFam L0) : CF :=
  fun L => {t | ∃ h : L = L0, (Eq.mp (congrArg (fun L => Set (PeriodicLatticeSite L) × ℕ × ℕ) h) t) ∈ F}

theorem mem_embedFam {L0 : PeriodicLatticeExtent} {F : CubeFam L0} {t : Set (PeriodicLatticeSite L0) × ℕ × ℕ} :
    t ∈ embedFam F L0 ↔ t ∈ F := by
  constructor
  · rintro ⟨h, ht⟩; exact ht
  · intro ht; exact ⟨rfl, ht⟩

/-- a described cube of the family `F` (one torus). -/
def IsClassCubeF {L : PeriodicLatticeExtent} (ell M : ℕ) (F : CubeFam L) (k : ℕ) (S : Tower L)
    (sites : Set (PeriodicLatticeSite L)) (j : ℕ) : Prop :=
  ∃ f, (sites, j, f) ∈ F ∧ IsClassCube ell M f k S sites j

/-- **the family class hypothesis, primitive form**: sites and plaquettes of `Ω₀` are covered by described cubes of `F`; every described cube of `F` is regular with its own factor `f`. -/
def ClassCoupledF {L : PeriodicLatticeExtent} (ell M : ℕ) (F : CubeFam L) (k : ℕ) (S : Tower L) (α₀ η : ℝ) (U : LinkCfg L) : Prop :=
  (∀ x ∈ S.Om 0, ∃ (sites : Set (PeriodicLatticeSite L)) (j : ℕ), IsClassCubeF ell M F k S sites j ∧ x ∈ sites) ∧
  (∀ p : PeriodicLatticePlaquette L, (∀ e ∈ periodicPlaquetteBoundaryEdges p, CubeBond (S.Om 0) e) →
    ∃ (sites : Set (PeriodicLatticeSite L)) (j : ℕ), IsClassCubeF ell M F k S sites j ∧
      ∀ e ∈ periodicPlaquetteBoundaryEdges p, CubeBond sites e) ∧
  (∀ (f : ℕ) (sites : Set (PeriodicLatticeSite L)) (j : ℕ), (sites, j, f) ∈ F →
    IsClassCube ell M f k S sites j → RegBodyH ell M f sites j α₀ η U)

theorem isClassCubeQ_embed {L0 : PeriodicLatticeExtent} {ell M k j : ℕ} {F : CubeFam L0} {S : Tower L0} {sites : Set (PeriodicLatticeSite L0)} :
    IsClassCubeQ ell M (embedFam F) k S sites j ↔ IsClassCubeF ell M F k S sites j := by
  unfold IsClassCubeQ IsClassCubeF
  simp only [mem_embedFam]

theorem classCoupledQ_embed {L0 : PeriodicLatticeExtent} {ell M k : ℕ} {F : CubeFam L0} {S : Tower L0} {α₀ η : ℝ} {U : LinkCfg L0} :
    ClassCoupledQ ell M (embedFam F) k S α₀ η U ↔ ClassCoupledF ell M F k S α₀ η U := by
  unfold ClassCoupledQ ClassCoupledF CoversOmQ CoversOmcQ CoversPlaqQ PerCubeRegularQ
  simp only [isClassCubeQ_embed, mem_embedFam]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩; exact ⟨h1, h2, h3⟩
  · rintro ⟨h1, h2, h3⟩; exact ⟨⟨h1, h2⟩, h3⟩

/-- **the family headline for one torus.** -/
def P428Target8FamilyTorus : Prop :=
  ∀ (ell : ℕ) (hell : 2 ≤ ell) (a : ℝ), 0 < a →
    ∃ m₁ : ℕ, 1 ≤ m₁ ∧ ∃ R₁ : ℕ, ∃ a₀ : ℝ, 0 < a₀ ∧ ∃ γ₀ : ℝ, 0 < γ₀ ∧
      ∀ m : ℕ, m₁ ≤ m → ∀ R : ℕ, R₁ ≤ R → ∀ (k : ℕ), 1 ≤ k → ∀ (Lu : PeriodicLatticeExtent) (α₀ : ℝ), 0 < α₀ →
        ∀ F : CubeFam (scaleUp ell k Lu),
          (∀ (s : Set (PeriodicLatticeSite (scaleUp ell k Lu))) (j f : ℕ), (s, j, f) ∈ F →
            10 ≤ f ∧ (f : ℝ) * ((ell ^ m : ℕ) : ℝ) * α₀ ≤ a₀) →
          TorusOK ell (ell ^ m) Lu →
          ∀ (S : Tower (scaleUp ell k Lu)), Admissible ell (ell ^ m) R k S →
          ∀ (Lam : Set (PeriodicLatticeSite Lu)), LambdaOK2 ell (ell ^ m) R k S Lam →
          ∀ (U : LinkCfg (scaleUp ell k Lu)),
            ClassCoupledF ell (ell ^ m) F k S α₀ ((ell : ℝ) ^ k)⁻¹ U →
            InstAtWD ell k (by omega) a Lu γ₀ S Lam U

theorem p428Target8FamilyTorus : P428Target8FamilyTorus := by
  intro ell hell a ha
  obtain ⟨m₁, hm₁, R₁, a₀, ha₀, γ₀, hγ, hF⟩ := p428Target8Family ell hell a ha
  refine ⟨m₁, hm₁, R₁, a₀, ha₀, γ₀, hγ, fun m hm R hR k hk Lu α₀ hα F hFs hT S hS Lam hL U hU => ?_⟩
  have hok : CubeFamOK (embedFam F) := ⟨fun L s j f hmem => by
    obtain ⟨h, ht⟩ := hmem
    subst h
    exact (hFs _ _ _ ht).1⟩
  have hsm : ∀ (L : PeriodicLatticeExtent) (s : Set (PeriodicLatticeSite L)) (j f : ℕ), (s, j, f) ∈ embedFam F L →
      (f : ℝ) * ((ell ^ m : ℕ) : ℝ) * α₀ ≤ a₀ := by
    intro L s j f hmem
    obtain ⟨h, ht⟩ := hmem
    subst h
    exact (hFs _ _ _ ht).2
  exact hF (embedFam F) hok m hm R hR k hk Lu α₀ hα hsm hT S hS Lam hL U (classCoupledQ_embed.2 hU)

end MXQ.Total

#print axioms MXQ.Total.p428Target8FamilyTorus
#print axioms MXQ.Total.classCoupledQ_embed
