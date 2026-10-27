import UNI_F

/-!
# UNI_Tor -- the family headline for ONE torus with the class "union of several big blocks" (lane union_cubes_20261018)

`MXQ_Tor.P428Target8FamilyTorus` (proved) takes the class cubes to be grid-aligned BOXES `z + f·M·ℓ^i` (r8 `IsClassCube`).  The print (CMP99b p.396) says "□ is a union of several big blocks of the lattice `T_{L^{-j}}`".
Here the box clause of `DescribedAt` is replaced by `BlockClosed (M ℓ^i) □` (`UNI_Base.UnionAt`, `UNI_Base.IsClassUnion`), in BOTH the coverage clauses and the per-member regularity clause; everything else is verbatim.
`ClassCoupledP Cl` is the class hypothesis for an arbitrary class predicate `Cl`; `FamTorusP Cl` the headline for it.  The box headline and the union headline are the two instances (`Iff.rfl`/`rfl`).
-/
set_option autoImplicit false

namespace UNI.Total

open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLaneG
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
open UNI.AllC

/-- a class predicate: for the torus `L`, parameters `ell M k`, tower `S`, the cube factor `f`, the site set and the index `j`. -/
abbrev ClassPred : Type :=
  ∀ (L : PeriodicLatticeExtent) (ell M k : ℕ) (_S : Tower L) (_f : ℕ) (_sites : Set (PeriodicLatticeSite L)) (_j : ℕ), Prop

/-- the r8 class: `IsClassCube` (grid-aligned box of side `f·M·ℓ^j`). -/
def boxClass : ClassPred := fun L ell M k S f sites j => IsClassCube ell M f k S sites j

/-- the printed class read as "a union of big blocks of level `j`" (no size clause). -/
def unionClass : ClassPred := fun L ell M k S _f sites j => IsClassUnion ell M k S sites j

/-- a described cube of the family `F` for the class `Cl`. -/
def IsClassCubeP {L : PeriodicLatticeExtent} (Cl : ClassPred) (ell M : ℕ) (F : CubeFam L) (k : ℕ) (S : Tower L)
    (sites : Set (PeriodicLatticeSite L)) (j : ℕ) : Prop :=
  ∃ f, (sites, j, f) ∈ F ∧ Cl L ell M k S f sites j

/-- **the family class hypothesis for the class `Cl`**: sites and plaquettes of `Ω₀` are covered by `Cl`-cubes of `F`; every `Cl`-cube of `F` is regular with its own factor `f`. -/
def ClassCoupledP {L : PeriodicLatticeExtent} (Cl : ClassPred) (ell M : ℕ) (F : CubeFam L) (k : ℕ) (S : Tower L) (α₀ η : ℝ) (U : LinkCfg L) : Prop :=
  (∀ x ∈ S.Om 0, ∃ (sites : Set (PeriodicLatticeSite L)) (j : ℕ), IsClassCubeP Cl ell M F k S sites j ∧ x ∈ sites) ∧
  (∀ p : PeriodicLatticePlaquette L, (∀ e ∈ periodicPlaquetteBoundaryEdges p, CubeBond (S.Om 0) e) →
    ∃ (sites : Set (PeriodicLatticeSite L)) (j : ℕ), IsClassCubeP Cl ell M F k S sites j ∧
      ∀ e ∈ periodicPlaquetteBoundaryEdges p, CubeBond sites e) ∧
  (∀ (f : ℕ) (sites : Set (PeriodicLatticeSite L)) (j : ℕ), (sites, j, f) ∈ F →
    Cl L ell M k S f sites j → RegBodyH ell M f sites j α₀ η U)

/-- **the family headline for one torus, for the class `Cl`.** -/
def FamTorusP (Cl : ClassPred) : Prop :=
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
            ClassCoupledP Cl ell (ell ^ m) F k S α₀ ((ell : ℝ) ^ k)⁻¹ U →
            InstAtWD ell k (by omega) a Lu γ₀ S Lam U

/-- the union-class family class hypothesis, written out. -/
def ClassCoupledU {L : PeriodicLatticeExtent} (ell M : ℕ) (F : CubeFam L) (k : ℕ) (S : Tower L) (α₀ η : ℝ) (U : LinkCfg L) : Prop :=
  (∀ x ∈ S.Om 0, ∃ (sites : Set (PeriodicLatticeSite L)) (j : ℕ),
    (∃ f, (sites, j, f) ∈ F ∧ IsClassUnion ell M k S sites j) ∧ x ∈ sites) ∧
  (∀ p : PeriodicLatticePlaquette L, (∀ e ∈ periodicPlaquetteBoundaryEdges p, CubeBond (S.Om 0) e) →
    ∃ (sites : Set (PeriodicLatticeSite L)) (j : ℕ), (∃ f, (sites, j, f) ∈ F ∧ IsClassUnion ell M k S sites j) ∧
      ∀ e ∈ periodicPlaquetteBoundaryEdges p, CubeBond sites e) ∧
  (∀ (f : ℕ) (sites : Set (PeriodicLatticeSite L)) (j : ℕ), (sites, j, f) ∈ F →
    IsClassUnion ell M k S sites j → RegBodyH ell M f sites j α₀ η U)

theorem classCoupledU_eq {L : PeriodicLatticeExtent} {ell M k : ℕ} {F : CubeFam L} {S : Tower L} {α₀ η : ℝ} {U : LinkCfg L} :
    ClassCoupledU ell M F k S α₀ η U ↔ ClassCoupledP unionClass ell M F k S α₀ η U := Iff.rfl

/-- **`P428Target8FamilyTorusU`**: the family headline for one torus; the class cubes are the printed "unions of several big blocks of level `j`" (`IsClassUnion`); statement otherwise identical to `MXQ.Total.P428Target8FamilyTorus`. -/
def P428Target8FamilyTorusU : Prop :=
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
            ClassCoupledU ell (ell ^ m) F k S α₀ ((ell : ℝ) ^ k)⁻¹ U →
            InstAtWD ell k (by omega) a Lu γ₀ S Lam U

theorem p428Target8FamilyTorusU_eq : P428Target8FamilyTorusU ↔ FamTorusP unionClass := Iff.rfl

/-! ## the proof: `P428Target8Family` (this lane's `UNI_F`, the family theorem for `IsClassCubeQ`/`IsClassUnion`) at the extension of `F` by the empty family -/

/-- a family on one torus, extended by the empty family elsewhere. -/
def embedFam {L0 : PeriodicLatticeExtent} (F : CubeFam L0) : CF :=
  fun L => {t | ∃ h : L = L0, (Eq.mp (congrArg (fun L => Set (PeriodicLatticeSite L) × ℕ × ℕ) h) t) ∈ F}

theorem mem_embedFam {L0 : PeriodicLatticeExtent} {F : CubeFam L0} {t : Set (PeriodicLatticeSite L0) × ℕ × ℕ} :
    t ∈ embedFam F L0 ↔ t ∈ F := by
  constructor
  · rintro ⟨h, ht⟩; exact ht
  · intro ht; exact ⟨rfl, ht⟩

theorem isClassCubeQ_embed {L0 : PeriodicLatticeExtent} {ell M k j : ℕ} {F : CubeFam L0} {S : Tower L0} {sites : Set (PeriodicLatticeSite L0)} :
    IsClassCubeQ ell M (embedFam F) k S sites j ↔ IsClassCubeP unionClass ell M F k S sites j := by
  unfold IsClassCubeQ IsClassCubeP unionClass
  simp only [mem_embedFam]

theorem classCoupledQ_embed {L0 : PeriodicLatticeExtent} {ell M k : ℕ} {F : CubeFam L0} {S : Tower L0} {α₀ η : ℝ} {U : LinkCfg L0} :
    ClassCoupledQ ell M (embedFam F) k S α₀ η U ↔ ClassCoupledU ell M F k S α₀ η U := by
  unfold ClassCoupledQ ClassCoupledU CoversOmQ CoversOmcQ CoversPlaqQ PerCubeRegularQ
  simp only [isClassCubeQ_embed, mem_embedFam, IsClassCubeP, unionClass]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩; exact ⟨h1, h2, h3⟩
  · rintro ⟨h1, h2, h3⟩; exact ⟨⟨h1, h2⟩, h3⟩

theorem p428Target8FamilyTorusU : P428Target8FamilyTorusU := by
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

end UNI.Total

#print axioms UNI.Total.p428Target8FamilyTorusU
#print axioms UNI.Total.classCoupledQ_embed
