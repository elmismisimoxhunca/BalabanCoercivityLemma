import NB29
/-!
# NB30 -- per-cube tower class with BOX hypotheses (every `ell ≥ 2`)

`cube_tower_class_box`: as `cube_tower_class_na`, with the cone hypotheses replaced by: every plaquette at
every site with forward offsets `≤ 5 ell^l` from `c.1` has its four bonds in the cube, and every bond with
base offsets `≤ ell^l` from `c.1` is a cube bond (`5 ell^j < N`).

No sorry / native_decide / axioms.
-/
set_option autoImplicit false
noncomputable section
namespace AdalyFormal.CurvBlock
open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.SuTwoLogExp (SU2)
open AdalyFormal.Balaban.BlockedBackground (ubarTowerSU2)
open AdalyFormal.Balaban.AdmissibleSubspace (CoarseLattice)

variable {L : PeriodicLatticeExtent}

theorem cube_tower_class_box (ell : ℕ) (hell : 2 ≤ ell)
    {U : PeriodicLinkConfiguration SU2 L} {B : PeriodicLatticeEdge L → Prop} {η a : ℝ} (j : ℕ)
    (hη : 0 < η) (ha0 : 0 ≤ a) (ha1 : a ≤ 1)
    (K : CubeChart U B η (a * (((ell : ℝ) ^ j * η)⁻¹ ^ 1)) (a * (((ell : ℝ) ^ j * η)⁻¹ ^ 2)))
    (hdvd : ∀ ρ, ell ^ j ∣ L ρ + 1) (hN : ∀ ρ, 5 * ell ^ j < L ρ + 1)
    (hsm : 4000000 * (ell : ℝ) ^ 2 * ((4 * Real.pi + 4) * a) ≤ 1)
    (l : ℕ) (hlj : l ≤ j) (c : PeriodicLatticeEdge L) (hc : c.1 ∈ CoarseLattice L (ell ^ l))
    (hboxP : ∀ z, (∀ σ, off c.1 z σ ≤ 5 * ell ^ l) → ∀ ν μ : Fin 3, plaqIn B (z, ν, μ))
    (hboxB : ∀ b : PeriodicLatticeEdge L, (∀ σ, off c.1 b.1 σ ≤ ell ^ l) → B b) :
    dv (ubarTowerSU2 ell (periodicGaugeTransform K.g U) l c)
      ≤ a * (1 + 3 * Real.pi * (4 * Real.pi + 4)) * ((ell : ℝ) ^ l / (ell : ℝ) ^ j) := by
  have hN2 : ∀ ρ, 2 * ell ^ j < L ρ + 1 := fun ρ => by have := hN ρ; omega
  have hN1 : ∀ ρ, ell ^ j < L ρ + 1 := fun ρ => by have := hN ρ; omega
  exact cube_tower_class_na ell hell j hη ha0 ha1 K hdvd hN2 hsm l hlj c hc
    (goodBd_of_box ell hell _ j hN hdvd l hlj c hc hboxP)
    (goodL_of_box ell (by omega) B j hN1 l hlj c hboxB)

end AdalyFormal.CurvBlock

#print axioms AdalyFormal.CurvBlock.cube_tower_class_box
