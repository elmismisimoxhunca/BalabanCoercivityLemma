import RawTower
import Lean.Util.CollectAxioms

set_option autoImplicit false

/-!
The literal output-only repair requested for `OneStepPropagationRaw`.
No raw operator, certified definition, or imported theorem is changed.

IMPORTANT: this proposition is not an induction hypothesis closed under the raw
physical-coordinate tower. Its input is global; its output is restricted. See
`ScaleFittedTower.lean` for a separately named, scale-aware conditional theorem.
We deliberately do NOT claim that theorem follows from this weaker proposition.
-/
noncomputable section
namespace DepthUniformity.Fitted

open AdalyFormal.Target.ClayStatement
  (PeriodicLatticeExtent PeriodicLatticeSite PeriodicLinkConfiguration)
open AdalyFormal.Balaban.SuTwoLogExp (SU2 M2)
open AdalyFormal.Balaban.RMapLipschitz (frobNorm)
open AdalyFormal.Balaban.AdmissibleSubspace (CoarseLattice)
open AdalyFormal.Balaban.BlockedBackground (ubarSU2)
open DepthUniformity.Strided (orientedPlaqHolS)

variable {L : PeriodicLatticeExtent}

/-- Literal output-only repair. The output basepoint must lie in the EXISTING
`CoarseLattice L ell`. The input quantifier, stride, polynomial, and raw average
are unchanged. This definition alone makes no assertion of truth. -/
def OneStepPropagationFitted (ell : ℕ) (C0 c2' : ℝ) : Prop :=
  ∀ (s : ℕ) (V : PeriodicLinkConfiguration SU2 L) (β : ℝ),
    0 ≤ β → β ≤ c2' →
    (∀ (y : PeriodicLatticeSite L) (μ ν : Fin 3),
      frobNorm (((orientedPlaqHolS s V y μ ν : SU2) : M2) - 1) ≤ β) →
    ∀ (y : PeriodicLatticeSite L), y ∈ CoarseLattice L ell →
      ∀ (μ ν : Fin 3),
      frobNorm
        (((orientedPlaqHolS (s * ell) (ubarSU2 s ell V) y μ ν : SU2) : M2) - 1) ≤
        (ell : ℝ)^2 * β + C0 * ((ell : ℝ)^2 * β)^2

theorem OneStepPropagationFitted_iff (ell : ℕ) (C0 c2' : ℝ) :
    OneStepPropagationFitted (L := L) ell C0 c2' ↔
    ∀ (s : ℕ) (V : PeriodicLinkConfiguration SU2 L) (β : ℝ),
      0 ≤ β → β ≤ c2' →
      (∀ (y : PeriodicLatticeSite L) (μ ν : Fin 3),
        frobNorm (((orientedPlaqHolS s V y μ ν : SU2) : M2) - 1) ≤ β) →
      ∀ (y : PeriodicLatticeSite L), y ∈ CoarseLattice L ell →
        ∀ (μ ν : Fin 3),
        frobNorm
          (((orientedPlaqHolS (s * ell) (ubarSU2 s ell V) y μ ν : SU2) : M2) - 1) ≤
          (ell : ℝ)^2 * β + C0 * ((ell : ℝ)^2 * β)^2 := Iff.rfl

/-- A comparison of logical strength only, not a use of the refuted antecedent. -/
theorem raw_implies_fitted (ell : ℕ) (C0 c2' : ℝ)
    (h : DepthUniformity.RawTower.OneStepPropagationRaw (L := L) ell C0 c2') :
    OneStepPropagationFitted (L := L) ell C0 c2' := by
  intro s V β hβ hc hV y _ μ ν
  exact h s V β hβ hc hV y μ ν

end DepthUniformity.Fitted

run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for n in #[`DepthUniformity.Fitted.OneStepPropagationFitted,
      `DepthUniformity.Fitted.OneStepPropagationFitted_iff,
      `DepthUniformity.Fitted.raw_implies_fitted] do
    let axioms ← Lean.collectAxioms n
    Lean.logInfo m!"FITTED_AXIOMS {n}: {axioms}"
    for ax in axioms do
      unless allowed.contains ax do
        throwError "Nonstandard axiom in {n}: {ax}"
