import M1B

/-!
# OGP0 -- the clause-3-free stratum-scaled bounds `M1Bounds12` / `M1Regular12` (lane m2_onegap_20261015)

`M1Bounds12` = lane B's `M1Bounds` with the third clause (`ddA`, never read by the F1-F3 consumers) replaced by `True`; the first three components are
literally those of `M1Bounds` (so `hB.1`, `hB.2.1`, `hB.2.2.1` of the copied consumers have the same types).
-/
set_option autoImplicit false
namespace AdalyFormal.OneGap12

open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane (Tower HT)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.RMapLipschitz (frobNorm)
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
open AdalyFormal.M1 (bstrat)

variable {L : PeriodicLatticeExtent}

def M1Bounds12 (S : Tower L) (ell M f k : ℕ) (α₀ η : ℝ) (A : Bond L → Matrix (Fin 2) (Fin 2) ℂ) : Prop :=
  (∀ e : Bond L, HT (A e)) ∧
  (∀ (e : Bond L) (j : ℕ), j ≤ bstrat S k e →
      frobNorm (A e) < (f : ℝ) * M * α₀ * (((ell : ℝ) ^ j * η)⁻¹ ^ 1)) ∧
  (∀ (μ ν : Fin 3) (x : PeriodicLatticeSite L) (j : ℕ),
      j ≤ bstrat S k (x, ν) → j ≤ bstrat S k (periodicLatticeShift x μ, ν) →
      frobNorm ((η⁻¹ : ℝ) • (A (periodicLatticeShift x μ, ν) - A (x, ν)))
        < (f : ℝ) * M * α₀ * (((ell : ℝ) ^ j * η)⁻¹ ^ 2)) ∧
  True

def M1Regular12 (ell M f k : ℕ) (S : Tower L) (α₀ η : ℝ) (U : LinkCfg L) : Prop :=
  ∃ (g : PeriodicLatticeSite L → Matrix.specialUnitaryGroup (Fin 2) ℂ) (A : Bond L → Matrix (Fin 2) (Fin 2) ℂ),
    (∀ e : Bond L, ((periodicGaugeTransform g U e : Matrix.specialUnitaryGroup (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ)
        = NormedSpace.exp (((η : ℂ) * Complex.I) • A e)) ∧
    M1Bounds12 S ell M f k α₀ η A

end AdalyFormal.OneGap12

#print axioms AdalyFormal.OneGap12.M1Regular12
