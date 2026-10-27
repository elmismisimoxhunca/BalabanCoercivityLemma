import M2B5c
import M2B1
import AdalyFormal.Balaban.BlockingLinkEstimate

/-!
# M2B6a -- matrix/`frobNorm` helpers and the exact Leibniz identity for the cut-off field (m2_bridge_20261014, Layer B1)

* `frob_smul`, `frob_neg`, `frob_sub_le`, `frob_scaled` : `frobNorm` calculus for real scalars.
* `ddTerm_eq` : for ANY bond field `B` and `ν ≠ μ`,  `curlA η B (x-ν) ν μ - curlA η B x ν μ
    = η⁻¹ • (B(x,μ) - B(x-ν,μ) - B(x-ν+μ,ν) + B(x-ν,ν) - B(x+ν,μ) + B(x,μ) + B(x+μ,ν) - B(x,ν))`.
* `Rid` : the Leibniz identity  `Ẽ - χ0 • E = -p(aP-a0) - m(aM-a0) + q(bP-b0) - r(cM-b0) + m(dM-b0) - (p+m) a0 + (q-r+m) b0`
  (`p,m,q,r` = the cutoff differences `χ(x+ν)-χ(x)`, `χ(x-ν)-χ(x)`, `χ(x+μ)-χ(x)`, `χ(x-ν+μ)-χ(x)`).
No sorry / native_decide / axiom.
-/
set_option autoImplicit false
set_option maxHeartbeats 8000000

namespace AdalyFormal.M2Bridge

open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane AdalyFormal.StatementLane2
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.RMapLipschitz (frobNorm)
open AdalyFormal.Balaban.CovariantHjMinimizer (periodicLatticeShiftBack periodicLatticeShift_shiftBack)

variable {L : PeriodicLatticeExtent}

abbrev M2m := Matrix (Fin 2) (Fin 2) ℂ

theorem frob_smul (r : ℝ) (X : M2m) : frobNorm (r • X) = |r| * frobNorm X := by
  rw [← Complex.coe_smul]
  exact AdalyFormal.Balaban.BlockingLinkEstimate.frobNorm_real_smul r X

theorem frob_add_le (X Y : M2m) : frobNorm (X + Y) ≤ frobNorm X + frobNorm Y :=
  AdalyFormal.Balaban.BlockingLinkEstimate.frobNorm_add_le X Y

theorem frob_neg (X : M2m) : frobNorm (-X) = frobNorm X := by
  have := frob_smul (-1) X
  simpa using this

theorem frob_sub_le (X Y : M2m) : frobNorm (X - Y) ≤ frobNorm X + frobNorm Y := by
  rw [sub_eq_add_neg]
  calc frobNorm (X + -Y) ≤ frobNorm X + frobNorm (-Y) := frob_add_le _ _
    _ = frobNorm X + frobNorm Y := by rw [frob_neg]

theorem frob_sum_le {ι : Type*} (s : Finset ι) (f : ι → M2m) : frobNorm (∑ i ∈ s, f i) ≤ ∑ i ∈ s, frobNorm (f i) :=
  AdalyFormal.Balaban.BlockingLinkEstimate.frobNorm_sum_le s f

theorem frob_zero' : frobNorm (0 : M2m) = 0 := AdalyFormal.Balaban.RMapLipschitz.frobNorm_zero

/-- from a bound on `η⁻¹ • Δ` to a bound on `Δ`. -/
theorem frob_scaled {η : ℝ} (hη : 0 < η) {Δ : M2m} {c : ℝ} (h : frobNorm ((η⁻¹ : ℝ) • Δ) ≤ c) : frobNorm Δ ≤ η * c := by
  have e : Δ = η • ((η⁻¹ : ℝ) • Δ) := by
    rw [smul_smul, mul_inv_cancel₀ hη.ne', one_smul]
  have : frobNorm Δ = η * frobNorm ((η⁻¹ : ℝ) • Δ) := by
    conv_lhs => rw [e]
    rw [frob_smul, abs_of_pos hη]
  rw [this]
  exact mul_le_mul_of_nonneg_left h hη.le

/-- the field cut off by a site function. -/
noncomputable def cutA (χ : PeriodicLatticeSite L → ℝ) (A : Bond L → M2m) : Bond L → M2m := fun e => χ e.1 • A e

theorem ddA_def (η : ℝ) (B : Bond L → M2m) (x : PeriodicLatticeSite L) (μ : Fin 3) :
    ddA η B x μ = (η⁻¹ : ℝ) • ∑ ν ∈ Finset.univ.filter (fun ν : Fin 3 => ν ≠ μ),
      (curlA η B (periodicLatticeShiftBack x ν) ν μ - curlA η B x ν μ) := rfl

theorem ddTerm_eq (η : ℝ) (B : Bond L → M2m) (x : PeriodicLatticeSite L) (μ ν : Fin 3) :
    curlA η B (periodicLatticeShiftBack x ν) ν μ - curlA η B x ν μ
      = (η⁻¹ : ℝ) • (B (x, μ) - B (periodicLatticeShiftBack x ν, μ)
          - B (periodicLatticeShift (periodicLatticeShiftBack x ν) μ, ν) + B (periodicLatticeShiftBack x ν, ν)
          - B (periodicLatticeShift x ν, μ) + B (x, μ) + B (periodicLatticeShift x μ, ν) - B (x, ν)) := by
  unfold curlA
  rw [periodicLatticeShift_shiftBack]
  module

theorem Rid (χ0 χP χM χQ χR : ℝ) (a0 aP aM bP b0 cM dM : M2m) :
    ((χ0 • a0 - χM • aM - χR • cM + χM • dM - χP • aP + χ0 • a0 + χQ • bP - χ0 • b0)
      - χ0 • (a0 - aM - cM + dM - aP + a0 + bP - b0))
    = (-(χP - χ0)) • (aP - a0) - (χM - χ0) • (aM - a0) + (χQ - χ0) • (bP - b0) - (χR - χ0) • (cM - b0)
      + (χM - χ0) • (dM - b0) - ((χP - χ0) + (χM - χ0)) • a0
      + (((χQ - χ0) - (χR - χ0)) + (χM - χ0)) • b0 := by
  module

end AdalyFormal.M2Bridge

#print axioms AdalyFormal.M2Bridge.frob_scaled
#print axioms AdalyFormal.M2Bridge.ddTerm_eq
#print axioms AdalyFormal.M2Bridge.Rid
