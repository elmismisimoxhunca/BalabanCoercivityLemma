import NuE5
import NuE3
import NtCvOG9

/-!
# NuE6 -- explicit linear forms of the nested instance at `ell = 2` (lane ncwdh_ell2_20261018)

With the atoms `X = R*M`, `M`, `K = cf*M` the region boundaries at `ell = 2` are linear.
-/
set_option autoImplicit false
set_option maxHeartbeats 16000000

namespace AdalyFormal.NcwdhTwo

open Finset
open AdalyFormal.Target.ClayStatement
open AdalyFormal.CoverNested
open AdalyFormal.CoverOmega
open AdalyFormal.StatementLane (scaleUp)

section
variable [CfData]
variable {M R : ℕ}

theorem vals2 (M R : ℕ) :
    neA' 2 M R = 4 * (R * M) + 4 * M ∧ neB' 2 M R = 4 * (R * M) + 4 * (CfData.cf * M) ∧
    neA 2 M R = 4 * (R * M) + 4 * (CfData.cf * M) + 4 * M ∧ neB 2 M R = 12 * (R * M) + 4 * (CfData.cf * M) + 16 * M ∧
    neP1 2 M R = 2 * (R * M) + 4 * M ∧ neP0 2 M R = R * M + 4 * M ∧
    neQ1 2 M R = 14 * (R * M) + 4 * (CfData.cf * M) + 16 * M ∧ neQ0 2 M R = 15 * (R * M) + 4 * (CfData.cf * M) + 16 * M ∧
    neN 2 M R = 16 * (R * M) + 8 * (CfData.cf * M) + 24 * M ∧ neLo M R = 2 * (R * M) + CfData.cf * M + 2 * M := by
  have e1 : neA' 2 M R = 4 * (R * M) + 4 * M := by unfold neA'; ring
  have e2 : neB' 2 M R = 4 * (R * M) + 4 * (CfData.cf * M) := by unfold neB'; ring
  have e3 : neA 2 M R = 4 * (R * M) + 4 * (CfData.cf * M) + 4 * M := by unfold neA; ring
  have e4 : neB 2 M R = 12 * (R * M) + 4 * (CfData.cf * M) + 16 * M := by unfold neB; ring
  have e5 : neP1 2 M R = 2 * (R * M) + 4 * M := by
    unfold neP1; rw [e1]; omega
  have e6 : neP0 2 M R = R * M + 4 * M := by
    unfold neP0; rw [e5]; omega
  have e7 : neQ1 2 M R = 14 * (R * M) + 4 * (CfData.cf * M) + 16 * M := by
    unfold neQ1; rw [e4]; ring
  have e8 : neQ0 2 M R = 15 * (R * M) + 4 * (CfData.cf * M) + 16 * M := by
    unfold neQ0; rw [e7]; ring
  have e9 : neN 2 M R = 16 * (R * M) + 8 * (CfData.cf * M) + 24 * M := by unfold neN; ring
  have e10 : neLo M R = 2 * (R * M) + CfData.cf * M + 2 * M := by unfold neLo; ring
  exact ⟨e1, e2, e3, e4, e5, e6, e7, e8, e9, e10⟩

theorem neC0_val2 (hM : 0 < M) : neC0 2 M R + 1 = 4 * (R * M) + 4 * M + 2 * (CfData.cf * M) - 2 * M := by
  have hcf := CfData.hcf
  obtain ⟨e1, -⟩ := vals2 M R
  unfold neC0
  rw [e1]
  have : CfData.cf * (2 * M) = 2 * (CfData.cf * M) := by ring
  have h2 : 10 * M ≤ CfData.cf * M := Nat.mul_le_mul_right _ hcf
  omega

end

end AdalyFormal.NcwdhTwo
