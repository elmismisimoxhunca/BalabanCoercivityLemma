import SH12

/-!
# SH13 -- the local-domain corollaries of p409_local_20261019 under the SHARP collar (`collarOK`) instead of `21 ell <= R`.

`local_in_class_box_sharp` : `Omega_0(square)` (the p.408 local domain, `2 p <= M`) lies in the class box `tilde-square^5` of factor 12 / `12 ell`.
`localOm0_sub_Om0_sharp`   : it also lies in the global `Omega_0`.
(Both are the `collarOK` versions of `AdalyFormal.P409L.local_in_class_box`, `AdalyFormal.P409L.localOm0_sub_Om0`; no new construction.)
-/
set_option autoImplicit false
set_option maxHeartbeats 16000000
set_option maxRecDepth 8000

namespace AdalyFormal.P409S

open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane AdalyFormal.StatementLane2 AdalyFormal.StatementLaneG AdalyFormal.M2Bridge
open AdalyFormal.GeneralClass
open AdalyFormal.P409
open AdalyFormal.P409W
open AdalyFormal.P409C5
open AdalyFormal.P409L

variable {L : PeriodicLatticeExtent}

theorem local_in_class_box_sharp {ell M R k j' p : ℕ} {S : Tower L} {c : PeriodicLatticeSite L}
    (hell : 2 ≤ ell) (hM : 0 < M) (hcol : collarOK ell M R (j' + 1))
    (hA : Admissible ell M R k S) (hD : IsDCube ell M k S (j' + 1) c) (hp : 2 * p ≤ M) :
    ∃ i f : ℕ, ((i = j' + 1 ∧ f = 12) ∨ (i + 1 = j' + 1 ∧ f = 12 * ell)) ∧
      IsClassCubeG ell M f k S (printedCube5 (bigSide M ell (j' + 1)) c) i ∧
      localOm0 ell p (bigSide M ell (j' + 1)) (j' + 1) c ⊆ printedCube5 (bigSide M ell (j' + 1)) c := by
  obtain ⟨i, f, h1, -, -, h4⟩ := cube5_is_class_box_sharp hell hM hcol hA hD
  exact ⟨i, f, h1, h4, localOm0_sub_cube5 c (localHalf_le_six hell hp)⟩

theorem localOm0_sub_Om0_sharp {ell M R k j' p : ℕ} {S : Tower L} {c : PeriodicLatticeSite L}
    (hell : 2 ≤ ell) (hM : 0 < M) (hcol : collarOK ell M R (j' + 1))
    (hA : Admissible ell M R k S) (hD : IsDCube ell M k S (j' + 1) c) (hp : 2 * p ≤ M) :
    localOm0 ell p (bigSide M ell (j' + 1)) (j' + 1) c ⊆ S.Om 0 := fun _ hy =>
  AdalyFormal.GeneralClass.om_anti hA.1 (Nat.zero_le j')
    (cube5_in_Om_sharp hell hM hcol hA hD (localOm0_sub_cube5 c (localHalf_le_six hell hp) hy))

end AdalyFormal.P409S
