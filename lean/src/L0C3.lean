import L0C2

/-!
# L0C3 -- the level-0 case of p.409 assembled (lane level0_class_20261019)

`P4L4.j0_print_holds` (lane p409_local_20261019): for a `D_0` cube `□` (p.408: a block in `T_1 \ Omega_1`), `Omega_0(□) = tilde-□^4` is a `DescribedAt0` box of factor 10 and `tilde-□^5` one of factor 12.
Here: both are cubes of the altered class WITH the p.396 unique-index clause (`IsClassCubeAlt`), and the family headline for that class holds unconditionally.
-/
set_option autoImplicit false
set_option maxHeartbeats 16000000

namespace AdalyFormal.L0C

open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane AdalyFormal.StatementLane2 AdalyFormal.StatementLaneG
open AdalyFormal.P409L
open AdalyFormal.P409C5
open UNI.Total

variable {L : PeriodicLatticeExtent}

theorem d0_in_altered_class {ell M R k p : ℕ} {S : Tower L} {c : PeriodicLatticeSite L}
    (hell : 2 ≤ ell) (hM : 0 < M) (hR : 21 * ell ≤ R) (hA : Admissible ell M R k S)
    (hD : IsDCubePrint ell M k S 0 c) :
    localOm0 ell p (bigSide M ell 0) 0 c = cubeR c (5 * M) ∧
    IsClassCubeAlt ell M 10 k S (cubeR c (5 * M)) 0 ∧
    IsClassCubeAlt ell M 12 k S (printedCube5 (bigSide M ell 0) c) 0 := by
  obtain ⟨h1, h2, h3⟩ := j0_print_holds (p := p) hell hM hR hA hD
  exact ⟨h1, (level0Class_iff hA _ 0).2 (Or.inl ⟨rfl, h2⟩), (level0Class_iff hA _ 0).2 (Or.inl ⟨rfl, h3⟩)⟩

/-- **the level-0 case of p.409 in Corollary 3.6, as a pair**: (i) every `D_0` cube's `Omega_0(□)` and `tilde-□^5` lie in a cube of the altered class (unique index `0`, factors `10`/`12`);
(ii) the family headline for the altered class (regularity of `U` demanded only on cube `∩ Omega_0`) holds. -/
theorem level0_case_complete :
    (∀ {L : PeriodicLatticeExtent} {ell M R k p : ℕ} {S : Tower L} {c : PeriodicLatticeSite L},
      2 ≤ ell → 0 < M → 21 * ell ≤ R → Admissible ell M R k S → IsDCubePrint ell M k S 0 c →
      localOm0 ell p (bigSide M ell 0) 0 c ⊆ cubeR c (5 * M) ∧
      IsClassCubeAlt ell M 10 k S (cubeR c (5 * M)) 0 ∧
      IsClassCubeAlt ell M 12 k S (printedCube5 (bigSide M ell 0) c) 0) ∧
    FamTorusCap := by
  refine ⟨fun hell hM hR hA hD => ?_, cap_unconditional⟩
  obtain ⟨h1, h2, h3⟩ := d0_in_altered_class (p := _) hell hM hR hA hD
  exact ⟨h1.le, h2, h3⟩

end AdalyFormal.L0C

#print axioms AdalyFormal.L0C.d0_in_altered_class
#print axioms AdalyFormal.L0C.level0_case_complete
