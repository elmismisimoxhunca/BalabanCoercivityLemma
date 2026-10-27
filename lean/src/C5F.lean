import C5E

/-!
# C5F -- the unit-torus presentation (every `k`, every `Lu`), as for `p409_setw_holds`.
-/
set_option autoImplicit false
set_option maxHeartbeats 16000000
set_option maxRecDepth 8000

namespace AdalyFormal.P409C5

open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.GeneralClass (IsClassSetW)
open UNI.AllC (IsClassUnion)

/-- **p.409 cube, union reading, every depth.** On the fine torus `scaleUp ell k Lu` (`M < Lu mu + 1`), for every admissible tower `S`, every
`j <= k`, every `D_j` cube centre `c` (a level-`j` grid point with a `B^j` block in the 8 blocks around it): `tilde-square^5 cap Omega_0` is
contained in a block-closed union of level-`i` blocks that is in the union class `IsClassUnion` and in `IsClassSetW ell M (12*ell)`. -/
theorem cube5_in_union_scaleUp {ell M R k j : ℕ} {Lu : PeriodicLatticeExtent}
    (hell : 2 ≤ ell) (hM : 0 < M) (hLu : ∀ μ : Fin 3, M < Lu μ + 1) (hR : 21 * ell ≤ R)
    {S : Tower (scaleUp ell k Lu)} (hA : Admissible ell M R k S)
    {c : PeriodicLatticeSite (scaleUp ell k Lu)} (hD : IsDCube ell M k S j c) :
    ∃ (sites : Set (PeriodicLatticeSite (scaleUp ell k Lu))) (i : ℕ),
      IsClassSetW ell M (12 * ell) k S sites i ∧ IsClassUnion ell M k S sites i ∧
      BlockClosed (bigSide M ell i) sites ∧
      (printedCube5 (bigSide M ell j) c ∩ S.Om 0) ⊆ sites := by
  have hgt : ∀ μ : Fin 3, bigSide M ell k < scaleUp ell k Lu μ + 1 := by
    intro μ
    have h1 : 0 < ell ^ k := pow_pos (by omega) k
    have h2 : M * ell ^ k < (Lu μ + 1) * ell ^ k := Nat.mul_lt_mul_of_pos_right (hLu μ) h1
    have h3 : 0 < (Lu μ + 1) * ell ^ k := Nat.mul_pos (Nat.succ_pos _) h1
    show M * ell ^ k < (Lu μ + 1) * ell ^ k - 1 + 1
    omega
  exact cube5_in_union hell hM hR hA hgt hD

end AdalyFormal.P409C5
