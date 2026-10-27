import AC_GE2
import AC_Base

/-!
# AC_CF -- cube-factor-FREE index lemma (lane allc_20261016, uniform-in-c milestone A1)

`cubeIndex_ge_pred`: a class cube of ANY factor `c` through a point of `Omega_n` has index `j >= n - 1` (`n <= j + 1`): the cube lies in `Omega_j \ Omega_{j+2}` and `Omega_n subset Omega_{j+2}` if `n >= j+2`.
No margin in `R`, no hypothesis on `c`.  Consequence `cube_blockClosed_pred`: that cube is a union of `b_{n-1}`-blocks.
(Contrast `AC_GE2.cube_scaleAC`, which needs `2 pdist + 3 c b_m <= 2 R b_m`.)
-/
set_option autoImplicit false
namespace AdalyFormal.M2GlueGeo

open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane AdalyFormal.StatementLane2
open AdalyFormal.M1 (om_anti)

variable {L : PeriodicLatticeExtent}

theorem cubeIndex_ge_pred {ell M R k c : ℕ} {S : Tower L} (hS : Admissible ell M R k S)
    {sites : Set (PeriodicLatticeSite L)} {j : ℕ} (hq : IsClassCube ell M c k S sites j)
    {q0 : PeriodicLatticeSite L} (hq0 : q0 ∈ sites) {n : ℕ} (hn : q0 ∈ S.Om n) : n ≤ j + 1 := by
  by_contra hc
  have hjn : j + 2 ≤ n := by omega
  have h2 : S.Om n ⊆ S.Om (j + 2) := om_anti hS hjn
  obtain ⟨-, -, hsub, -⟩ := hq.1
  rcases hsub hq0 with h | h
  · exact h.2 (om_anti hS (by omega : j + 1 ≤ j + 2) (h2 hn))
  · exact h.2 (h2 hn)

theorem cube_blockClosed_pred {ell M R k c : ℕ} {S : Tower L} (hS : Admissible ell M R k S) (hell : 2 ≤ ell) (hM : 0 < M)
    {sites : Set (PeriodicLatticeSite L)} {j : ℕ} (hq : IsClassCube ell M c k S sites j)
    {q0 : PeriodicLatticeSite L} (hq0 : q0 ∈ sites) {n : ℕ} (hn : q0 ∈ S.Om n) (hnk : n - 1 ≤ k) (hc : 10 ≤ c) :
    BlockClosed (bigSide M ell (n - 1)) sites :=
  haveI : AdalyFormal.AllC.CubeFactor c := ⟨hc⟩
  AdalyFormal.M2GlueGeo.cube_blockClosedAC (fc := c) hS hell hM hnk hq (by have := cubeIndex_ge_pred hS hq hq0 hn; omega)

end AdalyFormal.M2GlueGeo

#print axioms AdalyFormal.M2GlueGeo.cubeIndex_ge_pred
#print axioms AdalyFormal.M2GlueGeo.cube_blockClosed_pred
