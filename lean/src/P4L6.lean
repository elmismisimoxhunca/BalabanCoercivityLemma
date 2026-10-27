import P4L5

/-!
# P4L6 -- insensitivity to the (garbled) closed form of the collar sum on p.408.

The page prints `dist(Omega_n(square)^c, tilde-square^4) = 2R_0M_0L^nη + ... + 2R_0M_0L^{j-1}η = 2R_0M_0L^nη (L^{j-n} - 1/L - 1)`; the last closed form does not equal the sum of the listed terms,
so the half side `r0` of `Omega_0(square)` is read two ways.  This theorem does NOT use `localHalf` at all: for EVERY half side `r0` with `5 g ≤ r0 ≤ 6 g` (the print's only
stated constraint is `Omega_0(square) ⊂ tilde-square^5`, and `Omega_0(square) ⊇ tilde-square^4`) the cube `cubeR c r0` is in no class set of factor `f ≤ 10 ell - 1` (in particular `f = 12` for `ell >= 2`).
-/
set_option autoImplicit false
set_option maxHeartbeats 16000000
set_option maxRecDepth 8000

namespace AdalyFormal.P409L

open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane AdalyFormal.StatementLane2 AdalyFormal.StatementLaneG AdalyFormal.M2Bridge
open AdalyFormal.GeneralClass
open AdalyFormal.P409
open AdalyFormal.P409W
open AdalyFormal.P409C5

theorem anyr0_print_fails {ell M R r0 : ℕ} {Lf : PeriodicLatticeExtent}
    (hell : 2 ≤ ell) (hM : 0 < M) (hR : 21 * ell ≤ R)
    (hLf : ∀ μ, Lf μ + 1 = M * ell * (4 * R + 8))
    (hr5 : 5 * bigSide M ell 1 ≤ r0) (hr6 : r0 ≤ 6 * bigSide M ell 1) :
    ∃ (S : Tower Lf) (c : PeriodicLatticeSite Lf), Admissible ell M R 1 S ∧ IsDCube ell M 1 S 1 c ∧
      (∃ q, q ∈ towerBj S 0) ∧ (∃ q, q ∈ towerBj S 1) ∧
      cubeR c r0 ⊆ printedCube5 (bigSide M ell 1) c ∧ tildeCube 4 (bigSide M ell 1) c ⊆ cubeR c r0 ∧
      ∀ f : ℕ, f + 1 ≤ 10 * ell → ∀ (sites : Set (PeriodicLatticeSite Lf)) (i : ℕ),
        DescribedAt ell M f 1 S sites i → ¬ cubeR c r0 ⊆ sites := by
  obtain ⟨A0, A, B, B0, w, hAdm, hD, hN, hA0, hAB, hBB0, hAN, hw0, hw1, hw2, hq0, hq1, hgt, -, -⟩ :=
    tg_setup (Lf := Lf) hell hM hR hLf
  have hg : bigSide M ell 1 = M * ell := bigSide1 M ell
  have hg2 : M * 2 ≤ M * ell := Nat.mul_le_mul_left M hell
  refine ⟨TG A0 A B B0 Lf, w, hAdm, hD, hq0, hq1, ?_, ?_, ?_⟩
  · rw [printedCube5_eq]; exact cubeR_mono hr6
  · unfold tildeCube; exact cubeR_mono (by omega)
  · intro f hf sites i hDesc hsub
    obtain ⟨hik, ⟨z, hzeq⟩, hsB, -⟩ := hDesc
    refine tg_box_lower (ell := ell) (M := M) hN hA0 hAB hBB0 hAN r0 (by omega) ?_ f ?_ w hw0 hw1 hw2
      ⟨sites, i, hik, hsB, ⟨z, hzeq.2.subset⟩, fun y hy => hsub hy.1⟩
    · have : 24 * (M * ell) ≤ M * ell * (4 * R + 8) := by nlinarith
      omega
    · have : (f + 1) * M ≤ 10 * ell * M := Nat.mul_le_mul_right M hf
      have e : 10 * ell * M = 10 * (M * ell) := by ring
      have e2 : (f + 1) * M = f * M + M := by ring
      omega

end AdalyFormal.P409L

open AdalyFormal.P409L in
#print axioms anyr0_print_fails
