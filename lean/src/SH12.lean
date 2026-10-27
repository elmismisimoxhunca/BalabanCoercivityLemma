import SH11

/-!
# SH12 -- non-degeneracy witnesses and numerical instances.

* `torus_hyps_satisfiable` : the torus hypotheses of `cube5_sharp_all` / `cube5_fails_below_deep` are satisfiable for every `ell M R k`.
* `collar_values` : the threshold at `(ell, M, j) = (2, 1, 1)` is `R = 36` (not `42 = 21 ell`), at `(2, 3, 1)` it is `34`, at `(3, 1, 2)` it is `52`.
* `inst_sharp`, `inst_fails` : the two headline theorems instantiated at `ell = 2, M = 1, k = 1, j = 1` with `R = 36` and `R = 35` (the exact edge).
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

theorem torus_hyps_satisfiable (ell M R k : ℕ) (hM : 0 < M) (hell : 2 ≤ ell) :
    ∃ Lf : PeriodicLatticeExtent, (∀ μ : Fin 3, bigSide M ell k ∣ Lf μ + 1) ∧
      (∀ μ : Fin 3, (5 * R + 40) * bigSide M ell k ≤ Lf μ + 1) ∧ (∀ μ : Fin 3, bigSide M ell k < Lf μ + 1) := by
  have hgk : 0 < bigSide M ell k := bigSide_pos' hM (by omega) k
  have h1 : 1 ≤ (5 * R + 40) * bigSide M ell k := by nlinarith
  refine ⟨fun _ => (5 * R + 40) * bigSide M ell k - 1, ?_, ?_, ?_⟩
  · intro μ
    show bigSide M ell k ∣ (5 * R + 40) * bigSide M ell k - 1 + 1
    rw [Nat.sub_add_cancel h1]
    exact Dvd.intro_left _ rfl
  · intro μ
    show _ ≤ (5 * R + 40) * bigSide M ell k - 1 + 1
    rw [Nat.sub_add_cancel h1]
  · intro μ
    show _ < (5 * R + 40) * bigSide M ell k - 1 + 1
    rw [Nat.sub_add_cancel h1]
    nlinarith

theorem collar_values :
    (collarOK 2 1 36 1 ∧ ¬ collarOK 2 1 35 1 ∧ 36 < 21 * 2) ∧
    (collarOK 2 3 34 1 ∧ ¬ collarOK 2 3 33 1 ∧ 34 < 21 * 2) ∧
    (collarOK 3 1 52 2 ∧ ¬ collarOK 3 1 51 2 ∧ 52 < 21 * 3) := by
  refine ⟨⟨?_, ?_, by norm_num⟩, ⟨?_, ?_, by norm_num⟩, ⟨?_, ?_, by norm_num⟩⟩ <;>
    simp [collarOK, bigSide]

/-- the sharpness headline at `ell = 2, M = 1, k = 1, j = 1`, `R = 36` (the least admissible collar there). -/
theorem inst_sharp :
    ∃ (Lf : PeriodicLatticeExtent) (S : Tower Lf) (c : PeriodicLatticeSite Lf),
      Admissible 2 1 36 1 S ∧ IsDCube 2 1 1 S 1 c ∧ (∀ i : ℕ, i ≤ 1 → ∃ q, q ∈ towerBj S i) ∧
      IsClassCubeG 2 1 24 1 S (printedCube5 (bigSide 1 2 1) c) 0 ∧
      (∀ F : ℕ, F + 1 ≤ 24 → ¬ ∃ (sites : Set (PeriodicLatticeSite Lf)) (i : ℕ),
        IsClassSetW 2 1 F 1 S sites i ∧ printedCube5 (bigSide 1 2 1) c ⊆ sites) := by
  obtain ⟨Lf, hdiv, hbig, -⟩ := torus_hyps_satisfiable 2 1 36 1 (by norm_num) (by norm_num)
  have hcol : collarOK 2 1 36 (0 + 1) := collar_values.1.1
  obtain ⟨S, c, hA, -, hD, hstr, -, hW, -, -, hG⟩ := cube5_sharp_all (j' := 0) (k := 1) (Lf := Lf) (by norm_num) (by norm_num) hcol
    (by norm_num) hdiv hbig
  exact ⟨Lf, S, c, hA, hD, hstr, hG, hW⟩

/-- the failure headline at `ell = 2, M = 1, k = 1, j = 1`, `R = 35` (one below the threshold). -/
theorem inst_fails :
    ∃ (Lf : PeriodicLatticeExtent) (S : Tower Lf) (c : PeriodicLatticeSite Lf),
      Admissible 2 1 35 1 S ∧ IsDCube 2 1 1 S 1 c ∧ (∀ i : ℕ, i ≤ 1 → ∃ q, q ∈ towerBj S i) ∧
      (∃ y ∈ printedCube5 (bigSide 1 2 1) c, y ∉ S.Om 0) ∧
      ¬ ∃ i f : ℕ, ((i = 1 ∧ f = 12) ∨ (i + 1 = 1 ∧ f = 12 * 2)) ∧
        DescribedAt 2 1 f 1 S (printedCube5 (bigSide 1 2 1) c) i := by
  obtain ⟨Lf, hdiv, hbig, -⟩ := torus_hyps_satisfiable 2 1 35 1 (by norm_num) (by norm_num)
  have hlow : (35 + 3) * bigSide 1 2 0 < 18 * bigSide 1 2 (0 + 1) + 3 := by simp [bigSide]
  obtain ⟨S, c, hA, -, hD, hstr, hy, -, hnot⟩ := cube5_fails_below_deep (j' := 0) (k := 1) (Lf := Lf) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hlow hdiv hbig
  exact ⟨Lf, S, c, hA, hD, hstr, hy, hnot⟩

end AdalyFormal.P409S
