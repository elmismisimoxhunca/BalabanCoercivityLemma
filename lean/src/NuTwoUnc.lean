import NuTwoGeo

/-!
# NuTwoUnc -- at `ell = 2` the CENTRAL direction-0 bond of the thin component lies in no class cube (lane ncwdh_ell2_20261018)

`NsCvNe2.ne_layer_uncovered` (every site of the layer `x_0 = A' + cf Y_1` is in no class cube) needs `3 <= ell`: its omega goal `A' + 2 cf Y_1 <= B'` is
`2 cf <= (cf-1) ell`.  At `ell = 2` the thin component `[A', B') = [A', A' + (cf-1) Y_2)` is exactly `2 (cf-1)` cells of the level-1 grid (cell `Y_1 = 2M`), and the
level-1 aligned boxes of side `cf Y_1` that contain BOTH endpoints of the direction-0 bond `(xs, xs+1)`, `xs + 1 = A' + (cf-1) Y_1`, all lie inside the thin component.
So that bond (all `(x_1,x_2)`) is in no class cube: `PerCubeRegular2` does not constrain `U` on it.

* `neC0 ell M R` : the `x_0` of the lower endpoint, `A' + cf (ell M) - (ell M + 1)`.
* `ne2_bond_uncovered` : `ell = 2`: no class cube (any index `j`) contains both `x` and `x + e_0`, when `x_0 = neC0 2 M R`.
-/
set_option autoImplicit false
set_option maxRecDepth 8000
set_option maxHeartbeats 16000000

namespace AdalyFormal.CoverNested

open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLane2
open AdalyFormal.StatementLaneG
open AdalyFormal.Balaban.AdmissibleSubspace (Bond blockOf CoarseLattice mem_blockOf mem_CoarseLattice staircasePath)
open AdalyFormal.NonVac (pcd_gt_right2 pcd_gt_left2 iv_iff shift_val_N mem_box_N)
open AdalyFormal.NoCover (off_cases perCube_one pStar bStar_mem)

section nums
variable [CfData]
local notation "cfv" => CfData.cf

/-- the `x_0` of the lower endpoint of the central direction-0 bond of the thin component: `xs + 1 = A' + (cf - 1) (ell M)`. -/
def neC0 (ell M R : ℕ) : ℕ := neA' ell M R + cfv * (ell * M) - (ell * M + 1)

/-- thin interval, `x` inside, box of side `s` longer than the interval containing `x`: the box contains `P - 1` or `Q` (both outside `[P,Q)`). -/
theorem arith_thin (N x z P Q s : ℕ) (hxN : x < N) (hzN : z < N) (hP : 1 ≤ P) (hx : P ≤ x ∧ x < Q) (hQ : Q < N)
    (hs : (x + N - z) % N < s) (hthin : Q - P < s) :
    ∃ y0, y0 < N ∧ (y0 + N - z) % N < s ∧ ¬ (P ≤ y0 ∧ y0 < Q) ∧ (y0 = P - 1 ∨ y0 = Q) := by
  have hPm : P - 1 < N := by omega
  rw [off_cases N _ _ hxN hzN] at hs
  by_cases hc : x - P + 1 ≤ (if z ≤ x then x - z else x + N - z)
  · refine ⟨P - 1, hPm, ?_, by omega, Or.inl rfl⟩
    rw [off_cases N _ _ hPm hzN]
    split_ifs at hc hs ⊢ <;> omega
  · refine ⟨Q, hQ, ?_, by omega, Or.inr rfl⟩
    rw [off_cases N _ _ hQ hzN]
    split_ifs at hc hs ⊢ <;> omega

/-- the level-1 cell arithmetic: a box of side `Y cf` with corner `z` a multiple of `Y`, containing both `x` and `x + 1 = Y K`, and a further point `w`,
forces `w ∈ [Y (K - cf + 1), Y (K + cf - 1))`. -/
theorem arith_cell (N Y cf K z x w : ℕ) (hY : 0 < Y) (hxN : x < N) (hzN : z < N) (hwN : w < N)
    (hx : x + 1 = Y * K) (hz : Y ∣ z) (hcf1 : 1 ≤ cf) (hcfK : cf ≤ K)
    (h1 : (x + N - z) % N < Y * cf) (h2 : (x + 1 + N - z) % N < Y * cf) (hw : (w + N - z) % N < Y * cf)
    (hBN : Y * (K + cf - 1) < N) :
    Y * (K - cf + 1) ≤ w ∧ w < Y * (K + cf - 1) := by
  obtain ⟨q, rfl⟩ := hz
  have hKle : Y * K ≤ Y * (K + cf - 1) := Nat.mul_le_mul_left Y (by omega)
  have hx1N : x + 1 < N := by omega
  rw [off_cases N _ _ hxN hzN] at h1
  rw [off_cases N _ _ hx1N hzN] at h2
  by_cases hzx : Y * q ≤ x
  · rw [if_pos hzx] at h1
    rw [if_pos (by omega)] at h2
    have hq1 : K < q + cf := by
      by_contra hcon
      rw [not_lt] at hcon
      have : Y * (q + cf) ≤ Y * K := Nat.mul_le_mul_left Y hcon
      rw [Nat.mul_add] at this
      omega
    have hq2 : q < K := by
      by_contra hcon
      rw [not_lt] at hcon
      have : Y * K ≤ Y * q := Nat.mul_le_mul_left Y hcon
      omega
    have hA : Y * (K - cf + 1) ≤ Y * q := Nat.mul_le_mul_left Y (by omega)
    have hB : Y * q + Y * cf ≤ Y * (K + cf - 1) := by
      rw [← Nat.mul_add]; exact Nat.mul_le_mul_left Y (by omega)
    rw [off_cases N _ _ hwN hzN] at hw
    split_ifs at hw with hzw
    · omega
    · omega
  · rw [if_neg hzx] at h1
    have : Y * cf ≤ Y * K := Nat.mul_le_mul_left Y hcfK
    omega

/-- **at `ell = 2` the central direction-0 bond of the thin component of `neS 2 M R` lies in no class cube** (any cube factor `cf = cfv ≥ 10`, any index `j`). -/
theorem ne2_bond_uncovered {M R : ℕ} (hM : 0 < M) (hR : 1 ≤ R)
    (x : PeriodicLatticeSite (scaleUp 2 2 (neLu M R))) (hx : (x 0).val = neC0 2 M R)
    (sites : Set (PeriodicLatticeSite (scaleUp 2 2 (neLu M R)))) (j : ℕ)
    (hq : IsClassCube 2 M cfv 2 (neS 2 M R) sites j) :
    ¬ (x ∈ sites ∧ periodicLatticeShift x 0 ∈ sites) := by
  obtain ⟨l1, l2, l3, l4, l5, l6, l7, l8⟩ := ne_lin_two (ell := 2) (le_refl 2) hM hR
  have hcf := CfData.hcf
  have hN := ne_scaleUp (ell := 2) (R := R) (by norm_num) hM
  set N := neN 2 M R with hNdef
  have hNe : N = 4 * (2 * (2 * (R * M))) + 2 * (cfv * (2 * (2 * M))) + 6 * (2 * (2 * M)) := rfl
  have hlt : ∀ y : PeriodicLatticeSite (scaleUp 2 2 (neLu M R)), ∀ μ, (y μ).val < N :=
    fun y μ => by have := (y μ).isLt; have := hN μ; omega
  have e1 : cfv * (2 * (2 * M)) = 2 * (cfv * (2 * M)) := by ring
  have hN1 : 1 < N := by omega
  have hc2M : 10 * (2 * M) ≤ cfv * (2 * M) := Nat.mul_le_mul_right _ hcf
  have hxv : (x 0).val + (2 * M + 1) = 2 * (2 * (R * M)) + 2 * (2 * M) + cfv * (2 * M) := by
    rw [hx]; show neA' 2 M R + cfv * (2 * M) - (2 * M + 1) + (2 * M + 1) = _
    simp only [neA']; omega
  have hxA : neA' 2 M R ≤ (x 0).val ∧ (x 0).val < neB' 2 M R := by
    simp only [neA', neB']; omega
  obtain ⟨⟨hj, ⟨z, hzc, rfl⟩, hsub, ⟨w, hw, hwB⟩⟩, -⟩ := hq
  rintro ⟨hxs, hxs'⟩
  have hom2 : x ∈ (neS 2 M R).Om 2 := (neS_om2 x).2 (Or.inl hxA)
  have hj' : j = 0 ∨ j = 1 ∨ j = 2 := by omega
  rcases hj' with rfl | rfl | rfl
  · -- index 0: the cube lies in `Ω₀ \ Ω₂`, but `x ∈ Ω₂`
    have hom1 : x ∈ (neS 2 M R).Om 1 := (neS_om1 x).2 (by simp only [neP1, neQ1, neA', neB, neB'] at hxA ⊢; omega)
    rcases hsub hxs with h | h
    · exact h.2 hom1
    · exact h.2 hom2
  · -- index 1: the aligned level-1 boxes through both endpoints stay inside the thin component
    have hz0 : (2 * M) ∣ (z 0).val := by
      have h0 := hzc 0
      have : M * 2 ^ 1 = 2 * M := by ring
      simp only [bigSide] at h0
      rw [this] at h0
      exact Nat.dvd_of_mod_eq_zero h0
    have hbs : bigSide M 2 1 = 2 * M := by simp only [bigSide]; ring
    have hx0 := ((mem_box_N hN z x _).1 hxs).1
    have hx1 := ((mem_box_N hN z (periodicLatticeShift x 0) _).1 hxs').1
    have hw0 := ((mem_box_N hN z w _).1 hw).1
    have hs0 : ((periodicLatticeShift x 0) 0).val = (x 0).val + 1 := by
      rw [shift_val_N hN hN1, if_pos rfl]
      exact Nat.mod_eq_of_lt (by omega)
    rw [hs0] at hx1
    rw [hbs] at hx0 hx1 hw0
    have hx0' : ((x 0).val + N - (z 0).val) % N < 2 * M * cfv := by rw [Nat.mul_comm]; exact hx0
    have hx1' : ((x 0).val + 1 + N - (z 0).val) % N < 2 * M * cfv := by rw [Nat.mul_comm]; exact hx1
    have hw0' : ((w 0).val + N - (z 0).val) % N < 2 * M * cfv := by rw [Nat.mul_comm]; exact hw0
    have eK : (2 * M) * (2 * R + cfv + 1) = 2 * (2 * (R * M)) + cfv * (2 * M) + 2 * M := by ring
    have hxK : (x 0).val + 1 = (2 * M) * (2 * R + cfv + 1) := by omega
    have eB : (2 * M) * (2 * R + cfv + 1 + cfv - 1) = neB' 2 M R := by
      have : 2 * R + cfv + 1 + cfv - 1 = 2 * R + 2 * cfv := by omega
      rw [this]; simp only [neB']; ring
    have eA : (2 * M) * (2 * R + cfv + 1 - cfv + 1) = neA' 2 M R := by
      have : 2 * R + cfv + 1 - cfv + 1 = 2 * R + 2 := by omega
      rw [this]; simp only [neA']; ring
    have hB'N : neB' 2 M R < N := by simp only [neB']; omega
    have hAB := arith_cell N (2 * M) cfv (2 * R + cfv + 1) (z 0).val (x 0).val (w 0).val (by omega) (hlt x 0) (hlt z 0)
      (hlt w 0) hxK hz0 (by omega) (by omega) hx0' hx1' hw0' (by rw [eB]; exact hB'N)
    rw [eA, eB] at hAB
    exact hwB.2 ((neS_om2 w).2 (Or.inl hAB))
  · -- index 2: the cube is longer than the thin component and leaves `Ω₂`
    have hbs : bigSide M 2 2 = 2 * (2 * M) := by simp only [bigSide]; ring
    have hx0 := ((mem_box_N hN z x _).1 hxs).1
    rw [hbs] at hx0
    have hP : 1 ≤ neA' 2 M R := by simp only [neA']; omega
    have hB'N : neB' 2 M R < N := by simp only [neB']; omega
    have hthin : neB' 2 M R - neA' 2 M R < cfv * (2 * (2 * M)) := by
      simp only [neA', neB']; omega
    obtain ⟨y0, hy0N, hy0box, hy0out, hyc⟩ := arith_thin N (x 0).val (z 0).val (neA' 2 M R) (neB' 2 M R)
      (cfv * (2 * (2 * M))) (hlt x 0) (hlt z 0) hP hxA hB'N hx0 hthin
    have hy0 : y0 < scaleUp 2 2 (neLu M R) 0 + 1 := by have := hN 0; omega
    let y : PeriodicLatticeSite (scaleUp 2 2 (neLu M R)) := Function.update z 0 ⟨y0, hy0⟩
    have hyv : (y 0).val = y0 := by simp [y]
    have hy1 : y 1 = z 1 := by simp [y]
    have hy2 : y 2 = z 2 := by simp [y]
    have hpos : 0 < cfv * (2 * (2 * M)) := Nat.mul_pos (by omega) (by omega)
    have hyin : y ∈ siteBox z (cfv * bigSide M 2 2) := by
      rw [mem_box_N hN, hbs]
      refine ⟨?_, ?_, ?_⟩
      · rw [hyv]; exact hy0box
      · rw [hy1, show (z 1).val + N - (z 1).val = N by have := hlt z 1; omega, Nat.mod_self]; exact hpos
      · rw [hy2, show (z 2).val + N - (z 2).val = N by have := hlt z 2; omega, Nat.mod_self]; exact hpos
    have hy := hsub hyin
    have hyOm : y ∈ (neS 2 M R).Om 2 := by
      rcases hy with hy | hy
      · exact hy.1
      · exact absurd hy.1 (tw3_omHi 3 le_rfl y)
    rw [neS_om2, hyv] at hyOm
    have hgap := ne_gap_pos_two (ell := 2) (le_refl 2) hM hR
    rcases hyOm with h | h
    · exact hy0out h
    · rcases hyc with h' | h' <;> rw [h'] at h <;> simp only [neA, neB, neA', neB'] at h <;> omega

end nums

#print axioms arith_thin
#print axioms arith_cell
#print axioms ne2_bond_uncovered

end AdalyFormal.CoverNested
