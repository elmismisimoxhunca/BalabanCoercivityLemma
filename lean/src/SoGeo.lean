import NuTwoUnc

/-!
# SoGeo -- the decoupled centre `soC` of the thin component and the uncovered bond at general `ell` and class factor `c` (lane sites_only_20261019)

Tower `neS ell M R` of `NsCvNe2` with the `CfData` instance carrying the THIN WIDTH `w = cfv` (thin component `[A', B') = [A', A' + (w-1) Y_2)`),
class factor `c` a separate number linked by `ell (w - 1) = 2 (c - 1)`.  Then the level-1 grid (cell `Y_1 = ell M`) windows of `c` cells anchored at the two edges
of the thin component reach exactly to the same bond: `soC ell M R c + 1 = A' + (c-1) Y_1`, and `B' = A' + 2 (c-1) Y_1`.
* `soC`                : the lower endpoint of the central direction-0 bond.
* `so_bond_uncovered`  : no class cube of factor `c` (any index) contains both `x` and `x + e_0` when `x_0 = soC ell M R c`.
-/
set_option autoImplicit false
set_option maxRecDepth 8000
set_option maxHeartbeats 16000000

namespace AdalyFormal.SitesOnly

open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLane2
open AdalyFormal.StatementLaneG
open AdalyFormal.Balaban.AdmissibleSubspace (Bond blockOf CoarseLattice mem_blockOf mem_CoarseLattice staircasePath)
open AdalyFormal.NonVac (pcd_gt_right2 pcd_gt_left2 iv_iff shift_val_N mem_box_N)
open AdalyFormal.NoCover (off_cases perCube_one pStar bStar_mem)
open AdalyFormal.CoverNested

section nums
variable [CfData]
local notation "cfv" => CfData.cf

/-- the `x_0` of the lower endpoint of the central direction-0 bond of the thin component: `xs + 1 = A' + (c - 1) (ell M)`. -/
def soC (ell M R c : ℕ) : ℕ := neA' ell M R + c * (ell * M) - (ell * M + 1)

/-- the decoupling relation: thin width `cfv - 1` top blocks, class factor `c`. -/
def SoRel (ell c : ℕ) : Prop := ell * (cfv - 1) = 2 * (c - 1)

theorem soRel_atoms {ell c : ℕ} (h : SoRel ell c) (hc : 1 ≤ c) :
    ∃ w' c' : ℕ, cfv = w' + 1 ∧ c = c' + 1 ∧ ell * w' = 2 * c' := by
  have hcf := CfData.hcf
  refine ⟨cfv - 1, c - 1, by omega, by omega, h⟩

/-- the thin component in atoms: `cfv * Y_2 = Y_2 + 2 (c-1) Y_1`. -/
theorem so_thin_atoms {ell M c : ℕ} (h : SoRel ell c) (hc : 1 ≤ c) :
    cfv * (ell * (ell * M)) = ell * (ell * M) + 2 * ((c - 1) * (ell * M)) := by
  obtain ⟨w', c', e1, e2, e3⟩ := soRel_atoms h hc
  have : c - 1 = c' := by omega
  rw [this, e1]
  calc (w' + 1) * (ell * (ell * M)) = ell * (ell * M) + (ell * w') * (ell * M) := by ring
    _ = ell * (ell * M) + 2 * (c' * (ell * M)) := by rw [e3]; ring

theorem so_cfv_le {ell c : ℕ} (hell : 2 ≤ ell) (h : SoRel ell c) (hc : 1 ≤ c) : cfv ≤ c := by
  obtain ⟨w', c', e1, e2, e3⟩ := soRel_atoms h hc
  have : 2 * w' ≤ ell * w' := Nat.mul_le_mul_right _ hell
  omega

/-- `soC + 1` in atoms. -/
theorem soC_succ {ell M R c : ℕ} (hell : 2 ≤ ell) (hM : 0 < M) (hc : 1 ≤ c) :
    soC ell M R c + 1 = ell * (ell * (R * M)) + ell * (ell * M) + (c - 1) * (ell * M) := by
  have e1 : ell * M ≤ ell * (ell * M) := Nat.mul_le_mul_left _ (Nat.le_mul_of_pos_left _ (by omega))
  have hY1 : 0 < ell * M := Nat.mul_pos (by omega) hM
  have e2 : c * (ell * M) = (c - 1) * (ell * M) + ell * M := by
    obtain ⟨c', rfl⟩ : ∃ c', c = c' + 1 := ⟨c - 1, by omega⟩
    simp only [Nat.add_sub_cancel]; ring
  unfold soC neA'
  omega

theorem so_gap_atoms {ell M c : ℕ} (hell : 2 ≤ ell) (h : SoRel ell c) (hc : 1 ≤ c) :
    ell * (ell * M) ≤ cfv * (ell * (ell * M)) := Nat.le_mul_of_pos_left _ (by have := CfData.hcf; omega)

/-- **the central direction-0 bond of the thin component of `neS ell M R` lies in no class cube of factor `c`** (any index `j`). -/
theorem so_bond_uncovered {ell M R c : ℕ} (hell : 2 ≤ ell) (hM : 0 < M) (hR : 1 ≤ R)
    (hrel : SoRel ell c) (hc : 2 ≤ c)
    (x : PeriodicLatticeSite (scaleUp ell 2 (neLu M R))) (hx : (x 0).val = soC ell M R c)
    (sites : Set (PeriodicLatticeSite (scaleUp ell 2 (neLu M R)))) (j : ℕ)
    (hq : IsClassCube ell M c 2 (neS ell M R) sites j) :
    ¬ (x ∈ sites ∧ periodicLatticeShift x 0 ∈ sites) := by
  obtain ⟨l1, l2, l3, l4, l5, l6, l7, l8⟩ := ne_lin_two hell hM hR
  have hcf := CfData.hcf
  have hell0 : 0 < ell := by omega
  have hN := ne_scaleUp (ell := ell) (R := R) hell0 hM
  set N := neN ell M R with hNdef
  have hNe : N = 4 * (ell * (ell * (R * M))) + 2 * (cfv * (ell * (ell * M))) + 6 * (ell * (ell * M)) := rfl
  have hlt : ∀ y : PeriodicLatticeSite (scaleUp ell 2 (neLu M R)), ∀ μ, (y μ).val < N :=
    fun y μ => by have := (y μ).isLt; have := hN μ; omega
  have hthin := so_thin_atoms (M := M) hrel (by omega)
  have hsucc := soC_succ (ell := ell) (M := M) (R := R) hell hM (by omega : 1 ≤ c)
  have hY1 : 0 < ell * M := Nat.mul_pos hell0 hM
  have hY2 : 0 < ell * (ell * M) := Nat.mul_pos hell0 hY1
  have hY12 : ell * M ≤ ell * (ell * M) := Nat.mul_le_mul_left _ (Nat.le_mul_of_pos_left _ hell0)
  have hcm1 : 1 * (ell * M) ≤ (c - 1) * (ell * M) := Nat.mul_le_mul_right _ (by omega)
  have hN1 : 1 < N := by omega
  have hxA : neA' ell M R ≤ (x 0).val ∧ (x 0).val < neB' ell M R := by
    simp only [neA', neB']; omega
  obtain ⟨⟨hj, ⟨z, hzc, rfl⟩, hsub, ⟨w, hw, hwB⟩⟩, -⟩ := hq
  rintro ⟨hxs, hxs'⟩
  have hom2 : x ∈ (neS ell M R).Om 2 := (neS_om2 x).2 (Or.inl hxA)
  have hj' : j = 0 ∨ j = 1 ∨ j = 2 := by omega
  rcases hj' with rfl | rfl | rfl
  · -- index 0: the cube lies in `Ω₀ \ Ω₂`, but `x ∈ Ω₂`
    have hom1 : x ∈ (neS ell M R).Om 1 := (neS_om1 x).2 (by simp only [neP1, neQ1, neA', neB, neB'] at hxA ⊢; omega)
    rcases hsub hxs with h | h
    · exact h.2 hom1
    · exact h.2 hom2
  · -- index 1: the aligned level-1 boxes through both endpoints stay inside the thin component
    have hz0 : (ell * M) ∣ (z 0).val := by
      have h0 := hzc 0
      have : M * ell ^ 1 = ell * M := by ring
      simp only [bigSide] at h0
      rw [this] at h0
      exact Nat.dvd_of_mod_eq_zero h0
    have hbs : bigSide M ell 1 = ell * M := by simp only [bigSide]; ring
    have hx0 := ((mem_box_N hN z x _).1 hxs).1
    have hx1 := ((mem_box_N hN z (periodicLatticeShift x 0) _).1 hxs').1
    have hw0 := ((mem_box_N hN z w _).1 hw).1
    have hs0 : ((periodicLatticeShift x 0) 0).val = (x 0).val + 1 := by
      rw [shift_val_N hN hN1, if_pos rfl]
      exact Nat.mod_eq_of_lt (by omega)
    rw [hs0] at hx1
    rw [hbs] at hx0 hx1 hw0
    have hx0' : ((x 0).val + N - (z 0).val) % N < ell * M * c := by rw [Nat.mul_comm]; exact hx0
    have hx1' : ((x 0).val + 1 + N - (z 0).val) % N < ell * M * c := by rw [Nat.mul_comm]; exact hx1
    have hw0' : ((w 0).val + N - (z 0).val) % N < ell * M * c := by rw [Nat.mul_comm]; exact hw0
    have eK : (ell * M) * (ell * (R + 1) + (c - 1)) = ell * (ell * (R * M)) + ell * (ell * M) + (c - 1) * (ell * M) := by ring
    have hxK : (x 0).val + 1 = (ell * M) * (ell * (R + 1) + (c - 1)) := by omega
    have eB : (ell * M) * (ell * (R + 1) + (c - 1) + c - 1) = neB' ell M R := by
      have e1 : (ell * M) * (ell * (R + 1) + (c - 1) + c - 1) = (ell * M) * (ell * (R + 1) + 2 * (c - 1)) := by
        congr 1; omega
      rw [e1]
      simp only [neB']
      rw [hthin]
      ring
    have hRpos : 1 ≤ ell * (R + 1) := Nat.mul_pos hell0 (by omega)
    have eA : (ell * M) * (ell * (R + 1) + (c - 1) - c + 1) = neA' ell M R := by
      have e1 : ell * (R + 1) + (c - 1) - c + 1 = ell * (R + 1) := by omega
      rw [e1]; simp only [neA']; ring
    have hB'N : neB' ell M R < N := by simp only [neB']; omega
    have hKc : c ≤ ell * (R + 1) + (c - 1) := by
      have : 1 ≤ ell * (R + 1) := Nat.mul_pos hell0 (by omega)
      omega
    have hAB := arith_cell N (ell * M) c (ell * (R + 1) + (c - 1)) (z 0).val (x 0).val (w 0).val hY1 (hlt x 0) (hlt z 0)
      (hlt w 0) hxK hz0 (by omega) hKc hx0' hx1' hw0' (by rw [eB]; exact hB'N)
    rw [eA, eB] at hAB
    exact hwB.2 ((neS_om2 w).2 (Or.inl hAB))
  · -- index 2: the cube is longer than the thin component and leaves `Ω₂`
    have hbs : bigSide M ell 2 = ell * (ell * M) := by simp only [bigSide]; ring
    have hx0 := ((mem_box_N hN z x _).1 hxs).1
    rw [hbs] at hx0
    have hP : 1 ≤ neA' ell M R := by simp only [neA']; omega
    have hB'N : neB' ell M R < N := by simp only [neB']; omega
    have hcle := so_cfv_le hell hrel (by omega : 1 ≤ c)
    have hcY : cfv * (ell * (ell * M)) ≤ c * (ell * (ell * M)) := Nat.mul_le_mul_right _ hcle
    have hthin' : neB' ell M R - neA' ell M R < c * (ell * (ell * M)) := by
      simp only [neA', neB']; omega
    obtain ⟨y0, hy0N, hy0box, hy0out, hyc⟩ := arith_thin N (x 0).val (z 0).val (neA' ell M R) (neB' ell M R)
      (c * (ell * (ell * M))) (hlt x 0) (hlt z 0) hP hxA hB'N hx0 hthin'
    have hy0 : y0 < scaleUp ell 2 (neLu M R) 0 + 1 := by have := hN 0; omega
    let y : PeriodicLatticeSite (scaleUp ell 2 (neLu M R)) := Function.update z 0 ⟨y0, hy0⟩
    have hyv : (y 0).val = y0 := by simp [y]
    have hy1 : y 1 = z 1 := by simp [y]
    have hy2 : y 2 = z 2 := by simp [y]
    have hpos : 0 < c * (ell * (ell * M)) := Nat.mul_pos (by omega) hY2
    have hyin : y ∈ siteBox z (c * bigSide M ell 2) := by
      rw [mem_box_N hN, hbs]
      refine ⟨?_, ?_, ?_⟩
      · rw [hyv]; exact hy0box
      · rw [hy1, show (z 1).val + N - (z 1).val = N by have := hlt z 1; omega, Nat.mod_self]; exact hpos
      · rw [hy2, show (z 2).val + N - (z 2).val = N by have := hlt z 2; omega, Nat.mod_self]; exact hpos
    have hy := hsub hyin
    have hyOm : y ∈ (neS ell M R).Om 2 := by
      rcases hy with hy | hy
      · exact hy.1
      · exact absurd hy.1 (tw3_omHi 3 le_rfl y)
    rw [neS_om2, hyv] at hyOm
    have hgap := ne_gap_pos_two hell hM hR
    rcases hyOm with h | h
    · exact hy0out h
    · rcases hyc with h' | h' <;> rw [h'] at h <;> simp only [neA, neB, neA', neB'] at h <;> omega

end nums

#print axioms so_bond_uncovered

end AdalyFormal.SitesOnly
