import NsCvNe2

/-!
# NuTwoGeo -- the nested tower family of `NsCvNe2` for `ell = 2` (lane ncwdh_ell2_20261018)

The tower `neS ell M R`, the torus `neLu M R`, `Lam = neLam M R` of `NsCvNe2` are defined for every `ell`; the lemmas of that file are stated for `3 <= ell` only.
Here the geometric lemmas needed for `2 <= ell` are re-proved (`_two` suffix; same proofs with the linear facts `2 * X_j <= X_(j+1)` in place of `3 * ...`), and the
new fact of this lane is proved: at `ell = 2` the central direction-0 bond of the thin component lies in no class cube (`ne2_bond_uncovered`), while the site layer of
`NsCvNe2.ne_layer_uncovered` does not exist (`ne_lin_two` is all that is true: `2 * ... <= ...`).
-/
set_option autoImplicit false
set_option maxRecDepth 8000
set_option maxHeartbeats 16000000

namespace AdalyFormal.CoverNested

open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLane2
open AdalyFormal.StatementLaneG
open AdalyFormal.IngredientFamilyR2 (plaqIn)
open AdalyFormal.Balaban.CovariantOperators (SuTwo suTwoWitness suTwoWitness_ne_zero)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond blockOf CoarseLattice mem_blockOf mem_CoarseLattice staircasePath)
open AdalyFormal.Balaban.FullReparamC (freeBond freeBond_not_mem_staircase freeBond_not_dropped freeBond_coord_zero)
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
open AdalyFormal.Balaban.RegularUPerturbation (bondEnergy)
open AdalyFormal.NonVac (pcd_gt_right2 pcd_gt_left2 iv_iff shift_val_N mem_box_N)
open AdalyFormal.NoCover (off_cases perCube_one pStar bStar_mem)

section nums
variable [CfData]
local notation "cfv" => CfData.cf


omit [CfData] in
/-- the linear facts (atoms `X₂ = ell(ell(RM))`, `Y₂ = ell(ell M)`, `X₁ = ell(RM)`, `Y₁ = ell M`, `X₀ = RM`, `M`). -/
theorem ne_lin_two {ell M R : ℕ} (hell : 2 ≤ ell) (hM : 0 < M) (hR : 1 ≤ R) :
    2 * (ell * (R * M)) ≤ ell * (ell * (R * M)) ∧ 2 * (ell * M) ≤ ell * (ell * M) ∧
    2 * (R * M) ≤ ell * (R * M) ∧ 2 * M ≤ ell * M ∧ M ≤ R * M ∧ ell * M ≤ ell * (R * M) ∧
    ell * (ell * M) ≤ ell * (ell * (R * M)) ∧ 1 ≤ M := by
  refine ⟨Nat.mul_le_mul_right _ hell, Nat.mul_le_mul_right _ hell, Nat.mul_le_mul_right _ hell,
    Nat.mul_le_mul_right _ hell, Nat.le_mul_of_pos_left _ (by omega), ?_, ?_, hM⟩
  · exact Nat.mul_le_mul_left _ (Nat.le_mul_of_pos_left _ (by omega))
  · exact Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (Nat.le_mul_of_pos_left _ (by omega)))


theorem ne_geo3_two {ell M R : ℕ} (hell : 2 ≤ ell) (hM : 0 < M) (hR : 1 ≤ R) :
    Geo3 M ell R (neN ell M R) (neP0 ell M R) (neQ0 ell M R) (neP1 ell M R) (neQ1 ell M R)
      (neA' ell M R) (neB' ell M R) (neA ell M R) (neB ell M R) := by
  obtain ⟨l1, l2, l3, l4, l5, l6, l7, l8⟩ := ne_lin_two hell hM hR
  obtain ⟨c1, c2, c3, c4, c5⟩ := ne_lin_c2 (M := M) hell
  have hX1 : R * (M * ell) = ell * (R * M) := by ring
  have h2 : M * ell ^ 2 = ell * (ell * M) := by ring
  -- divisibility atoms
  have a0X2 : M ∣ ell * (ell * (R * M)) := ⟨ell * ell * R, by ring⟩
  have a0Y2 : M ∣ ell * (ell * M) := ⟨ell * ell, by ring⟩
  have a0X1 : M ∣ ell * (R * M) := ⟨ell * R, by ring⟩
  have a0X0 : M ∣ R * M := ⟨R, by ring⟩
  have a1X2 : M * ell ∣ ell * (ell * (R * M)) := ⟨ell * R, by ring⟩
  have a1Y2 : M * ell ∣ ell * (ell * M) := ⟨ell, by ring⟩
  have a1X1 : M * ell ∣ ell * (R * M) := ⟨R, by ring⟩
  have a2X2 : M * ell ^ 2 ∣ ell * (ell * (R * M)) := ⟨R, by ring⟩
  have a2Y2 : M * ell ^ 2 ∣ ell * (ell * M) := ⟨1, by ring⟩
  have lin : ∀ (k : ℕ) (a b d : ℕ), k ∣ ell * (ell * (R * M)) → k ∣ ell * (ell * M) →
      k ∣ a * (ell * (ell * (R * M))) + b * (cfv * (ell * (ell * M))) + d * (ell * (ell * M)) := fun k a b d h1 h2 =>
    Nat.dvd_add (Nat.dvd_add (Dvd.dvd.mul_left h1 a) (Dvd.dvd.mul_left (Dvd.dvd.mul_left h2 cfv) b)) (Dvd.dvd.mul_left h2 d)
  refine ⟨hM, by omega, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [neA', neB']; omega
  · simp only [neB', neA]; omega
  · simp only [neA, neB]; omega
  · simp only [neQ0, neQ1, neB, neN]; omega
  · simp only [neN]; exact lin M 4 2 6 a0X2 a0Y2
  · simp only [neN]; exact lin (M * ell) 4 2 6 a1X2 a1Y2
  · simp only [neN]; exact lin (M * ell ^ 2) 4 2 6 a2X2 a2Y2
  · simp only [neP0, neP1, neA']
    exact Nat.dvd_sub (Nat.dvd_sub (by simpa using lin M 1 0 1 a0X2 a0Y2) a0X1) a0X0
  · simp only [neQ0, neQ1, neB]
    exact Nat.dvd_add (Nat.dvd_add (by simpa using lin M 3 1 4 a0X2 a0Y2) a0X1) a0X0
  · simp only [neP1, neA']
    exact Nat.dvd_sub (by simpa using lin (M * ell) 1 0 1 a1X2 a1Y2) a1X1
  · simp only [neQ1, neB]
    exact Nat.dvd_add (by simpa using lin (M * ell) 3 1 4 a1X2 a1Y2) a1X1
  · simp only [neA']; simpa using lin (M * ell ^ 2) 1 0 1 a2X2 a2Y2
  · simp only [neB']; simpa using lin (M * ell ^ 2) 1 1 0 a2X2 a2Y2
  · simp only [neA]; simpa using lin (M * ell ^ 2) 1 1 1 a2X2 a2Y2
  · simp only [neB]; simpa using lin (M * ell ^ 2) 3 1 4 a2X2 a2Y2
  · simp only [neP0, neP1, neA']; omega
  · rfl
  · rw [hX1]; simp only [neP1, neA']; omega
  · rw [hX1]; rfl

theorem ne_admissible_two {ell M R : ℕ} (hell : 2 ≤ ell) (hM : 0 < M) (hR : 1 ≤ R) :
    Admissible ell M R 2 (neS ell M R) :=
  tw3_admissible (ne_geo3_two hell hM hR) (ne_scaleUp (by omega) hM)

theorem ne_between_level1_two {ell M R : ℕ} (hell : 2 ≤ ell) (hM : 0 < M) (hR : 1 ≤ R)
    (x : PeriodicLatticeSite (scaleUp ell 2 (neLu M R))) (hx : neB' ell M R ≤ (x 0).val ∧ (x 0).val < neA ell M R) :
    x ∈ (neS ell M R).Om 1 ∧ x ∉ (neS ell M R).Om 2 := by
  obtain ⟨l1, l2, l3, l4, l5, l6, l7, l8⟩ := ne_lin_two hell hM hR
  obtain ⟨c1, c2, c3, c4, c5⟩ := ne_lin_c2 (M := M) hell
  refine ⟨?_, ?_⟩
  · rw [neS_om1]; simp only [neP1, neQ1, neA', neB, neB', neA] at hx ⊢; omega
  · rw [neS_om2]; simp only [neA', neB', neA, neB] at hx ⊢; omega

theorem ne_gap_pos_two {ell M R : ℕ} (hell : 2 ≤ ell) (hM : 0 < M) (hR : 1 ≤ R) : neB' ell M R < neA ell M R := by
  obtain ⟨l1, l2, l3, l4, l5, l6, l7, l8⟩ := ne_lin_two hell hM hR
  simp only [neB', neA]; omega

/-! ## `TorusOK`, `Λ`, `LambdaOK2` -/

theorem torusOK_ne_two {ell M R : ℕ} (hell : 2 ≤ ell) (hdvd : ell ∣ M) (hM : 0 < M) :
    TorusOK ell M (neLu M R) := by
  have hle : ell ≤ M := Nat.le_of_dvd hM hdvd
  refine ⟨fun μ => ?_, fun μ => ?_, fun μ => ?_⟩ <;> rw [neLu_succ hM] <;> simp only [neNu]
  · exact Nat.dvd_add (Nat.dvd_add (Dvd.dvd.mul_left (Dvd.dvd.mul_left hdvd R) 4)
      (Dvd.dvd.mul_left (Dvd.dvd.mul_left hdvd cfv) 2)) (Dvd.dvd.mul_left hdvd 6)
  · omega
  · exact Nat.dvd_add (Nat.dvd_add (Dvd.dvd.mul_left (Dvd.dvd.mul_left (dvd_refl M) R) 4)
      (Dvd.dvd.mul_left (Dvd.dvd.mul_left (dvd_refl M) cfv) 2)) (Dvd.dvd.mul_left (dvd_refl M) 6)

theorem lambdaOK_ne_two {ell M R : ℕ} (hell : 2 ≤ ell) (hM : 0 < M) (hR : 1 ≤ R) :
    LambdaOK ell M R 2 (neS ell M R) (neLam M R) := by
  have hell0 : 0 < ell := by omega
  have hl2 : 0 < ell ^ 2 := pow_pos hell0 2
  have hA : neA ell M R = ell ^ 2 * (M * (R + (cfv + 1))) := by simp only [neA]; ring
  have hB : neB ell M R = ell ^ 2 * (M * (3 * R + (cfv + 4))) := by simp only [neB]; ring
  have hlo : neLo M R + M = M * (2 * R + (cfv + 2) + 1) := by unfold neLo; ring
  refine ⟨blockClosed_neLam hM, embNe ell M R hell0 hM, fun y μ => rfl, ?_, ?_⟩
  · intro y hy
    rw [neS_om2]
    right
    show neA ell M R ≤ ell ^ 2 * (y 0).val ∧ ell ^ 2 * (y 0).val < neB ell M R
    rw [hA, hB]
    have h1 : M * (2 * R + (cfv + 2)) ≤ (y 0).val := hy.1
    have h2 : (y 0).val < M * (2 * R + (cfv + 2) + 1) := by rw [← hlo]; exact hy.2
    constructor
    · exact Nat.mul_le_mul_left _ (le_trans (Nat.mul_le_mul_left M (by omega)) h1)
    · exact Nat.mul_lt_mul_of_pos_left (lt_of_lt_of_le h2 (Nat.mul_le_mul_left M (by omega))) hl2
  · intro y hy y' hy'
    have hcase : (y' 0).val < M * (R + (cfv + 1)) ∨ M * (3 * R + (cfv + 4)) ≤ (y' 0).val := by
      by_contra hcon
      push Not at hcon
      apply hy'
      rw [neS_om2]
      right
      show neA ell M R ≤ ell ^ 2 * (y' 0).val ∧ ell ^ 2 * (y' 0).val < neB ell M R
      rw [hA, hB]
      exact ⟨Nat.mul_le_mul_left _ hcon.1, Nat.mul_lt_mul_of_pos_left hcon.2 hl2⟩
    have hyN : (y 0).val < neNu M R := ne_lt hM y 0
    have hy'N : (y' 0).val < neNu M R := ne_lt hM y' 0
    have e4 : neNu M R = 4 * (R * M) + 2 * (cfv * M) + 6 * M := rfl
    have e5 : neLo M R = 2 * (R * M) + cfv * M + 2 * M := by unfold neLo; ring
    have e6 : M * (R + (cfv + 1)) = R * M + cfv * M + M := by ring
    have e7 : M * (3 * R + (cfv + 4)) = 3 * (R * M) + cfv * M + 4 * M := by ring
    have hMR : 0 < R * M := Nat.mul_pos (by omega) hM
    have hy1 := hy.1
    have hy2 := hy.2
    have hpd : R * M < pcd (neNu M R) (y 0).val (y' 0).val := by
      rcases hcase with h | h
      · exact pcd_gt_right2 (by omega) (by omega)
      · exact pcd_gt_left2 (by omega) hy'N (by omega)
    unfold pdist
    refine lt_of_lt_of_le ?_ (Finset.single_le_sum (f := fun μ : Fin 3 => pcd (neLu M R μ + 1) (y μ).val (y' μ).val)
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ 0))
    simpa [neLu_succ hM] using hpd

theorem lambdaOK2_ne_two {ell M R : ℕ} (hell : 2 ≤ ell) (hdvd : ell ∣ M) (hM : 0 < M) (hR : 1 ≤ R) :
    LambdaOK2 ell M R 2 (neS ell M R) (neLam M R) :=
  ⟨lambdaOK_ne_two hell hM hR, lamBlockSum_ne (by omega) hdvd hM⟩

theorem BseedNe_props_two {ell M R : ℕ} (hell : 2 ≤ ell) (hdvd : ell ∣ M) (hM : 0 < M) :
    OnLambdaTildeIn (neLam M R) ell (BseedNe (R := R) ell hM) ∧ OnLambdaT (neLam M R) (BseedNe (R := R) ell hM) ∧
      0 < bondEnergy (BseedNe (R := R) ell hM) ∧ BseedNe (R := R) ell hM ≠ 0 := by
  have hell2 : 2 ≤ ell := by omega
  have hdvd' : ∀ μ : Fin 3, ell ∣ neLu M R μ + 1 := fun μ => by
    rw [neLu_succ hM]
    simp only [neNu]
    exact Nat.dvd_add (Nat.dvd_add (Dvd.dvd.mul_left (Dvd.dvd.mul_left hdvd R) 4)
      (Dvd.dvd.mul_left (Dvd.dvd.mul_left hdvd cfv) 2)) (Dvd.dvd.mul_left hdvd 6)
  have hy : yNe (R := R) hM ∈ CoarseLattice (neLu M R) ell := by
    rw [mem_CoarseLattice]
    intro μ
    show (if μ = 0 then neLo M R else 0) % ell = 0
    split_ifs
    · exact Nat.mod_eq_zero_of_dvd (by unfold neLo; exact Dvd.dvd.mul_right hdvd _)
    · simp
  have hoff : ∀ b : Bond (neLu M R), b ≠ freeBond ell (yNe (R := R) hM) → BseedNe (R := R) ell hM b = 0 :=
    fun b hb => Pi.single_eq_of_ne hb _
  have hOn : OnLambdaT (neLam M R) (BseedNe (R := R) ell hM) := by
    intro b hb
    by_cases hbe : b = freeBond ell (yNe (R := R) hM)
    · exfalso
      apply hb
      have hy0 : ((yNe (R := R) hM) 0).val = neLo M R := by simp [yNe]
      have hfit : ((yNe (R := R) hM) 0).val + ell ≤ neLu M R 0 + 1 := by
        rw [hy0, neLu_succ hM]
        have : ell ≤ M := Nat.le_of_dvd hM hdvd
        have e : neNu M R = neLo M R + M * (2 * R + (cfv + 4)) := by unfold neNu neLo; ring
        have : M ≤ M * (2 * R + (cfv + 4)) := Nat.le_mul_of_pos_right _ (by omega)
        omega
      have h0 := freeBond_coord_zero (yNe (R := R) hM) hfit hell2
      subst hbe
      left
      show neLo M R ≤ ((freeBond ell (yNe (R := R) hM)).1 0).val ∧
        ((freeBond ell (yNe (R := R) hM)).1 0).val < neLo M R + M
      have : ell ≤ M := Nat.le_of_dvd hM hdvd
      omega
    · exact hoff b hbe
  have hne : ‖BseedNe (R := R) ell hM (freeBond ell (yNe (R := R) hM))‖ ^ 2 > 0 := by
    have : BseedNe (R := R) ell hM (freeBond ell (yNe (R := R) hM)) = suTwoWitness := Pi.single_eq_same _ _
    rw [this]
    have : suTwoWitness ≠ 0 := suTwoWitness_ne_zero
    positivity
  refine ⟨⟨?_, ?_⟩, hOn, ?_, ?_⟩
  · intro y hy' x hx b hb
    refine hoff b ?_
    rintro rfl
    exact freeBond_not_mem_staircase hell2 hdvd' (yNe (R := R) hM) hy y hy'.1 x hx hb
  · intro b hb
    refine hoff b ?_
    rintro rfl
    obtain ⟨c, hc1, hc2⟩ := hb
    exact freeBond_not_dropped hell2 hdvd' (yNe (R := R) hM) hy ⟨c, hc2⟩
  · have hle : ‖BseedNe (R := R) ell hM (freeBond ell (yNe (R := R) hM))‖ ^ 2
        ≤ ∑ b : Bond (neLu M R), ‖BseedNe (R := R) ell hM b‖ ^ 2 :=
      Finset.single_le_sum (f := fun b : Bond (neLu M R) => ‖BseedNe (R := R) ell hM b‖ ^ 2)
        (fun i _ => sq_nonneg _) (Finset.mem_univ _)
    unfold bondEnergy
    linarith
  · intro h
    have : BseedNe (R := R) ell hM (freeBond ell (yNe (R := R) hM)) = 0 := by rw [h]; rfl
    rw [this] at hne
    simp at hne

/-! ## the uncovered layer -/

end nums

#print axioms ne_admissible_two
#print axioms torusOK_ne_two
#print axioms lambdaOK2_ne_two
#print axioms BseedNe_props_two
#print axioms ne_between_level1_two

end AdalyFormal.CoverNested
