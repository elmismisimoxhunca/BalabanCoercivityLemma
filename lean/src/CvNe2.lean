import CvNe1

/-!
# CvNe2 -- the nested instance family in the headline regime: `k = 2`, every `ell ≥ 3`, every `M` with `ell ∣ M` (so every
`M = ell^m`, `m ≥ 1`), every `R ≥ 1` (lane cover_nested_20261016)

With `X₂ = ell²RM`, `Y₂ = ell²M` (top block `M ell²`), `X₁ = ell RM`, `Y₁ = ell M`, `X₀ = RM` (fine `x₀` coordinate):
* `Ω₂ = [X₂+Y₂, X₂+12Y₂) ∪ [X₂+13Y₂, 3X₂+16Y₂)`: a THIN component (`11` top blocks) and a FAT one, one top block apart;
* `Ω₁ = [X₂+Y₂−X₁, 3X₂+16Y₂+X₁)`: ONE interval containing both (the collar `R M ell`), so every site between the thin and the fat
  component is a level-1 site (`ne_between_level1`), not a level-0 one;
* `Ω₀ = Ω₁` widened by `R M`;
* `Λ = {M(2R+14) ≤ y₀ < M(2R+15)}` on the unit torus `N_u = M(4R+17)` (inside the fat component, collar `> RM`);
* the LAYER `x₀ = c := X₂+Y₂+12Y₁` inside the thin component: no site of the layer lies in any factor-12 class cube
  (`ne_layer_uncovered`; index 0: the cube stays in `Ω₁`; index 1: it stays in `Ω₂`; index 2: it leaves `Ω₂`).
Consequences proved here:
* `perCube_congr`: the class reads `U` only on bonds whose base lies in a class cube;
* `layerCfg c v` (`v` on every direction-1 bond based on the layer, `1` elsewhere) is in `PerCubeRegular2 .. 12 2 ..` for EVERY
  `v ∈ SU(2)` and every `α₀ > 0` (`ne_layer_class`);
* the layer plaquettes `(x; 0, 1)` lie in `plaqIn Ω₀` (the operators read them).
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
open AdalyFormal.NoCover (arith0 arith1 perCube_one pStar bStar_mem)

/-! ## numbers -/

def neNu (M R : ℕ) : ℕ := M * (4 * R + 17)
def neLu (M R : ℕ) : PeriodicLatticeExtent := fun _ => neNu M R - 1
def neA' (ell M R : ℕ) : ℕ := ell * (ell * (R * M)) + ell * (ell * M)
def neB' (ell M R : ℕ) : ℕ := ell * (ell * (R * M)) + 12 * (ell * (ell * M))
def neA (ell M R : ℕ) : ℕ := ell * (ell * (R * M)) + 13 * (ell * (ell * M))
def neB (ell M R : ℕ) : ℕ := 3 * (ell * (ell * (R * M))) + 16 * (ell * (ell * M))
def neP1 (ell M R : ℕ) : ℕ := neA' ell M R - ell * (R * M)
def neQ1 (ell M R : ℕ) : ℕ := neB ell M R + ell * (R * M)
def neP0 (ell M R : ℕ) : ℕ := neP1 ell M R - R * M
def neQ0 (ell M R : ℕ) : ℕ := neQ1 ell M R + R * M
def neN (ell M R : ℕ) : ℕ := 4 * (ell * (ell * (R * M))) + 17 * (ell * (ell * M))
/-- the layer coordinate. -/
def neC (ell M R : ℕ) : ℕ := neA' ell M R + 12 * (ell * M)

/-- the tower on the fine torus (`k = 2`). -/
def neS (ell M R : ℕ) : Tower (scaleUp ell 2 (neLu M R)) :=
  tw3 _ (neP0 ell M R) (neQ0 ell M R) (neP1 ell M R) (neQ1 ell M R) (neA' ell M R) (neB' ell M R) (neA ell M R) (neB ell M R)

theorem neNu_pos {M R : ℕ} (hM : 0 < M) : 0 < neNu M R := Nat.mul_pos hM (by omega)

theorem neLu_succ {M R : ℕ} (hM : 0 < M) (μ : Fin 3) : neLu M R μ + 1 = neNu M R := by
  have := neNu_pos (R := R) hM; simp only [neLu]; omega

theorem ne_scaleUp {ell M R : ℕ} (hell : 0 < ell) (hM : 0 < M) (μ : Fin 3) :
    scaleUp ell 2 (neLu M R) μ + 1 = neN ell M R := by
  have h1 := neLu_succ (R := R) hM μ
  have hN : neN ell M R = neNu M R * ell ^ 2 := by simp only [neN, neNu]; ring
  have : 0 < neNu M R * ell ^ 2 := Nat.mul_pos (neNu_pos hM) (pow_pos hell 2)
  simp only [scaleUp, h1]; omega

/-- the linear facts (atoms `X₂ = ell(ell(RM))`, `Y₂ = ell(ell M)`, `X₁ = ell(RM)`, `Y₁ = ell M`, `X₀ = RM`, `M`). -/
theorem ne_lin {ell M R : ℕ} (hell : 3 ≤ ell) (hM : 0 < M) (hR : 1 ≤ R) :
    3 * (ell * (R * M)) ≤ ell * (ell * (R * M)) ∧ 3 * (ell * M) ≤ ell * (ell * M) ∧
    3 * (R * M) ≤ ell * (R * M) ∧ 3 * M ≤ ell * M ∧ M ≤ R * M ∧ ell * M ≤ ell * (R * M) ∧
    ell * (ell * M) ≤ ell * (ell * (R * M)) ∧ 1 ≤ M := by
  refine ⟨Nat.mul_le_mul_right _ hell, Nat.mul_le_mul_right _ hell, Nat.mul_le_mul_right _ hell,
    Nat.mul_le_mul_right _ hell, Nat.le_mul_of_pos_left _ (by omega), ?_, ?_, hM⟩
  · exact Nat.mul_le_mul_left _ (Nat.le_mul_of_pos_left _ (by omega))
  · exact Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (Nat.le_mul_of_pos_left _ (by omega)))

theorem ne_geo3 {ell M R : ℕ} (hell : 3 ≤ ell) (hM : 0 < M) (hR : 1 ≤ R) :
    Geo3 M ell R (neN ell M R) (neP0 ell M R) (neQ0 ell M R) (neP1 ell M R) (neQ1 ell M R)
      (neA' ell M R) (neB' ell M R) (neA ell M R) (neB ell M R) := by
  obtain ⟨l1, l2, l3, l4, l5, l6, l7, l8⟩ := ne_lin hell hM hR
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
  have lin : ∀ (k : ℕ) (a b : ℕ), k ∣ ell * (ell * (R * M)) → k ∣ ell * (ell * M) →
      k ∣ a * (ell * (ell * (R * M))) + b * (ell * (ell * M)) := fun k a b h1 h2 =>
    Nat.dvd_add (Dvd.dvd.mul_left h1 a) (Dvd.dvd.mul_left h2 b)
  refine ⟨hM, by omega, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [neA', neB']; omega
  · simp only [neB', neA]; omega
  · simp only [neA, neB]; omega
  · simp only [neQ0, neQ1, neB, neN]; omega
  · simp only [neN]; exact lin M 4 17 a0X2 a0Y2
  · simp only [neN]; exact lin (M * ell) 4 17 a1X2 a1Y2
  · simp only [neN]; exact lin (M * ell ^ 2) 4 17 a2X2 a2Y2
  · simp only [neP0, neP1, neA']
    exact Nat.dvd_sub (Nat.dvd_sub (by simpa using lin M 1 1 a0X2 a0Y2) a0X1) a0X0
  · simp only [neQ0, neQ1, neB]
    exact Nat.dvd_add (Nat.dvd_add (lin M 3 16 a0X2 a0Y2) a0X1) a0X0
  · simp only [neP1, neA']
    exact Nat.dvd_sub (by simpa using lin (M * ell) 1 1 a1X2 a1Y2) a1X1
  · simp only [neQ1, neB]
    exact Nat.dvd_add (lin (M * ell) 3 16 a1X2 a1Y2) a1X1
  · simp only [neA']; simpa using lin (M * ell ^ 2) 1 1 a2X2 a2Y2
  · simp only [neB']; simpa using lin (M * ell ^ 2) 1 12 a2X2 a2Y2
  · simp only [neA]; simpa using lin (M * ell ^ 2) 1 13 a2X2 a2Y2
  · simp only [neB]; exact lin (M * ell ^ 2) 3 16 a2X2 a2Y2
  · simp only [neP0, neP1, neA']; omega
  · rfl
  · rw [hX1]; simp only [neP1, neA']; omega
  · rw [hX1]; rfl

theorem ne_admissible {ell M R : ℕ} (hell : 3 ≤ ell) (hM : 0 < M) (hR : 1 ≤ R) :
    Admissible ell M R 2 (neS ell M R) :=
  tw3_admissible (ne_geo3 hell hM hR) (ne_scaleUp (by omega) hM)

theorem neS_om0 {ell M R : ℕ} (x : PeriodicLatticeSite (scaleUp ell 2 (neLu M R))) :
    x ∈ (neS ell M R).Om 0 ↔ neP0 ell M R ≤ (x 0).val ∧ (x 0).val < neQ0 ell M R := tw3_om0 x
theorem neS_om1 {ell M R : ℕ} (x : PeriodicLatticeSite (scaleUp ell 2 (neLu M R))) :
    x ∈ (neS ell M R).Om 1 ↔ neP1 ell M R ≤ (x 0).val ∧ (x 0).val < neQ1 ell M R := tw3_om1 x
theorem neS_om2 {ell M R : ℕ} (x : PeriodicLatticeSite (scaleUp ell 2 (neLu M R))) :
    x ∈ (neS ell M R).Om 2 ↔ (neA' ell M R ≤ (x 0).val ∧ (x 0).val < neB' ell M R) ∨
      (neA ell M R ≤ (x 0).val ∧ (x 0).val < neB ell M R) := tw3_om2 x

/-! ## nesting: every site between the thin and the fat component is a level-1 site -/

/-- the sites strictly between the two `Ω₂` components lie in `Ω₁ \ Ω₂` (level 1), and there is at least one such site. -/
theorem ne_between_level1 {ell M R : ℕ} (hell : 3 ≤ ell) (hM : 0 < M) (hR : 1 ≤ R)
    (x : PeriodicLatticeSite (scaleUp ell 2 (neLu M R))) (hx : neB' ell M R ≤ (x 0).val ∧ (x 0).val < neA ell M R) :
    x ∈ (neS ell M R).Om 1 ∧ x ∉ (neS ell M R).Om 2 := by
  obtain ⟨l1, l2, l3, l4, l5, l6, l7, l8⟩ := ne_lin hell hM hR
  refine ⟨?_, ?_⟩
  · rw [neS_om1]; simp only [neP1, neQ1, neA', neB, neB', neA] at hx ⊢; omega
  · rw [neS_om2]; simp only [neA', neB', neA, neB] at hx ⊢; omega

theorem ne_gap_pos {ell M R : ℕ} (hell : 3 ≤ ell) (hM : 0 < M) (hR : 1 ≤ R) : neB' ell M R < neA ell M R := by
  obtain ⟨l1, l2, l3, l4, l5, l6, l7, l8⟩ := ne_lin hell hM hR
  simp only [neB', neA]; omega

/-! ## `TorusOK`, `Λ`, `LambdaOK2` -/

theorem ne_lt {M R : ℕ} (hM : 0 < M) (x : PeriodicLatticeSite (neLu M R)) (μ : Fin 3) : (x μ).val < neNu M R := by
  have := (x μ).isLt; have := neLu_succ (R := R) hM μ; omega

def neLam (M R : ℕ) : Set (PeriodicLatticeSite (neLu M R)) :=
  {y | M * (2 * R + 14) ≤ (y 0).val ∧ (y 0).val < M * (2 * R + 14) + M}

theorem torusOK_ne {ell M R : ℕ} (hell : 3 ≤ ell) (hdvd : ell ∣ M) (hM : 0 < M) :
    TorusOK ell M (neLu M R) := by
  refine ⟨fun μ => ?_, fun μ => ?_, fun μ => ?_⟩ <;> rw [neLu_succ hM] <;> simp only [neNu]
  · exact Dvd.dvd.mul_right hdvd _
  · have : ell ≤ M := Nat.le_of_dvd hM hdvd
    nlinarith
  · exact Dvd.intro _ rfl

theorem blockClosed_neLam {M R : ℕ} (hM : 0 < M) : BlockClosed M (neLam M R) := by
  intro x hx y hy
  have h := hy 0
  have hx' : M * (2 * R + 14) ≤ (x 0).val ∧ (x 0).val < M * (2 * R + 15) := by
    refine ⟨hx.1, ?_⟩; have := hx.2; rw [show M * (2 * R + 15) = M * (2 * R + 14) + M by ring]; exact this
  rw [iv_iff hM] at hx'
  have : M * (2 * R + 14) ≤ (y 0).val ∧ (y 0).val < M * (2 * R + 15) := by
    rw [iv_iff hM, h]; exact hx'
  refine ⟨this.1, ?_⟩
  have := this.2; rw [show M * (2 * R + 15) = M * (2 * R + 14) + M by ring] at this; exact this

theorem lamBlockSum_ne {ell M R : ℕ} (hell : 0 < ell) (hdvd : ell ∣ M) (hM : 0 < M) :
    LamBlockSum ell (neLam M R) := by
  intro x hx
  obtain ⟨a, ha⟩ := hdvd
  have hxN : ∀ μ, (x μ).val < neNu M R := fun μ => ne_lt hM x μ
  let y : PeriodicLatticeSite (neLu M R) := fun μ => ⟨ell * ((x μ).val / ell),
    lt_of_le_of_lt (Nat.mul_div_le _ _) (by have := neLu_succ (R := R) hM μ; have := hxN μ; omega)⟩
  have hyv : ∀ μ, (y μ).val = ell * ((x μ).val / ell) := fun μ => rfl
  have e1 : M * (2 * R + 14) = ell * (a * (2 * R + 14)) := by rw [ha]; ring
  have e2 : M * (2 * R + 14) + M = ell * (a * (2 * R + 15)) := by rw [ha]; ring
  refine ⟨y, ⟨?_, ?_⟩, ?_⟩
  · rw [mem_CoarseLattice]; intro μ; rw [hyv]; exact Nat.mul_mod_right _ _
  · intro x' hx'
    rw [mem_blockOf] at hx'
    have h0 := hx' 0
    rw [hyv] at h0
    have hx0 : ell * (a * (2 * R + 14)) ≤ (x 0).val ∧ (x 0).val < ell * (a * (2 * R + 15)) := by
      have := hx.1; have := hx.2; omega
    rw [iv_iff hell] at hx0
    have hq1 : a * (2 * R + 14) ≤ (x 0).val / ell := hx0.1
    have hq2 : (x 0).val / ell + 1 ≤ a * (2 * R + 15) := hx0.2
    have m1 : ell * (a * (2 * R + 14)) ≤ ell * ((x 0).val / ell) := Nat.mul_le_mul_left ell hq1
    have m2 : ell * ((x 0).val / ell + 1) ≤ ell * (a * (2 * R + 15)) := Nat.mul_le_mul_left ell hq2
    constructor
    · omega
    · have : ell * ((x 0).val / ell + 1) = ell * ((x 0).val / ell) + ell := by ring
      omega
  · rw [mem_blockOf]
    intro μ
    rw [hyv]
    have h1 := Nat.div_add_mod (x μ).val ell
    have h2 := Nat.mod_lt (x μ).val hell
    refine ⟨Nat.mul_div_le _ _, ?_⟩
    generalize ell * ((x μ).val / ell) = A at h1 ⊢
    omega

/-- the embedding `y ↦ ell² · y`. -/
def embNe (ell M R : ℕ) (hell : 0 < ell) (hM : 0 < M) (y : PeriodicLatticeSite (neLu M R)) :
    PeriodicLatticeSite (scaleUp ell 2 (neLu M R)) :=
  fun μ => ⟨ell ^ 2 * (y μ).val, by
    have h2 := ne_scaleUp (ell := ell) (R := R) hell hM μ
    have h3 : (y μ).val < neNu M R := ne_lt hM y μ
    have h4 : ell ^ 2 * (y μ).val < ell ^ 2 * neNu M R := Nat.mul_lt_mul_of_pos_left h3 (pow_pos hell 2)
    have h5 : ell ^ 2 * neNu M R = neN ell M R := by simp only [neN, neNu]; ring
    omega⟩

theorem lambdaOK_ne {ell M R : ℕ} (hell : 3 ≤ ell) (hM : 0 < M) (hR : 1 ≤ R) :
    LambdaOK ell M R 2 (neS ell M R) (neLam M R) := by
  have hell0 : 0 < ell := by omega
  have hl2 : 0 < ell ^ 2 := pow_pos hell0 2
  refine ⟨blockClosed_neLam hM, embNe ell M R hell0 hM, fun y μ => rfl, ?_, ?_⟩
  · intro y hy
    rw [neS_om2]
    right
    show neA ell M R ≤ ell ^ 2 * (y 0).val ∧ ell ^ 2 * (y 0).val < neB ell M R
    have hA : neA ell M R = ell ^ 2 * (M * (R + 13)) := by simp only [neA]; ring
    have hB : neB ell M R = ell ^ 2 * (M * (3 * R + 16)) := by simp only [neB]; ring
    rw [hA, hB]
    have h1 := hy.1; have h2 := hy.2
    constructor
    · exact Nat.mul_le_mul_left _ (le_trans (by nlinarith) h1)
    · exact Nat.mul_lt_mul_of_pos_left (lt_of_lt_of_le h2 (by nlinarith)) hl2
  · intro y hy y' hy'
    have hcase : (y' 0).val < M * (R + 13) ∨ M * (3 * R + 16) ≤ (y' 0).val := by
      by_contra hcon
      push Not at hcon
      apply hy'
      rw [neS_om2]
      right
      show neA ell M R ≤ ell ^ 2 * (y' 0).val ∧ ell ^ 2 * (y' 0).val < neB ell M R
      have hA : neA ell M R = ell ^ 2 * (M * (R + 13)) := by simp only [neA]; ring
      have hB : neB ell M R = ell ^ 2 * (M * (3 * R + 16)) := by simp only [neB]; ring
      rw [hA, hB]
      exact ⟨Nat.mul_le_mul_left _ hcon.1, Nat.mul_lt_mul_of_pos_left hcon.2 hl2⟩
    have hyN : (y 0).val < neNu M R := ne_lt hM y 0
    have hy'N : (y' 0).val < neNu M R := ne_lt hM y' 0
    have e4 : neNu M R = 4 * (R * M) + 17 * M := by simp only [neNu]; ring
    have e5 : M * (2 * R + 14) = 2 * (R * M) + 14 * M := by ring
    have e6 : M * (R + 13) = R * M + 13 * M := by ring
    have e7 : M * (3 * R + 16) = 3 * (R * M) + 16 * M := by ring
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

theorem lambdaOK2_ne {ell M R : ℕ} (hell : 3 ≤ ell) (hdvd : ell ∣ M) (hM : 0 < M) (hR : 1 ≤ R) :
    LambdaOK2 ell M R 2 (neS ell M R) (neLam M R) :=
  ⟨lambdaOK_ne hell hM hR, lamBlockSum_ne (by omega) hdvd hM⟩

theorem neLam_nonempty {M R : ℕ} (hM : 0 < M) : (neLam M R).Nonempty := by
  refine ⟨fun μ => ⟨if μ = 0 then M * (2 * R + 14) else 0, ?_⟩, ?_⟩
  · rw [neLu_succ hM]
    have : 0 < neNu M R := neNu_pos hM
    split_ifs
    · simp only [neNu]; nlinarith
    · exact this
  · show M * (2 * R + 14) ≤ (if (0 : Fin 3) = 0 then M * (2 * R + 14) else 0) ∧
      (if (0 : Fin 3) = 0 then M * (2 * R + 14) else 0) < M * (2 * R + 14) + M
    simp only [if_true]; omega

/-! ## a nonzero `B̃ ∈ Λ̃` -/

def yNe {M R : ℕ} (hM : 0 < M) : PeriodicLatticeSite (neLu M R) :=
  fun μ => ⟨if μ = 0 then M * (2 * R + 14) else 0, by
    rw [neLu_succ hM]
    have : 0 < neNu M R := neNu_pos hM
    split_ifs
    · simp only [neNu]; nlinarith
    · exact this⟩

noncomputable def BseedNe {M R : ℕ} (ell : ℕ) (hM : 0 < M) : Bond (neLu M R) → SuTwo :=
  Pi.single (freeBond ell (yNe (R := R) hM)) suTwoWitness

theorem BseedNe_props {ell M R : ℕ} (hell : 3 ≤ ell) (hdvd : ell ∣ M) (hM : 0 < M) :
    OnLambdaTildeIn (neLam M R) ell (BseedNe (R := R) ell hM) ∧ OnLambdaT (neLam M R) (BseedNe (R := R) ell hM) ∧
      0 < bondEnergy (BseedNe (R := R) ell hM) ∧ BseedNe (R := R) ell hM ≠ 0 := by
  have hell2 : 2 ≤ ell := by omega
  have hdvd' : ∀ μ : Fin 3, ell ∣ neLu M R μ + 1 := fun μ => by
    rw [neLu_succ hM]; exact Dvd.dvd.mul_right hdvd _
  have hy : yNe (R := R) hM ∈ CoarseLattice (neLu M R) ell := by
    rw [mem_CoarseLattice]
    intro μ
    show (if μ = 0 then M * (2 * R + 14) else 0) % ell = 0
    split_ifs
    · exact Nat.mod_eq_zero_of_dvd (Dvd.dvd.mul_right hdvd _)
    · simp
  have hoff : ∀ b : Bond (neLu M R), b ≠ freeBond ell (yNe (R := R) hM) → BseedNe (R := R) ell hM b = 0 :=
    fun b hb => Pi.single_eq_of_ne hb _
  have hOn : OnLambdaT (neLam M R) (BseedNe (R := R) ell hM) := by
    intro b hb
    by_cases hbe : b = freeBond ell (yNe (R := R) hM)
    · exfalso
      apply hb
      have hy0 : ((yNe (R := R) hM) 0).val = M * (2 * R + 14) := by simp [yNe]
      have hfit : ((yNe (R := R) hM) 0).val + ell ≤ neLu M R 0 + 1 := by
        rw [hy0, neLu_succ hM]
        have : ell ≤ M := Nat.le_of_dvd hM hdvd
        have e : neNu M R = M * (2 * R + 14) + M * (2 * R + 3) := by simp only [neNu]; ring
        have : M ≤ M * (2 * R + 3) := Nat.le_mul_of_pos_right _ (by omega)
        omega
      have h0 := freeBond_coord_zero (yNe (R := R) hM) hfit hell2
      subst hbe
      left
      show M * (2 * R + 14) ≤ ((freeBond ell (yNe (R := R) hM)).1 0).val ∧
        ((freeBond ell (yNe (R := R) hM)).1 0).val < M * (2 * R + 14) + M
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

/-- **no site of the layer `x₀ = c` lies in a factor-12 class cube** (every index `j ≤ 2`). -/
theorem ne_layer_uncovered {ell M R : ℕ} (hell : 3 ≤ ell) (hM : 0 < M) (hR : 1 ≤ R)
    (x : PeriodicLatticeSite (scaleUp ell 2 (neLu M R))) (hx : (x 0).val = neC ell M R)
    (sites : Set (PeriodicLatticeSite (scaleUp ell 2 (neLu M R)))) (j : ℕ)
    (hq : IsClassCube ell M 12 2 (neS ell M R) sites j) : x ∉ sites := by
  obtain ⟨l1, l2, l3, l4, l5, l6, l7, l8⟩ := ne_lin hell hM hR
  have hN := ne_scaleUp (ell := ell) (R := R) (by omega) hM
  set N := neN ell M R with hNdef
  have hNe : N = 4 * (ell * (ell * (R * M))) + 17 * (ell * (ell * M)) := rfl
  obtain ⟨⟨hj, ⟨z, -, rfl⟩, hsub, ⟨w, hw, hwB⟩⟩, -⟩ := hq
  intro hxs
  have hlt : ∀ y : PeriodicLatticeSite (scaleUp ell 2 (neLu M R)), ∀ μ, (y μ).val < N :=
    fun y μ => by have := (y μ).isLt; have := hN μ; omega
  have hx0 := ((mem_box_N hN z x _).1 hxs).1
  have hxc : (x 0).val = neA' ell M R + 12 * (ell * M) := by rw [hx]; rfl
  have hA'v : neA' ell M R = ell * (ell * (R * M)) + ell * (ell * M) := rfl
  have hB'v : neB' ell M R = ell * (ell * (R * M)) + 12 * (ell * (ell * M)) := rfl
  have hj' : j = 0 ∨ j = 1 ∨ j = 2 := by omega
  rcases hj' with rfl | rfl | rfl
  · -- index 0: the cube stays inside the thin component, hence inside `Ω₁`, and misses `B⁰`
    have hw0 := ((mem_box_N hN z w _).1 hw).1
    simp only [bigSide, pow_zero, mul_one] at hx0 hw0
    have hxc' : (x 0).val = neA' ell M R + 12 * M + 12 * (ell * M - M) := by
      rw [hxc]; have : M ≤ ell * M := by omega
      omega
    -- a 12M-window through x lies in [A', B')
    have hwJ : neA' ell M R < (w 0).val ∧ (w 0).val < neB' ell M R := by
      have h := arith0 N _ _ _ (neA' ell M R + 12 * (ell * M - M)) (neB' ell M R) M (by rw [hxc']; ring)
        (hlt x 0) (hlt z 0) (hlt w 0) hx0 hw0 (by rw [hA'v, hB'v]; omega) (by rw [hB'v, hNe]; omega)
      omega
    have hw1 : w ∈ (neS ell M R).Om 1 := by
      rw [neS_om1]; simp only [neP1, neQ1, neB] at hwJ ⊢; rw [hA'v] at hwJ ⊢; rw [hB'v] at hwJ; omega
    exact hwB.2 hw1
  · -- index 1: the cube stays inside the thin component, hence inside `Ω₂`, and misses `B¹`
    have hw0 := ((mem_box_N hN z w _).1 hw).1
    simp only [bigSide, pow_one] at hx0 hw0
    have hwJ := arith0 N _ _ _ (neA' ell M R) (neB' ell M R) (M * ell) (by rw [hxc]; ring)
      (hlt x 0) (hlt z 0) (hlt w 0) hx0 hw0 (by rw [hA'v, hB'v]; nlinarith) (by rw [hB'v, hNe]; omega)
    have hw2 : w ∈ (neS ell M R).Om 2 := by
      rw [neS_om2]; left; exact ⟨hwJ.1.le, hwJ.2⟩
    exact hwB.2 hw2
  · -- index 2: the cube is longer than the thin component and leaves `Ω₂`
    simp only [bigSide] at hx0
    have hPpos : 1 ≤ neA' ell M R := by rw [hA'v]; omega
    have hthick : neA' ell M R + 24 * (M * ell) ≤ neB' ell M R := by rw [hA'v, hB'v]; nlinarith
    have hthin : neB' ell M R - neA' ell M R < 12 * (M * ell ^ 2) := by
      rw [hA'v, hB'v]; have : M * ell ^ 2 = ell * (ell * M) := by ring
      rw [this]; omega
    have hB'N : neB' ell M R < N := by rw [hB'v, hNe]; omega
    obtain ⟨hy0N, hy0box, hy0out⟩ := arith1 N _ _ (neA' ell M R) (neB' ell M R) (M * ell) (M * ell ^ 2)
      (by rw [hxc]; ring) (hlt x 0) (hlt z 0) hPpos hx0 hthick hB'N hthin
    generalize hY : (if 12 * (M * ell) + 1 ≤ (if (z 0).val ≤ (x 0).val then (x 0).val - (z 0).val
      else (x 0).val + N - (z 0).val) then neA' ell M R - 1 else neB' ell M R) = y0 at hy0N hy0box hy0out
    have hy0 : y0 < scaleUp ell 2 (neLu M R) 0 + 1 := by have := hN 0; omega
    let y : PeriodicLatticeSite (scaleUp ell 2 (neLu M R)) := Function.update z 0 ⟨y0, hy0⟩
    have hyv : (y 0).val = y0 := by simp [y]
    have hy1 : y 1 = z 1 := by simp [y]
    have hy2 : y 2 = z 2 := by simp [y]
    have hpos : 0 < 12 * bigSide M ell 2 := by
      simp only [bigSide]; have : 0 < M * ell ^ 2 := Nat.mul_pos hM (pow_pos (by omega) 2)
      omega
    have hyin : y ∈ siteBox z (12 * bigSide M ell 2) := by
      rw [mem_box_N hN]
      refine ⟨?_, ?_, ?_⟩
      · rw [hyv]; simpa [bigSide] using hy0box
      · rw [hy1, show (z 1).val + N - (z 1).val = N by have := hlt z 1; omega, Nat.mod_self]; exact hpos
      · rw [hy2, show (z 2).val + N - (z 2).val = N by have := hlt z 2; omega, Nat.mod_self]; exact hpos
    have hy := hsub hyin
    have hyOm : y ∈ (neS ell M R).Om 2 := by
      rcases hy with hy | hy
      · exact hy.1
      · exact absurd hy.1 (tw3_omHi 3 le_rfl y)
    rw [neS_om2, hyv] at hyOm
    have hyc : y0 = neA' ell M R - 1 ∨ y0 = neB' ell M R := by rw [← hY]; split_ifs <;> simp
    have hgap := ne_gap_pos hell hM hR
    rcases hyOm with h | h
    · exact hy0out h
    · rcases hyc with h' | h' <;> rw [h'] at h <;> simp only [neA, neB] at h <;> rw [hA'v, hB'v] at * <;> omega

/-- the layer lies in `Ω₂` (thin component) and in `Ω₀`. -/
theorem ne_layer_mem {ell M R : ℕ} (hell : 3 ≤ ell) (hM : 0 < M) (hR : 1 ≤ R)
    (x : PeriodicLatticeSite (scaleUp ell 2 (neLu M R))) (hx : (x 0).val = neC ell M R) :
    x ∈ (neS ell M R).Om 2 ∧ x ∈ (neS ell M R).Om 0 := by
  obtain ⟨l1, l2, l3, l4, l5, l6, l7, l8⟩ := ne_lin hell hM hR
  refine ⟨?_, ?_⟩
  · rw [neS_om2, hx]; left; simp only [neC, neA', neB']; omega
  · rw [neS_om0, hx]; simp only [neC, neA', neP0, neP1, neQ0, neQ1, neB]; omega

/-! ## the class reads `U` only on bonds based in class cubes; the layer configuration -/

theorem perCube_congr {L : PeriodicLatticeExtent} {ell M f k : ℕ} {S : Tower L} {α₀ η : ℝ} {U U' : LinkCfg L}
    (h : PerCubeRegular2 ell M f k S α₀ η U)
    (hUU : ∀ e : Bond L, (∃ (sites : Set (PeriodicLatticeSite L)) (j : ℕ), IsClassCube ell M f k S sites j ∧ e.1 ∈ sites) →
      U' e = U e) :
    PerCubeRegular2 ell M f k S α₀ η U' := by
  intro sites j hq
  obtain ⟨g, A, h1, h2, h3⟩ := h sites j hq
  refine ⟨g, A, fun e he => ?_, h2, h3⟩
  have : periodicGaugeTransform g U' e = periodicGaugeTransform g U e := by
    simp only [periodicGaugeTransform, hUU e ⟨sites, j, hq, he.1⟩]
  rw [this]
  exact h1 e he

/-- the LAYER configuration: `v` on every direction-1 bond based at `x₀ = c`, `1` elsewhere. -/
def layerCfg {L : PeriodicLatticeExtent} (c : ℕ) (v : Matrix.specialUnitaryGroup (Fin 2) ℂ) : LinkCfg L :=
  fun e => if (e.1 0).val = c ∧ e.2 = 1 then v else 1

/-- **the layer configuration is in the factor-12 class for every `v ∈ SU(2)` and every `α₀ > 0`.** -/
theorem ne_layer_class {ell M R : ℕ} (hell : 3 ≤ ell) (hM : 0 < M) (hR : 1 ≤ R)
    (v : Matrix.specialUnitaryGroup (Fin 2) ℂ) {α₀ : ℝ} (hα : 0 < α₀) :
    PerCubeRegular2 ell M 12 2 (neS ell M R) α₀ ((ell : ℝ) ^ 2)⁻¹ (layerCfg (neC ell M R) v) := by
  have hη : (0 : ℝ) < ((ell : ℝ) ^ 2)⁻¹ := by
    have : (0 : ℝ) < ell := by exact_mod_cast (show 0 < ell by omega)
    positivity
  refine perCube_congr (perCube_one (by omega) hM (by norm_num) hα hη) (fun e he => ?_)
  obtain ⟨sites, j, hq, hes⟩ := he
  have hne : (e.1 0).val ≠ neC ell M R := fun h => ne_layer_uncovered hell hM hR e.1 h sites j hq hes
  simp [layerCfg, hne]

/-! ## the layer plaquettes are read by the operators -/

theorem ne_layer_plaqIn {ell M R : ℕ} (hell : 3 ≤ ell) (hM : 0 < M) (hR : 1 ≤ R)
    (x : PeriodicLatticeSite (scaleUp ell 2 (neLu M R))) (hx : (x 0).val = neC ell M R) :
    pStar x ∈ plaqIn ((neS ell M R).Om 0) := by
  obtain ⟨l1, l2, l3, l4, l5, l6, l7, l8⟩ := ne_lin hell hM hR
  have hN := ne_scaleUp (ell := ell) (R := R) (by omega) hM
  have hcv : neC ell M R = ell * (ell * (R * M)) + ell * (ell * M) + 12 * (ell * M) := rfl
  have hN1 : 1 < neN ell M R := by simp only [neN]; omega
  have memJ : ∀ y : PeriodicLatticeSite (scaleUp ell 2 (neLu M R)),
      ((y 0).val = (x 0).val ∨ (y 0).val = (x 0).val + 1) → y ∈ (neS ell M R).Om 0 := by
    intro y hy
    rw [neS_om0]
    simp only [neP0, neP1, neA', neQ0, neQ1, neB]
    rcases hy with h | h <;> rw [h, hx, hcv] <;> constructor <;> omega
  have s0 : ∀ y : PeriodicLatticeSite (scaleUp ell 2 (neLu M R)), (y 0).val = (x 0).val →
      ((periodicLatticeShift y 0) 0).val = (x 0).val + 1 := by
    intro y hy
    rw [shift_val_N hN hN1, if_pos rfl, hy, hx, Nat.mod_eq_of_lt (by rw [hcv]; simp only [neN]; omega)]
  have s1 : ∀ y : PeriodicLatticeSite (scaleUp ell 2 (neLu M R)),
      ((periodicLatticeShift y 1) 0).val = (y 0).val := by
    intro y
    rw [shift_val_N hN hN1, if_neg (by decide)]
  intro e he
  simp only [periodicPlaquetteBoundaryEdges, pStar, Finset.mem_insert, Finset.mem_singleton] at he
  rcases he with rfl | rfl | rfl | rfl
  · exact ⟨memJ _ (Or.inl rfl), memJ _ (Or.inr (s0 x rfl))⟩
  · exact ⟨memJ _ (Or.inr (s0 x rfl)), memJ _ (Or.inr (by rw [s1, s0 x rfl]))⟩
  · exact ⟨memJ _ (Or.inl (s1 x)), memJ _ (Or.inr (s0 _ (s1 x)))⟩
  · exact ⟨memJ _ (Or.inl rfl), memJ _ (Or.inl (s1 x))⟩

#print axioms ne_admissible
#print axioms ne_between_level1
#print axioms torusOK_ne
#print axioms lambdaOK2_ne
#print axioms BseedNe_props
#print axioms ne_layer_uncovered
#print axioms ne_layer_class
#print axioms ne_layer_plaqIn

end AdalyFormal.CoverNested
