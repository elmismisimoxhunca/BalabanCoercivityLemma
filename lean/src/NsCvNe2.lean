import NsCvNe1

/-!
# NsCvNe2 [cube-factor-parametrised copy of CvNe2; strong-NCWDH lane] -- the nested instance family in the headline regime: `k = 2`, every `ell ≥ 3`, every `M` with `ell ∣ M` (so every
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

/-! ## the cube factor as data (root namespace: visible from every lane) -/


/-- the cube factor `cf` of the class (`IsClassCube ell M cf ..`), `cf ≥ 10` (the range of the headline `Total`).  It enters the
nested family through the width `(cf-1) Y₂` of the thin component, the layer position `X₂ + Y₂ + cf Y₁`, and the (even) torus
multiplier `W = 2 cf + 6`.  Carried as an instance so that every downstream definition and lemma stays textually unchanged. -/
class CfData : Type where
  cf : ℕ
  hcf : 10 ≤ cf


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


/-- local abbreviation used inside this file only -/
local notation "cfv" => CfData.cf


/-! ## the class reads `U` only on bonds based in class cubes; the layer configuration (generic) -/

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


/-- arithmetic of the index-0/1 window (cube factor `cf`): a `cf M`-window through `x = P1' + cf M` stays strictly inside `(P1', Q1')`. -/
theorem arith0c (cf N x z w P1' Q1' M : ℕ) (hx : x = P1' + cf * M) (hxN : x < N) (hzN : z < N) (hwN : w < N)
    (h1 : (x + N - z) % N < cf * M) (h2 : (w + N - z) % N < cf * M) (thick : P1' + 2 * (cf * M) ≤ Q1') (o4 : Q1' < N) :
    P1' < w ∧ w < Q1' := by
  rw [off_cases N _ _ hxN hzN] at h1
  rw [off_cases N _ _ hwN hzN] at h2
  split_ifs at h1 h2 <;> omega

/-- index-2 window (cube factor `cf`): a `cf s`-window through `x` contains `P1' - 1` or `Q1'`, both outside `[P1', Q1')`. -/
theorem arith1c (cf N x z P1' Q1' M s : ℕ) (hx : x = P1' + cf * M) (hxN : x < N) (hzN : z < N) (hP : 1 ≤ P1')
    (h1 : (x + N - z) % N < cf * s) (thick : P1' + 2 * (cf * M) ≤ Q1') (o4 : Q1' < N) (thin : Q1' - P1' < cf * s) :
    let y0 := if cf * M + 1 ≤ (if z ≤ x then x - z else x + N - z) then P1' - 1 else Q1'
    y0 < N ∧ (y0 + N - z) % N < cf * s ∧ ¬ (P1' ≤ y0 ∧ y0 < Q1') := by
  intro y0
  rw [off_cases N _ _ hxN hzN] at h1
  have hy0 : y0 < N := by simp only [y0]; split_ifs <;> omega
  refine ⟨hy0, ?_, ?_⟩
  · rw [off_cases N _ _ hy0 hzN]
    simp only [y0]
    split_ifs at h1 ⊢ <;> omega
  · simp only [y0]; split_ifs <;> omega


/-! ## numbers -/

section nums
variable [CfData]

/-- the unit torus side `N_u = M (4R + 2cf + 6)` (EVEN multiplier: every transverse side `ell² N_u` is even). -/
def neNu (M R : ℕ) : ℕ := 4 * (R * M) + 2 * (cfv * M) + 6 * M
def neLu (M R : ℕ) : PeriodicLatticeExtent := fun _ => neNu M R - 1
def neA' (ell M R : ℕ) : ℕ := ell * (ell * (R * M)) + ell * (ell * M)
def neB' (ell M R : ℕ) : ℕ := ell * (ell * (R * M)) + cfv * (ell * (ell * M))
def neA (ell M R : ℕ) : ℕ := ell * (ell * (R * M)) + cfv * (ell * (ell * M)) + ell * (ell * M)
def neB (ell M R : ℕ) : ℕ := 3 * (ell * (ell * (R * M))) + cfv * (ell * (ell * M)) + 4 * (ell * (ell * M))
def neP1 (ell M R : ℕ) : ℕ := neA' ell M R - ell * (R * M)
def neQ1 (ell M R : ℕ) : ℕ := neB ell M R + ell * (R * M)
def neP0 (ell M R : ℕ) : ℕ := neP1 ell M R - R * M
def neQ0 (ell M R : ℕ) : ℕ := neQ1 ell M R + R * M
def neN (ell M R : ℕ) : ℕ := 4 * (ell * (ell * (R * M))) + 2 * (cfv * (ell * (ell * M))) + 6 * (ell * (ell * M))
/-- the layer coordinate `X₂ + Y₂ + cf Y₁`. -/
def neC (ell M R : ℕ) : ℕ := neA' ell M R + cfv * (ell * M)
/-- the lower end of `Λ` (unit coordinate): `M (2R + cf + 2)`. -/
def neLo (M R : ℕ) : ℕ := M * (2 * R + (cfv + 2))

/-- the tower on the fine torus (`k = 2`). -/
def neS (ell M R : ℕ) : Tower (scaleUp ell 2 (neLu M R)) :=
  tw3 _ (neP0 ell M R) (neQ0 ell M R) (neP1 ell M R) (neQ1 ell M R) (neA' ell M R) (neB' ell M R) (neA ell M R) (neB ell M R)

theorem neNu_pos {M R : ℕ} (hM : 0 < M) : 0 < neNu M R := by unfold neNu; omega

theorem neLu_succ {M R : ℕ} (hM : 0 < M) (μ : Fin 3) : neLu M R μ + 1 = neNu M R := by
  have := neNu_pos (R := R) hM; simp only [neLu]; omega

theorem ne_scaleUp {ell M R : ℕ} (hell : 0 < ell) (hM : 0 < M) (μ : Fin 3) :
    scaleUp ell 2 (neLu M R) μ + 1 = neN ell M R := by
  have h1 := neLu_succ (R := R) hM μ
  have hN : neN ell M R = neNu M R * ell ^ 2 := by simp only [neN, neNu]; ring
  have : 0 < neNu M R * ell ^ 2 := Nat.mul_pos (neNu_pos hM) (pow_pos hell 2)
  simp only [scaleUp, h1]; omega

omit [CfData] in
/-- the linear facts (atoms `X₂ = ell(ell(RM))`, `Y₂ = ell(ell M)`, `X₁ = ell(RM)`, `Y₁ = ell M`, `X₀ = RM`, `M`). -/
theorem ne_lin {ell M R : ℕ} (hell : 3 ≤ ell) (hM : 0 < M) (hR : 1 ≤ R) :
    3 * (ell * (R * M)) ≤ ell * (ell * (R * M)) ∧ 3 * (ell * M) ≤ ell * (ell * M) ∧
    3 * (R * M) ≤ ell * (R * M) ∧ 3 * M ≤ ell * M ∧ M ≤ R * M ∧ ell * M ≤ ell * (R * M) ∧
    ell * (ell * M) ≤ ell * (ell * (R * M)) ∧ 1 ≤ M := by
  refine ⟨Nat.mul_le_mul_right _ hell, Nat.mul_le_mul_right _ hell, Nat.mul_le_mul_right _ hell,
    Nat.mul_le_mul_right _ hell, Nat.le_mul_of_pos_left _ (by omega), ?_, ?_, hM⟩
  · exact Nat.mul_le_mul_left _ (Nat.le_mul_of_pos_left _ (by omega))
  · exact Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (Nat.le_mul_of_pos_left _ (by omega)))

/-- the cube-factor facts (atoms `cf M`, `cf Y₁`, `cf Y₂`). -/
theorem ne_lin_c {ell M : ℕ} (hell : 3 ≤ ell) :
    10 * M ≤ cfv * M ∧ 3 * (cfv * M) ≤ cfv * (ell * M) ∧
    3 * (cfv * (ell * M)) ≤ cfv * (ell * (ell * M)) ∧
    10 * (ell * M) ≤ cfv * (ell * M) ∧ 10 * (ell * (ell * M)) ≤ cfv * (ell * (ell * M)) := by
  have hc := CfData.hcf
  refine ⟨Nat.mul_le_mul_right _ hc, ?_, ?_, Nat.mul_le_mul_right _ hc, Nat.mul_le_mul_right _ hc⟩
  · calc 3 * (cfv * M) ≤ ell * (cfv * M) := Nat.mul_le_mul_right _ hell
      _ = cfv * (ell * M) := by ring
  · calc 3 * (cfv * (ell * M)) ≤ ell * (cfv * (ell * M)) := Nat.mul_le_mul_right _ hell
      _ = cfv * (ell * (ell * M)) := by ring

/-- the cube-factor facts for `2 ≤ ell` (factor 2 in place of 3). -/
theorem ne_lin_c2 {ell M : ℕ} (hell : 2 ≤ ell) :
    10 * M ≤ cfv * M ∧ 2 * (cfv * M) ≤ cfv * (ell * M) ∧
    2 * (cfv * (ell * M)) ≤ cfv * (ell * (ell * M)) ∧
    10 * (ell * M) ≤ cfv * (ell * M) ∧ 10 * (ell * (ell * M)) ≤ cfv * (ell * (ell * M)) := by
  have hc := CfData.hcf
  refine ⟨Nat.mul_le_mul_right _ hc, ?_, ?_, Nat.mul_le_mul_right _ hc, Nat.mul_le_mul_right _ hc⟩
  · calc 2 * (cfv * M) ≤ ell * (cfv * M) := Nat.mul_le_mul_right _ hell
      _ = cfv * (ell * M) := by ring
  · calc 2 * (cfv * (ell * M)) ≤ ell * (cfv * (ell * M)) := Nat.mul_le_mul_right _ hell
      _ = cfv * (ell * (ell * M)) := by ring

theorem ne_geo3 {ell M R : ℕ} (hell : 3 ≤ ell) (hM : 0 < M) (hR : 1 ≤ R) :
    Geo3 M ell R (neN ell M R) (neP0 ell M R) (neQ0 ell M R) (neP1 ell M R) (neQ1 ell M R)
      (neA' ell M R) (neB' ell M R) (neA ell M R) (neB ell M R) := by
  obtain ⟨l1, l2, l3, l4, l5, l6, l7, l8⟩ := ne_lin hell hM hR
  obtain ⟨c1, c2, c3, c4, c5⟩ := ne_lin_c (M := M) hell
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
  obtain ⟨c1, c2, c3, c4, c5⟩ := ne_lin_c (M := M) hell
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
  {y | neLo M R ≤ (y 0).val ∧ (y 0).val < neLo M R + M}

theorem torusOK_ne {ell M R : ℕ} (hell : 3 ≤ ell) (hdvd : ell ∣ M) (hM : 0 < M) :
    TorusOK ell M (neLu M R) := by
  have hle : ell ≤ M := Nat.le_of_dvd hM hdvd
  refine ⟨fun μ => ?_, fun μ => ?_, fun μ => ?_⟩ <;> rw [neLu_succ hM] <;> simp only [neNu]
  · exact Nat.dvd_add (Nat.dvd_add (Dvd.dvd.mul_left (Dvd.dvd.mul_left hdvd R) 4)
      (Dvd.dvd.mul_left (Dvd.dvd.mul_left hdvd cfv) 2)) (Dvd.dvd.mul_left hdvd 6)
  · omega
  · exact Nat.dvd_add (Nat.dvd_add (Dvd.dvd.mul_left (Dvd.dvd.mul_left (dvd_refl M) R) 4)
      (Dvd.dvd.mul_left (Dvd.dvd.mul_left (dvd_refl M) cfv) 2)) (Dvd.dvd.mul_left (dvd_refl M) 6)

theorem blockClosed_neLam {M R : ℕ} (hM : 0 < M) : BlockClosed M (neLam M R) := by
  intro x hx y hy
  have h := hy 0
  have hx' : M * (2 * R + (cfv + 2)) ≤ (x 0).val ∧ (x 0).val < M * (2 * R + (cfv + 2) + 1) := by
    refine ⟨hx.1, ?_⟩
    have := hx.2
    rw [show M * (2 * R + (cfv + 2) + 1) = neLo M R + M by unfold neLo; ring]; exact this
  rw [iv_iff hM] at hx'
  have : M * (2 * R + (cfv + 2)) ≤ (y 0).val ∧ (y 0).val < M * (2 * R + (cfv + 2) + 1) := by
    rw [iv_iff hM, h]; exact hx'
  refine ⟨this.1, ?_⟩
  have := this.2
  rw [show M * (2 * R + (cfv + 2) + 1) = neLo M R + M by unfold neLo; ring] at this; exact this

theorem lamBlockSum_ne {ell M R : ℕ} (hell : 0 < ell) (hdvd : ell ∣ M) (hM : 0 < M) :
    LamBlockSum ell (neLam M R) := by
  intro x hx
  obtain ⟨a, ha⟩ := hdvd
  have hxN : ∀ μ, (x μ).val < neNu M R := fun μ => ne_lt hM x μ
  let y : PeriodicLatticeSite (neLu M R) := fun μ => ⟨ell * ((x μ).val / ell),
    lt_of_le_of_lt (Nat.mul_div_le _ _) (by have := neLu_succ (R := R) hM μ; have := hxN μ; omega)⟩
  have hyv : ∀ μ, (y μ).val = ell * ((x μ).val / ell) := fun μ => rfl
  have e1 : neLo M R = ell * (a * (2 * R + (cfv + 2))) := by unfold neLo; rw [ha]; ring
  have e2 : neLo M R + M = ell * (a * (2 * R + (cfv + 2) + 1)) := by unfold neLo; rw [ha]; ring
  refine ⟨y, ⟨?_, ?_⟩, ?_⟩
  · rw [mem_CoarseLattice]; intro μ; rw [hyv]; exact Nat.mul_mod_right _ _
  · intro x' hx'
    rw [mem_blockOf] at hx'
    have h0 := hx' 0
    rw [hyv] at h0
    have hx0 : ell * (a * (2 * R + (cfv + 2))) ≤ (x 0).val ∧ (x 0).val < ell * (a * (2 * R + (cfv + 2) + 1)) := by
      have := hx.1; have := hx.2; omega
    rw [iv_iff hell] at hx0
    have hq1 : a * (2 * R + (cfv + 2)) ≤ (x 0).val / ell := hx0.1
    have hq2 : (x 0).val / ell + 1 ≤ a * (2 * R + (cfv + 2) + 1) := hx0.2
    have m1 : ell * (a * (2 * R + (cfv + 2))) ≤ ell * ((x 0).val / ell) := Nat.mul_le_mul_left ell hq1
    have m2 : ell * ((x 0).val / ell + 1) ≤ ell * (a * (2 * R + (cfv + 2) + 1)) := Nat.mul_le_mul_left ell hq2
    constructor
    · show neLo M R ≤ (x' 0).val
      omega
    · show (x' 0).val < neLo M R + M
      have : ell * ((x 0).val / ell + 1) = ell * ((x 0).val / ell) + ell := by ring
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

theorem lambdaOK2_ne {ell M R : ℕ} (hell : 3 ≤ ell) (hdvd : ell ∣ M) (hM : 0 < M) (hR : 1 ≤ R) :
    LambdaOK2 ell M R 2 (neS ell M R) (neLam M R) :=
  ⟨lambdaOK_ne hell hM hR, lamBlockSum_ne (by omega) hdvd hM⟩

theorem neLo_lt {M R : ℕ} (hM : 0 < M) : neLo M R + M < neNu M R := by
  have e5 : neLo M R = 2 * (R * M) + cfv * M + 2 * M := by unfold neLo; ring
  unfold neNu; omega

theorem neLam_nonempty {M R : ℕ} (hM : 0 < M) : (neLam M R).Nonempty := by
  have hlt := neLo_lt (R := R) hM
  refine ⟨fun μ => ⟨if μ = 0 then neLo M R else 0, ?_⟩, ?_⟩
  · rw [neLu_succ hM]
    have : 0 < neNu M R := neNu_pos hM
    split_ifs
    · omega
    · exact this
  · show neLo M R ≤ (if (0 : Fin 3) = 0 then neLo M R else 0) ∧
      (if (0 : Fin 3) = 0 then neLo M R else 0) < neLo M R + M
    simp only [if_true]; omega

/-! ## a nonzero `B̃ ∈ Λ̃` -/

def yNe {M R : ℕ} (hM : 0 < M) : PeriodicLatticeSite (neLu M R) :=
  fun μ => ⟨if μ = 0 then neLo M R else 0, by
    rw [neLu_succ hM]
    have hlt := neLo_lt (R := R) hM
    have : 0 < neNu M R := neNu_pos hM
    split_ifs
    · omega
    · exact this⟩

noncomputable def BseedNe {M R : ℕ} (ell : ℕ) (hM : 0 < M) : Bond (neLu M R) → SuTwo :=
  Pi.single (freeBond ell (yNe (R := R) hM)) suTwoWitness

theorem BseedNe_props {ell M R : ℕ} (hell : 3 ≤ ell) (hdvd : ell ∣ M) (hM : 0 < M) :
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

/-- **no site of the layer `x₀ = c` lies in a factor-`cf` class cube** (every index `j ≤ 2`). -/
theorem ne_layer_uncovered {ell M R : ℕ} (hell : 3 ≤ ell) (hM : 0 < M) (hR : 1 ≤ R)
    (x : PeriodicLatticeSite (scaleUp ell 2 (neLu M R))) (hx : (x 0).val = neC ell M R)
    (sites : Set (PeriodicLatticeSite (scaleUp ell 2 (neLu M R)))) (j : ℕ)
    (hq : IsClassCube ell M cfv 2 (neS ell M R) sites j) : x ∉ sites := by
  obtain ⟨l1, l2, l3, l4, l5, l6, l7, l8⟩ := ne_lin hell hM hR
  obtain ⟨c1, c2, c3, c4, c5⟩ := ne_lin_c (M := M) hell
  have hcf := CfData.hcf
  have hN := ne_scaleUp (ell := ell) (R := R) (by omega) hM
  set N := neN ell M R with hNdef
  have hNe : N = 4 * (ell * (ell * (R * M))) + 2 * (cfv * (ell * (ell * M))) + 6 * (ell * (ell * M)) := rfl
  obtain ⟨⟨hj, ⟨z, -, rfl⟩, hsub, ⟨w, hw, hwB⟩⟩, -⟩ := hq
  intro hxs
  have hlt : ∀ y : PeriodicLatticeSite (scaleUp ell 2 (neLu M R)), ∀ μ, (y μ).val < N :=
    fun y μ => by have := (y μ).isLt; have := hN μ; omega
  have hx0 := ((mem_box_N hN z x _).1 hxs).1
  have hxc : (x 0).val = neA' ell M R + cfv * (ell * M) := by rw [hx]; rfl
  have hA'v : neA' ell M R = ell * (ell * (R * M)) + ell * (ell * M) := rfl
  have hB'v : neB' ell M R = ell * (ell * (R * M)) + cfv * (ell * (ell * M)) := rfl
  have hj' : j = 0 ∨ j = 1 ∨ j = 2 := by omega
  rcases hj' with rfl | rfl | rfl
  · -- index 0: the cube stays inside the thin component, hence inside `Ω₁`, and misses `B⁰`
    have hw0 := ((mem_box_N hN z w _).1 hw).1
    simp only [bigSide, pow_zero, mul_one] at hx0 hw0
    obtain ⟨q, hq⟩ : ∃ q, ell * M = M + q := ⟨ell * M - M, by omega⟩
    have hcq : cfv * (ell * M) = cfv * M + cfv * q := by rw [hq]; ring
    have hxc' : (x 0).val = (neA' ell M R + cfv * q) + cfv * M := by rw [hxc, hcq]; omega
    -- a `cf M`-window through x lies in [A', B')
    have hwJ : neA' ell M R < (w 0).val ∧ (w 0).val < neB' ell M R := by
      have h := arith0c cfv N _ _ _ (neA' ell M R + cfv * q) (neB' ell M R) M hxc'
        (hlt x 0) (hlt z 0) (hlt w 0) hx0 hw0 (by rw [hA'v, hB'v]; omega) (by rw [hB'v, hNe]; omega)
      omega
    have hw1 : w ∈ (neS ell M R).Om 1 := by
      rw [neS_om1]; simp only [neP1, neQ1, neB] at hwJ ⊢; rw [hA'v] at hwJ ⊢; rw [hB'v] at hwJ; omega
    exact hwB.2 hw1
  · -- index 1: the cube stays inside the thin component, hence inside `Ω₂`, and misses `B¹`
    have hw0 := ((mem_box_N hN z w _).1 hw).1
    simp only [bigSide, pow_one] at hx0 hw0
    have hcm : cfv * (M * ell) = cfv * (ell * M) := by ring
    have hwJ := arith0c cfv N _ _ _ (neA' ell M R) (neB' ell M R) (M * ell) (by rw [hxc]; ring)
      (hlt x 0) (hlt z 0) (hlt w 0) hx0 hw0 (by rw [hA'v, hB'v, hcm]; omega) (by rw [hB'v, hNe]; omega)
    have hw2 : w ∈ (neS ell M R).Om 2 := by
      rw [neS_om2]; left; exact ⟨hwJ.1.le, hwJ.2⟩
    exact hwB.2 hw2
  · -- index 2: the cube is longer than the thin component and leaves `Ω₂`
    simp only [bigSide] at hx0
    have hcm : cfv * (M * ell) = cfv * (ell * M) := by ring
    have hMe : M * ell ^ 2 = ell * (ell * M) := by ring
    have hPpos : 1 ≤ neA' ell M R := by rw [hA'v]; omega
    have hthick : neA' ell M R + 2 * (cfv * (M * ell)) ≤ neB' ell M R := by rw [hA'v, hB'v, hcm]; omega
    have hthin : neB' ell M R - neA' ell M R < cfv * (M * ell ^ 2) := by
      rw [hA'v, hB'v, hMe]; omega
    have hB'N : neB' ell M R < N := by rw [hB'v, hNe]; omega
    obtain ⟨hy0N, hy0box, hy0out⟩ := arith1c cfv N _ _ (neA' ell M R) (neB' ell M R) (M * ell) (M * ell ^ 2)
      (by rw [hxc]; ring) (hlt x 0) (hlt z 0) hPpos hx0 hthick hB'N hthin
    generalize hY : (if cfv * (M * ell) + 1 ≤ (if (z 0).val ≤ (x 0).val then (x 0).val - (z 0).val
      else (x 0).val + N - (z 0).val) then neA' ell M R - 1 else neB' ell M R) = y0 at hy0N hy0box hy0out
    have hy0 : y0 < scaleUp ell 2 (neLu M R) 0 + 1 := by have := hN 0; omega
    let y : PeriodicLatticeSite (scaleUp ell 2 (neLu M R)) := Function.update z 0 ⟨y0, hy0⟩
    have hyv : (y 0).val = y0 := by simp [y]
    have hy1 : y 1 = z 1 := by simp [y]
    have hy2 : y 2 = z 2 := by simp [y]
    have hpos : 0 < cfv * bigSide M ell 2 := by
      simp only [bigSide]
      exact Nat.mul_pos (by omega) (Nat.mul_pos hM (pow_pos (by omega) 2))
    have hyin : y ∈ siteBox z (cfv * bigSide M ell 2) := by
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
  obtain ⟨c1, c2, c3, c4, c5⟩ := ne_lin_c (M := M) hell
  refine ⟨?_, ?_⟩
  · rw [neS_om2, hx]; left; simp only [neC, neA', neB']; omega
  · rw [neS_om0, hx]; simp only [neC, neA', neP0, neP1, neQ0, neQ1, neB]; omega

/-- **the layer configuration is in the factor-`cf` class for every `v ∈ SU(2)` and every `α₀ > 0`.** -/
theorem ne_layer_class {ell M R : ℕ} (hell : 3 ≤ ell) (hM : 0 < M) (hR : 1 ≤ R)
    (v : Matrix.specialUnitaryGroup (Fin 2) ℂ) {α₀ : ℝ} (hα : 0 < α₀) :
    PerCubeRegular2 ell M cfv 2 (neS ell M R) α₀ ((ell : ℝ) ^ 2)⁻¹ (layerCfg (neC ell M R) v) := by
  have hη : (0 : ℝ) < ((ell : ℝ) ^ 2)⁻¹ := by
    have : (0 : ℝ) < ell := by exact_mod_cast (show 0 < ell by omega)
    positivity
  have hcf := CfData.hcf
  refine perCube_congr (perCube_one (by omega) hM (by omega) hα hη) (fun e he => ?_)
  obtain ⟨sites, j, hq, hes⟩ := he
  have hne : (e.1 0).val ≠ neC ell M R := fun h => ne_layer_uncovered hell hM hR e.1 h sites j hq hes
  simp [layerCfg, hne]

/-! ## the layer plaquettes are read by the operators -/

theorem ne_layer_plaqIn {ell M R : ℕ} (hell : 3 ≤ ell) (hM : 0 < M) (hR : 1 ≤ R)
    (x : PeriodicLatticeSite (scaleUp ell 2 (neLu M R))) (hx : (x 0).val = neC ell M R) :
    pStar x ∈ plaqIn ((neS ell M R).Om 0) := by
  obtain ⟨l1, l2, l3, l4, l5, l6, l7, l8⟩ := ne_lin hell hM hR
  obtain ⟨c1, c2, c3, c4, c5⟩ := ne_lin_c (M := M) hell
  have hN := ne_scaleUp (ell := ell) (R := R) (by omega) hM
  have hcv : neC ell M R = ell * (ell * (R * M)) + ell * (ell * M) + cfv * (ell * M) := rfl
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

end nums

#print axioms ne_admissible
#print axioms ne_between_level1
#print axioms torusOK_ne
#print axioms lambdaOK2_ne
#print axioms BseedNe_props
#print axioms ne_layer_uncovered
#print axioms ne_layer_class
#print axioms ne_layer_plaqIn

end AdalyFormal.CoverNested
