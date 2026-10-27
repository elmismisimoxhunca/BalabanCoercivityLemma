import NC2
import NV5

/-!
# NC3 -- what the class `PerCubeRegular2` does NOT constrain (lane nocover_20261015)

* `perCube_update`: `PerCubeRegular2` reads `U` only on the `CubeBond`s of class cubes.  If the base site of a bond `b` lies in no class
  cube, then `Function.update U b v ∈ PerCubeRegular2` for EVERY `v ∈ SU(2)` whenever `U ∈ PerCubeRegular2`.
* `perCube_one`: the constant configuration `1` is in the class (`g = 1`, `A = 0`) for every `α₀ > 0`, `η > 0`, `ell, M, f > 0`.
* `tw2_uncovered`: on the two-component tower `tw2` (NC2), when the second level-1 component `[P1',Q1')` is thinner than one index-1
  cube (`Q1' - P1' < 12 M ell`) but at least `24 M` thick, the site with `x₀ = P1' + 12 M` lies in NO class cube of factor 12
  (index 0: the cube would stay inside `Ω₁` and miss `B⁰`; index 1: the cube would leave `Ω₁`).
* `negOne`: the central element `-1 ∈ SU(2)`; `hol_update_negOne`: flipping the single link `(x, 1)` to `-1` in the constant
  configuration gives the plaquette `(x; 0, 1)` the holonomy `-1`.
-/
set_option autoImplicit false
set_option maxRecDepth 8000
set_option maxHeartbeats 16000000

namespace AdalyFormal.NoCover

open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLane2
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
open AdalyFormal.Balaban.RMapLipschitz (frobNorm frobNorm_zero)
open AdalyFormal.NonVac (shift_val_N mem_box_N)

/-! ## 1. the class reads `U` only on cube bonds -/

theorem perCube_update {L : PeriodicLatticeExtent} {ell M f k : ℕ} {S : Tower L} {α₀ η : ℝ} {U : LinkCfg L}
    (h : PerCubeRegular2 ell M f k S α₀ η U) (b : Bond L)
    (hb : ∀ (sites : Set (PeriodicLatticeSite L)) (j : ℕ), IsClassCube ell M f k S sites j → b.1 ∉ sites)
    (v : Matrix.specialUnitaryGroup (Fin 2) ℂ) :
    PerCubeRegular2 ell M f k S α₀ η (Function.update U b v) := by
  intro sites j hq
  obtain ⟨g, A, h1, h2, h3⟩ := h sites j hq
  refine ⟨g, A, fun e he => ?_, h2, h3⟩
  have hne : e ≠ b := by
    intro heq
    exact hb sites j hq (heq ▸ he.1)
  have : periodicGaugeTransform g (Function.update U b v) e = periodicGaugeTransform g U e := by
    simp only [periodicGaugeTransform, Function.update_of_ne hne]
  rw [this]
  exact h1 e he

/-- the class bound is positive -/
theorem classBound_pos {ell M f : ℕ} {α₀ η : ℝ} (hell : 0 < ell) (hM : 0 < M) (hf : 0 < f) (hα : 0 < α₀) (hη : 0 < η)
    (j n : ℕ) : 0 < (f : ℝ) * M * α₀ * (((ell : ℝ) ^ j * η)⁻¹ ^ n) := by
  have h1 : (0 : ℝ) < f := by exact_mod_cast hf
  have h2 : (0 : ℝ) < M := by exact_mod_cast hM
  have h3 : (0 : ℝ) < (ell : ℝ) ^ j * η := mul_pos (pow_pos (by exact_mod_cast hell) j) hη
  positivity

theorem curlA_zero {L : PeriodicLatticeExtent} (η : ℝ) (x : PeriodicLatticeSite L) (a b : Fin 3) :
    curlA η (fun _ : Bond L => (0 : Matrix (Fin 2) (Fin 2) ℂ)) x a b = 0 := by
  simp [curlA]

theorem ddA_zero {L : PeriodicLatticeExtent} (η : ℝ) (x : PeriodicLatticeSite L) (μ : Fin 3) :
    ddA η (fun _ : Bond L => (0 : Matrix (Fin 2) (Fin 2) ℂ)) x μ = 0 := by
  simp [ddA, curlA_zero]

/-- the constant configuration `1` is in the class. -/
theorem perCube_one {L : PeriodicLatticeExtent} {ell M f k : ℕ} {S : Tower L} {α₀ η : ℝ}
    (hell : 0 < ell) (hM : 0 < M) (hf : 0 < f) (hα : 0 < α₀) (hη : 0 < η) :
    PerCubeRegular2 ell M f k S α₀ η (fun _ => 1) := by
  intro sites j _
  refine ⟨fun _ => 1, fun _ => 0, fun e _ => ⟨?_, ?_, ?_⟩, fun μ ν x _ _ => ?_, fun μ x _ => ?_⟩
  · simp [HT]
  · simp [periodicGaugeTransform]
  · rw [frobNorm_zero]; exact classBound_pos hell hM hf hα hη j 1
  · simp only [sub_self, smul_zero, frobNorm_zero]; exact classBound_pos hell hM hf hα hη j 2
  · rw [ddA_zero, frobNorm_zero]; exact classBound_pos hell hM hf hα hη j 3

/-! ## 2. the central element `-1` and the flipped plaquette -/

/-- `-1 ∈ SU(2)`. -/
def negOne : Matrix.specialUnitaryGroup (Fin 2) ℂ :=
  ⟨-1, by
    rw [Matrix.mem_specialUnitaryGroup_iff]
    refine ⟨?_, ?_⟩
    · rw [Matrix.mem_unitaryGroup_iff]; simp
    · simp [Matrix.det_neg]⟩

theorem negOne_coe : ((negOne : Matrix.specialUnitaryGroup (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) = -1 := rfl

theorem negOne_ne_one : negOne ≠ 1 := by
  intro h
  have := congrArg (fun g : Matrix.specialUnitaryGroup (Fin 2) ℂ => ((g : Matrix (Fin 2) (Fin 2) ℂ) 0 0)) h
  simp [negOne_coe] at this
  norm_num at this

theorem negOne_mul_self : negOne * negOne = 1 := by
  apply Subtype.ext
  show (-1 : Matrix (Fin 2) (Fin 2) ℂ) * (-1) = 1
  simp

theorem negOne_inv : negOne⁻¹ = negOne := inv_eq_of_mul_eq_one_right negOne_mul_self

/-- flipping ONE link `(x,1)` of the constant configuration to `-1` gives the plaquette `(x; 0,1)` the holonomy `-1`. -/
theorem hol_update_negOne {L : PeriodicLatticeExtent} {N : ℕ} (hN : ∀ μ, L μ + 1 = N) (hN1 : 1 < N)
    (x : PeriodicLatticeSite L) :
    periodicPlaquetteHolonomy (Function.update (fun _ => (1 : Matrix.specialUnitaryGroup (Fin 2) ℂ)) ((x, 1) : Bond L) negOne)
      ((x, ⟨((0 : Fin 3), (1 : Fin 3)), by decide⟩) : PeriodicLatticePlaquette L) = negOne := by
  have hs : periodicLatticeShift x 0 ≠ x := by
    intro h
    have := congrArg (fun y : PeriodicLatticeSite L => (y 0).val) h
    rw [shift_val_N hN hN1, if_pos rfl] at this
    have hx := (x 0).isLt
    have hN0 := hN 0
    by_cases hlt : (x 0).val + 1 < N
    · rw [Nat.mod_eq_of_lt hlt] at this; omega
    · have he : (x 0).val + 1 = N := by omega
      rw [he, Nat.mod_self] at this; omega
  have e1 : ((x, (0 : Fin 3)) : Bond L) ≠ (x, 1) := by
    intro h; have := congrArg Prod.snd h; simp at this
  have e2 : ((periodicLatticeShift x 0, (1 : Fin 3)) : Bond L) ≠ (x, 1) := by
    intro h; exact hs (congrArg Prod.fst h)
  have e3 : ((periodicLatticeShift x 1, (0 : Fin 3)) : Bond L) ≠ (x, 1) := by
    intro h; have := congrArg Prod.snd h; simp at this
  simp only [periodicPlaquetteHolonomy]
  rw [Function.update_of_ne e1, Function.update_of_ne e2, Function.update_of_ne e3, Function.update_self]
  simp [negOne_inv]

/-! ## 3. the uncovered site of the thin component -/

theorem off_cases (N a z : ℕ) (ha : a < N) (hz : z < N) :
    (a + N - z) % N = if z ≤ a then a - z else a + N - z := by
  split_ifs with h
  · have : a + N - z = (a - z) + N := by omega
    rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
  · rw [Nat.mod_eq_of_lt (by omega)]

/-- index-0 window: a 12M-window through `x = P1' + 12M` stays strictly inside the thin component. -/
theorem arith0 (N x z w P1' Q1' M : ℕ) (hx : x = P1' + 12 * M) (hxN : x < N) (hzN : z < N) (hwN : w < N)
    (h1 : (x + N - z) % N < 12 * M) (h2 : (w + N - z) % N < 12 * M) (thick : P1' + 24 * M ≤ Q1') (o4 : Q1' < N) :
    P1' < w ∧ w < Q1' := by
  rw [off_cases N _ _ hxN hzN] at h1
  rw [off_cases N _ _ hwN hzN] at h2
  split_ifs at h1 h2 <;> omega

/-- index-1 window: a `12 s`-window through `x` contains `P1' - 1` or `Q1'`, both outside the thin component. -/
theorem arith1 (N x z P1' Q1' M s : ℕ) (hx : x = P1' + 12 * M) (hxN : x < N) (hzN : z < N) (hP : 1 ≤ P1')
    (h1 : (x + N - z) % N < 12 * s) (thick : P1' + 24 * M ≤ Q1') (o4 : Q1' < N) (thin : Q1' - P1' < 12 * s) :
    let y0 := if 12 * M + 1 ≤ (if z ≤ x then x - z else x + N - z) then P1' - 1 else Q1'
    y0 < N ∧ (y0 + N - z) % N < 12 * s ∧ ¬ (P1' ≤ y0 ∧ y0 < Q1') := by
  intro y0
  rw [off_cases N _ _ hxN hzN] at h1
  have hy0 : y0 < N := by simp only [y0]; split_ifs <;> omega
  refine ⟨hy0, ?_, ?_⟩
  · rw [off_cases N _ _ hy0 hzN]
    simp only [y0]
    split_ifs at h1 ⊢ <;> omega
  · simp only [y0]; split_ifs <;> omega

/-- the arithmetic the uncovered-site argument needs. -/
structure Thin (M ell N P0 Q0 P1 Q1 P0' Q0' P1' Q1' : ℕ) : Prop where
  hM : 0 < M
  ord : Q1 ≤ Q0 ∧ Q0 ≤ P0' ∧ P0' < P1' ∧ Q1' < N
  thick : P1' + 24 * M ≤ Q1'
  thin : Q1' - P1' < 12 * (M * ell)

theorem tw2_uncovered {M ell N P0 Q0 P1 Q1 P0' Q0' P1' Q1' : ℕ} (T : Thin M ell N P0 Q0 P1 Q1 P0' Q0' P1' Q1')
    {L : PeriodicLatticeExtent} (hN : ∀ μ, L μ + 1 = N) (x : PeriodicLatticeSite L) (hx : (x 0).val = P1' + 12 * M)
    (sites : Set (PeriodicLatticeSite L)) (j : ℕ)
    (hq : IsClassCube ell M 12 1 (tw2 L P0 Q0 P1 Q1 P0' Q0' P1' Q1') sites j) : x ∉ sites := by
  obtain ⟨hM, ⟨o1, o2, o3, o4⟩, thick, thin⟩ := T
  obtain ⟨⟨hj, ⟨z, -, rfl⟩, hsub, ⟨w, hw, hwB⟩⟩, -⟩ := hq
  intro hxs
  have hlt : ∀ y : PeriodicLatticeSite L, ∀ μ, (y μ).val < N := fun y μ => by have := (y μ).isLt; have := hN μ; omega
  have hx0 := ((mem_box_N hN z x _).1 hxs).1
  have hj' : j = 0 ∨ j = 1 := by omega
  rcases hj' with rfl | rfl
  · -- index 0: every site of the cube lies in the thin component of `Ω₁`, so the cube misses `B⁰`
    have hw0 := ((mem_box_N hN z w _).1 hw).1
    simp only [bigSide, pow_zero, mul_one] at hx0 hw0
    have hwJ := arith0 N _ _ _ P1' Q1' M hx (hlt x 0) (hlt z 0) (hlt w 0) hx0 hw0 thick o4
    have hw1 : w ∈ (tw2 L P0 Q0 P1 Q1 P0' Q0' P1' Q1').Om 1 := by rw [tw2_om1]; exact Or.inr ⟨hwJ.1.le, hwJ.2⟩
    exact hwB.2 hw1
  · -- index 1: the cube is longer than the thin component and leaves `Ω₁`
    simp only [bigSide, pow_one] at hx0
    have hPpos : 1 ≤ P1' := by omega
    obtain ⟨hy0N, hy0box, hy0out⟩ := arith1 N _ _ P1' Q1' M (M * ell) hx (hlt x 0) (hlt z 0) hPpos hx0 thick o4 thin
    generalize hY : (if 12 * M + 1 ≤ (if (z 0).val ≤ (x 0).val then (x 0).val - (z 0).val else (x 0).val + N - (z 0).val)
      then P1' - 1 else Q1') = y0 at hy0N hy0box hy0out
    have hy0 : y0 < L 0 + 1 := by have := hN 0; omega
    let y : PeriodicLatticeSite L := Function.update z 0 ⟨y0, hy0⟩
    have hyv : (y 0).val = y0 := by simp [y]
    have hy1 : y 1 = z 1 := by simp [y]
    have hy2 : y 2 = z 2 := by simp [y]
    have hpos : 0 < 12 * bigSide M ell 1 := by
      simp only [bigSide, pow_one]
      have : 0 < M * ell := by
        rcases Nat.eq_zero_or_pos ell with h0 | h0
        · subst h0; simp at thin
        · exact Nat.mul_pos hM h0
      omega
    have hyin : y ∈ siteBox z (12 * bigSide M ell 1) := by
      rw [mem_box_N hN]
      refine ⟨?_, ?_, ?_⟩
      · rw [hyv]; simpa [bigSide] using hy0box
      · rw [hy1, show (z 1).val + N - (z 1).val = N by have := hlt z 1; omega, Nat.mod_self]; exact hpos
      · rw [hy2, show (z 2).val + N - (z 2).val = N by have := hlt z 2; omega, Nat.mod_self]; exact hpos
    have hy := hsub hyin
    have hyOm : y ∈ (tw2 L P0 Q0 P1 Q1 P0' Q0' P1' Q1').Om 1 := by
      rcases hy with hy | hy
      · exact hy.1
      · exact absurd hy.1 (tw2_omHi 2 le_rfl y)
    rw [tw2_om1, hyv] at hyOm
    have hyc : y0 = P1' - 1 ∨ y0 = Q1' := by rw [← hY]; split_ifs <;> simp
    rcases hyOm with h | h
    · omega
    · exact hy0out h

#print axioms perCube_update
#print axioms perCube_one
#print axioms negOne_ne_one
#print axioms hol_update_negOne
#print axioms tw2_uncovered

end AdalyFormal.NoCover
