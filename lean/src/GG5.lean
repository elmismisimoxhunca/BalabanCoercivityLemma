import GG4

/-!
# GG5 -- class cubes as group-level charts; MR4 with a proportional interface constant (m2_glue2, 2026-10-15)

* `gchart_of_cube`: for every class cube (`IsClassCube … sites j`), `PerCubeRegular2 ell M f k S α₀ η U` gives a
  `GChart U g sites t₁ t₂` with `t₁ = fMα₀ ℓ^{-j}`, `t₂ = (1 + 4t₁)·fMα₀ ℓ^{-2j}` (when `t₁ + fMα₀ℓ^{-2j} ≤ 1`).
* `patchCoercive_class_prop`: MR4's `patchCoercive_class_exists` with the interface constant `a' = C·12Mα₀`
  (`1 ≤ C`, `C·12Mα₀ ≤ a₀`): this is the form in which a proportional `InterfaceCharts` composes.
No sorry / axiom.
-/
set_option autoImplicit false
set_option maxHeartbeats 8000000

namespace AdalyFormal.M2Glue2

open Matrix
open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.SuTwoLogExp (SU2 M2 su2Exp su2Log)
open AdalyFormal.Balaban.RMapLipschitz (frobNorm frobSq frobSq_nonneg)
open AdalyFormal.Balaban.Bch2 (IsSu2 frobNorm_add_le frobNorm_nonneg frobNorm_smul)
open scoped Matrix

variable {L : PeriodicLatticeExtent}

/-- the SU(2) element of a chart bond is `su2Exp (iηA)`. -/
theorem gauge_eq_su2Exp {G : SU2} {η : ℝ} {A : M2} (hA : AdalyFormal.StatementLane.HT A)
    (h : (G : M2) = NormedSpace.exp ((((η : ℂ) * Complex.I)) • A)) : G = su2Exp (chZ η A) := by
  apply Subtype.ext
  rw [coe_su2Exp (isSu2_chZ η hA), chZ, ← h]

/-- **class cube ⇒ group-level chart.** -/
theorem gchart_of_cube {ell M f k : ℕ} {S : AdalyFormal.StatementLane.Tower L} {α₀ η : ℝ} (hη : 0 < η)
    {U : LinkCfg L} (hP : AdalyFormal.StatementLane2.PerCubeRegular2 ell M f k S α₀ η U)
    {sites : Set (PeriodicLatticeSite L)} {j : ℕ} (hq : AdalyFormal.StatementLane.IsClassCube ell M f k S sites j)
    (hsm : (f : ℝ) * M * α₀ * ((ell : ℝ) ^ j)⁻¹ + (f : ℝ) * M * α₀ * (((ell : ℝ) ^ j)⁻¹) ^ 2 ≤ 1)
    (hell : 0 < ell) :
    ∃ g : PeriodicLatticeSite L → SU2, GChart U g sites ((f : ℝ) * M * α₀ * ((ell : ℝ) ^ j)⁻¹)
      ((1 + 4 * ((f : ℝ) * M * α₀ * ((ell : ℝ) ^ j)⁻¹)) * ((f : ℝ) * M * α₀ * (((ell : ℝ) ^ j)⁻¹) ^ 2)) := by
  obtain ⟨g, A, hA, hD, -⟩ := hP sites j hq
  refine ⟨g, ?_, ?_⟩
  · intro x ν hx hxν
    obtain ⟨hHT, hU, hb⟩ := hA (x, ν) ⟨hx, hxν⟩
    rw [gauge_eq_su2Exp hHT hU]
    refine (exp_sub_one_le (isSu2_chZ η hHT)).trans ?_
    rw [frobNorm_chZ hη.le]
    have hl : (0 : ℝ) < (ell : ℝ) ^ j := by positivity
    have := mul_lt_mul_of_pos_left hb hη
    rw [pow_one, mul_inv, show η * ((f : ℝ) * M * α₀ * (((ell : ℝ) ^ j)⁻¹ * η⁻¹))
      = (f : ℝ) * M * α₀ * ((ell : ℝ) ^ j)⁻¹ * (η * η⁻¹) by ring, mul_inv_cancel₀ hη.ne', mul_one] at this
    exact this.le
  · intro x μ ν hx hxν hxμ hxμν
    obtain ⟨hHT0, hU0, hb0⟩ := hA (x, ν) ⟨hx, hxν⟩
    obtain ⟨hHT1, hU1, hb1⟩ := hA (periodicLatticeShift x μ, ν) ⟨hxμ, hxμν⟩
    have hd := hD μ ν x ⟨hx, hxν⟩ ⟨hxμ, hxμν⟩
    rw [gauge_eq_su2Exp hHT0 hU0, gauge_eq_su2Exp hHT1 hU1]
    set c1 : ℝ := (f : ℝ) * M * α₀ * ((ell : ℝ) ^ j)⁻¹ with hc1
    set c2 : ℝ := (f : ℝ) * M * α₀ * (((ell : ℝ) ^ j)⁻¹) ^ 2 with hc2
    have hl : (0 : ℝ) < (ell : ℝ) ^ j := by positivity
    have hZ0 : frobNorm (chZ η (A (x, ν))) ≤ c1 := by
      rw [frobNorm_chZ hη.le]
      have := mul_lt_mul_of_pos_left hb0 hη
      rw [pow_one, mul_inv, show η * ((f : ℝ) * M * α₀ * (((ell : ℝ) ^ j)⁻¹ * η⁻¹))
        = (f : ℝ) * M * α₀ * ((ell : ℝ) ^ j)⁻¹ * (η * η⁻¹) by ring, mul_inv_cancel₀ hη.ne', mul_one] at this
      exact this.le
    have hZd : frobNorm (chZ η (A (periodicLatticeShift x μ, ν)) - chZ η (A (x, ν))) ≤ c2 := by
      rw [chZ_sub, frobNorm_chZ hη.le]
      rw [frobNorm_smul, abs_of_pos (inv_pos.mpr hη)] at hd
      have := mul_lt_mul_of_pos_left hd (mul_pos hη hη)
      have e : η * η * (η⁻¹ * frobNorm (A (periodicLatticeShift x μ, ν) - A (x, ν)))
          = η * frobNorm (A (periodicLatticeShift x μ, ν) - A (x, ν)) := by field_simp
      rw [e, mul_inv, show η * η * ((f : ℝ) * M * α₀ * (((ell : ℝ) ^ j)⁻¹ * η⁻¹) ^ 2)
        = (f : ℝ) * M * α₀ * (((ell : ℝ) ^ j)⁻¹) ^ 2 * ((η * η⁻¹) ^ 2) by ring, mul_inv_cancel₀ hη.ne',
        one_pow, mul_one] at this
      exact this.le
    have hsm' : frobNorm (chZ η (A (x, ν))) + frobNorm (chZ η (A (periodicLatticeShift x μ, ν)) - chZ η (A (x, ν)))
        ≤ 1 := by linarith
    refine (exp_lip (isSu2_chZ η hHT0) (isSu2_chZ η hHT1) hsm').trans ?_
    have := frobNorm_nonneg (chZ η (A (periodicLatticeShift x μ, ν)) - chZ η (A (x, ν)))
    have : 0 ≤ 1 + 4 * frobNorm (chZ η (A (x, ν))) := by have := frobNorm_nonneg (chZ η (A (x, ν))); linarith
    calc (1 + 4 * frobNorm (chZ η (A (x, ν)))) * frobNorm (chZ η (A (periodicLatticeShift x μ, ν)) - chZ η (A (x, ν)))
        ≤ (1 + 4 * c1) * c2 :=
          mul_le_mul (by linarith) hZd (frobNorm_nonneg _)
            (by have := frobNorm_nonneg (chZ η (A (x, ν))); linarith)
      _ = _ := rfl

/-- **MR4 with a proportional interface constant.** -/
theorem patchCoercive_class_prop {ell : ℕ} (hell : 2 ≤ ell) {a : ℝ} (ha : 0 < a) :
    ∃ cW : ℝ, 0 < cW ∧ ∃ a₀ : ℝ, 0 < a₀ ∧ ∃ D : ℕ, 12 * ell + 10 ≤ D ∧
    (∀ d, D ≤ d → AdalyFormal.M1NonFlat.epsNF ell (AdalyFormal.M1NonFlat.PkA a) (AdalyFormal.M1NonFlat.thetaN ell) d
      ≤ cW / 2) ∧
    ∀ {M R k : ℕ} {Lu : PeriodicLatticeExtent} (hell0 : 0 < ell)
      {S : AdalyFormal.StatementLane.Tower (AdalyFormal.StatementLane.scaleUp ell k Lu)}
      (_hS : AdalyFormal.StatementLane.Admissible ell M R k S) (_hM : 0 < M) (_hR1 : 1 ≤ R)
      (_hR24 : 24 ≤ R) (_hRl : 3 * 12 ≤ R * ell)
      (_hR4 : (5 + 4) * 1 * ell ≤ R) (_hroom : 17 * ell ≤ R * M) {d : ℕ} (_hdD : D ≤ d)
      (_hdM : d + 64 * ell ^ 2 + 2 ≤ M)
      {W : ℕ} (_hW : 1 ≤ W) (_hWR : W ≤ R * M * ell)
      (U : LinkCfg (AdalyFormal.StatementLane.scaleUp ell k Lu)) (cs : ℝ) (Lam : Set (PeriodicLatticeSite Lu))
      (_hp : AdalyFormal.M1IMS.HatPack (ell := ell) (k := k) (S := S) (W := W) U a cs)
      (ρ : ℝ) (_hρ : 0 ≤ ρ) (_hreg : AdalyFormal.M1IMS.HolRegime S ell k U ρ) (ε1 : ℝ) (_hε1 : 0 < ε1)
      (_hη : AdalyFormal.M1IMS.etaC ell W cs ρ ε1 < 1)
      (η : ℝ) (_hη0 : 0 < η) (α₀ : ℝ) (_hα0 : 0 < α₀)
      (_hP : AdalyFormal.StatementLane2.PerCubeRegular2 ell M 12 k S α₀ η U)
      (C : ℝ) (_hC : 1 ≤ C) (_hCa : C * (((12 : ℕ) : ℝ) * M * α₀) ≤ a₀)
      (_hI : AdalyFormal.M2Route.InterfaceCharts ell M k d S U η (C * (((12 : ℕ) : ℝ) * M * α₀))),
      AdalyFormal.M1IMS.PatchCoercive ell M k 1 5 Lu hell0 S U a Lam
        ((1 - AdalyFormal.M1IMS.etaC ell W cs ρ ε1) * min a (cW - AdalyFormal.M1NonFlat.epsNF ell
          (AdalyFormal.M1NonFlat.PkA a) (AdalyFormal.M1NonFlat.thetaN ell) d)
          - 2 * AdalyFormal.M1IMS.nuC ell ρ) := by
  obtain ⟨cW, hcW, a₀, ha₀, D, hD, hDle, hmain⟩ := AdalyFormal.M2Route.patchCoercive_class_exists hell ha
  refine ⟨cW, hcW, a₀, ha₀, D, hD, hDle, ?_⟩
  intro M R k Lu hell0 S hS hM hR1 hR24 hRl hR4 hroom d hdD hdM W hW hWR U cs Lam hp ρ hρ hreg ε1 hε1 hη η hη0 α₀
    hα0 hP C hC hCa hI
  have h12 : (0 : ℝ) ≤ ((12 : ℕ) : ℝ) * M * α₀ := by positivity
  exact hmain hell0 hS hM hR1 hR24 hRl hR4 hroom hdD hdM hW hWR U cs Lam hp ρ hρ hreg ε1 hε1 hη η hη0 α₀ hα0 hP
    _ (by nlinarith) hCa hI

end AdalyFormal.M2Glue2
