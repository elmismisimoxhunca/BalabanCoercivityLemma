import M2B6e
import AdalyFormal.Balaban.BlockedGaugeGuardAlgebraExp

/-!
# M2B7 -- the cut-off configuration `V = exp(i η χ A)` and the class-to-regime bridge (m2_bridge_20261014, Layer B1/B5)

* `expHT_mem` : `exp(i t X) ∈ SU(2)` for `X` Hermitian traceless; `Vcfg η B hB` : the link configuration `exp(i η B)`.
* `m1Regular_Vcfg` : if `B` satisfies lane B's `M1Bounds` then `Vcfg` satisfies `M1Regular` (gauge `g ≡ 1`).
* **`regime_of_class`** (the corner `z` of the cube `sites = siteBox z (f·M·ell^i)` is an input) : for a class cube (`IsClassCube`, factor `f`, index `i`) on which `PerCubeRegular2` holds at `α₀`, and `w ≥ 64 ell^i`, there is a
  link configuration `V` on the WHOLE torus (any torus: the cube may be wider than the torus in some directions) with `M1Regular ell M f k S (ell³·2α₀) η V` (ONE global gauge, lane B's stratum-weighted regime),
  a cutoff `χ` with `0 ≤ χ ≤ 1`, supported `6` inside the cube, equal to `1` on the core `{x | ∀ σ narrow, 2w+4 ≤ offc z x σ ∧ offc z x σ + 2w+5 ≤ s}` (`σ` narrow: `s ≤ L σ + 1`; in a WIDE coordinate the cube wraps and no cutoff is used),
  and `V = U^g` (the cube gauge) on every cube bond whose base has `χ = 1`.
No sorry / native_decide / axiom.
-/
set_option autoImplicit false
set_option maxHeartbeats 16000000

namespace AdalyFormal.M2Bridge

open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane AdalyFormal.StatementLane2
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
open AdalyFormal.Balaban.RMapLipschitz (frobNorm)
open AdalyFormal.M1 (M1Bounds M1Regular)

open scoped Matrix

variable {L : PeriodicLatticeExtent}

theorem expHT_mem (t : ℝ) {X : M2m} (hX : HT X) :
    NormedSpace.exp (((t : ℂ) * Complex.I) • X) ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ := by
  obtain ⟨h1, h2⟩ := hX
  set Y : M2m := ((t : ℂ) * Complex.I) • X with hY
  have hYh : Yᴴ = -Y := by
    rw [hY, Matrix.conjTranspose_smul, h1]
    have : star ((t : ℂ) * Complex.I) = -((t : ℂ) * Complex.I) := by
      simp [star_mul']
    rw [this, neg_smul]
  have htr : Matrix.trace Y = 0 := by rw [hY, Matrix.trace_smul, h2]; simp
  exact AdalyFormal.Balaban.SuTwoLogExp.exp_antiHerm_traceless_mem_special hYh htr

/-- the link configuration `exp(i η B)`. -/
noncomputable def Vcfg (η : ℝ) (B : Bond L → M2m) (hB : ∀ e, HT (B e)) : LinkCfg L :=
  fun e => ⟨NormedSpace.exp (((η : ℂ) * Complex.I) • B e), expHT_mem η (hB e)⟩

theorem Vcfg_coe (η : ℝ) (B : Bond L → M2m) (hB : ∀ e, HT (B e)) (e : Bond L) :
    ((Vcfg η B hB e : Matrix.specialUnitaryGroup (Fin 2) ℂ) : M2m) = NormedSpace.exp (((η : ℂ) * Complex.I) • B e) := rfl

theorem gauge_one' (U : LinkCfg L) : periodicGaugeTransform (fun _ => (1 : Matrix.specialUnitaryGroup (Fin 2) ℂ)) U = U := by
  funext e; simp [periodicGaugeTransform]

theorem m1Regular_Vcfg {ell M f k : ℕ} {S : Tower L} {α₀' η : ℝ} {B : Bond L → M2m} (hB : M1Bounds S ell M f k α₀' η B) :
    M1Regular ell M f k S α₀' η (Vcfg η B hB.1) := by
  refine ⟨fun _ => 1, B, fun e => ?_, hB⟩
  rw [gauge_one']
  rfl

section bridge

variable {ell M R f k i : ℕ} {S : Tower L} {α₀ η : ℝ}

theorem regime_of_class (hA : Admissible ell M R k S) (hell : 1 ≤ ell) (hf : 1 ≤ f) (hM : 1 ≤ M)
    (hα : 0 < α₀) (hη : 0 < η) {U : LinkCfg L} (hP : PerCubeRegular2 ell M f k S α₀ η U)
    {sites : Set (PeriodicLatticeSite L)} (hq : IsClassCube ell M f k S sites i)
    {z : PeriodicLatticeSite L} (hz : sites = siteBox z (f * bigSide M ell i))
    (hL : ∀ σ, 1 ≤ L σ) {w : ℕ} (hw : 64 * ell ^ i ≤ w) (hs7 : 7 ≤ f * bigSide M ell i) :
    ∃ (g : PeriodicLatticeSite L → Matrix.specialUnitaryGroup (Fin 2) ℂ)
      (χ : PeriodicLatticeSite L → ℝ) (V : LinkCfg L),
      M1Regular ell M f k S ((ell : ℝ) ^ 3 * (2 * α₀)) η V ∧
      (∀ x, 0 ≤ χ x ∧ χ x ≤ 1) ∧
      (∀ x, χ x ≠ 0 → ∀ y, pdist x y ≤ 6 → y ∈ sites) ∧
      (∀ x, (∀ σ, f * bigSide M ell i ≤ L σ + 1 →
          2 * w + 4 ≤ offc z x σ ∧ offc z x σ + 2 * w + 5 ≤ f * bigSide M ell i) → χ x = 1) ∧
      (∀ e : Bond L, CubeBond sites e → χ e.1 = 1 → V e = periodicGaugeTransform g U e) := by
  obtain ⟨g, A, hc1, hc2, hc3⟩ := hP sites i hq
  have hd : CubeData ell M f k α₀ η sites i A :=
    ⟨fun e he => (hc1 e he).1, fun e he => (hc1 e he).2.2, hc2, hc3⟩
  have hE1 : 1 ≤ ell ^ i := Nat.one_le_pow _ _ hell
  have hw1 : 1 ≤ w := le_trans (by omega) hw
  have hcut := cutoff_spec z hw1 hs7 hL
  rw [← hz] at hcut
  have hwR : (64 : ℝ) * (ell : ℝ) ^ i ≤ w := by exact_mod_cast hw
  have hE1R : (1 : ℝ) ≤ (ell : ℝ) ^ i := by exact_mod_cast hE1
  have hwpos : (0 : ℝ) < w := by exact_mod_cast hw1
  have h1 : 64 * (1 / (w : ℝ)) * (ell : ℝ) ^ i ≤ 1 := by
    rw [show 64 * (1 / (w : ℝ)) * (ell : ℝ) ^ i = (64 * (ell : ℝ) ^ i) / w by ring, div_le_one hwpos]
    exact hwR
  have h2 : 24 * (2 / (w : ℝ) ^ 2 + (1 / (w : ℝ)) ^ 2) * ((ell : ℝ) ^ i) ^ 2 ≤ 1 := by
    have e : 24 * (2 / (w : ℝ) ^ 2 + (1 / (w : ℝ)) ^ 2) * ((ell : ℝ) ^ i) ^ 2 = (72 * ((ell : ℝ) ^ i) ^ 2) / (w : ℝ) ^ 2 := by
      field_simp; ring
    rw [e, div_le_one (by positivity)]
    nlinarith
  have hB := cutA_M1Bounds hA hell hf hM hα hη hq hd hcut h1 h2
  refine ⟨g, chi z (cutFam (f * bigSide M ell i) w L), Vcfg η (cutA (chi z (cutFam (f * bigSide M ell i) w L)) A) hB.1,
    m1Regular_Vcfg hB, fun x => ⟨hcut.nonneg x, hcut.le_one x⟩, hcut.supp, ?_, ?_⟩
  · intro x hx
    exact cutoff_core z hw1 hs7 hL x hx
  · intro e he hχ
    apply Subtype.ext
    rw [Vcfg_coe]
    unfold cutA
    rw [hχ, one_smul]
    exact ((hc1 e he).2.1).symm

end bridge

end AdalyFormal.M2Bridge
