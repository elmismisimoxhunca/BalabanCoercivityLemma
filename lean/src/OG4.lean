import OG3
import PP5

/-!
# OG4 -- `regime_of_virtual` (lane m2_onegap_20261015)

The analogue of `M2Bridge.regime_of_class` for a VIRTUAL cube: a box `siteBox z s` carrying a gauge `g` and a field `A` with `CubeData` at index `i`
(`U^g = exp(iηA)` on its bonds) and the stratum window `bstrat ≤ i + 1` on its bonds -- the only property of a class cube the cut-off lemmas use.
Conclusion as `regime_of_class`: a global `M1Regular` configuration `V` at constant `ℓ³·2α₀`, equal to `U^g` on the bonds based in the core.
-/
set_option autoImplicit false
set_option maxHeartbeats 16000000
set_option maxRecDepth 8000
namespace AdalyFormal.OneGap

open AdalyFormal.M2Bridge
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane AdalyFormal.StatementLane2
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
open AdalyFormal.Balaban.RMapLipschitz (frobNorm)
open AdalyFormal.M1 (M1Bounds M1Regular bstrat)

variable {L : PeriodicLatticeExtent}

theorem m1Regular12_Vcfg {ell M f k : ℕ} {S : Tower L} {α₀' η : ℝ} {B : Bond L → M2m}
    (hB : AdalyFormal.OneGap12.M1Bounds12 S ell M f k α₀' η B) :
    AdalyFormal.OneGap12.M1Regular12 ell M f k S α₀' η (Vcfg η B hB.1) := by
  refine ⟨fun _ => 1, B, fun e => ?_, hB⟩
  rw [gauge_one']
  rfl

theorem regime_of_virtual {ell M R f k i s : ℕ} {S : Tower L} {α₀ η : ℝ} (hA : Admissible ell M R k S)
    (hell : 1 ≤ ell) (hf : 1 ≤ f) (hM : 1 ≤ M) (hα : 0 < α₀) (hη : 0 < η) {U : LinkCfg L} {z : PeriodicLatticeSite L}
    (hL : ∀ σ, 1 ≤ L σ) {w : ℕ} (hw : 64 * ell ^ i ≤ w) (hs7 : 7 ≤ s)
    (g : PeriodicLatticeSite L → Matrix.specialUnitaryGroup (Fin 2) ℂ) (A : Bond L → M2m)
    (hd : CubeData12 ell M f α₀ η (siteBox z s) i A)
    (hwin : ∀ e : Bond L, CubeBond (siteBox z s) e → bstrat S k e ≤ i + 1)
    (hexp : ∀ e : Bond L, CubeBond (siteBox z s) e →
      ((periodicGaugeTransform g U e : Matrix.specialUnitaryGroup (Fin 2) ℂ) : M2m)
        = NormedSpace.exp (((η : ℂ) * Complex.I) • A e)) :
    ∃ (χ : PeriodicLatticeSite L → ℝ) (V : LinkCfg L),
      AdalyFormal.OneGap12.M1Regular12 ell M f k S ((ell : ℝ) ^ 3 * (2 * α₀)) η V ∧
      (∀ x, 0 ≤ χ x ∧ χ x ≤ 1) ∧
      (∀ x, χ x ≠ 0 → ∀ y, pdist x y ≤ 6 → y ∈ siteBox z s) ∧
      (∀ x, (∀ σ, s ≤ L σ + 1 → 2 * w + 4 ≤ offc z x σ ∧ offc z x σ + 2 * w + 5 ≤ s) → χ x = 1) ∧
      (∀ e : Bond L, CubeBond (siteBox z s) e → χ e.1 = 1 → V e = periodicGaugeTransform g U e) := by
  have hE1 : 1 ≤ ell ^ i := Nat.one_le_pow _ _ hell
  have hw1 : 1 ≤ w := le_trans (by omega) hw
  have hcut := cutoff_spec z hw1 hs7 hL
  have hwR : (64 : ℝ) * (ell : ℝ) ^ i ≤ w := by exact_mod_cast hw
  have hE1R : (1 : ℝ) ≤ (ell : ℝ) ^ i := by exact_mod_cast hE1
  have hwpos : (0 : ℝ) < w := by exact_mod_cast hw1
  have h1 : 64 * (1 / (w : ℝ)) * (ell : ℝ) ^ i ≤ 1 := by
    rw [show 64 * (1 / (w : ℝ)) * (ell : ℝ) ^ i = (64 * (ell : ℝ) ^ i) / w by ring, div_le_one hwpos]
    exact hwR
  have hB := vcutA_M1Bounds12 hA hell hf hM hα hη hwin hd hcut h1
  refine ⟨chi z (cutFam s w L), Vcfg η (cutA (chi z (cutFam s w L)) A) hB.1,
    m1Regular12_Vcfg hB, fun x => ⟨hcut.nonneg x, hcut.le_one x⟩, hcut.supp, ?_, ?_⟩
  · intro x hx
    exact cutoff_core z hw1 hs7 hL x hx
  · intro e he hχ
    apply Subtype.ext
    rw [Vcfg_coe]
    unfold cutA
    rw [hχ, one_smul]
    exact (hexp e he).symm

end AdalyFormal.OneGap

#print axioms AdalyFormal.OneGap.regime_of_virtual
