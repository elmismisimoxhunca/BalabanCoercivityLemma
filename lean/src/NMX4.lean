import NMX3
import MXQ_Br

/-!
# NMX4 -- `headline_regime_nonvacuousMixed` and the instance corollaries (lane nonvac_mixed_20261017)

GENERATED from tools/NMX4.template by tools/gen_nmx4.py (the witness-list text is the same string in every theorem).

`headline_regime_nonvacuousMixed`: for `ell ≥ 2`, `m ≥ 1`, `R ≥ 1`, `a₀ > 0`, every bounded set `Φ` of factors `≥ 10`, factors `f₁ ≠ f₂` in `Φ` and `q ≥ R`
with `f₁ ≤ w < f₂` (`w = R + ell q`): `2 ≤ k` (the witness has `k = 2`), a proper three-stratum tower, `Λ ≠ ∅`, a curved non-pure-gauge `U`, a nonzero `B̃ ∈ Λ̃`,
per-cube smallness at every `f ∈ Φ`, `ClassCoupledΦ`, no wrap-around, and the mixed block: the factors that cover `Ω₀` alone are exactly those `≤ w`;
`f₁` covers (sites and plaquettes), `f₂` does not, `f₂`-cubes occur.
`headline_regime_nonvacuousMixed_gap`: the same for every pair with `max f₁ (R (1+ell)) + ell ≤ f₂` (the `q` is produced).
`headline_instance_inequalityMixed`: with the constants of the proved `MXP.Total.p428Target8Mixed` (chosen before `Φ, m, R`): `WellDefG` and `γ₀ ‖B̃‖² ≤ genForm (C B̃)` on the witness.
`headline_instance_inequalityFamily`: the same through `MXQ.Total.p428Target8Family` with the family `famPhi Φ`.
-/
set_option autoImplicit false
set_option maxRecDepth 8000
set_option maxHeartbeats 64000000

namespace AdalyFormal.NonVacMix

open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLane2
open AdalyFormal.StatementLaneG
open AdalyFormal.NonVacC
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
open AdalyFormal.Balaban.RegularUPerturbation (bondEnergy)

/-- every `f₂ ≥ max f₁ (R (1+ell)) + ell` leaves room for a width `w = R + ell q` with `q ≥ R` and `f₁ ≤ w < f₂`. -/
theorem exists_q {ell R f₁ f₂ : ℕ} (hell : 2 ≤ ell) (hR : 1 ≤ R) (hf : max f₁ (R * (1 + ell)) + ell ≤ f₂) :
    ∃ q : ℕ, R ≤ q ∧ f₁ ≤ R + ell * q ∧ R + ell * q < f₂ := by
  obtain ⟨L, hL⟩ : ∃ L, L = max f₁ (R * (1 + ell)) := ⟨_, rfl⟩
  have hL1 : f₁ ≤ L := by rw [hL]; exact le_max_left _ _
  have hL2 : R * (1 + ell) ≤ L := by rw [hL]; exact le_max_right _ _
  have hell0 : 0 < ell := by omega
  have hRe : R * (1 + ell) = R + R * ell := by ring
  obtain ⟨q, hq⟩ : ∃ q, q = (L - R + ell - 1) / ell := ⟨_, rfl⟩
  have h1 := Nat.div_add_mod (L - R + ell - 1) ell
  have h2 := Nat.mod_lt (L - R + ell - 1) hell0
  rw [← hq] at h1
  have hq1 : L - R ≤ ell * q := by omega
  have hq2 : ell * q ≤ L - R + ell - 1 := by omega
  refine ⟨q, ?_, by omega, by omega⟩
  by_contra hlt
  push Not at hlt
  have h3 : ell * q < ell * R := Nat.mul_lt_mul_of_pos_left hlt hell0
  have h4 := mul_comm ell R
  omega

theorem headline_regime_nonvacuousMixed {ell m R q f₁ f₂ F : ℕ} {Φ : Set ℕ} (hell : 2 ≤ ell) (hm : 1 ≤ m) (hR : 1 ≤ R)
    {a₀ : ℝ} (ha₀ : 0 < a₀)
    (hΦ : ∀ f ∈ Φ, 10 ≤ f ∧ f ≤ F) (hf₁ : f₁ ∈ Φ) (hf₂ : f₂ ∈ Φ)
    (hq : R ≤ q) (h1w : f₁ ≤ R + ell * q) (hwf2 : R + ell * q < f₂) :
    ∃ (k : ℕ) (Lu : PeriodicLatticeExtent) (S : Tower (scaleUp ell k Lu)) (Lam : Set (PeriodicLatticeSite Lu))
      (U : LinkCfg (scaleUp ell k Lu)) (α₀ : ℝ) (Bt : Bond Lu → SuTwo),
      2 ≤ k ∧ TorusOK ell (ell ^ m) Lu ∧ Admissible ell (ell ^ m) R k S ∧ LambdaOK2 ell (ell ^ m) R k S Lam ∧
      0 < α₀ ∧ (∀ f ∈ Φ, (f : ℝ) * ((ell ^ m : ℕ) : ℝ) * α₀ ≤ a₀) ∧
      MXP.AllC.ClassCoupledΦ ell (ell ^ m) Φ k S α₀ ((ell : ℝ) ^ k)⁻¹ U ∧
      (∃ p, p ∈ towerBj S 0) ∧ (∃ p, p ∈ towerBj S 1) ∧ (∃ p, p ∈ towerBj S 2) ∧
      (∃ p, p ∉ S.Om 0) ∧
      (∃ z, z ∈ S.Om 2 ∧ periodicLatticeShift z 0 ∈ S.Om 2 ∧ plaq U z ≠ 1) ∧
      (¬ ∃ g : PeriodicLatticeSite (scaleUp ell k Lu) → G2, periodicGaugeTransform g U = fun _ => (1 : G2)) ∧
      Lam.Nonempty ∧ (LamPrime ell Lam).Nonempty ∧
      OnLambdaTildeIn Lam ell Bt ∧ OnLambdaT Lam Bt ∧ 0 < bondEnergy Bt ∧ Bt ≠ 0 ∧
      (∀ f ∈ Φ, ∀ j : ℕ, j ≤ k → ∀ μ : Fin 3, 6 * (f * bigSide (ell ^ m) ell j) ≤ scaleUp ell k Lu μ + 1) ∧
      (∀ f ∈ Φ, ∀ (sites : Set (PeriodicLatticeSite (scaleUp ell k Lu))) (j : ℕ),
        IsClassCube ell (ell ^ m) f k S sites j → ∃ x, x ∉ sites) ∧
      (∀ g : ℕ, 2 ≤ g → (CoversOm0c ell (ell ^ m) g k S ↔ g ≤ R + ell * q)) ∧
      CoversOm0p ell (ell ^ m) f₁ k S ∧ ¬ CoversOm0c ell (ell ^ m) f₂ k S ∧ f₁ ≠ f₂ ∧
      (∃ x ∈ S.Om 0, ∃ (sites : Set (PeriodicLatticeSite (scaleUp ell k Lu))) (j : ℕ),
        IsClassCube ell (ell ^ m) f₂ k S sites j ∧ x ∈ sites) := by
  have hF : R + ell * q ≤ F := by have := (hΦ f₂ hf₂).2; omega
  have hF1 : 1 ≤ F := by have := (hΦ f₁ hf₁).1; have := (hΦ f₁ hf₁).2; omega
  exact nonvac_core_mix (T := F) hell (dvd_pow_self ell (by omega)) (pow_pos (by omega) m) hR hq hF1 hF hΦ hf₁ hf₂ h1w hwf2 ha₀

theorem headline_regime_nonvacuousMixed_gap {ell m R f₁ f₂ F : ℕ} {Φ : Set ℕ} (hell : 2 ≤ ell) (hm : 1 ≤ m) (hR : 1 ≤ R)
    {a₀ : ℝ} (ha₀ : 0 < a₀)
    (hΦ : ∀ f ∈ Φ, 10 ≤ f ∧ f ≤ F) (hf₁ : f₁ ∈ Φ) (hf₂ : f₂ ∈ Φ)
    (hgap : max f₁ (R * (1 + ell)) + ell ≤ f₂) :
    ∃ q : ℕ, R ≤ q ∧ f₁ ≤ R + ell * q ∧ R + ell * q < f₂ ∧
    ∃ (k : ℕ) (Lu : PeriodicLatticeExtent) (S : Tower (scaleUp ell k Lu)) (Lam : Set (PeriodicLatticeSite Lu))
      (U : LinkCfg (scaleUp ell k Lu)) (α₀ : ℝ) (Bt : Bond Lu → SuTwo),
      2 ≤ k ∧ TorusOK ell (ell ^ m) Lu ∧ Admissible ell (ell ^ m) R k S ∧ LambdaOK2 ell (ell ^ m) R k S Lam ∧
      0 < α₀ ∧ (∀ f ∈ Φ, (f : ℝ) * ((ell ^ m : ℕ) : ℝ) * α₀ ≤ a₀) ∧
      MXP.AllC.ClassCoupledΦ ell (ell ^ m) Φ k S α₀ ((ell : ℝ) ^ k)⁻¹ U ∧
      (∃ p, p ∈ towerBj S 0) ∧ (∃ p, p ∈ towerBj S 1) ∧ (∃ p, p ∈ towerBj S 2) ∧
      (∃ p, p ∉ S.Om 0) ∧
      (∃ z, z ∈ S.Om 2 ∧ periodicLatticeShift z 0 ∈ S.Om 2 ∧ plaq U z ≠ 1) ∧
      (¬ ∃ g : PeriodicLatticeSite (scaleUp ell k Lu) → G2, periodicGaugeTransform g U = fun _ => (1 : G2)) ∧
      Lam.Nonempty ∧ (LamPrime ell Lam).Nonempty ∧
      OnLambdaTildeIn Lam ell Bt ∧ OnLambdaT Lam Bt ∧ 0 < bondEnergy Bt ∧ Bt ≠ 0 ∧
      (∀ f ∈ Φ, ∀ j : ℕ, j ≤ k → ∀ μ : Fin 3, 6 * (f * bigSide (ell ^ m) ell j) ≤ scaleUp ell k Lu μ + 1) ∧
      (∀ f ∈ Φ, ∀ (sites : Set (PeriodicLatticeSite (scaleUp ell k Lu))) (j : ℕ),
        IsClassCube ell (ell ^ m) f k S sites j → ∃ x, x ∉ sites) ∧
      (∀ g : ℕ, 2 ≤ g → (CoversOm0c ell (ell ^ m) g k S ↔ g ≤ R + ell * q)) ∧
      CoversOm0p ell (ell ^ m) f₁ k S ∧ ¬ CoversOm0c ell (ell ^ m) f₂ k S ∧ f₁ ≠ f₂ ∧
      (∃ x ∈ S.Om 0, ∃ (sites : Set (PeriodicLatticeSite (scaleUp ell k Lu))) (j : ℕ),
        IsClassCube ell (ell ^ m) f₂ k S sites j ∧ x ∈ sites) := by
  obtain ⟨q, hq, h1w, hwf2⟩ := exists_q (f₁ := f₁) (f₂ := f₂) hell hR hgap
  exact ⟨q, hq, h1w, hwf2, headline_regime_nonvacuousMixed hell hm hR ha₀ hΦ hf₁ hf₂ hq h1w hwf2⟩

theorem headline_instance_inequalityMixed (ell : ℕ) (hell : 2 ≤ ell) (a : ℝ) (ha : 0 < a) :
    ∃ m₁ : ℕ, 1 ≤ m₁ ∧ ∃ R₁ : ℕ, ∃ (a₀ γ₀ : ℝ), 0 < a₀ ∧ 0 < γ₀ ∧
      ∀ (Φ : Set ℕ) (F f₁ f₂ q : ℕ), (∀ f ∈ Φ, 10 ≤ f ∧ f ≤ F) → f₁ ∈ Φ → f₂ ∈ Φ →
      ∀ m : ℕ, m₁ ≤ m → ∀ R : ℕ, max R₁ 1 ≤ R → R ≤ q → f₁ ≤ R + ell * q → R + ell * q < f₂ →
      ∃ (k : ℕ) (Lu : PeriodicLatticeExtent) (S : Tower (scaleUp ell k Lu)) (Lam : Set (PeriodicLatticeSite Lu))
      (U : LinkCfg (scaleUp ell k Lu)) (α₀ : ℝ) (Bt : Bond Lu → SuTwo),
      2 ≤ k ∧ TorusOK ell (ell ^ m) Lu ∧ Admissible ell (ell ^ m) R k S ∧ LambdaOK2 ell (ell ^ m) R k S Lam ∧
      0 < α₀ ∧ (∀ f ∈ Φ, (f : ℝ) * ((ell ^ m : ℕ) : ℝ) * α₀ ≤ a₀) ∧
      MXP.AllC.ClassCoupledΦ ell (ell ^ m) Φ k S α₀ ((ell : ℝ) ^ k)⁻¹ U ∧
      (∃ p, p ∈ towerBj S 0) ∧ (∃ p, p ∈ towerBj S 1) ∧ (∃ p, p ∈ towerBj S 2) ∧
      (∃ p, p ∉ S.Om 0) ∧
      (∃ z, z ∈ S.Om 2 ∧ periodicLatticeShift z 0 ∈ S.Om 2 ∧ plaq U z ≠ 1) ∧
      (¬ ∃ g : PeriodicLatticeSite (scaleUp ell k Lu) → G2, periodicGaugeTransform g U = fun _ => (1 : G2)) ∧
      Lam.Nonempty ∧ (LamPrime ell Lam).Nonempty ∧
      OnLambdaTildeIn Lam ell Bt ∧ OnLambdaT Lam Bt ∧ 0 < bondEnergy Bt ∧ Bt ≠ 0 ∧
      (∀ f ∈ Φ, ∀ j : ℕ, j ≤ k → ∀ μ : Fin 3, 6 * (f * bigSide (ell ^ m) ell j) ≤ scaleUp ell k Lu μ + 1) ∧
      (∀ f ∈ Φ, ∀ (sites : Set (PeriodicLatticeSite (scaleUp ell k Lu))) (j : ℕ),
        IsClassCube ell (ell ^ m) f k S sites j → ∃ x, x ∉ sites) ∧
      (∀ g : ℕ, 2 ≤ g → (CoversOm0c ell (ell ^ m) g k S ↔ g ≤ R + ell * q)) ∧
      CoversOm0p ell (ell ^ m) f₁ k S ∧ ¬ CoversOm0c ell (ell ^ m) f₂ k S ∧ f₁ ≠ f₂ ∧
      (∃ x ∈ S.Om 0, ∃ (sites : Set (PeriodicLatticeSite (scaleUp ell k Lu))) (j : ℕ),
        IsClassCube ell (ell ^ m) f₂ k S sites j ∧ x ∈ sites) ∧
        GenP.WellDefG (gparams ell k Lu (by omega) S U a Lam) ∧
        γ₀ * bondEnergy Bt ≤
          GenP.genForm (gparams ell k Lu (by omega) S U a Lam)
            (WithLp.toLp 2 (GenP.genC (gparams ell k Lu (by omega) S U a Lam) Bt)) := by
  obtain ⟨m₁, hm₁, R₁, a₀, ha₀, γ₀, hγ₀, hU⟩ := MXP.Total.p428Target8Mixed ell hell a ha
  refine ⟨m₁, hm₁, R₁, a₀, γ₀, ha₀, hγ₀, fun Φ F f₁ f₂ q hΦ hf₁ hf₂ m hm R hR hqR h1w hwf2 => ?_⟩
  obtain ⟨k, Lu, S, Lam, U, α₀, Bt, hk, hT, hA, hL, hα, hαS, hCC, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18⟩ :=
    headline_regime_nonvacuousMixed (m := m) hell (le_trans hm₁ hm) (le_trans (le_max_right _ _) hR) ha₀ hΦ hf₁ hf₂ hqR h1w hwf2
  have hmain := hU Φ (fun f hf => (hΦ f hf).1) m hm R (le_trans (le_max_left _ _) hR) k (by omega) Lu α₀ hα hαS hT S hA Lam hL U hCC
  exact ⟨k, Lu, S, Lam, U, α₀, Bt, hk, hT, hA, hL, hα, hαS, hCC, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18,
    hmain.1, hmain.2 Bt h8 h9⟩

theorem headline_instance_inequalityFamily (ell : ℕ) (hell : 2 ≤ ell) (a : ℝ) (ha : 0 < a) :
    ∃ m₁ : ℕ, 1 ≤ m₁ ∧ ∃ R₁ : ℕ, ∃ (a₀ γ₀ : ℝ), 0 < a₀ ∧ 0 < γ₀ ∧
      ∀ (Φ : Set ℕ) (F f₁ f₂ q : ℕ), (∀ f ∈ Φ, 10 ≤ f ∧ f ≤ F) → f₁ ∈ Φ → f₂ ∈ Φ →
      ∀ m : ℕ, m₁ ≤ m → ∀ R : ℕ, max R₁ 1 ≤ R → R ≤ q → f₁ ≤ R + ell * q → R + ell * q < f₂ →
      ∃ (k : ℕ) (Lu : PeriodicLatticeExtent) (S : Tower (scaleUp ell k Lu)) (Lam : Set (PeriodicLatticeSite Lu))
      (U : LinkCfg (scaleUp ell k Lu)) (α₀ : ℝ) (Bt : Bond Lu → SuTwo),
      2 ≤ k ∧ TorusOK ell (ell ^ m) Lu ∧ Admissible ell (ell ^ m) R k S ∧ LambdaOK2 ell (ell ^ m) R k S Lam ∧
      0 < α₀ ∧ (∀ f ∈ Φ, (f : ℝ) * ((ell ^ m : ℕ) : ℝ) * α₀ ≤ a₀) ∧
      MXP.AllC.ClassCoupledΦ ell (ell ^ m) Φ k S α₀ ((ell : ℝ) ^ k)⁻¹ U ∧
      (∃ p, p ∈ towerBj S 0) ∧ (∃ p, p ∈ towerBj S 1) ∧ (∃ p, p ∈ towerBj S 2) ∧
      (∃ p, p ∉ S.Om 0) ∧
      (∃ z, z ∈ S.Om 2 ∧ periodicLatticeShift z 0 ∈ S.Om 2 ∧ plaq U z ≠ 1) ∧
      (¬ ∃ g : PeriodicLatticeSite (scaleUp ell k Lu) → G2, periodicGaugeTransform g U = fun _ => (1 : G2)) ∧
      Lam.Nonempty ∧ (LamPrime ell Lam).Nonempty ∧
      OnLambdaTildeIn Lam ell Bt ∧ OnLambdaT Lam Bt ∧ 0 < bondEnergy Bt ∧ Bt ≠ 0 ∧
      (∀ f ∈ Φ, ∀ j : ℕ, j ≤ k → ∀ μ : Fin 3, 6 * (f * bigSide (ell ^ m) ell j) ≤ scaleUp ell k Lu μ + 1) ∧
      (∀ f ∈ Φ, ∀ (sites : Set (PeriodicLatticeSite (scaleUp ell k Lu))) (j : ℕ),
        IsClassCube ell (ell ^ m) f k S sites j → ∃ x, x ∉ sites) ∧
      (∀ g : ℕ, 2 ≤ g → (CoversOm0c ell (ell ^ m) g k S ↔ g ≤ R + ell * q)) ∧
      CoversOm0p ell (ell ^ m) f₁ k S ∧ ¬ CoversOm0c ell (ell ^ m) f₂ k S ∧ f₁ ≠ f₂ ∧
      (∃ x ∈ S.Om 0, ∃ (sites : Set (PeriodicLatticeSite (scaleUp ell k Lu))) (j : ℕ),
        IsClassCube ell (ell ^ m) f₂ k S sites j ∧ x ∈ sites) ∧
        MXQ.AllC.ClassCoupledQ ell (ell ^ m) (MXQ.Total.famPhi Φ) k S α₀ ((ell : ℝ) ^ k)⁻¹ U ∧
        GenP.WellDefG (gparams ell k Lu (by omega) S U a Lam) ∧
        γ₀ * bondEnergy Bt ≤
          GenP.genForm (gparams ell k Lu (by omega) S U a Lam)
            (WithLp.toLp 2 (GenP.genC (gparams ell k Lu (by omega) S U a Lam) Bt)) := by
  obtain ⟨m₁, hm₁, R₁, a₀, ha₀, γ₀, hγ₀, hU⟩ := MXQ.Total.p428Target8Family ell hell a ha
  refine ⟨m₁, hm₁, R₁, a₀, γ₀, ha₀, hγ₀, fun Φ F f₁ f₂ q hΦ hf₁ hf₂ m hm R hR hqR h1w hwf2 => ?_⟩
  obtain ⟨k, Lu, S, Lam, U, α₀, Bt, hk, hT, hA, hL, hα, hαS, hCC, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18⟩ :=
    headline_regime_nonvacuousMixed (m := m) hell (le_trans hm₁ hm) (le_trans (le_max_right _ _) hR) ha₀ hΦ hf₁ hf₂ hqR h1w hwf2
  have hCQ := MXQ.Total.classCoupledΦ_toQ hCC
  have hmain := hU (MXQ.Total.famPhi Φ) ⟨fun _ _ _ f hm' => (hΦ f hm').1⟩ m hm R (le_trans (le_max_left _ _) hR) k (by omega) Lu α₀ hα
    (fun L s j f hm' => hαS f hm') hT S hA Lam hL U hCQ
  exact ⟨k, Lu, S, Lam, U, α₀, Bt, hk, hT, hA, hL, hα, hαS, hCC, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18,
    hCQ, hmain.1, hmain.2 Bt h8 h9⟩

end AdalyFormal.NonVacMix
